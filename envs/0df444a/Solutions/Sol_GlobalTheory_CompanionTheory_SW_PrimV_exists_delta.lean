-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimV.exists_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:28:29.174377+00:00
-- url     : https://prove2.me/submissions/681d56b0-7189-460d-ad48-38268b8bb6c8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalPrimitiveVectorCompactRescale
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_basis_of_not_mem
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimV
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.PrimV
theorem _root_.solution [CharZero F] (h2 : Module.finrank F E = 2) :
    ∃ (b : Module.Basis (Fin 2) F E) (Δ : F), b 0 = 1 ∧ b 1 * b 1 = algebraMap F E Δ ∧ Δ ≠ 0 := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  obtain ⟨x, hx⟩ : ∃ x : E, x ∉ (algebraMap F E).range := by
    by_contra hcon
    push_neg at hcon
    have : (⊥ : Subalgebra F E) = ⊤ := by
      ext y
      simpa [Algebra.mem_bot] using hcon y
    have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 this
    omega
  obtain ⟨b0, h00, h01⟩ := basis_of_not_mem h2 hx
  have hxx : x * x = algebraMap F E (b0.repr (x * x) 0) + algebraMap F E (b0.repr (x * x) 1) * x := by
    have := b0.sum_repr (x * x)
    rw [Fin.sum_univ_two, h00, h01] at this
    simp only [Algebra.smul_def, mul_one] at this
    exact this.symm
  set q := b0.repr (x * x) 0
  set p := b0.repr (x * x) 1
  have hδ : x - algebraMap F E (p / 2) ∉ (algebraMap F E).range := by
    rintro ⟨c, hc⟩
    apply hx
    refine ⟨c + p / 2, ?_⟩
    rw [map_add, hc]
    ring
  obtain ⟨b, hb0, hb1⟩ := basis_of_not_mem h2 hδ
  have h2F : algebraMap F E 2 = 2 := map_ofNat _ 2
  have hsq : b 1 * b 1 = algebraMap F E (q + p / 2 * (p / 2)) := by
    have hp2 : algebraMap F E p = 2 * algebraMap F E (p / 2) := by
      rw [← h2F, ← map_mul]
      congr 1
      ring
    rw [hb1, map_add, map_mul]
    linear_combination hxx + x * hp2
  refine ⟨b, q + p / 2 * (p / 2), hb0, hsq, fun h0 => ?_⟩
  rw [h0, map_zero, hb1] at hsq
  have : x - algebraMap F E (p / 2) = 0 := mul_self_eq_zero.1 hsq
  exact hδ ⟨0, by rw [this, map_zero]⟩
end GlobalTheory.CompanionTheory.SW.PrimV
