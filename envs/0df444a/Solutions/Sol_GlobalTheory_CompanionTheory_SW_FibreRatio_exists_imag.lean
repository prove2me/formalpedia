-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FibreRatio.exists_imag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:12:29.942488+00:00
-- url     : https://prove2.me/submissions/6648e52f-fb66-4e53-82c0-9bbde6a64643

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasureStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresContinuityStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresTransitivityStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalGramFiberRankOneSetFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_conj_invol
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreRatio_exists_conj_ne
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_bd_zero_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_succ_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_succ
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_RingDiag_uni_zero_zero
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
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.bd_zero_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_succ_zero
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_succ
attribute [local simp] GlobalTheory.CompanionTheory.SW.RingDiag.uni_zero_zero



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreRatio
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}
namespace GlobalTheory.CompanionTheory.SW.FibreRatio
theorem _root_.solution (h : IsCMExt F E σ) :
    ∃ w : E, σ w = -w ∧ ∀ e : E, ∃ a c : F, a • (1 : E) + c • w = e := by
  obtain ⟨e, he⟩ := exists_conj_ne h
  refine ⟨e - σ e, by rw [map_sub, conj_invol h]; ring, ?_⟩
  set w := e - σ e with hw
  have hw' : σ w = -w := by rw [hw, map_sub, conj_invol h]; ring
  have hw0 : w ≠ 0 := fun h0 => he (sub_eq_zero.mp h0).symm
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hli : LinearIndependent F ![(1 : E), w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : s • (1 : E) - t • w = 0 := by
      have := congrArg σ hst
      have e1 : ∀ (a : F) (x : E), σ (a • x) = a • σ x := fun a x => by
        rw [Algebra.smul_def, map_mul, AlgHom.commutes, Algebra.smul_def]
      rw [map_add, e1, e1, map_one, hw', map_zero, smul_neg] at this
      rw [sub_eq_add_neg]
      exact this
    have h3 : (2 * s) • (1 : E) = 0 := by
      have : (2 * s) • (1 : E) = (s • (1 : E) + t • w) + (s • (1 : E) - t • w) := by
        rw [two_mul, add_smul]; abel
      rw [this, hst, h1, add_zero]
    have hs : s = 0 := by
      have := (smul_eq_zero.mp h3).resolve_right one_ne_zero
      exact (mul_eq_zero.mp this).resolve_left h2
    have ht : t = 0 := by
      rw [hs, zero_smul, zero_add] at hst
      exact (smul_eq_zero.mp hst).resolve_right hw0
    exact ⟨hs, ht⟩
  have htop := hli.span_eq_top_of_card_eq_finrank' (by simp [h.2.2.1])
  intro x
  have hx : x ∈ Submodule.span F (Set.range ![(1 : E), w]) := by rw [htop]; trivial
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.union_singleton] at hx
  rw [Set.pair_comm, Submodule.mem_span_pair] at hx
  exact hx
end GlobalTheory.CompanionTheory.SW.FibreRatio
