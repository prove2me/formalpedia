-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimV.primitiveCompact_nonsplit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:46:59.493797+00:00
-- url     : https://prove2.me/submissions/0364b176-a400-4540-abab-771a06ae520f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalPrimitiveVectorCompactRescale
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_primitiveCompact_of_multiplicative
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_gg_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_gg_rr
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_rr_gg
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_rr_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_rr_zero
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_rr_one
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_nontrivial_of_basis
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_Nf_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_Nf_ne
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_compact_Nf
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
variable {L K : Type*} [NormedField L] [ProperSpace L]
variable [CommRing K] [Algebra L K] [TopologicalSpace K] (bs : Module.Basis (Fin 2) L K)
namespace GlobalTheory.CompanionTheory.SW.PrimV
theorem _root_.solution (h0 : bs 0 = 1) {D : L} (hd : bs 1 * bs 1 = algebraMap L K D)
    (hD : ∀ s, s * s ≠ D) (hg : Continuous (gg (bs 1) : L × L → K)) (M : ℕ) : UniP K M := by
  haveI := nontrivial_of_basis bs h0
  refine primitiveCompact_of_multiplicative M (fun x => ‖Nf D (rr bs x)‖) ?_ ?_ ?_ (fun _ => norm_nonneg _) ?_ ?_
  · simp [rr_zero, Nf]
  · simp [rr_one bs h0, Nf]
  · intro x y
    simp only [rr_mul bs h0 hd, Nf_mul, norm_mul]
  · intro x hx
    show IsUnit x ∧ 0 < ‖Nf D (rr bs x)‖
    have hxg := gg_rr bs h0 x
    have hp : rr bs x ≠ 0 := by
      intro h
      apply hx
      rw [← hxg, h]
      simp [gg]
    have hn := Nf_ne hD hp
    generalize rr bs x = p at hxg hp hn ⊢
    refine ⟨isUnit_iff_exists_inv.2 ⟨gg (bs 1) (p.1 / Nf D p, -p.2 / Nf D p), ?_⟩, norm_pos_iff.2 hn⟩
    rw [← hxg, gg_mul hd]
    have e1 : p.1 * (p.1 / Nf D p) + D * (p.2 * (-p.2 / Nf D p)) = 1 := by
      field_simp
      simp only [Nf]
      ring
    have e2 : p.1 * (-p.2 / Nf D p) + p.2 * (p.1 / Nf D p) = 0 := by
      field_simp
      ring
    simp only [e1, e2]
    simp [gg]
  · have : {x : K | ‖Nf D (rr bs x)‖ ≤ 1} = gg (bs 1) '' {p : L × L | ‖Nf D p‖ ≤ 1} := by
      ext x
      constructor
      · intro hx
        exact ⟨rr bs x, hx, gg_rr bs h0 x⟩
      · rintro ⟨p, hp, rfl⟩
        show ‖Nf D (rr bs (gg (bs 1) p))‖ ≤ 1
        rw [rr_gg bs h0]
        exact hp
    rw [this]
    exact (compact_Nf hD).image hg
end GlobalTheory.CompanionTheory.SW.PrimV
