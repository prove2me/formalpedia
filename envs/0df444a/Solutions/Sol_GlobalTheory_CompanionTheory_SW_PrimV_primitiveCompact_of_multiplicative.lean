-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimV.primitiveCompact_of_multiplicative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:11:43.015918+00:00
-- url     : https://prove2.me/submissions/88ec4f6f-32bc-4419-bf59-3b9bf4ba7367

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalPrimitiveVectorCompactRescale
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
namespace GlobalTheory.CompanionTheory.SW.PrimV
theorem _root_.solution {K : Type*} [CommRing K] [Nontrivial K] [TopologicalSpace K] (M : ℕ) (ν : K → ℝ)
    (h0 : ν 0 = 0) (h1 : ν 1 = 1) (hm : ∀ x y, ν (x * y) = ν x * ν y) (hn : ∀ x, 0 ≤ ν x)
    (hu : ∀ x, x ≠ 0 → IsUnit x ∧ 0 < ν x) (hc : IsCompact {x | ν x ≤ 1}) : UniP K M := by
  refine ⟨Set.pi Set.univ fun _ => {x | ν x ≤ 1}, isCompact_univ_pi fun _ => hc, ?_⟩
  rintro y ⟨z, hz⟩
  have hex : ∃ j, y j ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hy0 : y = 0 := funext hcon
    rw [hy0, dotProduct_zero] at hz
    exact zero_ne_one hz
  obtain ⟨j, hj⟩ := hex
  haveI : Nonempty (Fin M) := ⟨j⟩
  obtain ⟨i, hi⟩ := Finite.exists_max (fun k => ν (y k))
  have hyi : y i ≠ 0 := by
    intro h
    have h2 := hi j
    simp only [h, h0] at h2
    exact absurd (hu _ hj).2 (not_lt.2 h2)
  obtain ⟨w, hw⟩ := (hu _ hyi).1
  have hwi : ((w⁻¹ : Kˣ) : K) * y i = 1 := by rw [← hw]; exact Units.inv_mul w
  have hνw : ν ((w⁻¹ : Kˣ) : K) * ν (y i) = 1 := by rw [← hm, hwi, h1]
  refine ⟨w⁻¹, Pi.single i 1, ?_, ?_, ?_⟩
  · intro k _
    show ν ((((w⁻¹ : Kˣ) : K) • y) k) ≤ 1
    rw [Pi.smul_apply, smul_eq_mul, hm, ← hνw]
    exact mul_le_mul_of_nonneg_left (hi k) (hn _)
  · intro k _
    show ν ((Pi.single i (1 : K) : Fin M → K) k) ≤ 1
    by_cases hk : k = i
    · subst hk; simp [h1]
    · simp [Pi.single_eq_of_ne hk, h0]
  · simp [hwi]
end GlobalTheory.CompanionTheory.SW.PrimV
