-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimV.compact_Nf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:27:15.514277+00:00
-- url     : https://prove2.me/submissions/a1cfedf1-3479-440b-b65f-fd09c386ad06

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LocAtA
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalPrimitiveVectorCompactRescale
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimV_Nf_ne
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
namespace GlobalTheory.CompanionTheory.SW.PrimV
theorem _root_.solution {D : L} (hD : ∀ s, s * s ≠ D) : IsCompact {p : L × L | ‖Nf D p‖ ≤ 1} := by
  have hcont : Continuous fun p : L × L => ‖Nf D p‖ := by
    unfold Nf; fun_prop
  have hs : IsCompact (Metric.sphere (0 : L × L) 1) := isCompact_sphere _ _
  have hne : (Metric.sphere (0 : L × L) 1).Nonempty := ⟨(1, 0), by simp [Prod.norm_def]⟩
  obtain ⟨q0, hq0, hmin⟩ := hs.exists_isMinOn hne hcont.continuousOn
  have hq00 : q0 ≠ 0 := by
    rintro rfl
    simp at hq0
  have hm : 0 < ‖Nf D q0‖ := norm_pos_iff.2 (Nf_ne hD hq00)
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_le hcont continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (0 : L × L)) (r := 1 + 1 / ‖Nf D q0‖)).subset ?_
  intro p hp
  rw [mem_closedBall_zero_iff]
  by_cases hp0 : p = 0
  · subst hp0
    simp only [norm_zero]
    positivity
  obtain ⟨w, hw⟩ : ∃ w : L, ‖w‖ = ‖p‖ := by
    rw [Prod.norm_def]
    rcases max_choice ‖p.1‖ ‖p.2‖ with h | h
    · exact ⟨p.1, h.symm⟩
    · exact ⟨p.2, h.symm⟩
  have hpn : 0 < ‖p‖ := norm_pos_iff.2 hp0
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
    exact hp0 (norm_eq_zero.1 hw.symm)
  have hq : w⁻¹ • p ∈ Metric.sphere (0 : L × L) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, hw]
    field_simp
  have h1 : ‖Nf D q0‖ ≤ ‖Nf D (w⁻¹ • p)‖ := hmin hq
  have h2 : Nf D p = w ^ 2 * Nf D (w⁻¹ • p) := by
    simp only [Nf, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    field_simp
  have h3 : ‖p‖ ^ 2 * ‖Nf D q0‖ ≤ 1 := by
    have h4 : ‖Nf D p‖ ≤ 1 := hp
    rw [h2, norm_mul, norm_pow, hw] at h4
    exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans h4
  have h5 : ‖p‖ ^ 2 ≤ 1 / ‖Nf D q0‖ := by
    rw [le_div_iff₀ hm]; exact h3
  have h6 : 0 < 1 / ‖Nf D q0‖ := by positivity
  by_cases h7 : ‖p‖ ≤ 1
  · linarith
  · push_neg at h7
    nlinarith
end GlobalTheory.CompanionTheory.SW.PrimV
