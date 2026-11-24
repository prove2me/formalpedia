-- Prove2me | solution 1 for GlobalTheory.mul_star_anisotropic_proper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:22:35.776212+00:00
-- url     : https://prove2.me/submissions/c1202c6c-bada-4261-a7f9-d23c80fece70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCompactPreimageMulStarAnisotropicSubmodule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (V : Submodule E (Matrix (Fin r) (Fin r) E)), (∀ z ∈ V, z * star z = 0 → z = 0) → ∀ B : Set (Matrix (Fin r) (Fin r) E), IsCompact B → IsCompact {z : Matrix (Fin r) (Fin r) E | z ∈ V ∧ z * star z ∈ B} := by
  intro F E _ _ _ _ hU r V hV B hB
  letI : NormedAddCommGroup (Matrix (Fin r) (Fin r) E) := Matrix.normedAddCommGroup
  letI : NormedSpace E (Matrix (Fin r) (Fin r) E) := Matrix.normedSpace
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : ProperSpace (Matrix (Fin r) (Fin r) E) := FiniteDimensional.proper E _
  have hsE : Continuous (star : E → E) :=
    AddMonoidHomClass.continuous_of_bound (starAddEquiv : E ≃+ E) 1 (fun x => by simp [hU.norm_star])
  haveI : ContinuousStar E := ⟨hsE⟩
  have hQc : Continuous fun z : Matrix (Fin r) (Fin r) E => z * star z :=
    continuous_id.mul continuous_star
  have hQs : ∀ (d : E) (z : Matrix (Fin r) (Fin r) E), (d • z) * star (d • z) = (d * star d) • (z * star z) := by
    intro d z
    rw [star_smul, smul_mul_smul_comm]
  have hnd : ∀ d : E, ‖d * star d‖ = ‖d‖ ^ 2 := by
    intro d; rw [norm_mul, hU.norm_star, sq]
  have hVc : IsClosed (V : Set (Matrix (Fin r) (Fin r) E)) := Submodule.closed_of_finiteDimensional V
  obtain ⟨k, hk⟩ := NormedField.exists_one_lt_norm E
  set A : Set (Matrix (Fin r) (Fin r) E) := {w | w ∈ V ∧ ‖k‖⁻¹ ≤ ‖w‖ ∧ ‖w‖ ≤ 1} with hA
  have hAc : IsCompact A := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact hVc.inter ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
    · exact (Metric.isBounded_closedBall (x := (0 : Matrix (Fin r) (Fin r) E)) (r := 1)).subset
        (fun w hw => by simpa using hw.2.2)
  have hkpos : 0 < ‖k‖⁻¹ := inv_pos.mpr (lt_trans one_pos hk)
  have hA0 : ∀ w ∈ A, 0 < ‖w * star w‖ := by
    intro w hw
    apply norm_pos_iff.mpr
    intro h0
    have := hV w hw.1 h0
    have h1 := hw.2.1
    rw [this, norm_zero] at h1
    linarith
  obtain ⟨c, hc0, hc⟩ : ∃ c : ℝ, 0 < c ∧ ∀ w ∈ A, c ≤ ‖w * star w‖ := by
    rcases A.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨w₀, hw₀, hmin⟩ := hAc.exists_isMinOn hne (hQc.norm.continuousOn)
      exact ⟨_, hA0 w₀ hw₀, fun w hw => hmin hw⟩
  obtain ⟨R, hR⟩ := (hB.isBounded).subset_closedBall 0
  apply Metric.isCompact_of_isClosed_isBounded
  · exact hVc.inter (hB.isClosed.preimage hQc)
  · apply (Metric.isBounded_closedBall (x := (0 : Matrix (Fin r) (Fin r) E)) (r := Real.sqrt (|R| / c))).subset
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    have hQR : ‖z * star z‖ ≤ |R| := by
      have := hR hz.2
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this.trans (le_abs_self R)
    by_cases hz0 : z = 0
    · rw [hz0, norm_zero]; exact Real.sqrt_nonneg _
    obtain ⟨d, hd0, hd1, hd2, -⟩ := rescale_to_shell hk one_pos hz0
    have hdA : d • z ∈ A := ⟨V.smul_mem d hz.1, by simpa using hd2, hd1.le⟩
    have h1 := hc _ hdA
    rw [hQs, norm_smul, hnd] at h1
    rw [norm_smul] at hd1
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hc0]
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd0

    have hdz : (‖d‖ * ‖z‖) ^ 2 ≤ 1 := by
      have : 0 ≤ ‖d‖ * ‖z‖ := by positivity
      nlinarith
    have hQ0 : 0 ≤ ‖z * star z‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖z‖)]
end GlobalTheory
