-- Prove2me | solution 1 for GlobalTheory.matrix_inv_entries_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:19:57.602842+00:00
-- url     : https://prove2.me/submissions/7dd3b338-833a-40c2-a5e0-0df3016d9794

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MatrixInvEntriesBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open NumberField IsDedekindDomain
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (R : Type) [NormedCommRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R] (n : ℕ) (G : Matrix (Fin n) (Fin n) R → ℝ) (hG : Continuous G) (hU : ∀ c, G c ≠ 0 → IsUnit c) (B ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, (∀ c : Matrix (Fin n) (Fin n) R, (∀ i j, ‖c i j‖ ≤ B) → G c ≤ C) ∧ ∀ c : GL (Fin n) R, (∀ i j, ‖c.1 i j‖ ≤ B) → ε ≤ G c.1 → ∀ i j, ‖c⁻¹.1 i j‖ ≤ C := by
  haveI : ProperSpace R := FiniteDimensional.proper_real R
  haveI : CompleteSpace R := FiniteDimensional.complete ℝ R
  set K : Set (Matrix (Fin n) (Fin n) R) := Set.pi Set.univ (fun _ => Set.pi Set.univ (fun _ => Metric.closedBall (0 : R) B)) with hK
  have hKc : IsCompact K := isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_closedBall _ _))
  have hmemK : ∀ c : Matrix (Fin n) (Fin n) R, (∀ i j, ‖c i j‖ ≤ B) → c ∈ K := by
    intro c h i _ j _
    simpa [Metric.mem_closedBall, dist_zero_right] using h i j
  obtain ⟨C1, hC1⟩ := hKc.exists_bound_of_continuousOn hG.continuousOn
  set K' := K ∩ {c | ε ≤ G c} with hK'
  have hK'c : IsCompact K' := hKc.inter_right (isClosed_le continuous_const hG)
  let f : Matrix (Fin n) (Fin n) R → (Fin n → Fin n → R) := fun c => fun i j => (c⁻¹) i j
  have hf : ContinuousOn f K' := by
    intro c hc
    have hu : IsUnit c := hU c (ne_of_gt (lt_of_lt_of_le hε hc.2))
    have hdet : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).1 hu
    obtain ⟨u, hu'⟩ := hdet
    have h1 : ContinuousAt Ring.inverse c.det := by
      rw [← hu']; exact NormedRing.inverse_continuousAt u
    exact (continuousAt_matrix_inv c h1).continuousWithinAt
  obtain ⟨C2, hC2⟩ := hK'c.exists_bound_of_continuousOn hf
  refine ⟨max C1 C2, ?_, ?_⟩
  · intro c hc
    exact le_trans (le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hC1 c (hmemK c hc))) (le_max_left _ _)
  · intro c hc hGc i j
    have hm : c.1 ∈ K' := ⟨hmemK _ hc, hGc⟩
    have h2 := hC2 _ hm
    have h3 : ‖f c.1 i j‖ ≤ ‖f c.1‖ := le_trans (norm_le_pi_norm (f c.1 i) j) (norm_le_pi_norm (f c.1) i)
    rw [Matrix.coe_units_inv]
    exact le_trans (le_trans h3 h2) (le_max_right _ _)
end GlobalTheory
