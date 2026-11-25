-- Prove2me | solution 1 for GlobalTheory.exists_int_comb_norm_sub_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:59:43.950309+00:00
-- url     : https://prove2.me/submissions/6bef0286-c166-43a6-9c67-d1b4bcc28081

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_AbsTwoMulInnerLeOfNormSubEqInfDist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open scoped InnerProductSpace
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace GlobalTheory
theorem _root_.solution (k : ℕ) (v : Fin k → E) {x : E}
    (hx : x ∈ span ℝ (Set.range v)) :
    ∃ w ∈ span ℤ (Set.range v), ‖x - w‖ ^ 2 ≤ (∑ i, ‖v i‖ ^ 2) / 4 := by
  induction k generalizing x with
  | zero =>
    refine ⟨0, zero_mem _, ?_⟩
    have : x = 0 := by simpa using hx
    simp [this]
  | succ k ih =>
    set U : Submodule ℝ E := span ℝ (Set.range (Fin.init v)) with hU
    have : FiniteDimensional ℝ U := FiniteDimensional.span_of_finite ℝ (Set.finite_range _)
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℝ).1 hx
    set a := c (Fin.last k)
    set u := v (Fin.last k)
    set y := ∑ i : Fin k, c i.castSucc • v i.castSucc with hy
    have hyU : y ∈ U := sum_mem fun i _ => smul_mem _ _ (subset_span ⟨i, rfl⟩)
    set p := U.starProjection u
    have hpU : p ∈ U := U.starProjection_apply_mem u
    have hq : u - p ∈ Uᗮ := U.sub_starProjection_mem_orthogonal u
    set t : ℝ := a - round a
    have ht : |t| ≤ 1 / 2 := abs_sub_round a
    obtain ⟨w, hw, hle⟩ := ih (Fin.init v) (x := y + t • p) (add_mem hyU (smul_mem _ _ hpU))
    have hwU : w ∈ U := span_subset_span ℤ ℝ _ hw
    refine ⟨w + round a • u, add_mem (span_mono ?_ hw) (smul_mem _ _ (subset_span ⟨_, rfl⟩)), ?_⟩
    · rintro _ ⟨i, rfl⟩; exact ⟨_, rfl⟩
    have e : ∑ i, c i • v i - (w + round a • u) = (y + t • p - w) + t • (u - p) := by
      rw [Fin.sum_univ_castSucc, ← Int.cast_smul_eq_zsmul ℝ]
      simp only [t]; module
    have hz : y + t • p - w ∈ U := sub_mem (add_mem hyU (smul_mem _ _ hpU)) hwU
    have horth : ⟪y + t • p - w, t • (u - p)⟫_ℝ = 0 :=
      U.inner_right_of_mem_orthogonal hz (smul_mem _ _ hq)
    have hup : ‖u - p‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      have h1 : ⟪p, u - p⟫_ℝ = 0 := U.inner_right_of_mem_orthogonal hpU hq
      have h2 := norm_add_sq_real p (u - p)
      rw [add_sub_cancel, h1] at h2
      nlinarith [sq_nonneg ‖p‖]
    have ht2 : t ^ 2 ≤ 1 / 4 := by
      rw [← sq_abs]; nlinarith [abs_nonneg t]
    rw [e, norm_add_sq_real, horth, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      Fin.sum_univ_castSucc]
    have : t ^ 2 * ‖u - p‖ ^ 2 ≤ 1 / 4 * ‖u‖ ^ 2 :=
      mul_le_mul ht2 hup (sq_nonneg _) (by norm_num)
    have hle' : ‖y + t • p - w‖ ^ 2 ≤ (∑ i : Fin k, ‖v i.castSucc‖ ^ 2) / 4 := hle
    linarith
end GlobalTheory
