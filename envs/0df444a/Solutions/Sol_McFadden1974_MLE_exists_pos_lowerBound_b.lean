-- Prove2me | solution 1 for McFadden1974.MLE.exists_pos_lowerBound_b
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T23:52:19.916426+00:00
-- url     : https://prove2.me/submissions/21fd881c-9288-4a61-a05e-4e269f395584

import Mathlib
import Definitions.Def_McFadden1974_MLE_Model
import Definitions.Def_McFadden1974_MLE_Axioms

set_option autoImplicit false

open scoped RealInnerProductSpace in
theorem McFadden1974.MLE.exists_pos_lowerBound_b_aux
    {K : ℕ} (d : McFadden1974.MLE.Data K) (h6 : d.Axiom6) :
    ∃ bstar : ℝ, 0 < bstar ∧ ∀ γ : EuclideanSpace ℝ (Fin K), ‖γ‖ = 1 → bstar ≤ d.b γ := by
  classical
  set A : Set (EuclideanSpace ℝ (Fin K)) := Metric.sphere 0 1 with hA
  have hbdd : ∀ γ : EuclideanSpace ℝ (Fin K), BddAbove (Set.range fun x :
      (Σ n : Fin d.N, Fin (d.J n) × Fin (d.J n)) =>
        (d.S x.1 x.2.1 : ℝ) * ⟪d.z x.1 x.2.2 - d.z x.1 x.2.1, γ⟫) :=
    fun γ => (Set.finite_range _).bddAbove
  -- positivity on the sphere
  have hpos : ∀ γ ∈ A, 0 < d.b γ := by
    intro γ hγ
    have hγ0 : γ ≠ 0 := by
      intro h; rw [hA, h, Metric.mem_sphere, dist_self] at hγ; norm_num at hγ
    by_contra hle
    push Not at hle
    apply hγ0
    apply h6
    intro n i j
    have := le_ciSup (hbdd γ) (⟨n, (i, j)⟩ : Σ n : Fin d.N, Fin (d.J n) × Fin (d.J n))
    exact le_trans this hle
  rcases A.eq_empty_or_nonempty with hE | hne
  · refine ⟨1, one_pos, fun γ hγ => ?_⟩
    have : γ ∈ A := by rw [hA, mem_sphere_zero_iff_norm]; exact hγ
    rw [hE] at this; exact absurd this (Set.notMem_empty _)
  · have hlsc : LowerSemicontinuous d.b := by
      unfold McFadden1974.MLE.Data.b
      apply lowerSemicontinuous_ciSup hbdd
      intro x
      apply Continuous.lowerSemicontinuous
      exact continuous_const.mul (continuous_const.inner continuous_id)
    obtain ⟨a, ha, hmin⟩ := (hlsc.lowerSemicontinuousOn A).exists_isMinOn hne (isCompact_sphere 0 1)
    refine ⟨d.b a, hpos a ha, fun γ hγ => ?_⟩
    have : γ ∈ A := by rw [hA, mem_sphere_zero_iff_norm]; exact hγ
    exact hmin this

open scoped RealInnerProductSpace in
theorem solution
    {K : ℕ} (d : McFadden1974.MLE.Data K) (h5 : d.Axiom5) (h6 : d.Axiom6) :
    ∃ bstar : ℝ, 0 < bstar ∧ ∀ γ : EuclideanSpace ℝ (Fin K), ‖γ‖ = 1 → bstar ≤ d.b γ := by
  exact McFadden1974.MLE.exists_pos_lowerBound_b_aux d h6
