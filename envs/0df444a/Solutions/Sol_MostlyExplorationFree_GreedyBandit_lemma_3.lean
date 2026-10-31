-- Prove2me | solution 1 for MostlyExplorationFree.GreedyBandit.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T18:46:06.535693+00:00
-- url     : https://prove2.me/submissions/91682561-8aa6-47be-800e-e8bf088a7a47

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Model

open Matrix MeasureTheory ProbabilityTheory
open MostlyExplorationFree.GreedyBandit

theorem solution {d : ℕ} (hd : 1 ≤ d) (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (β : Fin 2 → Fin d → ℝ) (xmax bmax lam0 : ℝ)
    (hA1 : ParameterSet μ β xmax bmax) (hA3 : CovariateDiversity μ lam0) (u : Fin d → ℝ) :
    ENNReal.ofReal (lam0 / xmax ^ 2) ≤ μ {x | 0 ≤ x ⬝ᵥ u} := by
  obtain ⟨hxmax, hXb, -⟩ := hA1
  obtain ⟨hlam0, hdiv⟩ := hA3
  set S : Set (Fin d → ℝ) := {y | 0 ≤ y ⬝ᵥ u} with hS
  have hSm : MeasurableSet S :=
    measurableSet_le measurable_const
      ((continuous_id.dotProduct continuous_const).measurable)
  set i0 : Fin d := ⟨0, hd⟩
  set v : Fin d → ℝ := Pi.single i0 1 with hv
  have hvv : v ⬝ᵥ v = 1 := by simp [hv]
  set M := halfSpaceSecondMoment μ u with hM
  -- Step 1: λ₀ ≤ vᵀ M v.
  have h1 : lam0 ≤ v ⬝ᵥ (M *ᵥ v) := by
    have h := hdiv u
    rw [← hM] at h
    unfold lambdaMin at h
    by_cases hb : BddBelow (Set.range fun w : {w : Fin d → ℝ // w ⬝ᵥ w = 1} => w.1 ⬝ᵥ (M *ᵥ w.1))
    · exact h.trans (ciInf_le hb ⟨v, hvv⟩)
    · rw [Real.iInf_of_not_bddBelow hb] at h
      linarith
  have hvMv : v ⬝ᵥ (M *ᵥ v) = M i0 i0 := by
    simp [hv]
  rw [hvMv, hM] at h1
  simp only [halfSpaceSecondMoment, Matrix.of_apply] at h1
  -- Step 2: the integrand is at most x_max² on S, almost surely.
  have h2 : ∫ x, S.indicator (fun y : Fin d → ℝ => y i0 * y i0) x ∂μ
      ≤ ∫ x, S.indicator (fun _ => xmax ^ 2) x ∂μ := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun x => Set.indicator_nonneg
        (fun y _ => mul_self_nonneg (y i0)) x)
    · exact (integrable_const (xmax ^ 2)).indicator hSm
    · filter_upwards [hXb] with x hx
      by_cases hxS : x ∈ S
      · simp only [Set.indicator_of_mem hxS]
        unfold l2norm at hx
        have hxx : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))
        have hsq : x ⬝ᵥ x ≤ xmax ^ 2 := by
          rw [← Real.sq_sqrt hxx]
          exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hx 2
        have hsingle : x i0 * x i0 ≤ x ⬝ᵥ x := by
          simp only [dotProduct]
          exact Finset.single_le_sum (f := fun j => x j * x j)
            (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i0)
        linarith
      · simp [Set.indicator_of_notMem hxS]
  rw [integral_indicator_const _ hSm, smul_eq_mul] at h2
  have h3 : lam0 ≤ (μ S).toReal * xmax ^ 2 := by
    have := h1.trans h2
    simpa [measureReal_def] using this
  rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
  rw [div_le_iff₀ (by positivity)]
  exact h3
