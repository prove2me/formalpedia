-- Prove2me | solution 1 for Kyprianou.Ch02.levyAbsPowIntegrableIffLargeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:28:00.934238+00:00
-- url     : https://prove2.me/submissions/c9b7d0a9-cca7-4261-99fa-17b19a1ead2b

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    (n : ℕ) (hn : 2 ≤ n) :
    (Integrable (fun x : ℝ => |x| ^ n) ν ↔
      Integrable (fun x : ℝ => |x| ^ n)
        (ν.restrict {x : ℝ | 1 ≤ |x|})) ∧
    (Integrable (fun x : ℝ => |x| ^ n)
        (ν.restrict {x : ℝ | 1 ≤ |x|}) →
      Integrable (fun x : ℝ => x ^ n) ν) := by
  let s : Set ℝ := {x | |x| < 1}
  let l : Set ℝ := {x | 1 ≤ |x|}
  have hm : Measurable (fun x : ℝ => |x| ^ n) := by fun_prop
  have hs : MeasurableSet s :=
    measurableSet_lt continuous_abs.measurable measurable_const
  have hb : Integrable (fun x : ℝ => min 1 (x ^ 2)) ν :=
    ⟨(continuous_const.min (continuous_pow 2)).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
        (fun x : ℝ => le_min zero_le_one (sq_nonneg x)))).2 hν.2⟩
  have hsmall : IntegrableOn (fun x : ℝ => |x| ^ n) s ν := by
    have hbr : Integrable (fun x : ℝ => min 1 (x ^ 2)) (ν.restrict s) := hb.restrict
    refine hbr.mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hs] with x hx
    change |x| < 1 at hx
    have hpow : |x| ^ n ≤ |x| ^ 2 :=
      Bound.pow_le_pow_right_of_le_one_or_one_le (Or.inr ⟨abs_nonneg x, hx.le, hn⟩)
    have hsq : |x| ^ 2 = x ^ 2 := sq_abs x
    have hx2 : x ^ 2 ≤ 1 := by
      simpa only [sq_abs, one_pow] using
        (pow_le_pow_left₀ (abs_nonneg x) hx.le 2)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg x) n),
      min_eq_right hx2]
    exact hpow.trans_eq hsq
  have hu : s ∪ l = Set.univ := by
    ext x
    simp only [s, l, Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact lt_or_ge |x| 1
  have hiff : Integrable (fun x : ℝ => |x| ^ n) ν ↔
      Integrable (fun x : ℝ => |x| ^ n) (ν.restrict l) := by
    constructor
    · intro h
      exact h.restrict
    · intro h
      have hlarge : IntegrableOn (fun x : ℝ => |x| ^ n) l ν := h
      have hall := hsmall.union hlarge
      rwa [hu, integrableOn_univ] at hall
  refine ⟨hiff, ?_⟩
  intro h
  refine (hiff.mpr h).mono' (by fun_prop) ?_
  exact Filter.Eventually.of_forall (fun x => by
    simp [Real.norm_eq_abs, abs_pow])
