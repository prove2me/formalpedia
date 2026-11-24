-- Prove2me | solution 1 for Kyprianou.Ch02.bvPathEqualGridJordanSumsTendstoV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:54:19.930864+00:00
-- url     : https://prove2.me/submissions/37170175-5d43-4af2-8aef-3f47a2367ee3

import Theorems.Thm_Kyprianou_Ch02_equalGridSignedSumV1
import Theorems.Thm_Kyprianou_Ch02_positiveNegativeSumLimitV1
import Theorems.Thm_Kyprianou_Ch02_bvRightContinuousEqualGridVariationTendstoV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (f : ℝ≥0 → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hbv : LocallyBoundedVariationOn f univ)
    (hr : ∀ t : ℝ≥0, ContinuousWithinAt f (Ici t) t) :
    let g (n k : ℕ) : ℝ≥0 := a+(b-a)*(k : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
    let d (n k : ℕ) : ℝ := f (g n (k+1)) - f (g n k)
    let v := variationOnFromTo f univ
    Tendsto (fun n => (∑ k : Fin (n+1), max (d n k) 0,
      ∑ k : Fin (n+1), max (-d n k) 0)) atTop
      (nhds (((v a b + (f b-f a))/2), ((v a b-(f b-f a))/2))) := by
  dsimp only
  let g (n k : ℕ) : ℝ≥0 := a+(b-a)*(k : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
  let d (n k : ℕ) : ℝ := f (g n (k+1)) - f (g n k)
  let v := variationOnFromTo f univ
  have hvar : Tendsto (fun n => ∑ k ∈ Finset.range (n+1), |d n k|)
      atTop (nhds (v a b)) :=
    Kyprianou.Ch02.bvRightContinuousEqualGridVariationTendstoV1 f a b hab hbv
      hr
  have hvar' : Tendsto (fun n => ∑ k : Fin (n+1), |d n k|) atTop (nhds (v a b)) := by
    have he (n : ℕ) : (∑ k : Fin (n+1), |d n k|) =
        ∑ k ∈ Finset.range (n+1), |d n k| :=
      Fin.sum_univ_eq_sum_range (fun k : ℕ => |d n k|) (n+1)
    simpa only [he] using hvar
  exact Kyprianou.Ch02.positiveNegativeSumLimitV1 d (v a b) (f b-f a) hvar'
    (fun n => Kyprianou.Ch02.equalGridSignedSumV1 f a b hab n)
