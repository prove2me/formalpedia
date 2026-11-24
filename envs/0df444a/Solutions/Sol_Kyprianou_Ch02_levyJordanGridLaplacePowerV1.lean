-- Prove2me | solution 1 for Kyprianou.Ch02.levyJordanGridLaplacePowerV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T00:31:00.510638+00:00
-- url     : https://prove2.me/submissions/a8530733-7b9d-44cf-8bf5-9e52ecdf15a4

import Theorems.Thm_Kyprianou_Ch02_levyEqualGridProductExpectationPowerV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : ℝ≥0) (n : ℕ) (u v : ℝ) :
    let g (k : ℕ) := t*(k : ℝ≥0)/((n+1 : ℕ) : ℝ≥0)
    let d (k : ℕ) (ω : Ω) := X (g (k+1)) ω-X (g k) ω
    let Z := X (t/((n+1 : ℕ) : ℝ≥0))
    (∫ ω, Real.exp (-(u*(∑ i : Fin (n+1), max (d i.val ω) 0)+
      v*(∑ i : Fin (n+1), max (-d i.val ω) 0))) ∂P) =
      (∫ ω, Real.exp (-(u*max (Z ω) 0+v*max (-Z ω) 0)) ∂P)^(n+1) := by
  dsimp only
  let f (x : ℝ) := Real.exp (-(u*max x 0+v*max (-x) 0))
  have hf : Measurable f := by unfold f; fun_prop
  have he := Kyprianou.Ch02.levyEqualGridProductExpectationPowerV1 P X hX t n f hf
  dsimp only at he
  rw [← he]
  apply integral_congr_ae
  filter_upwards [] with ω
  simp only [f, ← Real.exp_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
