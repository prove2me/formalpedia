-- Prove2me | solution 1 for Kyprianou.Ch01.iidFixedLengthCharFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:27:25.604331+00:00
-- url     : https://prove2.me/submissions/0b1c80cc-3d73-47c2-8113-84f2fadd309f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped BigOperators
set_option autoImplicit false

/-! A fixed-length IID sum has characteristic function equal to a power. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (hIncMeas : ∀ n : ℕ, Measurable (increment n))
    (hIID : iIndepFun increment P)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hCommon : ∀ n : ℕ, HasLaw (increment n) jumpLaw P)
    (n : ℕ) (xi : ℝ) :
    charFun (P.map (fun ω =>
      ∑ i ∈ Finset.range n, increment i ω)) xi =
      (charFun jumpLaw xi) ^ n := by
  have hprod :
      charFun (P.map (fun ω =>
        ∑ i ∈ Finset.range n, increment i ω)) =
      ∏ i ∈ Finset.range n, charFun (P.map (increment i)) := by
    exact ProbabilityTheory.iIndepFun.charFun_map_fun_finsetSum_eq_prod
      (s := Finset.range n)
      (X := increment)
      (fun i _ => (hIncMeas i).aemeasurable)
      (hIID.restrict (Finset.range n))
  calc
    charFun (P.map (fun ω =>
      ∑ i ∈ Finset.range n, increment i ω)) xi =
        ∏ i ∈ Finset.range n, charFun (P.map (increment i)) xi := by
          simpa only [Finset.prod_apply] using congrFun hprod xi
    _ = ∏ i ∈ Finset.range n, charFun jumpLaw xi := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [(hCommon i).map_eq]
    _ = (charFun jumpLaw xi) ^ n := by simp
