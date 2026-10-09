-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.indep_prefix_next_singleton
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T14:11:15.758108+00:00
-- url     : https://prove2.me/submissions/c807e7db-eebf-47e4-981f-854782ba4ca5

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f : ℕ → ℝ) (hM : IsSeatModel P X f) (k : ℕ) :
    IndepFun
      (fun ω : Ω => fun i : (Finset.Icc 1 k) => X i.1 ω)
      (fun ω : Ω => fun i : ({k + 1} : Finset ℕ) => X i.1 ω) P := by
  have hdisj : Disjoint (Finset.Icc 1 k) ({k + 1} : Finset ℕ) := by
    apply Finset.disjoint_left.mpr
    intro i hI hJ
    have hik : i ≤ k := (Finset.mem_Icc.mp hI).2
    have hij : i = k + 1 := Finset.mem_singleton.mp hJ
    omega
  exact ProbabilityTheory.iIndepFun.indepFun_finset
    (Finset.Icc 1 k) ({k + 1} : Finset ℕ) hdisj hM.indep hM.meas
