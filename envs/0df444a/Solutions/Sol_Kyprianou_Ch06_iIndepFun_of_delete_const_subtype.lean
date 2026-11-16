-- Prove2me | solution 1 for Kyprianou.Ch06.iIndepFun_of_delete_const_subtype
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:33:03.66199+00:00
-- url     : https://prove2.me/submissions/d74dd31c-8b3d-4ac1-b748-c6238166e1c6

import Mathlib.Probability.Independence.Basic
import Theorems.Thm_Kyprianou_Ch06_iIndepFun_of_delete_constant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory

/-- Independence is unchanged when inserting one deterministic zero coordinate
into an independent family indexed by the complement of that coordinate. -/
theorem solution
    {Ω ι : Type} [MeasurableSpace Ω] [DecidableEq ι]
    (P : Measure Ω) (hprob : P Set.univ = 1)
    (f : ι → Ω → Real) (k : ι)
    (hconst : f k = fun _ => 0)
    (haway : ProbabilityTheory.iIndepFun
      (fun j : {j : ι // j ≠ k} => f j.val) P) :
    ProbabilityTheory.iIndepFun f P := by
  apply Kyprianou.Ch06.iIndepFun_of_delete_constant P hprob f k hconst
  intro S hk A hA
  have hinj : Function.Injective
      (fun j : S => (⟨j.val, by intro heq; exact hk (heq ▸ j.property)⟩ : {j : ι // j ≠ k})) := by
    intro a b hab
    have hv : a.val = b.val :=
      congrArg (fun j : {j : ι // j ≠ k} => j.val) hab
    exact Subtype.ext hv
  have hS : ProbabilityTheory.iIndepFun (fun j : S => f j.val) P := by
    convert haway.precomp hinj using 1
  have hrect := (ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul.mp hS)
    Finset.univ (sets := fun j : S => A j.val) (by
      intro j _
      exact hA j.val j.property)
  have hset : (⋂ i ∈ S, f i ⁻¹' A i) =
      (⋂ j : S, f j.val ⁻¹' A j.val) := by
    ext ω
    simp
  rw [← Finset.prod_coe_sort, hset]
  simpa using hrect
