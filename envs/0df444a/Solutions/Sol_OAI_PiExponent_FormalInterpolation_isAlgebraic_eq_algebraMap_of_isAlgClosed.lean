-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.isAlgebraic_eq_algebraMap_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T07:20:28.279998+00:00
-- url     : https://prove2.me/submissions/823af5b8-7513-43c9-96c1-f9df31dfccd3

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

theorem solution
    {E : Type} [Field E] [Algebra Complex E] (x : E) (hx : IsAlgebraic Complex x) :
    ∃ a : Complex, x = algebraMap Complex E a := by
  have : Algebra.IsAlgebraic Complex (IntermediateField.adjoin Complex {x}) :=
    IntermediateField.isAlgebraic_adjoin (fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hx.isIntegral)
  have hbot : IntermediateField.adjoin Complex {x} = ⊥ :=
    IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
  have hxmem : x ∈ IntermediateField.adjoin Complex {x} :=
    IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
  rw [hbot, IntermediateField.mem_bot] at hxmem
  obtain ⟨a, ha⟩ := hxmem
  exact ⟨a, ha.symm⟩
