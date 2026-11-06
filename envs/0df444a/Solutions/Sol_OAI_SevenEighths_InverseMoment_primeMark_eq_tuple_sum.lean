-- Prove2me | solution 1 for OAI.SevenEighths.InverseMoment.primeMark_eq_tuple_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:11:04.187201+00:00
-- url     : https://prove2.me/submissions/5feef914-554d-4258-b8e7-8302b5f89fa0

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Marks

set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators
noncomputable section
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]
namespace OAI.SevenEighths.InverseMoment
theorem _root_.solution (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    primeMark I L a A = ∑ p ∈ I.pi L,
      ∏ i ∈ I.attach, if p i.1 i.2 ∈ A then a i.1 (p i.1 i.2) else 0 := by
  exact Finset.prod_sum I L (fun i p => if p ∈ A then a i p else 0)
end OAI.SevenEighths.InverseMoment
