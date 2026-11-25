-- Prove2me | solution 1 for LovaszTheta.dotProduct_tensor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:47:01.699596+00:00
-- url     : https://prove2.me/submissions/7adf8579-7e81-4cce-8eb3-7fa5d15b6433

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open LovaszTheta
variable {V : Type*}
namespace LovaszTheta
theorem _root_.solution {k : ℕ} {ι : Type*} [Fintype ι] (a b : Fin k → ι → ℝ) :
    dotProduct (fun j : Fin k → ι => ∏ i, a i (j i)) (fun j => ∏ i, b i (j i))
      = ∏ i, dotProduct (a i) (b i) := by
  classical
  simp only [dotProduct]
  rw [Fintype.prod_sum (fun i x => a i x * b i x)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.prod_mul_distrib]
end LovaszTheta
