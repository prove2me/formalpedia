-- Prove2me | solution 1 for HypercliqueFalse.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T09:24:37.427279+00:00
-- url     : https://prove2.me/submissions/99bb1470-4eae-4b51-8093-e9c3330a46ba

import Mathlib

set_option autoImplicit false
namespace HypercliqueFalse

lemma sum_split {q : ℕ} (F : Fin q → Fin q → ℤ) :
    ∑ i, ∑ j, F i j = ∑ i, F i i + ∑ i, ∑ j ∈ Finset.Ioi i, (F i j + F j i) := by
  have h1 : ∀ i : Fin q, ∑ j, F i j = ∑ j ∈ Finset.Iio i, F i j + F i i + ∑ j ∈ Finset.Ioi i, F i j := by
    intro i
    have : (Finset.univ : Finset (Fin q)) = Finset.Iio i ∪ {i} ∪ Finset.Ioi i := by
      ext j; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_Iio, Finset.mem_singleton,
        Finset.mem_Ioi, true_iff]; omega
    rw [this, Finset.sum_union, Finset.sum_union, Finset.sum_singleton]
    · rw [Finset.disjoint_singleton_right]; simp
    · rw [Finset.disjoint_left]; intro j hj hj'
      simp only [Finset.mem_union, Finset.mem_Iio, Finset.mem_singleton, Finset.mem_Ioi] at hj hj'
      omega
  have h2 : ∑ i, ∑ j ∈ Finset.Iio i, F i j = ∑ i, ∑ j ∈ Finset.Ioi i, F j i := by
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun j => Finset.Ioi j)]
    intro x y; simp
  simp_rw [h1, Finset.sum_add_distrib, h2]
  ring

theorem lemma_3_1 (q a b : ℕ) (hq : 2 ≤ q) (U : Fin q → Fin q → Matrix (Fin a) (Fin b) ℤ)
    (V : Fin q → Fin q → Matrix (Fin b) (Fin a) ℤ) :
    ∑ i, ∑ j, (U i j * V i j).trace =
      ∑ i, ∑ j, (U i j * V j i).trace +
        ∑ i, ∑ j ∈ Finset.Ioi i, ((U i j - U j i) * (V i j - V j i)).trace := by
  rw [sum_split (fun i j => (U i j * V i j).trace), sum_split (fun i j => (U i j * V j i).trace)]
  beta_reduce
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
  have key : ∀ i : Fin q, ∑ j ∈ Finset.Ioi i, ((U i j * V i j).trace + (U j i * V j i).trace) =
      ∑ j ∈ Finset.Ioi i, ((U i j * V j i).trace + (U j i * V i j).trace) +
      ∑ j ∈ Finset.Ioi i, ((U i j * V i j).trace - (U j i * V i j).trace -
              ((U i j * V j i).trace - (U j i * V j i).trace)) := by
    intro i
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib]
  ring

end HypercliqueFalse

theorem solution (q a b : ℕ) (hq : 2 ≤ q) (U : Fin q → Fin q → Matrix (Fin a) (Fin b) ℤ)
    (V : Fin q → Fin q → Matrix (Fin b) (Fin a) ℤ) :
    ∑ i, ∑ j, (U i j * V i j).trace =
      ∑ i, ∑ j, (U i j * V j i).trace +
        ∑ i, ∑ j ∈ Finset.Ioi i, ((U i j - U j i) * (V i j - V j i)).trace :=
  HypercliqueFalse.lemma_3_1 q a b hq U V
