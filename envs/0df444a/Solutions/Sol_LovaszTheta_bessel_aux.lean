-- Prove2me | solution 1 for LovaszTheta.bessel_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:37:59.826813+00:00
-- url     : https://prove2.me/submissions/a35928b0-dc62-4558-8091-ca5dfc72e999

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
theorem _root_.solution {ι κ : Type*} [Fintype ι] (S : Finset κ) (u : κ → ι → ℝ)
    (hu1 : ∀ i ∈ S, dotProduct (u i) (u i) = 1)
    (hu0 : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → dotProduct (u i) (u j) = 0) (c : ι → ℝ) :
    ∑ i ∈ S, dotProduct c (u i) ^ 2 ≤ dotProduct c c := by
  classical
  set w := c - ∑ i ∈ S, dotProduct c (u i) • u i with hw
  have h1 : ∀ j ∈ S, dotProduct (∑ i ∈ S, dotProduct c (u i) • u i) (u j) = dotProduct c (u j) := by
    intro j hj
    rw [sum_dotProduct, Finset.sum_eq_single j]
    · rw [smul_dotProduct, hu1 j hj, smul_eq_mul, mul_one]
    · intro i hi hij; rw [smul_dotProduct, hu0 i hi j hj hij, smul_zero]
    · intro h; exact absurd hj h
  have h0 : 0 ≤ dotProduct w w := by
    simp only [dotProduct, ← sq]; exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h2 : dotProduct w w = dotProduct c c - ∑ i ∈ S, dotProduct c (u i) ^ 2 := by
    have hA : dotProduct (∑ i ∈ S, dotProduct c (u i) • u i) (∑ i ∈ S, dotProduct c (u i) • u i)
        = ∑ i ∈ S, dotProduct c (u i) ^ 2 := by
      rw [dotProduct_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [dotProduct_smul, h1 j hj, smul_eq_mul, sq]
    have hB : dotProduct c (∑ i ∈ S, dotProduct c (u i) • u i) =
        ∑ i ∈ S, dotProduct c (u i) ^ 2 := by
      rw [dotProduct_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [dotProduct_smul, smul_eq_mul, sq]
    rw [hw, sub_dotProduct, dotProduct_sub, dotProduct_sub, hA, hB,
      dotProduct_comm (∑ i ∈ S, dotProduct c (u i) • u i) c, hB]
    ring
  linarith
end LovaszTheta
