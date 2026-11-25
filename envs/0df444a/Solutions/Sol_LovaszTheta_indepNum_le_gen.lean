-- Prove2me | solution 1 for LovaszTheta.indepNum_le_gen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T14:48:18.767009+00:00
-- url     : https://prove2.me/submissions/c59e2a46-e747-4dc7-ba6b-29c3640ae812

module
public import Mathlib
public import Definitions.Def_ThetaLib_Theta
public import Theorems.Thm_LovaszTheta_bessel_aux

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open LovaszTheta
variable {V : Type*}
namespace LovaszTheta
theorem _root_.solution [Finite V] (G : SimpleGraph V) {ι : Type*} [Fintype ι]
    (u : V → ι → ℝ)
    (hu1 : ∀ i, dotProduct (u i) (u i) = 1)
    (hu0 : ∀ i j, i ≠ j → ¬ G.Adj i j → dotProduct (u i) (u j) = 0)
    {c : ι → ℝ} (hc : dotProduct c c = 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ∀ i, 1 ≤ t * dotProduct c (u i) ^ 2) :
    (G.indepNum : ℝ) ≤ t := by
  obtain ⟨S, hS⟩ := G.exists_isNIndepSet_indepNum
  have hind := hS.isIndepSet
  rw [← hS.card_eq]
  have hb := bessel_aux S u (fun i _ => hu1 i)
    (fun i hi j hj hij => hu0 i j hij (hind hi hj hij)) c
  rw [hc] at hb
  have : ∀ i ∈ S, (1 : ℝ) ≤ t * dotProduct c (u i) ^ 2 := fun i _ => ht i
  have hsum : (S.card : ℝ) ≤ t * ∑ i ∈ S, dotProduct c (u i) ^ 2 := by
    rw [Finset.mul_sum]
    simpa using Finset.sum_le_sum this
  nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ S) => sq_nonneg (dotProduct c (u i)))]
end LovaszTheta
