-- Prove2me | solution 1 for NaturalProofs.sum_resample
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:38:12.206877+00:00
-- url     : https://prove2.me/submissions/97938471-2db0-49fa-88c9-924011d2862d

module
public import Mathlib
public import Definitions.Def_NaturalProofs_Prob

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open Finset
variable {Ω Ω' A B I X : Type} [Fintype Ω] [Fintype Ω'] [Fintype A] [Fintype B] [Fintype I]
  [Fintype X]
namespace NaturalProofs
theorem _root_.solution [DecidableEq I] (e : I) (h : (I → X) → ℝ) :
    ∑ ω : I → X, ∑ z : X, h (Function.update ω e z) = Fintype.card X * ∑ ω, h ω := by
  set φ := Equiv.funSplitAt e X
  have hupd : ∀ (x z : X) (r : {j // j ≠ e} → X),
      Function.update (φ.symm (x, r)) e z = φ.symm (z, r) := by
    intro x z r
    funext j
    by_cases hj : j = e
    · subst hj
      simp [φ, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [φ, Equiv.funSplitAt, Equiv.piSplitAt, hj]
  rw [← Equiv.sum_comp φ.symm (fun ω => ∑ z : X, h (Function.update ω e z)),
    ← Equiv.sum_comp φ.symm h]
  simp only [Fintype.sum_prod_type, hupd]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_comm]
end NaturalProofs
