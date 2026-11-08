-- Prove2me | solution 1 for LimitedPersuasion.rhoE_eq_of_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:52:10.803808+00:00
-- url     : https://prove2.me/submissions/dd36aee1-55b8-4b9e-abcb-558bd3e2f5c1

import Mathlib
import Definitions.Def_LimitedPersuasion_Model

open LimitedPersuasion in
theorem solution {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ} [NeZero n]
    (I : Instance T n) (hsym : I.IsSymmetric) (i : Fin n) :
    I.rhoE = ∑ θ, I.q θ * I.ρ (θ i) := by
  have key : ∀ j : Fin n, ∑ θ, I.q θ * I.ρ (θ j) = ∑ θ, I.q θ * I.ρ (θ i) := by
    intro j
    let e : Equiv.Perm (Fin n → T) :=
      { toFun := fun θ => θ ∘ Equiv.swap i j
        invFun := fun θ => θ ∘ Equiv.swap i j
        left_inv := fun θ => by funext k; simp
        right_inv := fun θ => by funext k; simp }
    rw [← Equiv.sum_comp e (fun θ => I.q θ * I.ρ (θ j))]
    refine Finset.sum_congr rfl fun θ _ => ?_
    show I.q (θ ∘ Equiv.swap i j) * I.ρ ((θ ∘ Equiv.swap i j) j) = _
    rw [hsym, Function.comp_apply, Equiv.swap_apply_right]
  unfold Instance.rhoE
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun j _ => le_of_eq (key j)
  · exact Finset.le_sup' (fun j : Fin n => ∑ θ, I.q θ * I.ρ (θ j)) (Finset.mem_univ i)
