-- Prove2me | solution 1 for GrahamPollak.graham_pollak
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:23:43.064998+00:00
-- url     : https://prove2.me/submissions/3aa5c863-cada-416a-ae01-2487104416d3

module
public import Mathlib
public import Definitions.Def_GrahamPollakLib_GrahamPollak
public import Theorems.Thm_GrahamPollak_sq_sum_eq

set_option autoImplicit true
@[expose] public section
public section
open GrahamPollak
variable {V : Type*}
namespace GrahamPollak
theorem _root_.solution [Fintype V] [DecidableEq V] {m : ℕ} (A B : Fin m → Finset V)
    (h : IsBicliqueDecomposition A B) : Fintype.card V - 1 ≤ m := by
  by_contra hlt
  rw [not_le] at hlt
  let S : Fin (m + 1) → Finset V := Fin.cons Finset.univ A
  let L : (V → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) :=
    LinearMap.pi fun j => ∑ v ∈ S j, LinearMap.proj v
  have hL : ∀ x j, L x j = ∑ v ∈ S j, x v := by
    intro x j; simp [L]
  have hker : LinearMap.ker L ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker] at hx
  have hsum : ∑ v, x v = 0 := by
    have := congrFun hx 0
    rw [hL] at this
    simpa [S] using this
  have hA : ∀ i, ∑ v ∈ A i, x v = 0 := by
    intro i
    have := congrFun hx i.succ
    rw [hL] at this
    simpa [S] using this
  have hsq := sq_sum_eq h x
  simp only [hA, zero_mul, Finset.sum_const_zero, mul_zero, add_zero, hsum] at hsq
  have h0 : ∑ v, x v ^ 2 = 0 := by simpa using hsq.symm
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => sq_nonneg (x v))).mp h0
  apply hx0
  funext v
  simpa using hall v (Finset.mem_univ v)
end GrahamPollak
