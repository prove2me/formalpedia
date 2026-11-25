-- Prove2me | solution 1 for GrahamPollak.sum_prod_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:16:03.479591+00:00
-- url     : https://prove2.me/submissions/e52a244f-b6cb-441b-bb48-9bc9ffdbda46

module
public import Mathlib
public import Definitions.Def_GrahamPollakLib_GrahamPollak

set_option autoImplicit true
@[expose] public section
public section
open GrahamPollak
variable {V : Type*}
variable [DecidableEq V]
namespace GrahamPollak
theorem _root_.solution [Fintype V] {m : ℕ} (A B : Fin m → Finset V) (x : V → ℝ) :
    ∑ i, (∑ u ∈ A i, x u) * (∑ v ∈ B i, x v) =
      ∑ u, ∑ v, x u * x v * ∑ i, ((if u ∈ A i ∧ v ∈ B i then 1 else 0 : ℝ)) := by
  have hA : ∀ (S : Finset V), ∑ u ∈ S, x u = ∑ u, if u ∈ S then x u else 0 := fun S => by
    rw [← Finset.sum_filter]; congr 1; ext; simp
  simp only [hA]
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp_all
end GrahamPollak
