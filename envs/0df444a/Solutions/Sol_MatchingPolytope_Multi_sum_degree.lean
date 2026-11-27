-- Prove2me | solution 1 for MatchingPolytope.Multi.sum_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:23:21.491826+00:00
-- url     : https://prove2.me/submissions/31507069-c322-4fac-9706-678ff3bb82c9

module
public import Mathlib
public import Definitions.Def_MatchingPolytope_Multigraph
public import Theorems.Thm_MatchingPolytope_Multi_Valid_pair
public import Theorems.Thm_MatchingPolytope_Multi_mem_gcut_singleton

set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
namespace MatchingPolytope.Multi
theorem _root_.solution {β : Type*} [AddCommMonoid β] (hV : Valid ends W F) {D : Finset E}
    (hD : D ⊆ F) (S : Finset V) (x : E → β) :
    ∑ v ∈ S, ∑ e ∈ gcut ends D {v}, x e =
      ∑ e ∈ gcut ends D S, x e + 2 • ∑ e ∈ inside ends D S, x e := by
  classical
  have h1 : ∀ v, ∑ e ∈ gcut ends D {v}, x e = ∑ e ∈ D, if v ∈ ends e then x e else 0 := by
    intro v
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext e
    rw [mem_gcut_singleton hV hD, Finset.mem_filter]
  simp_rw [h1]
  rw [Finset.sum_comm, gcut, inside, Finset.sum_filter, Finset.sum_filter, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  obtain ⟨a, b, hab, -, -, h⟩ := hV.pair (hD he)
  have h2 : ∀ v, (if v ∈ ends e then x e else 0) =
      (if v = a then x e else 0) + (if v = b then x e else 0) := by
    intro v
    by_cases hva : v = a
    · subst hva; simp [h, hab]
    · simp [h, hva]
  simp_rw [h2]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [h, Sym2.mem_iff, forall_eq_or_imp, forall_eq, exists_eq_or_imp]
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha, hb, two_smul]
end MatchingPolytope.Multi
