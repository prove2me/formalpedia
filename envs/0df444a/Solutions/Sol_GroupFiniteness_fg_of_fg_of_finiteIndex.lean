-- Prove2me | solution 1 for GroupFiniteness.fg_of_fg_of_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-20T17:08:03.258688+00:00
-- url     : https://prove2.me/submissions/8f83e764-1c9d-4820-bc8e-d8994f4d10f8

import Mathlib

/-!
# Finite generation: the two directions across a finite-index subgroup

Mathlib has Schreier's lemma `Subgroup.fg_of_index_ne_zero`, that a finite-index subgroup of a
finitely generated group is finitely generated.  Wolf's Proposition 4.1 needs the converse as
well, that finite generation passes *up* from a finite-index subgroup, and the standard
"generators of the quotient together with the kernel" principle.
-/

namespace Wolf
namespace Lib

open Subgroup

/-- Transport finite generation along an isomorphism. -/
theorem fg_of_mulEquiv {A B : Type*} [Group A] [Group B] [Group.FG A] (e : A ≃* B) :
    Group.FG B :=
  Group.fg_of_surjective (f := (e : A →* B)) e.surjective

/-- Finite generation passes **up** from a subgroup of finite index: a finite generating set of
`H` together with a transversal of `H` generates the whole group. -/
theorem fg_of_fg_of_finiteIndex {G : Type*} [Group G] (H : Subgroup G)
    [H.FiniteIndex] [Group.FG H] : Group.FG G := by
  classical
  obtain ⟨T, hT, hTfin⟩ := (Group.fg_iff (G := H)).1 inferInstance
  set R : Set G := Set.range (fun q : G ⧸ H => Quotient.out q) with hR
  set A : Set G := H.subtype '' T ∪ R with hA
  have himg : Subgroup.closure (H.subtype '' T) = H := by
    rw [← MonoidHom.map_closure, hT, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine Group.fg_iff.2 ⟨A, ?_, (hTfin.image _).union (Set.finite_range _)⟩
  have hHle : H ≤ Subgroup.closure A := by
    rw [← himg]
    exact Subgroup.closure_mono Set.subset_union_left
  refine eq_top_iff.2 fun g _ => ?_
  have hrep : (Quotient.out (QuotientGroup.mk g : G ⧸ H)) ∈ Subgroup.closure A :=
    Subgroup.subset_closure (Set.mem_union_right _ ⟨_, rfl⟩)
  have hmem : (Quotient.out (QuotientGroup.mk g : G ⧸ H))⁻¹ * g ∈ H := by
    rw [← QuotientGroup.eq]
    exact Quotient.out_eq' _
  have := Subgroup.mul_mem _ hrep (hHle hmem)
  simpa using this

/-- If `Q` is finitely generated and `f : A →* Q` is onto with kernel inside `N`, then finitely
many elements of `A` together with `N` generate `A`. -/
theorem exists_finset_sup_eq_top {A Q : Type*} [Group A] [Group Q] [Group.FG Q]
    (f : A →* Q) (hf : Function.Surjective f) (N : Subgroup A) (hN : f.ker ≤ N) :
    ∃ T : Finset A, Subgroup.closure (T : Set A) ⊔ N = ⊤ := by
  classical
  obtain ⟨S, hS, hSfin⟩ := (Group.fg_iff (G := Q)).1 inferInstance
  have hpre : ∀ q : Q, ∃ a : A, f a = q := hf
  choose g hg using hpre
  refine ⟨hSfin.toFinset.image g, ?_⟩
  set K : Subgroup A := Subgroup.closure ((hSfin.toFinset.image g : Finset A) : Set A) ⊔ N with hK
  have hSK : S ⊆ (K : Set A).image f := by
    intro q hq
    refine ⟨g q, ?_, hg q⟩
    refine le_sup_left (a := Subgroup.closure _) (b := N) ?_
    refine Subgroup.subset_closure ?_
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Set.Finite.mem_toFinset]
    exact ⟨q, hq, rfl⟩
  refine eq_top_iff.2 fun a _ => ?_
  have hmap : Subgroup.map f K = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← hS, Subgroup.closure_le]
    intro q hq
    obtain ⟨x, hx, hxq⟩ := hSK hq
    exact ⟨x, hx, hxq⟩
  obtain ⟨k, hk, hkf⟩ : ∃ k ∈ K, f k = f a := by
    have : f a ∈ Subgroup.map f K := hmap ▸ Subgroup.mem_top _
    obtain ⟨k, hk, hkf⟩ := this
    exact ⟨k, hk, hkf⟩
  have : a * k⁻¹ ∈ f.ker := by simp [MonoidHom.mem_ker, hkf]
  have h1 : a * k⁻¹ ∈ K := le_sup_right (a := Subgroup.closure _) (b := N) (hN this)
  simpa using Subgroup.mul_mem _ h1 hk

end Lib
end Wolf

theorem solution {G : Type*} [Group G] (H : Subgroup G)
    [H.FiniteIndex] [Group.FG H] : Group.FG G :=
  Wolf.Lib.fg_of_fg_of_finiteIndex H
