-- Prove2me | solution 1 for Module.Basis.repr_mem_range_ratCast_of_forall_dual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/cfbd505a-e933-513f-bdb8-c6e544ddc120

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Basis_repr_mem_range_ratCast_of_forall_dual

set_option autoImplicit false

open scoped BigOperators

namespace RatCoords

theorem exists_sum_smul_eq_of_algebraMap {K : Type*} [Field K] [Algebra K ℂ]
    {ι E : Type*} [Fintype ι] [Fintype E]
    (col : ι → E → K) (β : E → K) (c : ι → ℂ)
    (hc : ∑ i, c i • ((algebraMap K ℂ) ∘ col i) = (algebraMap K ℂ) ∘ β) :
    ∃ x : ι → K, ∑ i, x i • col i = β := by
  classical
  haveI : FaithfulSMul K ℂ :=
    (faithfulSMul_iff_algebraMap_injective K ℂ).mpr (algebraMap K ℂ).injective
  rw [← Submodule.mem_span_range_iff_exists_fun]
  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent K (Set.range col)
  rw [← hs_span]
  by_contra hβ

  let fam : Option s → E → K := fun o => Option.casesOn o β (fun m => (m : E → K))
  have hfam : LinearIndependent K fam := by
    rw [linearIndependent_option]
    refine ⟨?_, ?_⟩
    · exact hs_li
    · show β ∉ Submodule.span K (Set.range (fun m : s => (m : E → K)))
      rwa [Subtype.range_coe_subtype, Set.setOf_mem_eq]

  have hfamC : LinearIndependent ℂ (fun o => (algebraMap K ℂ) ∘ fam o) :=
    (linearIndependent_algebraMap_comp_iff (v := fam)).mpr hfam
  rw [linearIndependent_option] at hfamC
  apply hfamC.2

  show (algebraMap K ℂ) ∘ β ∈
    Submodule.span ℂ (Set.range (fun m : s => (algebraMap K ℂ) ∘ (m : E → K)))
  rw [← hc]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_

  have hcol : col i ∈ Submodule.span K s := by
    rw [hs_span]; exact Submodule.subset_span (Set.mem_range_self i)
  let Φ : (E → K) →ₗ[K] (E → ℂ) :=
    { toFun := fun y => (algebraMap K ℂ) ∘ y
      map_add' := fun y z => by ext e; simp
      map_smul' := fun r y => by ext e; simp [Algebra.smul_def] }
  have h1 : Φ (col i) ∈ Submodule.span K (Φ '' s) := by
    rw [← Submodule.map_span]; exact Submodule.mem_map_of_mem hcol
  have h2 : Submodule.span K (Φ '' s) ≤
      (Submodule.span ℂ (Φ '' s)).restrictScalars K := Submodule.span_le_restrictScalars K ℂ _
  have h3 := h2 h1
  rw [Submodule.restrictScalars_mem] at h3
  have h4 : Φ '' s = Set.range (fun m : s => (algebraMap K ℂ) ∘ (m : E → K)) := by
    ext y
    simp only [Set.mem_image, Set.mem_range, Subtype.exists, exists_prop]
    constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
  rw [h4] at h3
  exact h3

theorem exists_finset_separating {V : Type*} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] [Module.Free ℂ V]
    {A : Type*} (φ : A → V →ₗ[ℂ] ℂ) (hinj : ∀ x : V, (∀ a : A, φ a x = 0) → x = 0) :
    ∃ s : Set (V →ₗ[ℂ] ℂ), s.Finite ∧ s ⊆ Set.range φ ∧
      ∀ x : V, (∀ ψ ∈ s, ψ x = 0) → x = 0 := by
  obtain ⟨s, hs_sub, hs_span, hs_li⟩ := exists_linearIndependent ℂ (Set.range φ)
  refine ⟨s, hs_li.setFinite, hs_sub, fun x hx => hinj x fun a => ?_⟩
  have ha : φ a ∈ Submodule.span ℂ s := by
    rw [hs_span]; exact Submodule.subset_span (Set.mem_range_self a)
  refine Submodule.span_induction (p := fun ψ _ => ψ x = 0) ?_ ?_ ?_ ?_ ha
  · exact fun ψ hψ => hx ψ hψ
  · simp
  · intro ψ χ _ _ hψ hχ; simp [hψ, hχ]
  · intro r ψ _ hψ; simp [hψ]

theorem main
    {ι : Type*} [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) {A : Type*} (φ : A → V →ₗ[ℂ] ℂ)
    (hinj : ∀ x : V, (∀ a : A, φ a x = 0) → x = 0)
    (hφb : ∀ (a : A) (i : ι), φ a (b i) ∈ Set.range ((↑) : ℚ → ℂ))
    (h : V) (hh : ∀ a : A, φ a h ∈ Set.range ((↑) : ℚ → ℂ)) (i : ι) :
    b.repr h i ∈ Set.range ((↑) : ℚ → ℂ) := by
  classical
  haveI : Module.Finite ℂ V := Module.Finite.of_basis b
  haveI : Module.Free ℂ V := Module.Free.of_basis b
  obtain ⟨s, hs_fin, hs_sub, hs_sep⟩ := exists_finset_separating φ hinj
  haveI : Fintype s := hs_fin.fintype

  choose aOf haOf using hs_sub

  choose q hq using hφb
  choose r hr using hh

  let col : ι → s → ℚ := fun i e => q (aOf e.2) i
  let β : s → ℚ := fun e => r (aOf e.2)

  let c : ι → ℂ := b.equivFun h
  have hsum : h = ∑ i, c i • b i := (b.sum_equivFun h).symm
  have hc : ∑ i, c i • ((algebraMap ℚ ℂ) ∘ col i) = (algebraMap ℚ ℂ) ∘ β := by
    funext e
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul,
      eq_ratCast, col, β, hq, hr]
    rw [haOf e.2]
    conv_rhs => rw [hsum]
    simp [map_sum, map_smul, smul_eq_mul]
  obtain ⟨x, hx⟩ := exists_sum_smul_eq_of_algebraMap col β c hc

  let h' : V := ∑ i, ((x i : ℚ) : ℂ) • b i
  have hval : ∀ e : s, (e : V →ₗ[ℂ] ℂ) h' = (e : V →ₗ[ℂ] ℂ) h := by
    intro e
    have hxe := congrFun hx e
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, col, β] at hxe

    have hxeC : ∑ i, ((x i : ℚ) : ℂ) * (q (aOf e.2) i : ℂ) = (r (aOf e.2) : ℂ) := by
      have := congrArg (fun t : ℚ => (t : ℂ)) hxe
      push_cast at this
      exact this
    simp only [hq, hr] at hxeC
    rw [← haOf e.2]
    simp only [h', map_sum, map_smul, smul_eq_mul]
    exact hxeC
  have heq : h' = h := by
    have h0 : h' - h = 0 := hs_sep _ fun ψ hψ => by
      have := hval ⟨ψ, hψ⟩
      simp [this]
    exact sub_eq_zero.mp h0
  have hcoord : b.repr h i = ((x i : ℚ) : ℂ) := by
    rw [← heq]
    simp [h', map_sum, map_smul, Module.Basis.repr_self, Finsupp.single_apply]
  exact ⟨x i, hcoord.symm⟩

end RatCoords

theorem solution
    {ι : Type*} [Fintype ι] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis ι ℂ V) {A : Type*} (φ : A → V →ₗ[ℂ] ℂ)
    (hinj : ∀ x : V, (∀ a : A, φ a x = 0) → x = 0)
    (hφb : ∀ (a : A) (i : ι), φ a (b i) ∈ Set.range ((↑) : ℚ → ℂ))
    (h : V) (hh : ∀ a : A, φ a h ∈ Set.range ((↑) : ℚ → ℂ)) (i : ι) :
    b.repr h i ∈ Set.range ((↑) : ℚ → ℂ) :=
  RatCoords.main b φ hinj hφb h hh i

end S_Module_Basis_repr_mem_range_ratCast_of_forall_dual
end P2MW
export P2MW.S_Module_Basis_repr_mem_range_ratCast_of_forall_dual (solution)
