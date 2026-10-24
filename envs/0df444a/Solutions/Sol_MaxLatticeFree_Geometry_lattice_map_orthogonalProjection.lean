-- Prove2me | solution 1 for MaxLatticeFree.Geometry.lattice_map_orthogonalProjection
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:35:27.260564+00:00
-- url     : https://prove2.me/submissions/ec7fafe7-5e41-470c-aa14-74c9302f62e4

import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_IsLatticeOf
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaSubspace

namespace MaxLatticeFree.Geometry.ProjectionProof

open Module Submodule Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Smith normal form separates the lattice directions killed by a real linear map. -/
lemma image_lattice_basis {m : ℕ} (b : Basis (Fin m) ℝ E)
    (K : Submodule ℝ E)
    (hK : K = span ℝ ((span ℤ (Set.range b) : Set E) ∩ (K : Set E)))
    (f : E →ₗ[ℝ] F) (hf : LinearMap.ker f = K) :
    ∃ k : ℕ, ∃ a : Fin k → F, LinearIndependent ℝ a ∧
      span ℝ (Set.range a) = LinearMap.range f ∧
      (span ℤ (Set.range b)).map (f.restrictScalars ℤ) = span ℤ (Set.range a) := by
  classical
  let Ξ : Submodule ℤ E := span ℤ (Set.range b)
  let N : Submodule ℤ Ξ := (K.restrictScalars ℤ).comap Ξ.subtype
  obtain ⟨k, snf⟩ := N.smithNormalForm (b.restrictScalars ℤ)
  let c : Basis (Fin m) ℝ E := snf.bM.ofZLatticeBasis ℝ Ξ
  have hc (i : Fin m) : c i = (snf.bM i : E) := by
    exact Basis.ofZLatticeBasis_apply ℝ Ξ snf.bM i
  have hhead : ∀ i ∈ Set.range snf.f, c i ∈ K := by
    rintro _ ⟨j, rfl⟩
    have ha : snf.a j ≠ 0 := by
      intro h
      apply snf.bN.ne_zero j
      apply Subtype.ext
      simp [snf.snf, h]
    have hn : ((snf.bN j : Ξ) : E) ∈ K := (snf.bN j).property
    have heq : ((snf.bN j : Ξ) : E) = (snf.a j : ℝ) • c (snf.f j) := by
      rw [snf.snf, hc]
      simp only [Submodule.coe_smul, Int.cast_smul_eq_zsmul]
    rw [heq] at hn
    exact (K.smul_mem_iff (by exact_mod_cast ha)).mp hn
  have hKhead : K = span ℝ (c '' Set.range snf.f) := by
    apply le_antisymm
    · rw [hK]
      apply span_le.mpr
      intro x hx
      apply c.mem_span_image.mpr
      intro i hi
      by_contra hi'
      have hz := snf.repr_eq_zero_of_notMem_range (⟨⟨x, hx.1⟩, hx.2⟩ : N) hi'
      have hcoord : c.repr x i = 0 := by
        rw [show c.repr x i = (snf.bM.repr ⟨x, hx.1⟩ i : ℝ) from
          Basis.ofZLatticeBasis_repr_apply ℝ Ξ snf.bM ⟨x, hx.1⟩ i]
        rw [hz, Int.cast_zero]
      exact (Finsupp.mem_support_iff.mp hi) hcoord
    · exact span_le.mpr (by rintro _ ⟨i, hi, rfl⟩; exact hhead i hi)
  let J : Type := {i : Fin m // i ∉ Set.range snf.f}
  let a : J → F := fun i => f (c i)
  have hzero : ∀ i ∈ Set.range snf.f, f (c i) = 0 := by
    intro i hi
    exact LinearMap.mem_ker.mp (hf ▸ hhead i hi)
  have hli : LinearIndependent ℝ a := by
    apply (c.linearIndependent.comp (fun i : J => (i : Fin m)) Subtype.val_injective).map
    rw [hf, hKhead]
    have heq : Set.range (fun i : J => c (i : Fin m)) = c '' (Set.range snf.f)ᶜ := by
      ext x
      simp only [mem_range, mem_image, mem_compl_iff]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, i.2, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, hi⟩, rfl⟩
    simp only [Function.comp_def]
    rw [heq]
    exact c.linearIndependent.disjoint_span_image disjoint_compl_left
  have hzspan : span ℤ (Set.range c) = Ξ := snf.bM.ofZLatticeBasis_span ℝ Ξ
  have hzimage : Ξ.map (f.restrictScalars ℤ) = span ℤ (Set.range a) := by
    rw [← hzspan, Submodule.map_span, ← Set.range_comp]
    apply le_antisymm
    · apply span_le.mpr
      rintro _ ⟨i, rfl⟩
      change f (c i) ∈ _
      by_cases hi : i ∈ Set.range snf.f
      · rw [hzero i hi]
        exact zero_mem _
      · exact subset_span ⟨(⟨i, hi⟩ : J), rfl⟩
    · apply span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact subset_span ⟨(i : Fin m), rfl⟩
  have hrimage : LinearMap.range f = span ℝ (Set.range a) := by
    rw [← Submodule.map_top f, ← c.span_eq, Submodule.map_span, ← Set.range_comp]
    apply le_antisymm
    · apply span_le.mpr
      rintro _ ⟨i, rfl⟩
      by_cases hi : i ∈ Set.range snf.f
      · rw [Function.comp_apply, hzero i hi]
        exact zero_mem _
      · exact subset_span ⟨(⟨i, hi⟩ : J), rfl⟩
    · apply span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact subset_span ⟨(i : Fin m), rfl⟩
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  have hrange : Set.range (a ∘ e) = Set.range a := e.surjective.range_comp a
  refine ⟨Fintype.card J, a ∘ e, hli.comp e e.injective, ?_, ?_⟩
  · rw [hrange, ← hrimage]
  · rw [hrange]
    exact hzimage

end MaxLatticeFree.Geometry.ProjectionProof

open Module Submodule Set
open MaxLatticeFree.Geometry MaxLatticeFree.Geometry.ProjectionProof

theorem solution {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hL : IsLambdaSubspace Λ V L) :
    IsLatticeOf (Λ.map (Lᗮ.starProjection : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)).toLinearMap.toAddMonoidHom)
      (Lᗮ ⊓ V) := by
  classical
  obtain ⟨m, a, ha, hspan, hΛeq⟩ := hΛ
  let b : Basis (Fin m) ℝ V := (Basis.span ha).map (LinearEquiv.ofEq _ _ hspan)
  have hb (i : Fin m) : (b i : EuclideanSpace ℝ (Fin n)) = a i := by
    simp [b, Basis.span_apply]
  let Ξ : Submodule ℤ V := span ℤ (Set.range b)
  have hmap : Ξ.map (V.subtype.restrictScalars ℤ) = Λ.toIntSubmodule := by
    dsimp [Ξ]
    rw [Submodule.map_span, ← Set.range_comp, hΛeq, AddSubgroup.toIntSubmodule_closure]
    congr 1
    ext x
    simp only [mem_range, Function.comp_apply, LinearMap.coe_restrictScalars,
      Submodule.subtype_apply, hb]
  have hXi (x : V) (hx : (x : EuclideanSpace ℝ (Fin n)) ∈ Λ) : x ∈ Ξ := by
    have hh : (x : EuclideanSpace ℝ (Fin n)) ∈ Ξ.map (V.subtype.restrictScalars ℤ) := by
      rw [hmap]
      exact hx
    obtain ⟨y, hy, hxy⟩ := hh
    exact (Subtype.val_injective hxy) ▸ hy
  let K : Submodule ℝ V := L.comap V.subtype
  have hK : K = span ℝ ((Ξ : Set V) ∩ (K : Set V)) := by
    apply le_antisymm
    · let Q : Submodule ℝ V := span ℝ ((Ξ : Set V) ∩ (K : Set V))
      have hLQ : L ≤ Q.map V.subtype := by
        obtain ⟨k, c, hc, hcspan, hcΛ⟩ := hL.2
        rw [← hcspan]
        apply span_le.mpr
        rintro _ ⟨i, rfl⟩
        have hci : c i ∈ L := hcspan ▸ subset_span (mem_range_self i)
        let v : V := ⟨c i, hL.1 hci⟩
        refine ⟨v, subset_span ⟨hXi v (hcΛ i), hci⟩, rfl⟩
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hLQ hx
      exact (Subtype.val_injective hxy) ▸ hy
    · exact span_le.mpr (fun x hx => hx.2)
  let π : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Lᗮ.starProjection.toLinearMap
  let f : V →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := π.comp V.subtype
  have hf : LinearMap.ker f = K := by
    dsimp [f, π, K]
    rw [LinearMap.ker_comp, Submodule.ker_starProjection, Submodule.orthogonal_orthogonal]
  obtain ⟨k, c, hc, hcspan, hcZ⟩ := image_lattice_basis b K hK f hf
  have hπV (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ V) : π x ∈ V := by
    have heq : π x = x - L.starProjection x := by
      apply eq_sub_iff_add_eq.mpr
      simpa only [π, ContinuousLinearMap.coe_coe, add_comm] using
        L.starProjection_add_starProjection_orthogonal x
    rw [heq]
    exact V.sub_mem hx (hL.1 (by simp))
  have hrange : LinearMap.range f = Lᗮ ⊓ V := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨by simp [f, π], hπV y y.2⟩
    · intro hx
      refine ⟨⟨x, hx.2⟩, ?_⟩
      exact Lᗮ.starProjection_eq_self_iff.mpr hx.1
  refine ⟨k, c, hc, hcspan.trans hrange, ?_⟩
  have hg : Λ.toIntSubmodule.map (π.restrictScalars ℤ) = span ℤ (Set.range c) := by
    rw [← hmap, ← Submodule.map_comp]
    exact hcZ
  have hhom : ((π.restrictScalars ℤ) : EuclideanSpace ℝ (Fin n) →+
      EuclideanSpace ℝ (Fin n)) = π.toAddMonoidHom := by
    ext x
    rfl
  have h := congrArg Submodule.toAddSubgroup hg
  simpa only [Submodule.map_toAddSubgroup, AddSubgroup.toIntSubmodule_toAddSubgroup,
    Submodule.span_int_eq_addSubgroupClosure, hhom] using h
