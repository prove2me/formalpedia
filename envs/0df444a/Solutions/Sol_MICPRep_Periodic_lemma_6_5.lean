-- Prove2me | solution 1 for MICPRep.Periodic.lemma_6_5
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:52:32.30169+00:00
-- url     : https://prove2.me/submissions/b4b44e99-6284-4349-8b08-ff9318e9fa1a

import Mathlib
import Theorems.Thm_MaxLatticeFree_Geometry_lovasz_maxLambdaFree_iff
import Definitions.Def_MICPRep_Periodic_Setting
import Definitions.Def_MaxLatticeFree_Geometry_IsLatticeOf
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaSubspace
import Definitions.Def_MaxLatticeFree_Geometry_intW
import Definitions.Def_MaxLatticeFree_Geometry_IsLambdaFree
import Definitions.Def_MaxLatticeFree_Geometry_affDim
import Definitions.Def_MaxLatticeFree_Geometry_Polyhedron
import Theorems.Thm_MICPRep_Periodic_lemma_6_3
import Theorems.Thm_MICPRep_Periodic_lemma_6_4

set_option linter.unusedVariables false
set_option linter.style.haveILetI false


open Pointwise

namespace SlabDependency
open MaxLatticeFree.Geometry

def LovaszStatement : Prop :=
  ∀ {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V) (hV : 0 < Module.finrank ℝ V)
    (S : Set (EuclideanSpace ℝ (Fin n))),
    IsMaxLambdaFree Λ V S ↔
      (IsPolyhedronIn V S ∧
        ∃ (P : Set (EuclideanSpace ℝ (Fin n))) (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))),
          IsPolytope P ∧ IsLambdaSubspace Λ V L ∧ S = P + (L : Set (EuclideanSpace ℝ (Fin n))) ∧
          affDim S = affDim P + (Module.finrank ℝ L : ℤ) ∧
          affDim P + (Module.finrank ℝ L : ℤ) = (Module.finrank ℝ V : ℤ) ∧
          (Λ : Set (EuclideanSpace ℝ (Fin n))) ∩ intW (V : Set (EuclideanSpace ℝ (Fin n))) S = ∅ ∧
          ∀ F : Set (EuclideanSpace ℝ (Fin n)), IsFacet S F → ∃ x ∈ Λ, x ∈ relint F) ∨
      (∃ v ∈ V, ∃ L : Submodule ℝ (EuclideanSpace ℝ (Fin n)), L ≤ V ∧
        Module.finrank ℝ L + 1 = Module.finrank ℝ V ∧
        S = v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n))) ∧ ¬ IsLambdaSubspace Λ V L)

end SlabDependency


namespace MICPRep.Periodic.SlabProof

lemma interior_sUnion_chain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (c : Set (Set E)) (hc : IsChain (· ⊆ ·) c)
    (hconv : ∀ S ∈ c, Convex ℝ S) (hne : c.Nonempty) :
    interior (⋃₀ c) ⊆ ⋃ S ∈ c, interior S := by
  classical
  haveI : Nonempty c := hne.to_subtype
  intro z hz
  obtain ⟨b, hzb, hb⟩ := exists_mem_interior_convexHull_affineBasis
    (mem_interior_iff_mem_nhds.mp hz)
  have hm (i : Fin (Module.finrank ℝ E + 1)) : ∃ S : c, b i ∈ (S : Set E) := by
    have hmem := hb (subset_convexHull ℝ (Set.range b) (Set.mem_range_self i))
    obtain ⟨S, hSc, hbS⟩ := Set.mem_sUnion.mp hmem
    exact ⟨⟨S, hSc⟩, hbS⟩
  choose f hf using hm
  have hdir : Directed (· ⊆ ·) (fun S : c => (S : Set E)) :=
    directedOn_iff_directed.mp hc.directedOn
  obtain ⟨S, hS⟩ := hdir.finset_le (Finset.univ.image f)
  have hrange : Set.range b ⊆ (S : Set E) := by
    rintro _ ⟨i, rfl⟩
    exact hS (f i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩) (hf i)
  have hsub := convexHull_min hrange (hconv S S.property)
  exact Set.mem_iUnion.mpr ⟨S, Set.mem_iUnion.mpr ⟨S.property, interior_mono hsub hzb⟩⟩

lemma exists_maximal_convex_avoiding_interior {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (D C : Set E)
    (hC : Convex ℝ C) (havoid : Disjoint (interior C) D) :
    ∃ S : Set E, C ⊆ S ∧ Convex ℝ S ∧ Disjoint (interior S) D ∧
      ∀ T : Set E, Convex ℝ T → Disjoint (interior T) D → S ⊆ T → T ⊆ S := by
  classical
  let F : Set (Set E) := {S | Convex ℝ S ∧ Disjoint (interior S) D}
  have hchain (c : Set (Set E)) (hcF : c ⊆ F) (hc : IsChain (· ⊆ ·) c)
      (hne : c.Nonempty) : ∃ ub ∈ F, ∀ S ∈ c, S ⊆ ub := by
    refine ⟨⋃₀ c, ⟨hc.directedOn.convex_sUnion (fun S hS => (hcF hS).1), ?_⟩,
      fun S hS => Set.subset_sUnion_of_mem hS⟩
    apply Set.disjoint_left.mpr
    intro z hz hzD
    have hm := interior_sUnion_chain c hc (fun S hS => (hcF hS).1) hne hz
    obtain ⟨S, hmem⟩ := Set.mem_iUnion.mp hm
    obtain ⟨hSc, hzint⟩ := Set.mem_iUnion.mp hmem
    exact Set.disjoint_left.mp (hcF hSc).2 hzint hzD
  obtain ⟨S, hCS, hmax⟩ := zorn_subset_nonempty F hchain C ⟨hC, havoid⟩
  refine ⟨S, hCS, hmax.prop.1, hmax.prop.2, ?_⟩
  intro T hT hTD hST
  exact hmax.2 ⟨hT, hTD⟩ hST

end MICPRep.Periodic.SlabProof


open scoped Pointwise

namespace MICPRep.Periodic.SlabProof
open MaxLatticeFree.Geometry

lemma intW_subtype {n : ℕ} (W C : Set (EuclideanSpace ℝ (Fin n))) (hCW : C ⊆ W) :
    intW W C = (Subtype.val : W → EuclideanSpace ℝ (Fin n)) ''
      interior ((Subtype.val : W → EuclideanSpace ℝ (Fin n)) ⁻¹' C) := by
  ext x
  constructor
  · rintro ⟨hx, ε, hε, hball⟩
    refine ⟨⟨x, hCW hx⟩, ?_, rfl⟩
    apply mem_interior_iff_mem_nhds.mpr
    apply Metric.mem_nhds_iff.mpr
    refine ⟨ε, hε, ?_⟩
    intro y hy
    exact hball ⟨hy, y.property⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
    refine ⟨show x ∈ (Subtype.val : W → EuclideanSpace ℝ (Fin n)) ⁻¹' C from interior_subset hx, ε, hε, ?_⟩
    rintro y ⟨hy, hyW⟩
    exact hball (show (⟨y, hyW⟩ : W) ∈ Metric.ball x ε from hy)

lemma intW_mono {n : ℕ} (W : Set (EuclideanSpace ℝ (Fin n)))
    {C S : Set (EuclideanSpace ℝ (Fin n))} (hCS : C ⊆ S) : intW W C ⊆ intW W S := by
  rintro x ⟨hx, ε, hε, hball⟩
  exact ⟨hCS hx, ε, hε, hball.trans hCS⟩

lemma maximal_relative {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (C : Set (EuclideanSpace ℝ (Fin n)))
    (hCV : C ⊆ V) (hC : Convex ℝ C)
    (hfree : Disjoint (intW (V : Set _) C) (Λ : Set _)) :
    ∃ S, C ⊆ S ∧ IsMaxLambdaFree Λ V S := by
  let D : Set V := (Subtype.val : V → EuclideanSpace ℝ (Fin n)) ⁻¹' (Λ : Set _)
  let C' : Set V := (Subtype.val : V → EuclideanSpace ℝ (Fin n)) ⁻¹' C
  have hC' : Convex ℝ C' := hC.linear_preimage V.subtype
  have hfree' : Disjoint (interior C') D := by
    apply Set.disjoint_left.mpr
    intro x hx hxD
    apply Set.disjoint_left.mp hfree _ hxD
    rw [intW_subtype _ _ hCV]
    exact ⟨x, hx, rfl⟩
  obtain ⟨S', hC'S', hconv, havoid, hmax⟩ :=
    exists_maximal_convex_avoiding_interior D C' hC' hfree'
  let S : Set (EuclideanSpace ℝ (Fin n)) := Subtype.val '' S'
  have hSV : S ⊆ V := by rintro x ⟨y, hy, rfl⟩; exact y.property
  have hpreS : (Subtype.val : V → EuclideanSpace ℝ (Fin n)) ⁻¹' S = S' :=
    Set.preimage_image_eq _ Subtype.val_injective
  have hCS : C ⊆ S := by
    intro x hx
    exact ⟨⟨x, hCV hx⟩, hC'S' hx, rfl⟩
  refine ⟨S, hCS, ⟨hSV, hconv.linear_image V.subtype, ?_⟩, ?_⟩
  · apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hxΛ, hxInt⟩
    rw [intW_subtype _ _ hSV] at hxInt
    change x ∈ (Subtype.val : V → EuclideanSpace ℝ (Fin n)) '' interior ((Subtype.val : V → EuclideanSpace ℝ (Fin n)) ⁻¹' S) at hxInt
    rw [hpreS] at hxInt
    obtain ⟨y, hy, rfl⟩ := hxInt
    exact Set.disjoint_left.mp havoid hy hxΛ
  · intro T hT hST
    apply Set.Subset.antisymm _ hST
    intro x hxT
    let x' : V := ⟨x, hT.1 hxT⟩
    have hT' : Convex ℝ ((Subtype.val : V → EuclideanSpace ℝ (Fin n)) ⁻¹' T) :=
      hT.2.1.linear_preimage V.subtype
    have hfreeT : Disjoint (interior ((Subtype.val : V → EuclideanSpace ℝ (Fin n)) ⁻¹' T)) D := by
      apply Set.disjoint_left.mpr
      intro y hy hyD
      have hyInt : (y : EuclideanSpace ℝ (Fin n)) ∈ intW (V : Set _) T := by
        rw [intW_subtype _ _ hT.1]
        exact ⟨y, hy, rfl⟩
      have he := hT.2.2
      have : (y : EuclideanSpace ℝ (Fin n)) ∈ (Λ : Set _) ∩ intW (V : Set _) T := ⟨hyD, hyInt⟩
      simp [he] at this
    have hST' : S' ⊆ (Subtype.val : V → EuclideanSpace ℝ (Fin n)) ⁻¹' T := by
      intro y hy
      exact hST ⟨y, hy, rfl⟩
    exact ⟨x', hmax _ hT' hfreeT hST' hxT, rfl⟩

lemma eq_of_intW_vadd_nonempty {n : ℕ}
    (V L : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hLV : L ≤ V)
    (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ V)
    (hInt : (intW (V : Set _) (v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n))))).Nonempty) : L = V := by
  let v' : V := ⟨v, hv⟩
  let L' : Submodule ℝ V := L.comap V.subtype
  have hsub : v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n))) ⊆ (V : Set _) := by
    rintro x ⟨w, hw, rfl⟩
    exact V.add_mem hv (hLV hw)
  have hpre : (Subtype.val : V → EuclideanSpace ℝ (Fin n)) ⁻¹' (v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n)))) =
      v' +ᵥ (L' : Set V) := by
    ext x
    constructor
    · rintro ⟨w, hw, he⟩
      refine ⟨⟨w, hLV hw⟩, hw, ?_⟩
      exact Subtype.ext he
    · rintro ⟨w, hw, he⟩
      refine ⟨(w : EuclideanSpace ℝ (Fin n)), hw, ?_⟩
      exact congrArg Subtype.val he
  rw [intW_subtype _ _ hsub, Set.image_nonempty] at hInt
  change (interior ((Subtype.val : V → EuclideanSpace ℝ (Fin n)) ⁻¹'
    (v +ᵥ (L : Set (EuclideanSpace ℝ (Fin n)))))).Nonempty at hInt
  rw [hpre, interior_vadd, Set.vadd_set_nonempty] at hInt
  have htop := L'.eq_top_of_nonempty_interior' hInt
  apply le_antisymm hLV
  intro x hx
  have : (⟨x, hx⟩ : V) ∈ L' := by rw [htop]; trivial
  exact this

lemma relative_bounded_plus_of_lovasz (hLovasz : SlabDependency.LovaszStatement)
    {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hΛ : IsLatticeOf Λ V) (hdim : 0 < Module.finrank ℝ V)
    (C : Set (EuclideanSpace ℝ (Fin n))) (hCV : C ⊆ V) (hC : Convex ℝ C)
    (hInt : (intW (V : Set _) C).Nonempty)
    (hfree : Disjoint (intW (V : Set _) C) (Λ : Set _)) :
    ∃ (P : Set (EuclideanSpace ℝ (Fin n))) (L : Submodule ℝ (EuclideanSpace ℝ (Fin n))),
      Bornology.IsBounded P ∧ IsLambdaSubspace Λ V L ∧ L ≠ V ∧ C ⊆ P + (L : Set _) := by
  obtain ⟨S, hCS, hmax⟩ := maximal_relative Λ V C hCV hC hfree
  have hIntS : (intW (V : Set _) S).Nonempty := hInt.mono (intW_mono _ hCS)
  rcases (hLovasz Λ V hΛ hdim S).mp hmax with ⟨hpoly, P, L, hP, hL, heq, hrest⟩ |
      ⟨v, hv, L, hLV, hLdim, heq, hirr⟩
  · have hPbounded : Bornology.IsBounded P := by
      obtain ⟨F, rfl⟩ := hP
      exact (F.finite_toSet.isCompact_convexHull ℝ).isBounded
    refine ⟨P, L, hPbounded, hL, ?_, heq ▸ hCS⟩
    intro hLV
    have hSV : S = (V : Set _) := by
      obtain ⟨z, hz, ε, hε, hball⟩ := hIntS
      rw [heq] at hz
      obtain ⟨p, hp, w, hw, he⟩ := Set.mem_add.mp hz
      have hpV : p ∈ V := by
        have hpS : p ∈ S := by
          rw [heq]
          exact Set.mem_add.mpr ⟨p, hp, 0, L.zero_mem, add_zero p⟩
        exact hmax.1.1 hpS
      apply Set.Subset.antisymm hmax.1.1
      intro x hx
      rw [heq]
      exact Set.mem_add.mpr ⟨p, hp, x - p, hLV.symm ▸ V.sub_mem hx hpV, by abel⟩
    have hzInt : (0 : EuclideanSpace ℝ (Fin n)) ∈ intW (V : Set _) S := by
      rw [hSV]
      exact ⟨V.zero_mem, 1, zero_lt_one, fun x hx => hx.2⟩
    have hz : (0 : EuclideanSpace ℝ (Fin n)) ∈ (Λ : Set _) ∩ intW (V : Set _) S :=
      ⟨Λ.zero_mem, hzInt⟩
    rw [hmax.1.2.2] at hz
    exact hz
  · exfalso
    rw [heq] at hIntS
    have hLV' := eq_of_intW_vadd_nonempty V L hLV v hv hIntS
    rw [hLV'] at hLdim
    omega

end MICPRep.Periodic.SlabProof


namespace MICPRep.Periodic.SlabProof
open MaxLatticeFree.Geometry

lemma lattice_of_discrete_span {n : ℕ}
    (N : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology N]
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hspan : Submodule.span ℝ (N : Set (EuclideanSpace ℝ (Fin n))) = V) :
    IsLatticeOf N.toAddSubgroup V := by
  classical
  let M : Submodule ℤ V := N.comap (V.subtype.restrictScalars ℤ)
  have hNV : (N : Set (EuclideanSpace ℝ (Fin n))) ⊆ (V : Set _) := by
    rw [← hspan]
    exact Submodule.subset_span
  have hImage : (V.subtype : V → EuclideanSpace ℝ (Fin n)) '' (M : Set V) = (N : Set _) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hNV hx⟩, hx, rfl⟩
  letI : DiscreteTopology M := by
    exact ZLattice.comap_discreteTopology ℝ N
      (e := V.subtype) continuous_subtype_val (Submodule.injective_subtype V)
  letI : IsZLattice ℝ M := ⟨by
    rw [← (Submodule.map_injective_of_injective (Submodule.injective_subtype V)).eq_iff,
      Submodule.map_span, Submodule.map_top, Submodule.range_subtype, hImage, hspan]⟩
  let bZ := Module.finBasis ℤ M
  let bR := bZ.ofZLatticeBasis ℝ M
  let a := fun i => (bR i : EuclideanSpace ℝ (Fin n))
  refine ⟨Module.finrank ℤ M, a, ?_, ?_, ?_⟩
  · exact bR.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  · change Submodule.span ℝ (Set.range (V.subtype ∘ bR)) = V
    rw [Set.range_comp, ← Submodule.map_span, bR.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  · have hZspan : Submodule.span ℤ (Set.range a) = N := by
      change Submodule.span ℤ (Set.range ((V.subtype.restrictScalars ℤ) ∘ bR)) = N
      rw [Set.range_comp, ← Submodule.map_span, bZ.ofZLatticeBasis_span ℝ]
      apply SetLike.ext'
      rw [Submodule.map_coe]
      exact hImage
    have he := congrArg Submodule.toAddSubgroup hZspan
    rw [← AddSubgroup.toIntSubmodule_closure] at he
    exact he.symm

noncomputable def piIntModule (d : ℕ) : Submodule ℤ (Fin d → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d)))

lemma piIntModule_coe (d : ℕ) : (piIntModule d : Set (Fin d → ℝ)) = intLattice d := by
  ext x
  change x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin d))) ↔ x ∈ intLattice d
  rw [(Pi.basisFun ℝ (Fin d)).mem_span_iff_repr_mem ℤ]
  constructor
  · intro hx
    choose z hz using hx
    refine ⟨z, ?_⟩
    ext i
    simpa using hz i
  · rintro ⟨z, rfl⟩ i
    exact ⟨z i, by simp⟩

noncomputable def euclideanIntModule (d : ℕ) : Submodule ℤ (EuclideanSpace ℝ (Fin d)) :=
  ZLattice.comap ℝ (piIntModule d) (EuclideanSpace.equiv (Fin d) ℝ).toLinearMap

instance euclideanIntModule_discrete (d : ℕ) : DiscreteTopology (euclideanIntModule d) := by
  unfold euclideanIntModule piIntModule
  infer_instance

lemma euclideanIntModule_mem {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    x ∈ euclideanIntModule d ↔ (EuclideanSpace.equiv (Fin d) ℝ) x ∈ intLattice d := by
  change (EuclideanSpace.equiv (Fin d) ℝ) x ∈ piIntModule d ↔ _
  rw [← SetLike.mem_coe, piIntModule_coe]

end MICPRep.Periodic.SlabProof


namespace MICPRep.Periodic.SlabProof
open scoped Pointwise

lemma integer_multiple {d : ℕ} {v : Fin d → ℝ} (hv : v ∈ ratPoints d) :
    ∃ m : ℤ, m ≠ 0 ∧ (m : ℝ) • v ∈ intLattice d := by
  classical
  rcases hv with ⟨q, rfl⟩
  obtain ⟨m, hm⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
  choose z hz using hm
  refine ⟨m, nonZeroDivisors.ne_zero m.property, z, ?_⟩
  ext i
  have hi : (z i : ℚ) = (m : ℤ) * q i := by simpa [Algebra.smul_def] using hz i
  change (z i : ℝ) = (m : ℤ) * (q i : ℝ)
  exact_mod_cast hi

lemma rational_mem_integer_span {d : ℕ} (L : Submodule ℝ (Fin d → ℝ))
    {v : Fin d → ℝ} (hv : v ∈ L) (hq : v ∈ ratPoints d) :
    v ∈ Submodule.span ℝ ((L : Set (Fin d → ℝ)) ∩ intLattice d) := by
  obtain ⟨m, hm, hmv⟩ := integer_multiple hq
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have h : (m : ℝ) • v ∈ Submodule.span ℝ ((L : Set (Fin d → ℝ)) ∩ intLattice d) :=
    Submodule.subset_span ⟨L.smul_mem (m : ℝ) hv, hmv⟩
  exact (Submodule.smul_mem_iff _ hmR).mp h

lemma direction_span_integer {d : ℕ} (F : AffineSubspace ℝ (Fin d → ℝ))
    (hF : IsRationalAffineSubspace F) :
    F.direction = Submodule.span ℝ ((F.direction : Set (Fin d → ℝ)) ∩ intLattice d) := by
  apply le_antisymm
  · have hd : F.direction = vectorSpan ℝ ((F : Set (Fin d → ℝ)) ∩ ratPoints d) := by
      conv_lhs => rw [hF.2]
      rw [direction_affineSpan]
    conv_lhs => rw [hd, vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro v ⟨x, hx, y, hy, rfl⟩
    apply rational_mem_integer_span F.direction
    · exact AffineSubspace.vsub_mem_direction hx.1 hy.1
    · rcases hx.2 with ⟨a, rfl⟩
      rcases hy.2 with ⟨b, rfl⟩
      refine ⟨a - b, ?_⟩
      ext i
      simp
  · exact Submodule.span_le.mpr fun _ hv => hv.1


lemma intLattice_subset_ratPoints (d : ℕ) : intLattice d ⊆ ratPoints d := by
  rintro x ⟨k, rfl⟩
  refine ⟨fun i => (k i : ℚ), ?_⟩
  ext i
  simp

lemma rational_of_span_integer {d : ℕ} (F : Submodule ℝ (Fin d → ℝ))
    (hF : F = Submodule.span ℝ ((F : Set (Fin d → ℝ)) ∩ intLattice d)) :
    IsRationalAffineSubspace F.toAffineSubspace := by
  refine ⟨⟨0, F.zero_mem⟩, ?_⟩
  apply SetLike.coe_injective
  change (F : Set (Fin d → ℝ)) = (affineSpan ℝ ((F : Set _) ∩ ratPoints d) : Set _)
  have hz : (0 : Fin d → ℝ) ∈ (F : Set _) ∩ ratPoints d := by
    exact ⟨F.zero_mem, ⟨0, by ext i; simp⟩⟩
  rw [← Set.insert_eq_of_mem hz, affineSpan_insert_zero]
  apply congrArg (fun M : Submodule ℝ (Fin d → ℝ) => (M : Set (Fin d → ℝ)))
  apply le_antisymm
  · conv_lhs => rw [hF]
    exact Submodule.span_mono (Set.inter_subset_inter_right _ (intLattice_subset_ratPoints d))
  · exact Submodule.span_le.mpr Set.inter_subset_left

lemma direction_rational {d : ℕ} (F : AffineSubspace ℝ (Fin d → ℝ))
    (hF : IsRationalAffineSubspace F) : IsRationalAffineSubspace F.direction.toAffineSubspace :=
  rational_of_span_integer F.direction (direction_span_integer F hF)

lemma intrinsic_eq_intW {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) :
    intrinsicInterior ℝ C = MaxLatticeFree.Geometry.intW (affineSpan ℝ C : Set _) C := by
  rw [intW_subtype _ _ (subset_affineSpan ℝ C)]
  rfl

end MICPRep.Periodic.SlabProof


open scoped Pointwise
namespace MICPRep.Periodic.SlabProof
open MaxLatticeFree.Geometry

lemma pi_bounded_plus_of_lovasz (hLovasz : SlabDependency.LovaszStatement)
    {d : ℕ} (F : Submodule ℝ (Fin d → ℝ))
    (hF : IsRationalAffineSubspace F.toAffineSubspace) (hdim : 0 < Module.finrank ℝ F)
    (C : Set (Fin d → ℝ)) (hC : Convex ℝ C) (hne : C.Nonempty)
    (hspan : affineSpan ℝ C = F.toAffineSubspace)
    (hfree : Disjoint (intrinsicInterior ℝ C) (intLattice d)) :
    ∃ (P : Set (Fin d → ℝ)) (L : Submodule ℝ (Fin d → ℝ)),
      Bornology.IsBounded P ∧ IsRationalAffineSubspace L.toAffineSubspace ∧
      L ≤ F ∧ L ≠ F ∧ C ⊆ P + (L : Set (Fin d → ℝ)) := by
  classical
  let e := EuclideanSpace.equiv (Fin d) ℝ
  let V := F.comap e.toLinearMap
  let N : Submodule ℤ (EuclideanSpace ℝ (Fin d)) := euclideanIntModule d ⊓ V.restrictScalars ℤ
  have hNmem (x : EuclideanSpace ℝ (Fin d)) : x ∈ N ↔ e x ∈ F ∧ e x ∈ intLattice d := by
    change (x ∈ euclideanIntModule d ∧ e x ∈ F) ↔ _
    rw [euclideanIntModule_mem, and_comm]
  have hNimage : e '' (N : Set (EuclideanSpace ℝ (Fin d))) =
      (F : Set (Fin d → ℝ)) ∩ intLattice d := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hNmem y).mp hy
    · intro hx
      exact ⟨e.symm x, (hNmem _).mpr (by simpa using hx), e.apply_symm_apply x⟩
  have hVmap : V.map e.toLinearMap = F :=
    Submodule.map_comap_eq_of_surjective e.surjective F
  have hNspan : Submodule.span ℝ (N : Set (EuclideanSpace ℝ (Fin d))) = V := by
    apply (Submodule.map_injective_of_injective e.injective)
    rw [Submodule.map_span, hVmap]
    change Submodule.span ℝ (e '' (N : Set _)) = F
    rw [hNimage]
    simpa only [Submodule.toAffineSubspace_direction] using
      (direction_span_integer F.toAffineSubspace hF).symm
  letI : DiscreteTopology N := by
    have hc : Continuous (fun x : N => (⟨x.val, x.property.1⟩ : euclideanIntModule d)) :=
      continuous_subtype_val.subtype_mk _
    apply DiscreteTopology.of_continuous_injective hc
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : euclideanIntModule d => (z : EuclideanSpace ℝ (Fin d))) hxy)
  have hΛ : IsLatticeOf N.toAddSubgroup V := lattice_of_discrete_span N V hNspan
  have hdimV : 0 < Module.finrank ℝ V := by
    have he := e.toLinearEquiv.finrank_map_eq V
    rw [hVmap] at he
    omega
  let D : Set (EuclideanSpace ℝ (Fin d)) := e.symm '' C
  have hDV : D ⊆ V := by
    rintro x ⟨y, hy, rfl⟩
    change e (e.symm y) ∈ F
    rw [e.apply_symm_apply]
    have := subset_affineSpan ℝ C hy
    simpa [hspan] using this
  have hspanD : affineSpan ℝ D = V.toAffineSubspace := by
    change affineSpan ℝ (e.symm.toLinearEquiv.toAffineEquiv.toAffineMap '' C) = _
    rw [← AffineSubspace.map_span, hspan]
    apply SetLike.coe_injective
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change e (e.symm y) ∈ F
      simpa using hy
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
  have hIntEq : intrinsicInterior ℝ D = intW (V : Set _) D := by
    rw [intrinsic_eq_intW, hspanD]
    rfl
  have hDconv : Convex ℝ D := hC.linear_image e.symm.toLinearMap
  have hDne : D.Nonempty := hne.image e.symm
  have hInt : (intW (V : Set _) D).Nonempty := by
    rw [← hIntEq]
    exact hDne.intrinsicInterior hDconv
  have hDfree : Disjoint (intW (V : Set _) D) (N.toAddSubgroup : Set _) := by
    apply Set.disjoint_left.mpr
    intro x hx hxN
    rw [← hIntEq, show D = e.symm.toLinearEquiv.toAffineEquiv '' C from rfl,
      e.symm.toLinearEquiv.toAffineEquiv.intrinsicInterior_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hlat := ((hNmem (e.symm y)).mp hxN).2
    rw [e.apply_symm_apply] at hlat
    exact Set.disjoint_left.mp hfree hy hlat
  obtain ⟨P, L, hP, hL, hLF, hDP⟩ :=
    relative_bounded_plus_of_lovasz hLovasz N.toAddSubgroup V hΛ hdimV D hDV hDconv hInt hDfree
  let L' := L.map e.toLinearMap
  have hL'F : L' ≤ F := by
    rw [← hVmap]
    exact Submodule.map_mono hL.1
  have hLrat : IsRationalAffineSubspace L'.toAffineSubspace := by
    apply rational_of_span_integer
    apply le_antisymm
    · obtain ⟨k, b, hb, hbs, hbN⟩ := hL.2
      change L.map e.toLinearMap ≤ _
      rw [← hbs, Submodule.map_span]
      apply Submodule.span_le.mpr
      rintro x ⟨y, ⟨i, rfl⟩, rfl⟩
      apply Submodule.subset_span
      refine ⟨?_, ((hNmem _).mp (hbN i)).2⟩
      exact ⟨b i, hbs ▸ Submodule.subset_span (Set.mem_range_self i), rfl⟩
    · exact Submodule.span_le.mpr Set.inter_subset_left
  refine ⟨e '' P, L', hP.image e.toContinuousLinearMap, hLrat, hL'F, ?_, ?_⟩
  · intro hLF'
    apply hLF
    apply (Submodule.map_injective_of_injective e.injective)
    exact hLF'.trans hVmap.symm
  · intro x hx
    have hxD : e.symm x ∈ D := ⟨x, hx, rfl⟩
    obtain ⟨p, hp, v, hv, he⟩ := Set.mem_add.mp (hDP hxD)
    apply Set.mem_add.mpr
    refine ⟨e p, ⟨p, hp, rfl⟩, e v, ⟨v, hv, rfl⟩, ?_⟩
    rw [← map_add, he, e.apply_symm_apply]

end MICPRep.Periodic.SlabProof


namespace MICPRep.Periodic.SlabProof

lemma intrinsic_integer_of_subsingleton {d : ℕ} (I : Set (Fin d → ℝ))
    (hZ : (I ∩ intLattice d).Nonempty) (hsub : (IZ I).Subsingleton) :
    (intrinsicInterior ℝ (IZ I) ∩ intLattice d).Nonempty := by
  obtain ⟨z, hzI, hzZ⟩ := hZ
  have hz : z ∈ IZ I := ⟨hzI, subset_affineSpan ℝ (I ∩ intLattice d) ⟨hzI, hzZ⟩⟩
  have heq : IZ I = {z} := Set.Subset.antisymm
    (fun w hw => Set.mem_singleton_iff.mpr (hsub hw hz)) (Set.singleton_subset_iff.mpr hz)
  rw [heq, intrinsicInterior_singleton]
  exact ⟨z, rfl, hzZ⟩

lemma intrinsic_integer_zero_dim (I : Set (Fin 0 → ℝ))
    (hZ : (I ∩ intLattice 0).Nonempty) :
    (intrinsicInterior ℝ (IZ I) ∩ intLattice 0).Nonempty :=
  intrinsic_integer_of_subsingleton I hZ (fun _ _ _ _ => Subsingleton.elim _ _)

lemma bounded_subset_slab {d : ℕ} (S : Set (Fin d → ℝ)) (hS : Bornology.IsBounded S) :
    ∃ l u : ℤ, S ⊆ slab d l u := by
  obtain ⟨C, hC⟩ := hS.exists_norm_le
  refine ⟨-⌈C⌉, ⌈C⌉, ?_⟩
  intro z hz i hi
  have hnorm : |z i| ≤ (⌈C⌉ : ℝ) := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm z i).trans ((hC z hz).trans (Int.le_ceil C))
  simpa only [Int.cast_neg] using abs_le.mp hnorm

lemma slab_of_bounded_plus {d : ℕ} (S P : Set (Fin d → ℝ))
    (hP : Bornology.IsBounded P) (L : Submodule ℝ (Fin d → ℝ))
    (hL : ∀ z ∈ L, ∀ i : Fin d, i.val = 0 → z i = 0)
    (hS : ∀ z ∈ S, ∃ p ∈ P, ∃ v ∈ L, z = p + v) :
    ∃ l u : ℤ, S ⊆ slab d l u := by
  obtain ⟨l, u, hbounds⟩ := bounded_subset_slab P hP
  refine ⟨l, u, ?_⟩
  intro z hz i hi
  obtain ⟨p, hp, v, hv, rfl⟩ := hS z hz
  have hv0 := hL v hv i hi
  simpa only [Pi.add_apply, hv0, add_zero] using hbounds hp i hi

end MICPRep.Periodic.SlabProof


open scoped Matrix
namespace MICPRep.Periodic.SlabProof.MatrixAux

lemma intMatVec_mul {d : ℕ} (U V : Matrix (Fin d) (Fin d) ℤ) (z : Fin d → ℝ) :
    intMatVec (U * V) z = intMatVec U (intMatVec V z) := by
  unfold intMatVec
  have hmul : (U * V).map (fun k : ℤ => (k : ℝ)) =
      U.map (fun k : ℤ => (k : ℝ)) * V.map (fun k : ℤ => (k : ℝ)) :=
    Matrix.map_mul (f := Int.castRingHom ℝ)
  rw [hmul, Matrix.mulVec_mulVec]

lemma intMatVec_one {d : ℕ} (z : Fin d → ℝ) :
    intMatVec (1 : Matrix (Fin d) (Fin d) ℤ) z = z := by
  simp [intMatVec, Matrix.map_one]

lemma intMatVec_integer {d : ℕ} (U : Matrix (Fin d) (Fin d) ℤ)
    {z : Fin d → ℝ} (hz : z ∈ intLattice d) : intMatVec U z ∈ intLattice d := by
  obtain ⟨a, rfl⟩ := hz
  refine ⟨U *ᵥ a, ?_⟩
  ext i
  exact RingHom.map_mulVec (Int.castRingHom ℝ) U a i

noncomputable def realEquiv {d : ℕ} (U : Matrix (Fin d) (Fin d) ℤ) (hU : IsUnit U) :
    (Fin d → ℝ) ≃ₗ[ℝ] (Fin d → ℝ) where
  toFun := intMatVec U
  invFun := intMatVec U⁻¹
  map_add' := Matrix.mulVec_add _
  map_smul' := Matrix.mulVec_smul _
  left_inv z := by
    rw [← intMatVec_mul, U.nonsing_inv_mul (U.isUnit_iff_isUnit_det.mp hU), intMatVec_one]
  right_inv z := by
    rw [← intMatVec_mul, U.mul_nonsing_inv (U.isUnit_iff_isUnit_det.mp hU), intMatVec_one]

lemma realEquiv_integer_iff {d : ℕ} (U : Matrix (Fin d) (Fin d) ℤ) (hU : IsUnit U)
    (z : Fin d → ℝ) : realEquiv U hU z ∈ intLattice d ↔ z ∈ intLattice d := by
  constructor
  · intro hz
    have h := intMatVec_integer U⁻¹ hz
    exact (realEquiv U hU).symm_apply_apply z ▸ h
  · exact intMatVec_integer U


lemma int_add {d : ℕ} {x y : Fin d → ℝ}
    (hx : x ∈ intLattice d) (hy : y ∈ intLattice d) : x + y ∈ intLattice d := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, by ext i; simp⟩

lemma int_sub {d : ℕ} {x y : Fin d → ℝ}
    (hx : x ∈ intLattice d) (hy : y ∈ intLattice d) : x - y ∈ intLattice d := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, by ext i; simp⟩

lemma affine_unimodular {d : ℕ} (U : Matrix (Fin d) (Fin d) ℤ) (hU : IsUnimodular U)
    (c : Fin d → ℝ) (hc : c ∈ intLattice d) :
    ∃ (A : Matrix (Fin d) (Fin d) ℚ) (b : Fin d → ℚ), IsUnit A ∧
      ratAff A b '' intLattice d = intLattice d ∧
      ratAff A b ⁻¹' intLattice d = intLattice d ∧
      ratAff A b = fun z => intMatVec U (z-c) := by
  have hU' : IsUnit U := hU
  obtain ⟨a, rfl⟩ := hc
  let A : Matrix (Fin d) (Fin d) ℚ := U.map (fun m : ℤ => (m : ℚ))
  let b : Fin d → ℚ := fun i => -((U *ᵥ a) i : ℚ)
  have heq : ratAff A b = fun z => intMatVec U (z - fun i => (a i : ℝ)) := by
    funext z
    have hA : A.map (fun q : ℚ => (q : ℝ)) = U.map (fun m : ℤ => (m : ℝ)) := by
      ext i j
      simp [A]
    unfold ratAff intMatVec
    rw [hA, Matrix.mulVec_sub]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, b, Rat.cast_neg, Rat.cast_intCast, sub_eq_add_neg]
    congr 1
    exact congrArg Neg.neg (RingHom.map_mulVec (Int.castRingHom ℝ) U a i)
  have hA : IsUnit A := hU.map (Int.castRingHom ℚ).mapMatrix
  have hpre : ratAff A b ⁻¹' intLattice d = intLattice d := by
    ext z
    rw [Set.mem_preimage, heq]
    change realEquiv U hU' (z - fun i => (a i : ℝ)) ∈ intLattice d ↔ _
    rw [realEquiv_integer_iff]
    constructor
    · intro hz
      simpa only [sub_add_cancel] using int_add hz (show (fun i => (a i : ℝ)) ∈ intLattice d from ⟨a,rfl⟩)
    · intro hz
      exact int_sub hz ⟨a, rfl⟩
  refine ⟨A, b, hA, ?_, hpre, heq⟩
  apply Set.Subset.antisymm
  · rintro x ⟨z, hz, rfl⟩
    have : z ∈ ratAff A b ⁻¹' intLattice d := by rw [hpre]; exact hz
    exact this
  · intro z hz
    let w := (realEquiv U hU').symm z + fun i => (a i : ℝ)
    have hw : w ∈ intLattice d := by
      apply int_add _ ⟨a,rfl⟩
      apply (realEquiv_integer_iff U hU' _).mp
      simpa using hz
    refine ⟨w, hw, ?_⟩
    rw [heq]
    change realEquiv U hU' (((realEquiv U hU').symm z + fun i => (a i : ℝ)) - fun i => (a i : ℝ)) = z
    rw [add_sub_cancel_right, LinearEquiv.apply_symm_apply]

end MICPRep.Periodic.SlabProof.MatrixAux


open scoped Matrix
namespace MICPRep.Periodic.SlabProof.FlagAux

noncomputable def restrictCoords {R : Type*} [CommRing R] {d k : ℕ} (hk : k ≤ d) :
    (Fin d → R) →ₗ[R] (Fin k → R) where
  toFun x i := x (Fin.castLE hk i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def blockMap {R : Type*} [CommRing R] {d k : ℕ} (hk : k ≤ d)
    (A : Matrix (Fin k) (Fin k) R) : (Fin d → R) →ₗ[R] (Fin d → R) where
  toFun x i := if hi : i.val < k then (A *ᵥ restrictCoords hk x) ⟨i.val, hi⟩ else x i
  map_add' x y := by
    ext i
    dsimp
    split_ifs <;> simp [Matrix.mulVec_add]
  map_smul' a x := by
    ext i
    dsimp
    split_ifs <;> simp [Matrix.mulVec_smul]

lemma restrictCoords_block {R : Type*} [CommRing R] {d k : ℕ} (hk : k ≤ d)
    (A : Matrix (Fin k) (Fin k) R) (x : Fin d → R) :
    restrictCoords hk (blockMap hk A x) = A *ᵥ restrictCoords hk x := by
  ext i
  simp [restrictCoords, blockMap, i.isLt]

lemma block_one {R : Type*} [CommRing R] {d k : ℕ} (hk : k ≤ d) :
    blockMap hk (1 : Matrix (Fin k) (Fin k) R) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  ext i
  simp [blockMap, restrictCoords]

lemma block_mul {R : Type*} [CommRing R] {d k : ℕ} (hk : k ≤ d)
    (A B : Matrix (Fin k) (Fin k) R) :
    blockMap hk (A * B) = (blockMap hk A).comp (blockMap hk B) := by
  apply LinearMap.ext
  intro x
  ext i
  change (if hi : i.val < k then ((A * B) *ᵥ restrictCoords hk x) ⟨i.val, hi⟩ else x i) =
    (if hi : i.val < k then (A *ᵥ restrictCoords hk (blockMap hk B x)) ⟨i.val, hi⟩
      else blockMap hk B x i)
  by_cases hi : i.val < k
  · simp only [dif_pos hi, restrictCoords_block, Matrix.mulVec_mulVec]
  · simp [hi, blockMap]

noncomputable def blockMat {R : Type*} [CommRing R] {d k : ℕ} (hk : k ≤ d) :
    Matrix (Fin k) (Fin k) R →* Matrix (Fin d) (Fin d) R where
  toFun A := (blockMap hk A).toMatrix'
  map_one' := by rw [block_one]; exact LinearMap.toMatrix'_one
  map_mul' A B := by rw [block_mul, LinearMap.toMatrix'_comp]

lemma blockMat_mulVec {R : Type*} [CommRing R] {d k : ℕ} (hk : k ≤ d)
    (A : Matrix (Fin k) (Fin k) R) (x : Fin d → R) :
    blockMat hk A *ᵥ x = blockMap hk A x := LinearMap.toMatrix'_mulVec _ _

lemma blockMat_cast {d k : ℕ} (hk : k ≤ d) (A : Matrix (Fin k) (Fin k) ℤ) :
    (blockMat hk A).map (fun m : ℤ => (m : ℝ)) =
      blockMat hk (A.map (fun m : ℤ => (m : ℝ))) := by
  ext i j
  by_cases hi : i.val < k <;>
    simp [blockMat, LinearMap.toMatrix'_apply, blockMap, restrictCoords, hi,
      Matrix.mulVec, dotProduct, Pi.single_apply]

lemma block_preserves_coord {d k : ℕ} (hk : k ≤ d)
    (A : Matrix (Fin k) (Fin k) ℝ) (x : Fin d → ℝ)
    (hx : x ∈ coordSubspace d (k : ℤ)) : blockMap hk A x ∈ coordSubspace d (k : ℤ) := by
  intro i hi
  have hn : ¬ i.val < k := by exact_mod_cast (not_lt.mpr hi)
  simpa [blockMap, hn] using hx i hi

lemma block_image_coord {d k : ℕ} (hk : k ≤ d)
    (A : Matrix (Fin k) (Fin k) ℝ) (hA : IsUnit A) :
    blockMap hk A '' coordSubspace d (k : ℤ) = coordSubspace d (k : ℤ) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact block_preserves_coord hk A y hy
  · intro hx
    refine ⟨blockMap hk A⁻¹ x, block_preserves_coord hk A⁻¹ x hx, ?_⟩
    have hh := congrArg (fun f : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) => f x)
      (block_mul hk A A⁻¹)
    rw [A.mul_nonsing_inv (A.isUnit_iff_isUnit_det.mp hA), block_one] at hh
    exact hh.symm

lemma rational_map {d k : ℕ} (L : Submodule ℝ (Fin d → ℝ))
    (hL : IsRationalAffineSubspace L.toAffineSubspace)
    (f : (Fin d → ℝ) →ₗ[ℝ] (Fin k → ℝ))
    (hf : ∀ v ∈ ratPoints d, f v ∈ ratPoints k) :
    IsRationalAffineSubspace (L.map f).toAffineSubspace := by
  let G := (L.map f).toAffineSubspace
  have hmap : G = L.toAffineSubspace.map f.toAffineMap := rfl
  have hspan : G = affineSpan ℝ (f '' ((L : Set (Fin d → ℝ)) ∩ ratPoints d)) := by
    rw [hmap, hL.2, AffineSubspace.map_span]
    rfl
  refine ⟨⟨0, (L.map f).zero_mem⟩, ?_⟩
  change G = affineSpan ℝ ((G : Set (Fin k → ℝ)) ∩ ratPoints k)
  apply le_antisymm
  · conv_lhs => rw [hspan]
    apply affineSpan_mono ℝ
    rintro v ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw.1, rfl⟩, hf w hw.2⟩
  · exact affineSpan_le.mpr fun _ hx => hx.1

lemma matrix_preserves_rational {d k : ℕ} (U : Matrix (Fin k) (Fin d) ℤ)
    {v : Fin d → ℝ} (hv : v ∈ ratPoints d) :
    U.map (fun m : ℤ => (m : ℝ)) *ᵥ v ∈ ratPoints k := by
  obtain ⟨q, rfl⟩ := hv
  refine ⟨U.map (fun m : ℤ => (m : ℚ)) *ᵥ q, ?_⟩
  ext i
  simp [Matrix.mulVec, dotProduct]

lemma restrict_preserves_rational {d k : ℕ} (hk : k ≤ d)
    {v : Fin d → ℝ} (hv : v ∈ ratPoints d) : restrictCoords hk v ∈ ratPoints k := by
  obtain ⟨q, rfl⟩ := hv
  exact ⟨fun i => q (Fin.castLE hk i), rfl⟩

lemma submodule_alignment {d : ℕ} (F : Submodule ℝ (Fin d → ℝ))
    (hF : IsRationalAffineSubspace F.toAffineSubspace) :
    ∃ U : Matrix (Fin d) (Fin d) ℤ, IsUnimodular U ∧
      intMatVec U '' (F : Set (Fin d → ℝ)) = coordSubspace d (Module.finrank ℝ F : ℤ) := by
  have hn : (F.toAffineSubspace : Set (Fin d → ℝ)).Nonempty := ⟨0, F.zero_mem⟩
  have hd : affDim F.toAffineSubspace = (Module.finrank ℝ F : ℤ) := by
    unfold affDim
    rw [if_pos hn, Submodule.toAffineSubspace_direction]
  have hZ : ((F.toAffineSubspace : Set (Fin d → ℝ)) ∩ intLattice d).Nonempty :=
    ⟨0, F.zero_mem, 0, by ext i; simp⟩
  obtain ⟨_, _, U, hU, hu, _⟩ := (MICPRep.Periodic.lemma_6_4 F.toAffineSubspace hF hd hZ).1
  exact ⟨U, hU, by simpa only [Submodule.toAffineSubspace_direction] using hu⟩

lemma intMatVec_mul {d : ℕ} (U V : Matrix (Fin d) (Fin d) ℤ) (z : Fin d → ℝ) :
    intMatVec (U * V) z = intMatVec U (intMatVec V z) := by
  unfold intMatVec
  have hmul : (U * V).map (fun m : ℤ => (m : ℝ)) =
      U.map (fun m : ℤ => (m : ℝ)) * V.map (fun m : ℤ => (m : ℝ)) :=
    Matrix.map_mul (f := Int.castRingHom ℝ)
  rw [hmul, Matrix.mulVec_mulVec]

lemma perm_unit {k : ℕ} (σ : Equiv.Perm (Fin k)) : IsUnit (σ.permMatrix ℤ) := by
  refine ⟨⟨σ.permMatrix ℤ, σ⁻¹.permMatrix ℤ, ?_, ?_⟩, rfl⟩ <;>
    rw [← Matrix.permMatrix_mul] <;> simp

lemma perm_cast {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    (σ.permMatrix ℤ).map (fun m : ℤ => (m : ℝ)) = σ.permMatrix ℝ := by
  ext i j
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix]

end MICPRep.Periodic.SlabProof.FlagAux

namespace MICPRep.Periodic.SlabProof
open FlagAux

lemma flag_alignment {d : ℕ} (F L : Submodule ℝ (Fin d → ℝ))
    (hF : IsRationalAffineSubspace F.toAffineSubspace)
    (hL : IsRationalAffineSubspace L.toAffineSubspace) (hLF : L ≤ F) (hne : L ≠ F) :
    ∃ U : Matrix (Fin d) (Fin d) ℤ, IsUnimodular U ∧
      intMatVec U '' (F : Set (Fin d → ℝ)) = coordSubspace d (Module.finrank ℝ F : ℤ) ∧
      ∀ v ∈ L, ∀ i : Fin d, i.val = 0 → intMatVec U v i = 0 := by
  classical
  let k := Module.finrank ℝ F
  have hk : k ≤ d := by simpa [k] using F.finrank_le
  obtain ⟨U, hU, hu⟩ := submodule_alignment F hF
  have hUr : IsUnit (U.map (fun m : ℤ => (m : ℝ))) :=
    hU.map (Int.castRingHom ℝ).mapMatrix
  let f : (Fin d → ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
    (restrictCoords hk).comp (Matrix.toLin' (U.map (fun m : ℤ => (m : ℝ))))
  let C := L.map f
  have hCrat : IsRationalAffineSubspace C.toAffineSubspace := by
    apply rational_map L hL f
    intro v hv
    exact restrict_preserves_rational hk (matrix_preserves_rational U hv)
  have him (x : Fin d → ℝ) (hx : x ∈ F) : intMatVec U x ∈ coordSubspace d (k : ℤ) := by
    rw [← hu]
    exact ⟨x, hx, rfl⟩
  have hinj {x y : Fin d → ℝ} (hx : x ∈ F) (hy : y ∈ F) (hxy : f x = f y) : x = y := by
    apply Matrix.mulVec_injective_of_isUnit hUr
    ext i
    by_cases hi : i.val < k
    · exact congrFun hxy ⟨i.val, hi⟩
    · have hki : (k : ℤ) ≤ (i.val : ℤ) := by exact_mod_cast (le_of_not_gt hi)
      exact (him x hx i hki).trans (him y hy i hki).symm
  have hCne : C ≠ ⊤ := by
    intro hC
    apply hne
    apply le_antisymm hLF
    intro x hx
    have hfx : f x ∈ C := by rw [hC]; trivial
    obtain ⟨y, hy, he⟩ := hfx
    exact hinj (hLF hy) hx he ▸ hy
  have hlt : Module.finrank ℝ C < k := by
    have hh := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hCne)
    simpa using hh
  have hk0 : 0 < k := lt_of_le_of_lt (Nat.zero_le _) hlt
  obtain ⟨V, hV, hv⟩ := submodule_alignment C hCrat
  let i₀ : Fin k := ⟨0, hk0⟩
  let i₁ : Fin k := ⟨Module.finrank ℝ C, hlt⟩
  let σ := Equiv.swap i₀ i₁
  let A := σ.permMatrix ℤ * V
  have hA : IsUnit A := (perm_unit σ).mul hV
  have hzero (v : Fin d → ℝ) (hvL : v ∈ L) : intMatVec A (f v) i₀ = 0 := by
    have hc : intMatVec V (f v) ∈ coordSubspace k (Module.finrank ℝ C : ℤ) := by
      rw [← hv]
      exact ⟨f v, ⟨v, hvL, rfl⟩, rfl⟩
    have hi := hc i₁ (by exact_mod_cast (le_refl (Module.finrank ℝ C)))
    change intMatVec (σ.permMatrix ℤ * V) (f v) i₀ = 0
    rw [intMatVec_mul]
    change (((σ.permMatrix ℤ).map (fun m : ℤ => (m : ℝ))) *ᵥ intMatVec V (f v)) i₀ = 0
    rw [perm_cast, Matrix.permMatrix_mulVec]
    simpa [σ] using hi
  let W := blockMat hk A
  have hW : IsUnit W := hA.map (blockMat hk)
  have hAr : IsUnit (A.map (fun m : ℤ => (m : ℝ))) :=
    hA.map (Int.castRingHom ℝ).mapMatrix
  have hWfun : intMatVec W = blockMap hk (A.map (fun m : ℤ => (m : ℝ))) := by
    funext v
    change ((blockMat hk A).map (fun m : ℤ => (m : ℝ))) *ᵥ v = _
    rw [blockMat_cast, blockMat_mulVec]
  refine ⟨W * U, hW.mul hU, ?_, ?_⟩
  · have hc : intMatVec (W * U) = fun v => intMatVec W (intMatVec U v) :=
      funext (intMatVec_mul W U)
    rw [hc, ← Set.image_image, hu, hWfun]
    exact block_image_coord hk _ hAr
  · intro v hvL i hi
    rw [intMatVec_mul, hWfun]
    have hik : i.val < k := by rw [hi]; exact hk0
    change (if h : i.val < k then
      ((A.map (fun m : ℤ => (m : ℝ))) *ᵥ restrictCoords hk (intMatVec U v)) ⟨i.val, h⟩
      else intMatVec U v i) = 0
    rw [dif_pos hik]
    have he : (⟨i.val, hik⟩ : Fin k) = i₀ := Fin.ext hi
    rw [he]
    exact hzero v hvL

end MICPRep.Periodic.SlabProof


open scoped Pointwise Matrix
namespace MICPRep.Periodic.SlabProof

lemma conditional_slab (hLovasz : SlabDependency.LovaszStatement)
    {d : ℕ} (I : Set (Fin d → ℝ)) (hI : Convex ℝ I)
    (hZ : (I ∩ intLattice d).Nonempty) :
    (intrinsicInterior ℝ (IZ I) ∩ intLattice d).Nonempty ∨
    ∃ (A : Matrix (Fin d) (Fin d) ℚ) (b : Fin d → ℚ), IsUnit A ∧
      ratAff A b '' intLattice d = intLattice d ∧
      ratAff A b ⁻¹' intLattice d = intLattice d ∧
      ∃ l u : ℤ, IZ (ratAff A b '' I) ⊆ slab d l u ∧
        (affZ (ratAff A b '' I) : Set (Fin d → ℝ)) =
          coordSubspace d (setDim (IZ I)) := by
  classical
  by_cases hgood : (intrinsicInterior ℝ (IZ I) ∩ intLattice d).Nonempty
  · exact Or.inl hgood
  right
  obtain ⟨hFrat, hkeep, hFZ, hFspan, htransport⟩ := lemma_6_3 I hI hZ
  obtain ⟨c, hcI, hcZ⟩ := hZ
  have hcF : c ∈ affZ I := subset_affineSpan ℝ (I ∩ intLattice d) ⟨hcI, hcZ⟩
  have hcIZ : c ∈ IZ I := ⟨hcI, hcF⟩
  have hdim : 0 < Module.finrank ℝ (affZ I).direction := by
    by_contra hn
    have hbot : (affZ I).direction = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
    apply hgood
    apply intrinsic_integer_of_subsingleton I ⟨c, hcI, hcZ⟩
    intro x hx y hy
    have hxy := AffineSubspace.vsub_mem_direction hx.2 hy.2
    rw [hbot] at hxy
    exact sub_eq_zero.mp hxy
  let t := (AffineEquiv.vaddConst ℝ c).symm
  let C : Set (Fin d → ℝ) := t '' IZ I
  have ht (z : Fin d → ℝ) : t z = z-c := rfl
  have htF : t '' (affZ I : Set (Fin d → ℝ)) = ((affZ I).direction : Set (Fin d → ℝ)) :=
    (AffineSubspace.coe_direction_eq_vsub_set_right hcF).symm
  have hCspan : affineSpan ℝ C = (affZ I).direction.toAffineSubspace := by
    change affineSpan ℝ (t.toAffineMap '' IZ I) = _
    rw [← AffineSubspace.map_span, ← hFspan]
    exact SetLike.coe_injective htF
  have hCconv : Convex ℝ C := (hI.inter (affZ I).convex).affine_image t.toAffineMap
  have hCne : C.Nonempty := ⟨t c, c, hcIZ, rfl⟩
  have hfree : Disjoint (intrinsicInterior ℝ C) (intLattice d) := by
    apply Set.disjoint_left.mpr
    intro z hz hzZ
    rw [show C = t '' IZ I from rfl, t.intrinsicInterior_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hxZ : x ∈ intLattice d := by
      have h := MatrixAux.int_add hzZ hcZ
      simpa only [ht, sub_add_cancel] using h
    exact hgood ⟨x, hx, hxZ⟩
  obtain ⟨P, L, hP, hLrat, hLF, hne, hCP⟩ :=
    pi_bounded_plus_of_lovasz hLovasz (affZ I).direction
      (direction_rational (affZ I) hFrat) hdim C hCconv hCne hCspan hfree
  obtain ⟨U, hU, hUF, hUL⟩ := flag_alignment (affZ I).direction L
    (direction_rational (affZ I) hFrat) hLrat hLF hne
  obtain ⟨A, b, hA, hAZ, hpre, heq⟩ := MatrixAux.affine_unimodular U hU c hcZ
  obtain ⟨hIZmap, hFmap⟩ := htransport A b hA hAZ hpre
  let f : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) := Matrix.toLin' (U.map (fun m : ℤ => (m : ℝ)))
  have hf (z : Fin d → ℝ) : f z = intMatVec U z := rfl
  have hImg : f '' C = IZ (ratAff A b '' I) := by
    rw [show C = t '' IZ I from rfl, Set.image_image]
    have he : (fun z => f (t z)) = ratAff A b := by
      rw [heq]
      rfl
    rw [he, hIZmap]
  have hP' : Bornology.IsBounded (f '' P) := hP.image f.toContinuousLinearMap
  obtain ⟨l, u, hlu⟩ := slab_of_bounded_plus (f '' C) (f '' P) hP' (L.map f)
    (by
      rintro z ⟨v, hv, rfl⟩ i hi
      exact hUL v hv i hi)
    (by
      rintro z ⟨x, hx, rfl⟩
      obtain ⟨p, hp, v, hv, he⟩ := Set.mem_add.mp (hCP hx)
      refine ⟨f p, ⟨p, hp, rfl⟩, f v, ⟨v, hv, rfl⟩, ?_⟩
      rw [← map_add, he])
  refine ⟨A, b, hA, hAZ, hpre, l, u, hImg ▸ hlu, ?_⟩
  have hdimEq : setDim (IZ I) = (Module.finrank ℝ (affZ I).direction : ℤ) := by
    unfold setDim
    rw [← hFspan]
    simp only [affDim, if_pos hFrat.1]
  rw [hdimEq, ← hUF, ← htF, Set.image_image, ← hFmap]
  apply congrArg (fun g : (Fin d → ℝ) → (Fin d → ℝ) => g '' (affZ I : Set (Fin d → ℝ)))
  rw [heq]
  rfl

end MICPRep.Periodic.SlabProof


open MICPRep.Periodic
open scoped ENNReal Matrix

/-- Conditional reduction: the sole unresolved assumption is the exact Lovász classification. -/
theorem conditional_solution (hLovasz : SlabDependency.LovaszStatement)
    {d : ℕ} (I : Set (Fin d → ℝ)) (hI : Convex ℝ I)
    (hZ : (I ∩ intLattice d).Nonempty) :
    (intrinsicInterior ℝ (IZ I) ∩ intLattice d).Nonempty ∨
    ∃ (A : Matrix (Fin d) (Fin d) ℚ) (b : Fin d → ℚ), IsUnit A ∧
      ratAff A b '' intLattice d = intLattice d ∧
      ratAff A b ⁻¹' intLattice d = intLattice d ∧
      ∃ l u : ℤ, IZ (ratAff A b '' I) ⊆ slab d l u ∧
        (affZ (ratAff A b '' I) : Set (Fin d → ℝ)) =
          coordSubspace d (setDim (IZ I)) := by
  exact SlabProof.conditional_slab hLovasz I hI hZ


theorem solution {d : ℕ} (I : Set (Fin d → ℝ)) (hI : Convex ℝ I)
    (hZ : (I ∩ intLattice d).Nonempty) :
    (intrinsicInterior ℝ (IZ I) ∩ intLattice d).Nonempty ∨
    ∃ (A : Matrix (Fin d) (Fin d) ℚ) (b : Fin d → ℚ), IsUnit A ∧
      ratAff A b '' intLattice d = intLattice d ∧
      ratAff A b ⁻¹' intLattice d = intLattice d ∧
      ∃ l u : ℤ, IZ (ratAff A b '' I) ⊆ slab d l u ∧
        (affZ (ratAff A b '' I) : Set (Fin d → ℝ)) = coordSubspace d (setDim (IZ I)) := by
  exact conditional_solution (@MaxLatticeFree.Geometry.lovasz_maxLambdaFree_iff) I hI hZ

