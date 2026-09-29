-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_base_mem_of_forall_isFinite_morphismRestrict_le_of_stable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/18ea2f45-d671-50e3-ab29-24d5145b73a2

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import Theorems.Thm_AlgebraicGeometry_LocallyQuasiFinite_exists_isFinite_morphismRestrict_of_irreducibleSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_base_mem_of_forall_isFinite_morphismRestrict_le_of_stable

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace SliceNonempty29

theorem ringHom_quasiFinite_of_etale {R S : Type u} [CommRing R] [CommRing S] {φ : R →+* S}
    (h : φ.Etale) : φ.QuasiFinite := by
  letI := φ.toAlgebra
  have : Algebra.Etale R S := h
  exact (inferInstance : Algebra.QuasiFinite R S)

theorem comp_base_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).base x = g.base (f.base x) := rfl

theorem locallyQuasiFinite_of_etale {X Y : Scheme.{u}} (a : X ⟶ Y) [Etale a] :
    LocallyQuasiFinite a := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  exact ringHom_quasiFinite_of_etale (HasRingHomProperty.appLE @Etale a inferInstance U V e)

theorem exists_isOpen_irreducible_subset {α : Type u} [TopologicalSpace α] [TopologicalSpace.NoetherianSpace α]
    {O : Set α} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ W : Set α, IsOpen W ∧ W.Nonempty ∧ IsIrreducible W ∧ W ⊆ O := by
  haveI : Nonempty O := hne.to_subtype
  obtain ⟨o, ho, hone, hoZ⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (irreducibleComponent (Classical.arbitrary O)) (irreducibleComponent_mem_irreducibleComponents _)
  refine ⟨Subtype.val '' o, hO.isOpenMap_subtype_val o ho, hone.image _, ?_, ?_⟩
  · refine IsIrreducible.image ?_ Subtype.val continuous_subtype_val.continuousOn
    exact ⟨hone, (isIrreducible_irreducibleComponent.2).open_subset ho hoZ⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2

section GroupLaw

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)

theorem mul_val_congr {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of k)} (e : t = t')
    (x y : SchemeHomOver t f) (x' y' : SchemeHomOver t' f) (hx : x.1 = x'.1) (hy : y.1 = y'.1) :
    (L.mul t x y).1 = (L.mul t' x' y').1 := by
  subst e
  obtain ⟨x, _⟩ := x; obtain ⟨x', _⟩ := x'; obtain ⟨y, _⟩ := y; obtain ⟨y', _⟩ := y'
  simp only at hx hy
  subst hx; subst hy
  rfl

theorem comp_translation {N : Scheme.{u}} (i : N ⟶ G) (n : Spec (CommRingCat.of k) ⟶ N)
    (hn : n ≫ i ≫ f = 𝟙 _) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : T ⟶ G) (hx : x ≫ f = t) :
    x ≫ (L.mul f ⟨f ≫ n ≫ i, by rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G, Category.id_comp _⟩).1 =
      (L.mul t ⟨t ≫ n ≫ i, by rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨x, hx⟩).1 := by
  have h := congrArg Subtype.val
    (L.mul_natural f t x hx ⟨f ≫ n ≫ i, by rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩
      ⟨𝟙 G, Category.id_comp _⟩)
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
  rw [h]
  apply mul_val_congr L rfl
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc, hx]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, Category.comp_id]

theorem comp_action {N S : Scheme.{u}} (i : N ⟶ G) (j : S ⟶ G) {T : Scheme.{u}}
    (ζ : T ⟶ CategoryTheory.Limits.pullback (i ≫ f) (j ≫ f)) :
    ζ ≫ (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) =
      (L.mul (ζ ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f) ≫ j ≫ f)
        ⟨ζ ≫ CategoryTheory.Limits.pullback.fst (i ≫ f) (j ≫ f) ≫ i, by
          simp only [Category.assoc]; rw [CategoryTheory.Limits.pullback.condition]⟩
        ⟨ζ ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f) ≫ j, by simp only [Category.assoc]⟩).1 := by
  have hfst : CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
        ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
      CategoryTheory.Limits.pullback.fst (i ≫ f) f = CategoryTheory.Limits.pullback.fst (i ≫ f) (j ≫ f) ≫ 𝟙 N :=
    CategoryTheory.Limits.pullback.lift_fst _ _ _
  have hsnd : CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
        ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫
      CategoryTheory.Limits.pullback.snd (i ≫ f) f = CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f) ≫ j :=
    CategoryTheory.Limits.pullback.lift_snd _ _ _
  rw [← Category.assoc, L.action_def]
  have h := congrArg Subtype.val
    (L.mul_natural (RelativeGroupLaw.actionSource f i) _
      (ζ ≫ CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _)) rfl
      (L.actionFstPoint i) (L.actionSndPoint i))
  rw [GoodReductionJacobian.schemeHomOverComp_coe] at h
  rw [h]
  apply mul_val_congr L
  · simp only [RelativeGroupLaw.actionSource, Category.assoc, reassoc_of% hsnd]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, RelativeGroupLaw.actionFstPoint_coe, Category.assoc,
      reassoc_of% hfst]
  · simp only [GoodReductionJacobian.schemeHomOverComp_coe, RelativeGroupLaw.actionSndPoint_coe, Category.assoc,
      hsnd]

end GroupLaw

end SliceNonempty29

open SliceNonempty29

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] (L : RelativeGroupLaw k f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    {N : Scheme.{u}} (i : N ⟶ G) [IsClosedImmersion i] (LN : RelativeGroupLaw k (i ≫ f))
    (h : ℕ) [SmoothOfRelativeDimension h (i ≫ f)]
    (hi : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LN.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)))
    (S : Scheme.{u}) (j : S ⟶ G) [IsAffine S] [Nonempty S] [LocallyOfFiniteType (j ≫ f)]
    (hEt : Etale (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i))
    (U : G.Opens) (hU : ∀ W : G.Opens, IsFinite ((CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) ∣_ W) → W ≤ U)
    (hUstab : ∀ (n : Spec (CommRingCat.of k) ⟶ N) (hn : n ≫ i ≫ f = 𝟙 _),
      (L.mul f ⟨f ≫ n ≫ i, by rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G, Category.id_comp _⟩).1 ⁻¹ᵁ U = U) :
    ∃ s : S, j.base s ∈ U := by
  haveI := hEt
  haveI : Smooth f := SmoothOfRelativeDimension.smooth g f

  have haf : (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) ≫ f =
      CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f) ≫ j ≫ f := by
    rw [Category.assoc, L.action_over, RelativeGroupLaw.actionSource, ← Category.assoc,
      CategoryTheory.Limits.pullback.lift_snd, Category.assoc]
  haveI : LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f) ≫ j ≫ f) := inferInstance
  haveI hsep : IsSeparated (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) := by
    have : IsSeparated ((CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) ≫ f) := by rw [haf]; infer_instance
    exact IsSeparated.of_comp _ f
  haveI hqc : QuasiCompact (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) := by
    have : QuasiCompact ((CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) ≫ f) := by rw [haf]; infer_instance
    exact QuasiCompact.of_comp _ f
  haveI hlqf : LocallyQuasiFinite (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) := locallyQuasiFinite_of_etale _

  have key : ∀ z : ↥(CategoryTheory.Limits.pullback (i ≫ f) (j ≫ f)), IsClosed {z} →
      ((CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i)).base z ∈ U → ∃ s : S, j.base s ∈ U := by
    intro z hz hzU
    set ζ := pointOfClosedPoint (CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f) ≫ j ≫ f) z hz with hζ
    have hζq : ζ ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f) ≫ j ≫ f = 𝟙 _ :=
      pointOfClosedPoint_comp _ z hz
    have hn : (ζ ≫ CategoryTheory.Limits.pullback.fst (i ≫ f) (j ≫ f)) ≫ i ≫ f = 𝟙 _ := by
      rw [Category.assoc, CategoryTheory.Limits.pullback.condition]; exact hζq
    have hx : (ζ ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f) ≫ j) ≫ f = 𝟙 _ := by
      simpa only [Category.assoc] using hζq
    have h1 := comp_action L i j ζ
    have h2 := comp_translation L i (ζ ≫ CategoryTheory.Limits.pullback.fst (i ≫ f) (j ≫ f)) hn (𝟙 _)
      (ζ ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f) ≫ j) hx
    have h12 : ζ ≫ (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) =
        (ζ ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f) ≫ j) ≫
          (L.mul f ⟨f ≫ (ζ ≫ CategoryTheory.Limits.pullback.fst (i ≫ f) (j ≫ f)) ≫ i, by rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G, Category.id_comp _⟩).1 := by
      rw [h1, h2]
      apply mul_val_congr L hζq
      · simp only [Category.id_comp, Category.assoc]
      · rfl
    have hζpt : ζ.base (IsLocalRing.closedPoint k) = z := pointOfClosedPoint_apply _ z hz _
    have hmem : ((L.mul f ⟨f ≫ (ζ ≫ CategoryTheory.Limits.pullback.fst (i ≫ f) (j ≫ f)) ≫ i, by rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G, Category.id_comp _⟩).1).base
        ((ζ ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f) ≫ j).base (IsLocalRing.closedPoint k)) ∈ U := by
      rw [← comp_base_apply, ← h12, comp_base_apply, hζpt]
      exact hzU
    have hstab := hUstab (ζ ≫ CategoryTheory.Limits.pullback.fst (i ≫ f) (j ≫ f)) hn
    have hpre : (ζ ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f) ≫ j).base (IsLocalRing.closedPoint k) ∈
        (L.mul f ⟨f ≫ (ζ ≫ CategoryTheory.Limits.pullback.fst (i ≫ f) (j ≫ f)) ≫ i, by rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G, Category.id_comp _⟩).1 ⁻¹ᵁ U := hmem
    rw [hstab] at hpre
    refine ⟨(CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)).base (ζ.base (IsLocalRing.closedPoint k)), ?_⟩
    simpa only [comp_base_apply] using hpre

  have hopen : IsOpenMap ((CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i)).base := Scheme.Hom.isOpenMap _
  obtain ⟨e⟩ : Nonempty (Spec (CommRingCat.of k) ⟶ N) := ⟨(LN.one (𝟙 _)).1⟩
  haveI hNS : Nonempty ↥(CategoryTheory.Limits.pullback (i ≫ f) (j ≫ f)) := by
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i ≫ f) (g := j ≫ f)
      (e.base (IsLocalRing.closedPoint k)) (Classical.arbitrary S) (Subsingleton.elim _ _)
    exact ⟨z⟩
  haveI : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsNoetherian G := {}
  haveI : TopologicalSpace.NoetherianSpace G := inferInstance
  obtain ⟨W, hWo, hWne, hWirr, hWIm⟩ := exists_isOpen_irreducible_subset (α := G)
    hopen.isOpen_range (Set.range_nonempty _)

  let Y₁ : G.Opens := ⟨W, hWo⟩
  haveI : IrreducibleSpace Y₁.toScheme := isIrreducible_iff_irreducibleSpace.mp hWirr
  obtain ⟨U₁, hU₁ne, hU₁fin⟩ :=
    AlgebraicGeometry.LocallyQuasiFinite.exists_isFinite_morphismRestrict_of_irreducibleSpace
      ((CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) ∣_ Y₁)
  have hW₁fin : IsFinite ((CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) ∣_ (Y₁.ι ''ᵁ U₁)) :=
    (MorphismProperty.arrow_mk_iso_iff @IsFinite (morphismRestrictRestrict _ Y₁ U₁)).1 hU₁fin
  have hW₁U : Y₁.ι ''ᵁ U₁ ≤ U := hU _ hW₁fin

  obtain ⟨u₁, hu₁⟩ := hU₁ne
  obtain ⟨z₀, hz₀⟩ : ∃ z₀, ((CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i)).base z₀ = Y₁.ι.base u₁ := hWIm u₁.2
  haveI : JacobsonSpace ↥(CategoryTheory.Limits.pullback (i ≫ f) (j ≫ f)) :=
    LocallyOfFiniteType.jacobsonSpace (CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f) ≫ j ≫ f)
  have hz₀mem : z₀ ∈ (((CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i)) ⁻¹ᵁ (Y₁.ι ''ᵁ U₁) : Set _) := by
    show ((CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i)).base z₀ ∈ Y₁.ι ''ᵁ U₁
    rw [hz₀]; exact ⟨u₁, hu₁, rfl⟩
  obtain ⟨z, hzW, hzcl⟩ := nonempty_inter_closedPoints ⟨z₀, hz₀mem⟩
    (((CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i)) ⁻¹ᵁ (Y₁.ι ''ᵁ U₁)).2.isLocallyClosed
  exact key z hzcl (hW₁U hzW)

end S_GoodReductionJacobian_RelativeGroupLaw_exists_base_mem_of_forall_isFinite_morphismRestrict_le_of_stable
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_base_mem_of_forall_isFinite_morphismRestrict_le_of_stable (solution)
