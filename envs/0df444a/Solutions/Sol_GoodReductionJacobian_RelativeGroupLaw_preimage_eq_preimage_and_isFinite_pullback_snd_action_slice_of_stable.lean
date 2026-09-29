-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.preimage_eq_preimage_and_isFinite_pullback_snd_action_slice_of_stable
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/b94ac407-f490-5f86-8f11-7d5c133cacc3

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawAction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_preimage_eq_preimage_and_isFinite_pullback_snd_action_slice_of_stable

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace SliceSatFin29

theorem comp_base_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).base x = g.base (f.base x) := rfl

theorem opens_eq_of_forall_isClosed_iff {X : Type u} [TopologicalSpace X] [JacobsonSpace X]
    {O₁ O₂ : TopologicalSpace.Opens X}
    (h : ∀ x : X, IsClosed ({x} : Set X) → (x ∈ O₁ ↔ x ∈ O₂)) : O₁ = O₂ := by
  have key : ∀ {P Q : TopologicalSpace.Opens X},
      (∀ x : X, IsClosed ({x} : Set X) → x ∈ P → x ∈ Q) → P ≤ Q := by
    intro P Q hPQ x hxP
    by_contra hxQ
    obtain ⟨y, ⟨hyP, hyQ⟩, hycl⟩ :=
      nonempty_inter_closedPoints (Z := (P : Set X) ∩ (Q : Set X)ᶜ) ⟨x, hxP, hxQ⟩
        (P.2.isLocallyClosed.inter Q.2.isClosed_compl.isLocallyClosed)
    exact hyQ (hPQ y hycl hyP)
  exact le_antisymm (key fun x hx => (h x hx).1) (key fun x hx => (h x hx).2)

theorem pullback_snd_congr (P : MorphismProperty Scheme.{u}) {X Y Z : Scheme.{u}} (f : X ⟶ Z)
    {g g' : Y ⟶ Z} (e : g = g') (h : P (pullback.snd f g)) : P (pullback.snd f g') := by
  subst e; exact h

theorem morphismRestrict_pullback_snd (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    [P.IsStableUnderBaseChange] {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) (U : Z.Opens)
    (hf : P (f ∣_ U)) : P (pullback.snd f g ∣_ (g ⁻¹ᵁ U)) := by
  have h1 : P (pullback.snd f U.ι) := by
    delta morphismRestrict at hf
    rwa [P.cancel_left_of_respectsIso] at hf
  have h2 : P (pullback.snd (pullback.snd f U.ι) (g ∣_ U)) := P.pullback_snd _ _ h1
  rw [← pullbackLeftPullbackSndIso_hom_snd f U.ι (g ∣_ U), P.cancel_left_of_respectsIso] at h2
  have h3 : P (pullback.snd f ((g ⁻¹ᵁ U).ι ≫ g)) := pullback_snd_congr P f (morphismRestrict_ι g U) h2
  delta morphismRestrict
  rw [P.cancel_left_of_respectsIso]
  rw [← pullbackLeftPullbackSndIso_hom_snd f g (g ⁻¹ᵁ U).ι, P.cancel_left_of_respectsIso]
  exact h3

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

noncomputable abbrev amap {N S : Scheme.{u}} (i : N ⟶ G) (j : S ⟶ G) : pullback (i ≫ f) (j ≫ f) ⟶ G :=
  CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i

theorem comp_action {N S : Scheme.{u}} (i : N ⟶ G) (j : S ⟶ G) {T : Scheme.{u}}
    (ζ : T ⟶ CategoryTheory.Limits.pullback (i ≫ f) (j ≫ f)) :
    ζ ≫ amap L i j =
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
  show ζ ≫ (_ ≫ L.action i) = _
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

theorem amap_over {N S : Scheme.{u}} (i : N ⟶ G) (j : S ⟶ G) :
    amap L i j ≫ f = CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f) ≫ j ≫ f := by
  show (CategoryTheory.Limits.pullback.map _ _ _ _ _ _ _ _ _ ≫ L.action i) ≫ f = _
  rw [Category.assoc, RelativeGroupLaw.action_over, RelativeGroupLaw.actionSource, ← Category.assoc,
    CategoryTheory.Limits.pullback.lift_snd, Category.assoc]

theorem preimage_fst_snd_eq_preimage_snd [IsAlgClosed k] {N S : Scheme.{u}} (i : N ⟶ G) (j : S ⟶ G)
    [LocallyOfFiniteType (j ≫ f)] (hEt : Etale (amap L i j)) (U : G.Opens)
    (hUstab : ∀ (n : Spec (CommRingCat.of k) ⟶ N) (hn : n ≫ i ≫ f = 𝟙 _),
      (L.mul f ⟨f ≫ n ≫ i, by rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩
        ⟨𝟙 G, Category.id_comp _⟩).1 ⁻¹ᵁ U = U) :
    (pullback.fst (amap L i j) j ≫ pullback.snd (i ≫ f) (j ≫ f)) ⁻¹ᵁ (j ⁻¹ᵁ U) =
      (pullback.snd (amap L i j) j) ⁻¹ᵁ (j ⁻¹ᵁ U) := by
  haveI := hEt
  haveI : LocallyOfFiniteType (amap L i j) := inferInstance
  haveI : JacobsonSpace ↥(pullback (amap L i j) j) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd (amap L i j) j ≫ j ≫ f)
  apply opens_eq_of_forall_isClosed_iff
  intro z hz
  set ρ := pointOfClosedPoint (pullback.snd (amap L i j) j ≫ j ≫ f) z hz with hρ
  have hρq : ρ ≫ pullback.snd (amap L i j) j ≫ j ≫ f = 𝟙 _ := pointOfClosedPoint_comp _ z hz
  have hρpt : ρ.base (IsLocalRing.closedPoint k) = z := pointOfClosedPoint_apply _ z hz _
  have hp2 : ρ ≫ pullback.snd (amap L i j) j ≫ j = (ρ ≫ pullback.fst (amap L i j) j) ≫ amap L i j := by
    rw [Category.assoc, pullback.condition]
  have hζq : (ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j ≫ f = 𝟙 _ := by
    rw [← amap_over L i j, ← Category.assoc, ← hp2, Category.assoc]
    exact hρq
  have hn : ((ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.fst (i ≫ f) (j ≫ f)) ≫ i ≫ f = 𝟙 _ := by
    rw [Category.assoc, pullback.condition]; exact hζq
  have hx : ((ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j) ≫ f = 𝟙 _ := by
    simpa only [Category.assoc] using hζq
  have h1 := comp_action L i j (ρ ≫ pullback.fst (amap L i j) j)
  have h2 := comp_translation L i ((ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.fst (i ≫ f) (j ≫ f)) hn (𝟙 _)
    ((ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j) hx
  have h12 : (ρ ≫ pullback.fst (amap L i j) j) ≫ amap L i j =
      ((ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j) ≫
        (L.mul f ⟨f ≫ ((ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.fst (i ≫ f) (j ≫ f)) ≫ i, by
            rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G, Category.id_comp _⟩).1 := by
    rw [h1, h2]
    apply mul_val_congr L hζq
    · simp only [Category.id_comp, Category.assoc]
    · rfl
  have hstab := hUstab ((ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.fst (i ≫ f) (j ≫ f)) hn
  rw [← hρpt]
  change ((ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j).base (IsLocalRing.closedPoint k) ∈
      (U : Set G) ↔ (ρ ≫ pullback.snd (amap L i j) j ≫ j).base (IsLocalRing.closedPoint k) ∈ (U : Set G)
  rw [hp2, h12, comp_base_apply _ (L.mul f _ _).1]
  constructor
  · intro hmem
    have hpre : ((ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j).base
        (IsLocalRing.closedPoint k) ∈
        (L.mul f ⟨f ≫ ((ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.fst (i ≫ f) (j ≫ f)) ≫ i, by
            rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G, Category.id_comp _⟩).1 ⁻¹ᵁ U := by
      rw [hstab]; exact hmem
    exact hpre
  · intro hmem
    have hpre : ((ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.snd (i ≫ f) (j ≫ f) ≫ j).base
        (IsLocalRing.closedPoint k) ∈
        (L.mul f ⟨f ≫ ((ρ ≫ pullback.fst (amap L i j) j) ≫ pullback.fst (i ≫ f) (j ≫ f)) ≫ i, by
            rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G, Category.id_comp _⟩).1 ⁻¹ᵁ U := hmem
    rw [hstab] at hpre
    exact hpre

end GroupLaw

end SliceSatFin29

open SliceSatFin29

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
    (U : G.Opens) (hUfin : IsFinite ((CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) ∣_ U))
    (hUstab : ∀ (n : Spec (CommRingCat.of k) ⟶ N) (hn : n ≫ i ≫ f = 𝟙 _),
      (L.mul f ⟨f ≫ n ≫ i, by rw [Category.assoc, Category.assoc, hn, Category.comp_id]⟩ ⟨𝟙 G, Category.id_comp _⟩).1 ⁻¹ᵁ U = U) :
    (CategoryTheory.Limits.pullback.fst (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j ≫ CategoryTheory.Limits.pullback.snd (i ≫ f) (j ≫ f)) ⁻¹ᵁ (j ⁻¹ᵁ U) =
        (CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) ⁻¹ᵁ (j ⁻¹ᵁ U) ∧
      IsFinite ((CategoryTheory.Limits.pullback.snd (CategoryTheory.Limits.pullback.map (i ≫ f) (j ≫ f) (i ≫ f) f (𝟙 N) j (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) (Category.comp_id _) ≫ L.action i) j) ∣_ (j ⁻¹ᵁ U)) :=
  ⟨preimage_fst_snd_eq_preimage_snd L i j hEt U hUstab,
    morphismRestrict_pullback_snd @IsFinite _ j U hUfin⟩

end S_GoodReductionJacobian_RelativeGroupLaw_preimage_eq_preimage_and_isFinite_pullback_snd_action_slice_of_stable
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_preimage_eq_preimage_and_isFinite_pullback_snd_action_slice_of_stable (solution)
