-- Prove2me | solution 1 for IsLocalRing.exists_noetherian_henselization
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-24T20:53:47.356495+00:00
-- url     : https://prove2.me/submissions/6e76a1f6-b6c5-4978-a70e-cd928968213f

import Mathlib
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.FinallySmall
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Unramified.LocalStructure

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Polynomial


namespace PhilipponPointedEtaleNeighborhoods

section

universe u

/-- The ring presheaf sending an étale scheme to its global sections. -/
def sections (X : Scheme.{u}) : X.Etaleᵒᵖ ⥤ CommRingCat.{u} :=
  (Scheme.Etale.forget X ⋙ Over.forget X).op ⋙ Scheme.Γ

variable {X : Scheme.{u}} {K : Type u} [Field K]
  (s : Spec (CommRingCat.of K) ⟶ X)

/-- Pointed étale neighborhoods of a field-valued point have a cofiltered,
initially small category of elements. The trivial topology suffices for
forming their colimit, even when the field is not separably closed. -/
def neighborhoodPoint : (⊥ : GrothendieckTopology X.Etale).Point where
  fiber := Scheme.Etale.forget X ⋙ coyoneda.obj (op (Over.mk s))
  isCofiltered := Functor.isCofiltered_elements _
  initiallySmall :=
    initiallySmall_of_essentiallySmall_weakly_initial_objectProperty
      (Functor.Elements.precomp (Scheme.AffineEtale.Spec X)
        (Scheme.Etale.forget X ⋙ coyoneda.obj (op (Over.mk s)))).essImage (by
      rintro ⟨Y, t⟩
      cases Y with | _ Y f
      obtain ⟨y, hy, rfl⟩ := Over.homMk_surjective t
      dsimp at y hy
      obtain ⟨R, j, _, y', rfl⟩ : ∃ (R : CommRingCat) (j : Spec (.of R) ⟶ Y)
          (_ : IsOpenImmersion j) (y' : _ ⟶ _), y' ≫ j = y := by
        obtain ⟨R, j, _, hj, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
          (x := y.base default) (U := ⊤) (by simp)
        refine ⟨R, j, inferInstance, _, IsOpenImmersion.lift_fac j y ?_⟩
        rintro _ ⟨a, rfl⟩
        rwa [Subsingleton.elim a default]
      exact ⟨_,
        ⟨Functor.elementsMk _ (Scheme.AffineEtale.mk (j ≫ f)) (Over.homMk y'), ⟨Iso.refl _⟩⟩,
        ⟨⟨MorphismProperty.Over.homMk j rfl (by simp), by cat_disch⟩⟩⟩)
  jointly_surjective {U} S hS t := by
    obtain rfl : S = ⊤ := GrothendieckTopology.bot_covering.mp hS
    exact ⟨U, 𝟙 _, by simp, t, by simp⟩

/-- The ring of germs of functions on pointed étale neighborhoods. -/
abbrev stalkRing : CommRingCat.{u} :=
  (neighborhoodPoint s).presheafFiber.obj (sections X)

/-- Evaluation of a section along a geometric point of its domain. -/
def evaluate (W : X.Etale) (t : (neighborhoodPoint s).fiber.obj W) :
    (sections X).obj (op W) ⟶ CommRingCat.of K :=
  (show Spec (CommRingCat.of K) ⟶ W.left from t.left).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom

/-- The morphism to the affinization of a neighborhood induced by its geometric point. -/
theorem point_toSpecΓ (W : X.Etale) (t : (neighborhoodPoint s).fiber.obj W) :
    (show Spec (CommRingCat.of K) ⟶ W.left from t.left) ≫ W.left.toSpecΓ =
      Spec.map (evaluate s W t) := by
  rw [Scheme.toSpecΓ_naturality, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
  rfl

/-- Evaluation at the geometric point descends to the ring of germs. -/
def evaluateGerm : stalkRing s ⟶ CommRingCat.of K :=
  (neighborhoodPoint s).presheafFiberDesc (evaluate s) (by
    intro W V g t
    change g.left.appTop ≫ t.left.appTop ≫ _ = (t.left ≫ g.left).appTop ≫ _
    rw [Scheme.Hom.comp_appTop, Category.assoc])

@[reassoc (attr := simp)]
theorem germ_evaluateGerm (W : X.Etale) (t : (neighborhoodPoint s).fiber.obj W) :
    (neighborhoodPoint s).toPresheafFiber W t (sections X) ≫ evaluateGerm s =
      evaluate s W t :=
  (neighborhoodPoint s).toPresheafFiber_presheafFiberDesc _ _ W t

@[simp] theorem evaluateGerm_germ (W : X.Etale)
    (t : (neighborhoodPoint s).fiber.obj W) (a : (sections X).obj (op W)) :
    evaluateGerm s ((neighborhoodPoint s).toPresheafFiber W t (sections X) a) =
      evaluate s W t a :=
  ConcreteCategory.congr_hom (germ_evaluateGerm s W t) a

/-- Nonzero evaluation characterizes the units of the étale stalk. -/
theorem isUnit_iff_evaluateGerm_ne_zero (a : stalkRing s) :
    IsUnit a ↔ evaluateGerm s a ≠ 0 := by
  refine ⟨fun h => (h.map (evaluateGerm s).hom).ne_zero, ?_⟩
  let Φ := neighborhoodPoint s
  obtain ⟨W, t, a, rfl⟩ := Φ.toPresheafFiber_jointly_surjective a
  rw [evaluateGerm_germ]
  intro ha
  let D := W.left.basicOpen a
  let tLeft : Spec (CommRingCat.of K) ⟶ W.left := t.left
  have hD : Set.range tLeft ⊆ Set.range D.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change z ∈ tLeft ⁻¹ᵁ W.left.basicOpen a
    rw [Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine']
    have h : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of K)).hom (tLeft.appTop a)) :=
      isUnit_iff_ne_zero.mpr ha
    exact (PrimeSpectrum.mem_basicOpen _ _).mpr (Ideal.notMem_of_isUnit _ h)
  let V := Scheme.Etale.mk (D.ι ≫ W.hom)
  let g : V ⟶ W := MorphismProperty.Over.homMk D.ι rfl trivial
  let t' : Φ.fiber.obj V := Over.homMk (IsOpenImmersion.lift D.ι tLeft hD) (by
    change IsOpenImmersion.lift D.ι tLeft hD ≫ D.ι ≫ W.hom = s
    rw [← Category.assoc, IsOpenImmersion.lift_fac]
    exact Over.w t)
  have ht : Φ.fiber.map g t' = t := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  have hu : IsUnit ((sections X).map g.op a) := by
    change IsUnit (D.ι.appTop a)
    apply RingedSpace.isUnit_of_isUnit_germ D.toScheme.toRingedSpace
    intro z hz
    apply (D.toScheme.mem_basicOpen_top _ _).mp
    rw [← Scheme.preimage_basicOpen_top]
    exact z.property
  rw [← ht, ← Φ.toPresheafFiber_w_apply g t' (sections X)]
  exact hu.map (Φ.toPresheafFiber V t' (sections X)).hom

instance : IsLocalRing (stalkRing s) := by
  let : Nontrivial (stalkRing s) := (evaluateGerm s).hom.domain_nontrivial
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro a
  by_cases ha : evaluateGerm s a = 0
  · right
    rw [isUnit_iff_evaluateGerm_ne_zero, map_sub, map_one, ha, sub_zero]
    exact one_ne_zero
  · exact Or.inl ((isUnit_iff_evaluateGerm_ne_zero s a).mpr ha)

instance : IsLocalHom (evaluateGerm s).hom where
  map_nonunit a h := (isUnit_iff_evaluateGerm_ne_zero s a).mpr h.ne_zero

/-- The image of evaluation realizes the residue field as a subfield of the field
of the geometric point. -/
theorem ker_evaluateGerm : RingHom.ker (evaluateGerm s).hom = IsLocalRing.maximalIdeal (stalkRing s) := by
  ext a
  rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    isUnit_iff_evaluateGerm_ne_zero, not_ne_iff]

end

section

universe u

variable {X : Scheme.{u}} {K : Type u} [Field K]
  (s : Spec (CommRingCat.of K) ⟶ X)

private abbrev point := neighborhoodPoint s

private abbrev germ (W : X.Etale) (t : (point s).fiber.obj W) :=
  (point s).toPresheafFiber W t (sections X)

/-- A finite family of germs can be represented on a single pointed neighborhood. -/
private theorem exists_representatives {ι : Type*} [Fintype ι] (a : ι → stalkRing s) :
    ∃ (W : X.Etale) (t : (point s).fiber.obj W) (b : ι → (sections X).obj (op W)),
      ∀ i, germ s W t (b i) = a i := by
  classical
  choose W t b h using fun i => (point s).toPresheafFiber_jointly_surjective (a i)
  let V (i : ι) : (point s).fiber.Elements := ⟨W i, t i⟩
  obtain ⟨Z, hZ⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image V)
  let f (i : ι) : Z ⟶ V i := (hZ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)).some
  refine ⟨Z.1, Z.2, fun i => (sections X).map (f i).val.op (b i), ?_⟩
  intro i
  rw [(point s).toPresheafFiber_w_apply]
  exact (congrArg (fun z => germ s (W i) z (b i)) (f i).property).trans (h i)

/-- The standard étale algebra inverting the derivative provides a neighborhood
on which the residue root extends to a section. -/
private theorem exists_root_germ {W : X.Etale} (t : (point s).fiber.obj W)
    (p : ((sections X).obj (op W))[X]) (hp : p.Monic) (a : K)
    (ha : p.eval₂ (evaluate s W t).hom a = 0)
    (hder : p.derivative.eval₂ (evaluate s W t).hom a ≠ 0) :
    ∃ b : stalkRing s, p.eval₂ (germ s W t).hom b = 0 ∧ evaluateGerm s b = a := by
  let R := (sections X).obj (op W)
  let P : StandardEtalePair R := ⟨p, hp, p.derivative, 1, 0, 1,
    by rw [mul_one, mul_zero, add_zero, pow_one]⟩
  let C := CommRingCat.of P.Ring
  let e : R ⟶ C := CommRingCat.ofHom (algebraMap R P.Ring)
  let : Algebra R K := (evaluate s W t).hom.toAlgebra
  have hP : P.HasMap a := ⟨ha, isUnit_iff_ne_zero.mpr hder⟩
  let r : C ⟶ CommRingCat.of K := CommRingCat.ofHom (P.lift a hP).toRingHom
  have her : e ≫ r = evaluate s W t := by
    apply ConcreteCategory.hom_ext
    intro z
    exact (P.lift a hP).commutes z
  have he : Etale (Spec.map e) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  let u := W.left.toSpecΓ
  let T := pullback u (Spec.map e)
  let v : T ⟶ W.left := pullback.fst _ _
  let k : T ⟶ Spec C := pullback.snd _ _
  let V : X.Etale := Scheme.Etale.mk (v ≫ W.hom)
  let g : V ⟶ W := MorphismProperty.Over.homMk v rfl trivial
  let tLeft : Spec (CommRingCat.of K) ⟶ W.left := t.left
  have hSquare : tLeft ≫ u = Spec.map r ≫ Spec.map e := by
    rw [← Spec.map_comp, her]
    exact point_toSpecΓ s W t
  let l : Spec (CommRingCat.of K) ⟶ T := pullback.lift tLeft (Spec.map r) hSquare
  have hlv : l ≫ v = tLeft := pullback.lift_fst _ _ _
  have hlk : l ≫ k = Spec.map r := pullback.lift_snd _ _ _
  let t' : (point s).fiber.obj V := Over.homMk l (by
    change l ≫ v ≫ W.hom = s
    rw [← Category.assoc, hlv]
    exact Over.w t)
  have ht' : (point s).fiber.map g t' = t := Over.OverMorphism.ext hlv
  let θ : C ⟶ Γ(T, ⊤) := (Scheme.ΓSpecIso C).inv ≫ k.appTop
  have hv : v.appTop = e ≫ θ := by
    have h := congrArg (fun m : T ⟶ Spec R => m.appTop)
      (pullback.condition (f := u) (g := Spec.map e))
    change (v ≫ u).appTop = (k ≫ Spec.map e).appTop at h
    simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, u] at h
    change (Scheme.ΓSpecIso R).hom ≫ v.appTop = (Spec.map e).appTop ≫ k.appTop at h
    calc
      v.appTop = (Scheme.ΓSpecIso R).inv ≫ (Scheme.ΓSpecIso R).hom ≫ v.appTop := by simp
      _ = e ≫ θ := by rw [h, Scheme.ΓSpecIso_inv_naturality_assoc]
  let β : C ⟶ stalkRing s := θ ≫ germ s V t'
  have hβ : e ≫ β = germ s W t := by
    change e ≫ θ ≫ germ s V t' = germ s W t
    rw [← Category.assoc, ← hv]
    change (sections X).map g.op ≫ germ s V t' = germ s W t
    rw [(point s).toPresheafFiber_w, ht']
  have hβr : β ≫ evaluateGerm s = r := by
    change (θ ≫ germ s V t') ≫ evaluateGerm s = r
    rw [Category.assoc, germ_evaluateGerm s V t']
    change ((Scheme.ΓSpecIso C).inv ≫ k.appTop) ≫
      l.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom = r
    rw [Category.assoc, ← Scheme.Hom.comp_appTop_assoc, hlk,
      Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  refine ⟨β P.X, ?_, ?_⟩
  · have hroot : p.eval₂ e.hom P.X = 0 := (StandardEtalePair.hasMap_X (P := P)).1
    rw [← hβ, CommRingCat.hom_comp, ← Polynomial.hom_eval₂, hroot, map_zero]
  · exact (ConcreteCategory.congr_hom hβr P.X).trans (P.lift_X a hP)

/-- A simple root in the field of the geometric point lifts to an étale germ. -/
theorem exists_lift_root {p : (stalkRing s)[X]} (hp : p.Monic) (a : K)
    (ha : p.eval₂ (evaluateGerm s).hom a = 0)
    (hder : p.derivative.eval₂ (evaluateGerm s).hom a ≠ 0) :
    ∃ b : stalkRing s, p.IsRoot b ∧ evaluateGerm s b = a := by
  obtain ⟨W, t, b, hb⟩ := exists_representatives s (fun i : p.support => p.coeff i)
  have hlifts : p ∈ Polynomial.lifts (germ s W t).hom := by
    apply (Polynomial.lifts_iff_coeff_lifts p).mpr
    intro i
    by_cases hi : i ∈ p.support
    · exact ⟨b ⟨i, hi⟩, hb ⟨i, hi⟩⟩
    · exact ⟨0, by rw [map_zero, Polynomial.notMem_support_iff.mp hi]⟩
  obtain ⟨q, rfl, _, hq⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hp
  have hEval : (evaluateGerm s).hom.comp (germ s W t).hom = (evaluate s W t).hom := by
    ext z
    exact evaluateGerm_germ s W t z
  rw [Polynomial.eval₂_map, hEval] at ha
  rw [Polynomial.derivative_map, Polynomial.eval₂_map, hEval] at hder
  obtain ⟨c, hc, hca⟩ := exists_root_germ s t q hq a ha hder
  exact ⟨c, (Polynomial.eval_map _ _).trans hc, hca⟩

instance henselianLocalRing : HenselianLocalRing (stalkRing s) where
  is_henselian p hp a ha hder := by
    rw [← ker_evaluateGerm, RingHom.mem_ker, ← Polynomial.eval₂_at_apply] at ha
    have h := (isUnit_iff_evaluateGerm_ne_zero s _).mp hder
    rw [← Polynomial.eval₂_at_apply] at h
    obtain ⟨b, hb, hba⟩ := exists_lift_root s hp (evaluateGerm s a) ha h
    refine ⟨b, hb, ?_⟩
    rw [← ker_evaluateGerm, RingHom.mem_ker, map_sub, hba, sub_self]

end

section

universe u

variable {X : Scheme.{u}} {K : Type u} [Field K]
  (s : Spec (CommRingCat.of K) ⟶ X)

/-- Pointed étale neighborhoods of a field-valued point. -/
abbrev Neighborhood := (neighborhoodPoint s).fiber.Elements

/-- The diagram of underlying schemes of the pointed neighborhoods. -/
abbrev neighborhoods : Neighborhood s ⥤ Scheme.{u} :=
  CategoryOfElements.π (neighborhoodPoint s).fiber ⋙ Scheme.Etale.forget X ⋙ Over.forget X

/-- The affine pointed neighborhoods form a coinitial full subcategory. -/
def IsAffineNeighborhood : ObjectProperty (Neighborhood s) :=
  fun W => IsAffine W.1.left

abbrev affineInclusion := (IsAffineNeighborhood s).ι

instance affineInclusion_initial : (affineInclusion s).Initial := by
  apply Functor.initial_of_exists_of_isCofiltered_of_fullyFaithful
  intro W
  let t : Spec (CommRingCat.of K) ⟶ W.1.left := W.2.left
  obtain ⟨j, z, hz⟩ := W.1.left.affineCover.exists_eq (t default)
  let i := W.1.left.affineCover.f j
  have hi : Set.range t ⊆ Set.range i := by
    rintro _ ⟨x, rfl⟩
    exact ⟨z, (Subsingleton.elim x default).symm ▸ hz⟩
  let V := Scheme.Etale.mk (i ≫ W.1.hom)
  let g : V ⟶ W.1 := MorphismProperty.Over.homMk i rfl trivial
  let l := IsOpenImmersion.lift i t hi
  have hl : l ≫ i = t := IsOpenImmersion.lift_fac ..
  let v : (neighborhoodPoint s).fiber.obj V := Over.homMk l (by
    change l ≫ i ≫ W.1.hom = s
    rw [← Category.assoc, hl]
    exact Over.w W.2)
  have hV : IsAffine V.left := by
    change IsAffine (W.1.left.affineCover.X j)
    infer_instance
  exact ⟨⟨⟨V, v⟩, hV⟩, ⟨⟨g, Over.OverMorphism.ext hl⟩⟩⟩

instance affineNeighborhoods_cofiltered : IsCofiltered (IsAffineNeighborhood s).FullSubcategory :=
  IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful (affineInclusion s) (fun W =>
    ⟨Functor.Initial.lift (affineInclusion s) W, ⟨Functor.Initial.homToLift (affineInclusion s) W⟩⟩)

instance affineNeighborhoods_initiallySmall : InitiallySmall.{u} (IsAffineNeighborhood s).FullSubcategory := by
  let F := affineInclusion s
  let I := fromInitialModel.{u} (Neighborhood s)
  let chooseAffine (i : InitialModel.{u} (Neighborhood s)) := Functor.Initial.lift F (I.obj i)
  apply initiallySmall_of_small_weakly_initial_set (Set.range chooseAffine)
  intro W
  obtain ⟨p⟩ : Nonempty (CostructuredArrow I (F.obj W)) := IsConnected.is_nonempty
  exact ⟨chooseAffine p.left, Set.mem_range_self _,
    ⟨F.preimage (Functor.Initial.homToLift F (I.obj p.left) ≫ p.hom)⟩⟩

private abbrev affineDiagram := affineInclusion s ⋙ neighborhoods s

private def affineCocone :=
  ((neighborhoodPoint s).presheafFiberCocone (sections X)).whisker (affineInclusion s).op

private def affineToSpec :
    affineDiagram s ≅ affineDiagram s ⋙ Scheme.Γ.rightOp ⋙ Scheme.Spec := by
  let α := (affineDiagram s).whiskerLeft ΓSpec.adjunction.unit
  have (W : (IsAffineNeighborhood s).FullSubcategory) : IsIso (α.app W) := by
    let : IsAffine W.obj.1.left := W.property
    change IsIso W.obj.1.left.toSpecΓ
    exact IsAffine.affine
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

/-- The colimit of section rings on affine neighborhoods gives a limit of schemes. -/
private def affineLimitCone : LimitCone (affineDiagram s) := by
  let h := (Functor.Final.isColimitWhiskerEquiv (affineInclusion s).op _).symm
    ((neighborhoodPoint s).isColimitPresheafFiberCocone (sections X))
  let c := coneRightOpOfCocone (affineCocone s)
  let hc : IsLimit c := isLimitConeRightOpOfCocone _ h
  exact ⟨(Cone.postcompose (affineToSpec s).inv).obj (Scheme.Spec.mapCone c),
    (IsLimit.postcomposeHomEquiv (affineToSpec s).symm _).symm
      (isLimitOfPreserves Scheme.Spec hc)⟩

/-- The spectrum of the étale local ring is the limit of the pointed
étale neighborhoods. -/
def neighborhoodLimitCone : LimitCone (neighborhoods s) :=
  Functor.Initial.limitConeOfComp (affineInclusion s) (affineLimitCone s)

@[simp] theorem neighborhoodLimitCone_pt :
    (neighborhoodLimitCone s).cone.pt = Spec (stalkRing s) := rfl

/-- The geometric point furnished by evaluation gives back the chosen lift
on every étale neighborhood. -/
theorem evaluation_comp_projection (W : Neighborhood s) :
    Spec.map (evaluateGerm s) ≫ (neighborhoodLimitCone s).cone.π.app W = W.2.left := by
  let F := affineInclusion s
  let V := Functor.Initial.lift F W
  let g := Functor.Initial.homToLift F W
  change Spec.map (evaluateGerm s) ≫
    (Functor.Initial.extendCone.obj (affineLimitCone s).cone).π.app W = W.2.left
  rw [Functor.Initial.extendCone_obj_π_app' (affineLimitCone s).cone g, ← Category.assoc]
  have h : Spec.map (evaluateGerm s) ≫ (affineLimitCone s).cone.π.app V = V.obj.2.left := by
    change Spec.map (evaluateGerm s) ≫
      Spec.map ((neighborhoodPoint s).toPresheafFiber V.obj.1 V.obj.2 (sections X)) ≫
        (affineToSpec s).inv.app V = V.obj.2.left
    rw [← Spec.map_comp_assoc, germ_evaluateGerm, ← point_toSpecΓ, Category.assoc]
    change V.obj.2.left ≫ (affineToSpec s).hom.app V ≫ (affineToSpec s).inv.app V = V.obj.2.left
    rw [Iso.hom_inv_id_app]
    exact Category.comp_id (show Spec (CommRingCat.of K) ⟶ (affineDiagram s).obj V from V.obj.2.left)
  rw [h]
  exact congrArg Over.Hom.left g.property

private abbrev identityNeighborhood : Neighborhood s :=
  ⟨Scheme.Etale.mk (𝟙 X), Over.homMk s (Category.comp_id _)⟩

/-- The morphism from the spectrum of the étale local ring to the original scheme. -/
def toBase : Spec (stalkRing s) ⟶ X :=
  (neighborhoodLimitCone s).cone.π.app (identityNeighborhood s)

theorem evaluation_comp_toBase : Spec.map (evaluateGerm s) ≫ toBase s = s :=
  evaluation_comp_projection s _

theorem projection_comp_hom (W : Neighborhood s) :
    (neighborhoodLimitCone s).cone.π.app W ≫ W.1.hom = toBase s := by
  let f : W.1 ⟶ (identityNeighborhood s).1 :=
    MorphismProperty.Over.homMk W.1.hom (Category.comp_id _) trivial
  let g : W ⟶ identityNeighborhood s := ⟨f, Over.OverMorphism.ext (Over.w W.2)⟩
  exact (neighborhoodLimitCone s).cone.w g

end

end PhilipponPointedEtaleNeighborhoods

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory IsLocalRing Polynomial


namespace PhilipponHenselianEtaleSection

variable (R : Type*) [CommRing R] [HenselianLocalRing R]

private abbrev ρ := Algebra.ofId R (ResidueField R)

private theorem exists_section_standardPair (P : StandardEtalePair R) (φ : P.Ring →ₐ[R] ResidueField R) :
    ∃ ψ : P.Ring →ₐ[R] R, (ρ R).comp ψ = φ := by
  have hx := (StandardEtalePair.hasMap_X (P := P)).map φ
  have hLift : ∀ p : R[X], p.Monic → ∀ a : ResidueField R,
      aeval a p = 0 → aeval a p.derivative ≠ 0 →
      ∃ b : R, p.IsRoot b ∧ residue R b = a :=
    ((HenselianLocalRing.TFAE R).out 0 1).mp (show HenselianLocalRing R from inferInstance)
  obtain ⟨b, hb, hres⟩ := hLift P.f P.monic_f (φ P.X)
    hx.1 (hx.isUnit_derivative_f.ne_zero)
  have hb' : P.HasMap b := by
    refine ⟨?_, ?_⟩
    · simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id,
        Polynomial.IsRoot.def] using hb
    · have h := hx.2.ne_zero
      rw [← hres, Polynomial.aeval_def, IsLocalRing.ResidueField.algebraMap_eq,
        Polynomial.eval₂_at_apply] at h
      simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using
        (residue_ne_zero_iff_isUnit _).mp h
  refine ⟨P.lift b hb', P.hom_ext ?_⟩
  change residue R (P.lift b hb' P.X) = φ P.X
  rw [P.lift_X, hres]

private theorem exists_section_standard {S : Type*} [CommRing S] [Algebra R S]
    [Algebra.IsStandardEtale R S] (φ : S →ₐ[R] ResidueField R) :
    ∃ ψ : S →ₐ[R] R, (ρ R).comp ψ = φ := by
  let P : StandardEtalePresentation R S := Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  obtain ⟨ψ, hψ⟩ := exists_section_standardPair R P.P (φ.comp P.equivRing.symm.toAlgHom)
  refine ⟨ψ.comp P.equivRing.toAlgHom, ?_⟩
  ext x
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using
    DFunLike.congr_fun hψ (P.equivRing x)

/-- An algebra map from an étale algebra to the residue field of a Henselian
local ring lifts to an algebra map to the ring. -/
theorem exists_section {S : Type*} [CommRing S] [Algebra R S] [Algebra.Etale R S]
    (φ : S →ₐ[R] ResidueField R) : ∃ ψ : S →ₐ[R] R, (ρ R).comp ψ = φ := by
  let Q := RingHom.ker φ.toRingHom
  let : Q.IsPrime := RingHom.ker_isPrime φ.toRingHom
  let : Algebra.IsEtaleAt R Q := Algebra.FormallyEtale.comp R S _
  obtain ⟨g, hg, hstd⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) Q
  have hu : IsUnit (φ g) := isUnit_iff_ne_zero.mpr hg
  let φ' : Localization.Away g →ₐ[R] ResidueField R := IsLocalization.Away.liftAlgHom g hu
  obtain ⟨ψ, hψ⟩ := exists_section_standard R φ'
  refine ⟨ψ.comp (IsScalarTower.toAlgHom R S (Localization.Away g)), ?_⟩
  ext x
  exact (DFunLike.congr_fun hψ (algebraMap S (Localization.Away g) x)).trans
    (IsLocalization.Away.lift_eq g hu x)

universe u

/-- A lift of the residue point to an étale scheme over a Henselian local
ring extends to a section over the ring. -/
theorem exists_scheme_section {R : Type u} [CommRing R] [HenselianLocalRing R]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of R)) [Etale g]
    (x : Spec (CommRingCat.of (ResidueField R)) ⟶ Y)
    (hx : x ≫ g = Spec.map (CommRingCat.ofHom (residue R))) :
    ∃ t : Spec (CommRingCat.of R) ⟶ Y,
      t ≫ g = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (residue R)) ≫ t = x := by
  obtain ⟨A, i, hi, hxI, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := x default) (U := ⊤) trivial
  have hr : Set.range x ⊆ Set.range i := by
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  let e := IsOpenImmersion.lift i x hr
  have he : e ≫ i = x := IsOpenImmersion.lift_fac ..
  obtain ⟨p, hp⟩ := Spec.map_surjective (i ≫ g)
  obtain ⟨q, hq⟩ := Spec.map_surjective e
  have hpq : p ≫ q = CommRingCat.ofHom (residue R) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hq, hp, ← Category.assoc, he, hx]
  have hpe : Etale (Spec.map p) := hp.symm ▸ (inferInstance : Etale (i ≫ g))
  let : Algebra R A := p.hom.toAlgebra
  let : Algebra.Etale R A := (HasRingHomProperty.Spec_iff (P := @Etale)).mp hpe
  let q' : A →ₐ[R] ResidueField R :=
    { toRingHom := q.hom
      commutes' := fun a => ConcreteCategory.congr_hom hpq a }
  obtain ⟨k, hk⟩ := exists_section R q'
  let k' : A ⟶ CommRingCat.of R := CommRingCat.ofHom k.toRingHom
  have hpk : p ≫ k' = 𝟙 _ := ConcreteCategory.hom_ext_iff.mpr k.commutes
  have hkq : k' ≫ CommRingCat.ofHom (residue R) = q := by
    apply ConcreteCategory.hom_ext
    intro a
    exact DFunLike.congr_fun hk a
  refine ⟨Spec.map k' ≫ i, ?_, ?_⟩
  · rw [Category.assoc, ← hp, ← Spec.map_comp, hpk, Spec.map_id]
  · rw [← Category.assoc, ← Spec.map_comp, hkq, hq, he]

end PhilipponHenselianEtaleSection

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponPointedEtaleNeighborhoods


namespace PhilipponOrdinaryHenselization

universe u

private abbrev spec {R A : Type u} [CommRing R] [CommRing A] (a : R →+* A) :=
  Spec.map (CommRingCat.ofHom a)

private abbrev closed (R : Type u) [CommRing R] [IsLocalRing R] := spec (IsLocalRing.residue R)

private theorem spec_comp {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    (a : R →+* S) (b : S →+* A) : spec b ≫ spec a = spec (b.comp a) :=
  (Spec.map_comp (CommRingCat.ofHom a) (CommRingCat.ofHom b)).symm

private theorem spec_injective {R A : Type u} [CommRing R] [CommRing A]
    {a b : R →+* A} (h : spec a = spec b) : a = b :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

private theorem eq_of_residue_eq {A : Type u} [CommRing A] [IsLocalRing A]
    {Y X : Scheme.{u}} (g : Y ⟶ X) [Etale g] {x y : Spec (.of A) ⟶ Y}
    (h : x ≫ g = y ≫ g) (hr : closed A ≫ x = closed A ≫ y) : x = y := by
  let p := pullback.lift x y h
  let d := pullback.diagonal g
  let : IsOpenImmersion d := inferInstanceAs (IsOpenImmersion (pullback.diagonal g))
  have hp : closed A ≫ p = (closed A ≫ x) ≫ d := by
    apply pullback.hom_ext
    · simp only [Category.assoc, p, d, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
    · simp only [Category.assoc, p, d, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, hr]
  let a := IsLocalRing.closedPoint (IsLocalRing.ResidueField A)
  have hc : closed A a = IsLocalRing.closedPoint A := IsLocalRing.comap_closedPoint (IsLocalRing.residue A)
  have ht : p (IsLocalRing.closedPoint A) ∈ Set.range d := by
    refine ⟨(closed A ≫ x) a, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← hp, Scheme.Hom.comp_apply, hc]
  have hRange : Set.range p ⊆ Set.range d := by
    rintro _ ⟨z, rfl⟩
    exact (IsLocalRing.specializes_closedPoint z).mem_open
      (d.isOpenEmbedding.isOpen_range.preimage p.continuous) ht
  let m := IsOpenImmersion.lift d p hRange
  have hm : m ≫ d = p := IsOpenImmersion.lift_fac ..
  have h₁ : m = x := by
    have h' := congrArg (· ≫ pullback.fst g g) hm
    simpa only [Category.assoc, p, d, pullback.diagonal_fst, Category.comp_id, pullback.lift_fst] using h'
  have h₂ : m = y := by
    have h' := congrArg (· ≫ pullback.snd g g) hm
    simpa only [Category.assoc, p, d, pullback.diagonal_snd, Category.comp_id, pullback.lift_snd] using h'
  exact h₁.symm.trans h₂

/-- A residue-field lift to an étale scheme extends uniquely to a lift over
the henselian base. -/
theorem existsUnique_lift {A : Type u} [CommRing A] [HenselianLocalRing A]
    {X Y : Scheme.{u}} (g : Y ⟶ X) [Etale g] (v : Spec (.of A) ⟶ X)
    (x : Spec (.of (IsLocalRing.ResidueField A)) ⟶ Y) (hx : x ≫ g = closed A ≫ v) :
    ∃! y : Spec (.of A) ⟶ Y, y ≫ g = v ∧ closed A ≫ y = x := by
  let z := pullback.lift x (closed A) hx
  have hz : z ≫ pullback.snd g v = closed A := pullback.lift_snd ..
  obtain ⟨w, hw, hw'⟩ :=
    PhilipponHenselianEtaleSection.exists_scheme_section (pullback.snd g v) z hz
  let y := w ≫ pullback.fst g v
  have hy : y ≫ g = v := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hw, Category.id_comp]
  have hyr : closed A ≫ y = x := by
    rw [← Category.assoc, hw', pullback.lift_fst]
  exact ⟨y, ⟨hy, hyr⟩, fun z hz => eq_of_residue_eq g (hz.1.trans hy.symm) (hz.2.trans hyr.symm)⟩

/-- A lift of the residue point gives a compatible map to the limit of all of
its pointed étale neighborhoods. -/
theorem existsUnique_to_neighborhoodLimit {K A : Type u} [Field K] [CommRing A] [HenselianLocalRing A]
    {X : Scheme.{u}} (s : Spec (.of K) ⟶ X) (v : Spec (.of A) ⟶ X)
    (a : K →+* IsLocalRing.ResidueField A) (ha : spec a ≫ s = closed A ≫ v) :
    ∃! y : Spec (.of A) ⟶ Spec (stalkRing s),
      y ≫ toBase s = v ∧ closed A ≫ y = spec a ≫ Spec.map (evaluateGerm s) := by
  classical
  have lifts (W : Neighborhood s) :
      ∃! l : Spec (.of A) ⟶ W.1.left,
        l ≫ W.1.hom = v ∧ closed A ≫ l = spec a ≫ W.2.left := by
    apply existsUnique_lift W.1.hom v
    rw [Category.assoc]
    rw [show W.2.left ≫ W.1.hom = s from Over.w W.2]
    exact ha
  choose l hl huniq using lifts
  let c : Cone (neighborhoods s) := ⟨_, {
    app := l
    naturality := fun W V k => by
      change 𝟙 _ ≫ l V = l W ≫ k.val.left
      rw [Category.id_comp]
      symm
      apply huniq V
      refine ⟨?_, ?_⟩
      · rw [Category.assoc, MorphismProperty.Over.w k.val]
        exact (hl W).1
      · rw [← Category.assoc, (hl W).2, Category.assoc]
        exact congrArg (spec a ≫ ·) (congrArg Over.Hom.left k.property) }⟩
  let M := neighborhoodLimitCone s
  let y := M.isLimit.lift c
  have hy (W : Neighborhood s) : y ≫ M.cone.π.app W = l W := M.isLimit.fac c W
  refine ⟨y, ⟨?_, ?_⟩, ?_⟩
  · let W : Neighborhood s := ⟨Scheme.Etale.mk (𝟙 X), Over.homMk s (Category.comp_id _)⟩
    calc
      y ≫ toBase s = y ≫ M.cone.π.app W ≫ W.1.hom := by rw [projection_comp_hom]
      _ = l W ≫ W.1.hom := by rw [← Category.assoc, hy]
      _ = v := (hl W).1
  · apply M.isLimit.hom_ext
    intro W
    change (closed A ≫ y) ≫ M.cone.π.app W = (spec a ≫ Spec.map (evaluateGerm s)) ≫ M.cone.π.app W
    rw [Category.assoc, hy, (hl W).2, Category.assoc, evaluation_comp_projection]
  · intro z hz
    apply M.isLimit.hom_ext
    intro W
    rw [hy]
    apply huniq W
    constructor
    · rw [Category.assoc, projection_comp_hom]
      exact hz.1
    · rw [← Category.assoc, hz.2, Category.assoc, evaluation_comp_projection]

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The ring of germs on the étale neighborhoods pointed by the actual
residue field of the local ring. -/
abbrev Ring := stalkRing (closed R)

/-- The structural map into the ordinary henselization. -/
def inclusion : R →+* Ring R := (Spec.preimage (toBase (closed R))).hom

private abbrev evaluation : Ring R →+* IsLocalRing.ResidueField R := (evaluateGerm (closed R)).hom

theorem spec_inclusion : spec (inclusion R) = toBase (closed R) :=
  Spec.map_preimage _

theorem evaluation_comp_inclusion : (evaluation R).comp (inclusion R) = IsLocalRing.residue R := by
  apply spec_injective
  rw [← spec_comp, spec_inclusion]
  exact evaluation_comp_toBase (closed R)

instance inclusion_isLocalHom : IsLocalHom (inclusion R) := by
  constructor
  intro x hx
  apply (IsLocalRing.residue_ne_zero_iff_isUnit x).mp
  rw [← evaluation_comp_inclusion, RingHom.comp_apply]
  exact (hx.map (evaluation R)).ne_zero

theorem evaluation_surjective : Function.Surjective (evaluation R) := by
  intro x
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective x
  exact ⟨inclusion R r, (DFunLike.congr_fun (evaluation_comp_inclusion R) r).trans hr⟩

/-- The residue field of the henselization is the residue field of the
original ring, via the map induced by the inclusion. -/
theorem residueMap_bijective : Function.Bijective (IsLocalRing.ResidueField.map (inclusion R)) := by
  let e := IsLocalRing.ResidueField.lift (evaluation R)
  have he : Function.Injective e := e.injective
  have h : e.comp (IsLocalRing.ResidueField.map (inclusion R)) = RingHom.id _ := by
    apply RingHom.ext
    intro x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
    rw [RingHom.comp_apply, IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.lift_residue_apply]
    exact DFunLike.congr_fun (evaluation_comp_inclusion R) r
  refine ⟨(IsLocalRing.ResidueField.map (inclusion R)).injective, fun x => ⟨e x, he ?_⟩⟩
  exact DFunLike.congr_fun h (e x)

/-- A local map from the base into a henselian local ring has a unique
local extension over the henselization. -/
theorem existsUnique_local_extension {A : Type u} [CommRing A] [HenselianLocalRing A]
    (f : R →+* A) [IsLocalHom f] :
    ∃! a : Ring R →+* A, IsLocalHom a ∧ a.comp (inclusion R) = f := by
  let k := IsLocalRing.ResidueField.map f
  have hk : spec k ≫ closed R = closed A ≫ spec f := by
    rw [spec_comp, spec_comp, IsLocalRing.ResidueField.map_comp_residue]
  obtain ⟨y, ⟨hy, hy'⟩, hunique⟩ := existsUnique_to_neighborhoodLimit (closed R) (spec f) k hk
  let a := (Spec.preimage y).hom
  have ea : spec a = y := Spec.map_preimage _
  have ha : a.comp (inclusion R) = f := by
    apply spec_injective
    rw [← spec_comp, ea, spec_inclusion]
    exact hy
  have hr : (IsLocalRing.residue A).comp a = k.comp (evaluation R) := by
    apply spec_injective
    rw [← spec_comp, ← spec_comp, ea]
    exact hy'
  refine ⟨a, ⟨⟨?_⟩, ha⟩, ?_⟩
  · intro x hx
    apply (isUnit_iff_evaluateGerm_ne_zero (closed R) x).mpr
    intro hx'
    have h := DFunLike.congr_fun hr x
    change IsLocalRing.residue A (a x) = k (evaluation R x) at h
    change evaluation R x = 0 at hx'
    rw [hx', map_zero] at h
    exact (hx.map (IsLocalRing.residue A)).ne_zero h
  · rintro b ⟨hb, hb'⟩
    let := hb
    have he : (IsLocalRing.residue A).comp b = k.comp (evaluation R) := by
      apply RingHom.ext
      intro x
      obtain ⟨z, hz⟩ := (residueMap_bijective R).2 (IsLocalRing.residue (Ring R) x)
      obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective z
      rw [IsLocalRing.ResidueField.map_residue] at hz
      let e := IsLocalRing.ResidueField.lift (evaluation R)
      have heq := congrArg e hz
      rw [IsLocalRing.ResidueField.lift_residue_apply, IsLocalRing.ResidueField.lift_residue_apply] at heq
      change evaluation R (inclusion R t) = evaluation R x at heq
      change IsLocalRing.residue A (b x) = k (evaluation R x)
      calc
        _ = IsLocalRing.ResidueField.map b (IsLocalRing.residue (Ring R) x) :=
          (IsLocalRing.ResidueField.map_residue b x).symm
        _ = IsLocalRing.residue A (b (inclusion R t)) := by rw [← hz, IsLocalRing.ResidueField.map_residue]
        _ = IsLocalRing.residue A (f t) :=
          congrArg (IsLocalRing.residue A) (DFunLike.congr_fun hb' t)
        _ = k (evaluation R x) := by
          rw [← heq, show evaluation R (inclusion R t) = IsLocalRing.residue R t from
            DFunLike.congr_fun (evaluation_comp_inclusion R) t]
          exact (IsLocalRing.ResidueField.map_residue f t).symm
    apply spec_injective
    rw [ea]
    apply hunique
    constructor
    · rw [← spec_inclusion, spec_comp, hb']
    · change closed A ≫ spec b = spec k ≫ spec (evaluation R)
      rw [spec_comp, spec_comp, he]

end PhilipponOrdinaryHenselization

end

section

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PhilipponMultiplicity.NoetherianCompletion

open scoped Topology

variable {R : Type*} [CommRing R]

theorem exists_powerSeriesMap (I : Ideal R) (hI : I.FG)
    {σ : Type*} [Finite σ] (a : σ → R) (ha : ∀ i, a i ∈ I) :
    ∃ f : MvPowerSeries σ R →+* AdicCompletion I R,
      (∀ r : R, f (MvPowerSeries.C r) = algebraMap R (AdicCompletion I R) r) ∧
      (∀ i : σ, f (MvPowerSeries.X i) = algebraMap R (AdicCompletion I R) (a i)) := by
  let S := AdicCompletion I R
  let J := I.map (algebraMap R S)
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  letI : IsAdicComplete J S := AdicCompletion.isAdicComplete_self I hI
  have hcomplete : CompleteSpace S ∧ T2Space S :=
    (IsAdic.isAdicComplete_iff (I := J) rfl).mp inferInstance
  letI : CompleteSpace S := hcomplete.1
  letI : T2Space S := hcomplete.2
  have hcont : Continuous (algebraMap R S) := continuous_of_discreteTopology
  have heval : MvPowerSeries.HasEval (fun i => algebraMap R S (a i)) := by
    constructor
    · intro i
      exact WithIdeal.isTopologicallyNilpotent_of_mem (Ideal.mem_map_of_mem _ (ha i))
    · simp only [Filter.cofinite_eq_bot]
      exact Filter.tendsto_bot
  refine ⟨MvPowerSeries.eval₂Hom hcont heval, ?_, ?_⟩
  · intro r
    simp [MvPowerSeries.coe_eval₂Hom, S]
  · intro i
    simp [MvPowerSeries.coe_eval₂Hom, S]

theorem powerSeriesMap_surjective (I : Ideal R) (hI : I.FG)
    {σ : Type*} [Finite σ] (a : σ → R)
    (ha : Ideal.span (Set.range a) = I)
    (f : MvPowerSeries σ R →+* AdicCompletion I R)
    (hC : ∀ r : R, f (MvPowerSeries.C r) = algebraMap R (AdicCompletion I R) r)
    (hX : ∀ i : σ, f (MvPowerSeries.X i) = algebraMap R (AdicCompletion I R) (a i)) :
    Function.Surjective f := by
  let S := AdicCompletion I R
  let J : Ideal (MvPowerSeries σ R) := Ideal.span (Set.range MvPowerSeries.X)
  have hmap : J.map f = I.map (algebraMap R S) := by
    change (Ideal.span (Set.range MvPowerSeries.X)).map f = _
    rw [Ideal.map_span, ← Set.range_comp]
    simp only [Function.comp_def, hX]
    simpa only [Ideal.map_span, ← Set.range_comp, Function.comp_def, S] using
      congrArg (Ideal.map (algebraMap R S)) ha
  letI : IsAdicComplete (I.map (algebraMap R S)) S :=
    AdicCompletion.isAdicComplete_self I hI
  letI : IsHausdorff (J.map f) S := hmap ▸ inferInstance
  apply surjective_of_mk_map_comp_surjective (I := J) f
  intro q
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I y)
  refine ⟨MvPowerSeries.C r, ?_⟩
  change Ideal.Quotient.mk (J.map f) (f (MvPowerSeries.C r)) =
    Ideal.Quotient.mk (J.map f) y
  rw [hC, Ideal.Quotient.eq, hmap]
  change algebraMap R (AdicCompletion I R) r - y ∈
    I.map (algebraMap R (AdicCompletion I R))
  rw [← AdicCompletion.ker_evalOneₐ_eq_map (I := I) hI]
  change AdicCompletion.evalOneₐ I (algebraMap R S r - y) = 0
  rw [map_sub]
  change Ideal.Quotient.mk I r - AdicCompletion.evalOneₐ I y = 0
  rw [hr, sub_self]

theorem isNoetherianRing_completion [IsNoetherianRing R] (I : Ideal R) :
    IsNoetherianRing (AdicCompletion I R) := by
  obtain ⟨n, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp I.fg_of_isNoetherianRing
  have hmem : ∀ i, a i ∈ I := fun i => ha ▸ Ideal.subset_span (Set.mem_range_self i)
  obtain ⟨f, hC, hX⟩ := exists_powerSeriesMap I I.fg_of_isNoetherianRing a hmem
  exact isNoetherianRing_of_surjective (MvPowerSeries (Fin n) R) (AdicCompletion I R) f
    (powerSeriesMap_surjective I I.fg_of_isNoetherianRing a ha f hC hX)

end PhilipponMultiplicity.NoetherianCompletion

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponPointedEtaleNeighborhoods
open PhilipponOrdinaryHenselization (inclusion spec_inclusion existsUnique_local_extension)
open scoped TensorProduct


namespace PhilipponHenselizationFlatness

universe u

private theorem flat_lift {X Y Z : Scheme.{u}} (g : Y ⟶ X) [Etale g] (f : Z ⟶ X) [Flat f]
    (v : Z ⟶ Y) (h : v ≫ g = f) : Flat v := by
  let s := pullback.lift v (𝟙 Z) (h.trans (Category.id_comp f).symm)
  have hs : s ≫ pullback.snd g f = 𝟙 Z := pullback.lift_snd ..
  let : Etale (s ≫ pullback.snd g f) := hs.symm ▸ inferInstanceAs (Etale (𝟙 Z))
  let : Etale s := Etale.of_comp s (pullback.snd g f)
  have H : Flat (s ≫ pullback.fst g f) := inferInstance
  rwa [pullback.lift_fst] at H

private theorem flat_of_finite_coefficients {H A : Type u} [CommRing H] [CommRing A] (v : H →+* A)
    (lift : ∀ (n : ℕ) (r : Fin n → H),
      ∃ (B : Type u) (_ : CommRing B) (j : B →+* H) (s : Fin n → B), (v.comp j).Flat ∧
        ∀ i, j (s i) = r i) : v.Flat := by
  let : Algebra H A := v.toAlgebra
  apply Module.Flat.of_forall_isTrivialRelation
  intro n r x hx
  obtain ⟨B, hB, j, s, hj, hs⟩ := lift n r
  let := hB
  let : Algebra B A := (v.comp j).toAlgebra
  let : Module.Flat B A := hj
  have h : ∑ i, s i • x i = 0 := by
    simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, RingHom.comp_apply, hs] using hx
  obtain ⟨k, c, y, hxy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
    (R := B) (M := A) (f := s) (x := x) h
  refine ⟨k, fun i j' => j (c i j'), y, ?_, ?_⟩
  · intro i
    simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, RingHom.comp_apply] using hxy i
  · intro l
    simpa only [map_sum, map_mul, hs, map_zero] using congrArg j (hc l)

/-- A flat map remains flat when it factors through the ordinary henselization. -/
theorem flat_extension {R A : Type u} [CommRing R] [IsLocalRing R] [CommRing A]
    (f : R →+* A) (hf : f.Flat) (a : PhilipponOrdinaryHenselization.Ring R →+* A)
    (ha : a.comp (inclusion R) = f) :
    a.Flat := by
  classical
  let s := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  let M := neighborhoodLimitCone s
  let J := (IsAffineNeighborhood s).FullSubcategory
  let initial := InitiallySmall.fromCofilteredInitialModel.{u} J
  let F := initial ⋙ affineInclusion s
  let D := F ⋙ neighborhoods s
  let c : Cone D := M.cone.whisker F
  let hc : IsLimit c := (Functor.Initial.isLimitWhiskerEquiv F M.cone).symm M.isLimit
  let : ∀ i, IsAffine (D.obj i) := fun i => (initial.obj i).property
  let v := Spec.map (CommRingCat.ofHom a)
  let g := Spec.map (CommRingCat.ofHom f)
  let : Flat g := Flat.SpecMap_iff.mpr hf
  have hv : v ≫ toBase s = g := by
    have h := congrArg (fun b : R →+* A => Spec.map (CommRingCat.ofHom b)) ha
    rw [CommRingCat.ofHom_comp, Spec.map_comp] at h
    calc
      v ≫ toBase s = v ≫ Spec.map (CommRingCat.ofHom (inclusion R)) :=
        congrArg (v ≫ ·) (spec_inclusion R).symm
      _ = g := h
  let E : Γ(c.pt, ⊤) ≅ PhilipponOrdinaryHenselization.Ring R := Scheme.ΓSpecIso _
  apply flat_of_finite_coefficients a
  intro n r
  choose i b hb using fun t => exists_appTop_π_eq_of_isAffine_of_isLimit D c hc (E.inv (r t))
  obtain ⟨j, hj⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image i)
  let q (t : Fin n) : j ⟶ i t := (hj (Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩)).some
  let p := c.π.app j
  let B := Γ(D.obj j, ⊤)
  let u := (p.appTop ≫ E.hom).hom
  let b' (t : Fin n) : B := (D.map (q t)).appTop (b t)
  have hcoeff (t : Fin n) : u (b' t) = r t := by
    have he : (D.map (q t)).appTop ≫ p.appTop = (c.π.app (i t)).appTop := by
      rw [← Scheme.Hom.comp_appTop, c.w]
    have hval := ConcreteCategory.congr_hom he (b t)
    change p.appTop ((D.map (q t)).appTop (b t)) = (c.π.app (i t)).appTop (b t) at hval
    change E.hom (p.appTop ((D.map (q t)).appTop (b t))) = r t
    rw [hval, hb]
    exact ConcreteCategory.congr_hom E.inv_hom_id (r t)
  let w := v ≫ p
  have hw : w ≫ (F.obj j).1.hom = g :=
    (Category.assoc v p (F.obj j).1.hom).trans
      ((congrArg (v ≫ ·) (projection_comp_hom s (F.obj j))).trans hv)
  let : Flat w := flat_lift _ _ _ hw
  have H : Spec.map (w.appTop ≫ (Scheme.ΓSpecIso (.of A)).hom) = w ≫ (D.obj j).isoSpec.hom := by
    rw [Spec.map_comp, SpecMap_ΓSpecIso_hom, ← Scheme.toSpecΓ_naturality]
    rfl
  have hlift : (w.appTop ≫ (Scheme.ΓSpecIso (.of A)).hom).hom.Flat := by
    apply Flat.SpecMap_iff.mp
    rw [H]
    infer_instance
  have hcomp : (w.appTop ≫ (Scheme.ΓSpecIso (.of A)).hom).hom = a.comp u := by
    rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc]
    rfl
  exact ⟨B, inferInstance, u, b', hcomp ▸ hlift, hcoeff⟩

/-- The ordinary henselization of a Noetherian local ring is Noetherian.
The map to the completion is local and flat, so Noetherianity descends. -/
theorem isNoetherianRing_henselization (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] : IsNoetherianRing (PhilipponOrdinaryHenselization.Ring R) := by
  let C := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let : HenselianLocalRing C := {
    toIsLocalRing := inferInstance
    is_henselian := fun p hp x hx hd =>
      HenselianRing.is_henselian (I := IsLocalRing.maximalIdeal C) p hp x hx (hd.map (Ideal.Quotient.mk _)) }
  let f := algebraMap R C
  obtain ⟨a, ⟨ha, hcomp⟩, _⟩ := existsUnique_local_extension R f
  let H := PhilipponOrdinaryHenselization.Ring R
  let : Algebra H C := a.toAlgebra
  let : Module.Flat H C := flat_extension f (RingHom.flat_algebraMap_iff.mpr inferInstance) a hcomp
  let : IsLocalHom (algebraMap H C) := ha
  let : Module.FaithfullyFlat H C := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : IsNoetherianRing C :=
    PhilipponMultiplicity.NoetherianCompletion.isNoetherianRing_completion (IsLocalRing.maximalIdeal R)
  exact Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
    (isNoetherian_of_linearEquiv (Algebra.TensorProduct.rid H C C).symm.toLinearEquiv)

/-- A Noetherian local ring has a Noetherian henselization with unchanged
residue field and the universal property for local homomorphisms. -/
theorem exists_noetherian_henselization (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ∃ (H : Type u) (_ : CommRing H) (_ : HenselianLocalRing H) (_ : IsNoetherianRing H)
      (i : R →+* H) (_ : IsLocalHom i),
      Function.Bijective (IsLocalRing.ResidueField.map i) ∧
      ∀ (A : Type u) [CommRing A] [HenselianLocalRing A] (f : R →+* A) [IsLocalHom f],
        ∃! g : H →+* A, IsLocalHom g ∧ g.comp i = f := by
  refine ⟨PhilipponOrdinaryHenselization.Ring R, inferInstance, inferInstance,
    isNoetherianRing_henselization R, inclusion R, inferInstance,
    PhilipponOrdinaryHenselization.residueMap_bijective R, ?_⟩
  intro A _ _ f _
  exact existsUnique_local_extension R f

end PhilipponHenselizationFlatness

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ∃ (H : Type u) (_ : CommRing H) (_ : HenselianLocalRing H) (_ : IsNoetherianRing H)
      (i : R →+* H) (_ : IsLocalHom i),
      Function.Bijective (IsLocalRing.ResidueField.map i) ∧
      ∀ (A : Type u) [CommRing A] [HenselianLocalRing A] (f : R →+* A) [IsLocalHom f],
        ∃! g : H →+* A, IsLocalHom g ∧ g.comp i = f := by
  exact PhilipponHenselizationFlatness.exists_noetherian_henselization R

end

end
