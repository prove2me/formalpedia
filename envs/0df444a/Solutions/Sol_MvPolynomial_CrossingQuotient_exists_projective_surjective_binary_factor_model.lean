-- Prove2me | solution 1 for MvPolynomial.CrossingQuotient.exists_projective_surjective_binary_factor_model
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-28T15:56:37.017066+00:00
-- url     : https://prove2.me/submissions/4a55b694-6788-4862-9aac-a9a87bedd05f

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_MvPolynomial_CrossingResolution

universe u
noncomputable section


set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MvPolynomial MvPolynomial.CrossingQuotient

namespace PhilipponNodeFactorCharts

variable {R : Type u} [CommRing R]

lemma chart_ext {t : R} {A : Type*} [CommRing A] [Algebra R A]
    {f g : CrossingQuotient R t →ₐ[R] A}
    (hU : f (U t) = g (U t)) (hV : f (V t) = g (V t)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · exact hU
  · exact hV

def toLeft (a b : R) : CrossingQuotient R (a * b) →ₐ[R] CrossingQuotient R a :=
  lift (a * b) (U a) (algebraMap R _ b * V a) (by
    rw [mul_left_comm, U_mul_V, map_mul]
    ring)

def toRight (a b : R) : CrossingQuotient R (a * b) →ₐ[R] CrossingQuotient R b :=
  lift (a * b) (algebraMap R _ a * U b) (V b) (by
    rw [mul_assoc, U_mul_V, map_mul])

@[simp] lemma toLeft_U (a b : R) : toLeft a b (U (a * b)) = U a := lift_U _ _ _ _
@[simp] lemma toLeft_V (a b : R) :
    toLeft a b (V (a * b)) = algebraMap R _ b * V a := lift_V _ _ _ _
@[simp] lemma toRight_U (a b : R) :
    toRight a b (U (a * b)) = algebraMap R _ a * U b := lift_U _ _ _ _
@[simp] lemma toRight_V (a b : R) : toRight a b (V (a * b)) = V b := lift_V _ _ _ _

abbrev LeftOverlap (a : R) := Localization.Away (V a)
abbrev RightOverlap (b : R) := Localization.Away (U b)

def rightToLeftOverlap (a b : R) : CrossingQuotient R b →ₐ[R] LeftOverlap a :=
  lift b (IsLocalization.Away.invSelf (V a))
    (algebraMap R _ b * algebraMap (CrossingQuotient R a) _ (V a)) (by
      rw [mul_left_comm, mul_comm (IsLocalization.Away.invSelf (V a)),
        IsLocalization.Away.mul_invSelf, mul_one])

def leftToRightOverlap (a b : R) : CrossingQuotient R a →ₐ[R] RightOverlap b :=
  lift a (algebraMap R _ a * algebraMap (CrossingQuotient R b) _ (U b))
    (IsLocalization.Away.invSelf (U b)) (by
      rw [mul_assoc, IsLocalization.Away.mul_invSelf, mul_one])

lemma leftToRight_isUnit (a b : R) : IsUnit ((leftToRightOverlap a b).toRingHom (V a)) := by
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, leftToRightOverlap, lift_V]
  exact IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf (U b))

lemma rightToLeft_isUnit (a b : R) : IsUnit ((rightToLeftOverlap a b).toRingHom (U b)) := by
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rightToLeftOverlap, lift_U]
  exact IsUnit.of_mul_eq_one_right _ (IsLocalization.Away.mul_invSelf (V a))

def overlapToRightRing (a b : R) : LeftOverlap a →+* RightOverlap b :=
  IsLocalization.Away.lift (S := LeftOverlap a) (V a)
    (g := (leftToRightOverlap a b).toRingHom) (leftToRight_isUnit a b)

def overlapToLeftRing (a b : R) : RightOverlap b →+* LeftOverlap a :=
  IsLocalization.Away.lift (S := RightOverlap b) (U b)
    (g := (rightToLeftOverlap a b).toRingHom) (rightToLeft_isUnit a b)

lemma overlapToRightRing_algebraMap (a b : R) (z : CrossingQuotient R a) :
    overlapToRightRing a b (algebraMap _ _ z) = leftToRightOverlap a b z :=
  IsLocalization.Away.lift_eq (S := LeftOverlap a) _ (leftToRight_isUnit a b) z

lemma overlapToLeftRing_algebraMap (a b : R) (z : CrossingQuotient R b) :
    overlapToLeftRing a b (algebraMap _ _ z) = rightToLeftOverlap a b z :=
  IsLocalization.Away.lift_eq (S := RightOverlap b) _ (rightToLeft_isUnit a b) z

def overlapToRight (a b : R) : LeftOverlap a →ₐ[R] RightOverlap b :=
  { overlapToRightRing a b with
    commutes' := fun r => by
      change overlapToRightRing a b (algebraMap R (LeftOverlap a) r) = _
      rw [IsScalarTower.algebraMap_apply R (CrossingQuotient R a) (LeftOverlap a) r]
      rw [overlapToRightRing_algebraMap]
      exact (leftToRightOverlap a b).commutes r }

def overlapToLeft (a b : R) : RightOverlap b →ₐ[R] LeftOverlap a :=
  { overlapToLeftRing a b with
    commutes' := fun r => by
      change overlapToLeftRing a b (algebraMap R (RightOverlap b) r) = _
      rw [IsScalarTower.algebraMap_apply R (CrossingQuotient R b) (RightOverlap b) r]
      rw [overlapToLeftRing_algebraMap]
      exact (rightToLeftOverlap a b).commutes r }

@[simp] lemma overlapToRight_algebraMap (a b : R) (z : CrossingQuotient R a) :
    overlapToRight a b (algebraMap _ _ z) = leftToRightOverlap a b z :=
  overlapToRightRing_algebraMap a b z

@[simp] lemma overlapToLeft_algebraMap (a b : R) (z : CrossingQuotient R b) :
    overlapToLeft a b (algebraMap _ _ z) = rightToLeftOverlap a b z :=
  overlapToLeftRing_algebraMap a b z

lemma overlapToRight_inv (a b : R) :
    overlapToRight a b (IsLocalization.Away.invSelf (V a)) =
      algebraMap (CrossingQuotient R b) (RightOverlap b) (U b) := by
  have h := congrArg (overlapToRight a b) (IsLocalization.Away.mul_invSelf (V a))
  simp only [map_mul, overlapToRight_algebraMap, leftToRightOverlap, lift_V, map_one] at h
  have h' := IsLocalization.Away.mul_invSelf (S := RightOverlap b) (U b)
  linear_combination (algebraMap (CrossingQuotient R b) (RightOverlap b) (U b)) * h -
    (overlapToRight a b (IsLocalization.Away.invSelf (V a))) * h'

lemma overlapToLeft_inv (a b : R) :
    overlapToLeft a b (IsLocalization.Away.invSelf (U b)) =
      algebraMap (CrossingQuotient R a) (LeftOverlap a) (V a) := by
  have h := congrArg (overlapToLeft a b) (IsLocalization.Away.mul_invSelf (U b))
  simp only [map_mul, overlapToLeft_algebraMap, rightToLeftOverlap, lift_U, map_one] at h
  have h' := IsLocalization.Away.mul_invSelf (S := LeftOverlap a) (V a)
  linear_combination (algebraMap (CrossingQuotient R a) (LeftOverlap a) (V a)) * h -
    (overlapToLeft a b (IsLocalization.Away.invSelf (U b))) * h'

lemma overlap_left_right (a b : R) :
    (overlapToLeft a b).comp (overlapToRight a b) = AlgHom.id R (LeftOverlap a) := by
  have h : ((overlapToLeft a b).comp (overlapToRight a b)).comp
      (IsScalarTower.toAlgHom R (CrossingQuotient R a) (LeftOverlap a)) =
      IsScalarTower.toAlgHom R (CrossingQuotient R a) (LeftOverlap a) := by
    apply chart_ext
    · simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', overlapToRight_algebraMap,
        leftToRightOverlap, lift_U, map_mul, AlgHom.commutes, overlapToLeft_algebraMap,
        rightToLeftOverlap, lift_U]
      rw [IsScalarTower.algebraMap_apply R (CrossingQuotient R a) (LeftOverlap a) a,
        ← U_mul_V, map_mul, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
    · simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', overlapToRight_algebraMap,
        leftToRightOverlap, lift_V, overlapToLeft_inv]
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (V a)) (S := LeftOverlap a)
  exact RingHom.ext fun z => congrArg (fun f : CrossingQuotient R a →ₐ[R] LeftOverlap a => f z) h

lemma overlap_right_left (a b : R) :
    (overlapToRight a b).comp (overlapToLeft a b) = AlgHom.id R (RightOverlap b) := by
  have h : ((overlapToRight a b).comp (overlapToLeft a b)).comp
      (IsScalarTower.toAlgHom R (CrossingQuotient R b) (RightOverlap b)) =
      IsScalarTower.toAlgHom R (CrossingQuotient R b) (RightOverlap b) := by
    apply chart_ext
    · simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', overlapToLeft_algebraMap,
        rightToLeftOverlap, lift_U, overlapToRight_inv]
    · simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', overlapToLeft_algebraMap,
        rightToLeftOverlap, lift_V, map_mul, AlgHom.commutes, overlapToRight_algebraMap,
        leftToRightOverlap, lift_V]
      rw [IsScalarTower.algebraMap_apply R (CrossingQuotient R b) (RightOverlap b) b,
        ← U_mul_V, map_mul]
      rw [mul_comm (algebraMap _ _ (U b)), mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (U b)) (S := RightOverlap b)
  exact RingHom.ext fun z => congrArg (fun f : CrossingQuotient R b →ₐ[R] RightOverlap b => f z) h

def overlapEquiv (a b : R) : LeftOverlap a ≃ₐ[R] RightOverlap b :=
  AlgEquiv.ofAlgHom (overlapToRight a b) (overlapToLeft a b)
    (overlap_right_left a b) (overlap_left_right a b)

lemma charts_agree_on_overlap (a b : R) :
    (IsScalarTower.toAlgHom R (CrossingQuotient R a) (LeftOverlap a)).comp (toLeft a b) =
      (rightToLeftOverlap a b).comp (toRight a b) := by
  apply chart_ext
  · simp only [AlgHom.comp_apply, toLeft_U, toRight_U, map_mul, AlgHom.commutes,
      rightToLeftOverlap, lift_U, IsScalarTower.coe_toAlgHom']
    symm
    rw [IsScalarTower.algebraMap_apply R (CrossingQuotient R a) (LeftOverlap a) a,
      ← U_mul_V, map_mul, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
  · simp only [AlgHom.comp_apply, toLeft_V, toRight_V, map_mul, AlgHom.commutes,
      rightToLeftOverlap, lift_V, IsScalarTower.coe_toAlgHom']

end PhilipponNodeFactorCharts



set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient

namespace PhilipponNodeFactorGluing
open PhilipponNodeFactorCharts
variable {R : Type u} [CommRing R]

abbrev LeftChart (a : R) : Scheme.{u} := Spec (.of (CrossingQuotient R a))
abbrev RightChart (b : R) : Scheme.{u} := Spec (.of (CrossingQuotient R b))
abbrev Overlap (a : R) : Scheme.{u} := Spec (.of (LeftOverlap a))

def leftOverlapMap (a : R) : Overlap a ⟶ LeftChart a :=
  Spec.map (CommRingCat.ofHom (algebraMap (CrossingQuotient R a) (LeftOverlap a)))

def overlapIso (a b : R) : Overlap a ≅ Spec (.of (RightOverlap b)) :=
  Scheme.Spec.mapIso (overlapEquiv a b).symm.toRingEquiv.toCommRingCatIso.op

def rightOverlapMap (a b : R) : Overlap a ⟶ RightChart b :=
  (overlapIso a b).hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap (CrossingQuotient R b) (RightOverlap b)))

instance leftOverlapMap_isOpenImmersion (a : R) : IsOpenImmersion (leftOverlapMap a) := by
  exact IsOpenImmersion.of_isLocalization (V a)

instance rightOverlapMap_isOpenImmersion (a b : R) : IsOpenImmersion (rightOverlapMap a b) := by
  haveI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (CrossingQuotient R b) (RightOverlap b)))) :=
    IsOpenImmersion.of_isLocalization (U b)
  unfold rightOverlapMap
  infer_instance

lemma rightOverlapMap_eq (a b : R) : rightOverlapMap a b =
    Spec.map (CommRingCat.ofHom (rightToLeftOverlap a b).toRingHom) := by
  change Spec.map (CommRingCat.ofHom (overlapToLeftRing a b)) ≫ _ = _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (fun z => overlapToLeftRing_algebraMap a b z))

def chartMapLeft (a b : R) : LeftChart a ⟶ Spec (.of (CrossingQuotient R (a * b))) :=
  Spec.map (CommRingCat.ofHom (toLeft a b).toRingHom)

def chartMapRight (a b : R) : RightChart b ⟶ Spec (.of (CrossingQuotient R (a * b))) :=
  Spec.map (CommRingCat.ofHom (toRight a b).toRingHom)

lemma chart_maps_agree (a b : R) :
    leftOverlapMap a ≫ chartMapLeft a b = rightOverlapMap a b ≫ chartMapRight a b := by
  rw [rightOverlapMap_eq]
  dsimp only [leftOverlapMap, chartMapLeft, chartMapRight]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom (charts_agree_on_overlap a b))

def Model (a b : R) : Scheme.{u} := pushout (leftOverlapMap a) (rightOverlapMap a b)

def ιLeft (a b : R) : LeftChart a ⟶ Model a b :=
  pushout.inl (leftOverlapMap a) (rightOverlapMap a b)

def ιRight (a b : R) : RightChart b ⟶ Model a b :=
  pushout.inr (leftOverlapMap a) (rightOverlapMap a b)

instance ιLeft_isOpenImmersion (a b : R) : IsOpenImmersion (ιLeft a b) := by
  exact inferInstanceAs (IsOpenImmersion
    (colimit.ι (span (leftOverlapMap a) (rightOverlapMap a b)) WalkingSpan.left))

instance ιRight_isOpenImmersion (a b : R) : IsOpenImmersion (ιRight a b) := by
  exact inferInstanceAs (IsOpenImmersion
    (colimit.ι (span (leftOverlapMap a) (rightOverlapMap a b)) WalkingSpan.right))

def toNode (a b : R) : Model a b ⟶ Spec (.of (CrossingQuotient R (a * b))) :=
  pushout.desc (chartMapLeft a b) (chartMapRight a b) (chart_maps_agree a b)

@[reassoc (attr := simp)] lemma ιLeft_toNode (a b : R) :
    ιLeft a b ≫ toNode a b = chartMapLeft a b := pushout.inl_desc _ _ _

@[reassoc (attr := simp)] lemma ιRight_toNode (a b : R) :
    ιRight a b ≫ toNode a b = chartMapRight a b := pushout.inr_desc _ _ _

lemma ι_jointly_surjective (a b : R) (x : Model a b) :
    (∃ y, ιLeft a b y = x) ∨ ∃ y, ιRight a b y = x := by
  obtain ⟨j, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (span (leftOverlapMap a) (rightOverlapMap a b)) x
  rcases j with (_ | (_ | _))
  · left
    refine ⟨leftOverlapMap a y, ?_⟩
    change (leftOverlapMap a ≫ ιLeft a b) y = x
    rw [show leftOverlapMap a ≫ ιLeft a b =
      colimit.ι (span (leftOverlapMap a) (rightOverlapMap a b)) WalkingSpan.zero from
        (by simpa only [ιLeft, Model, pushout.inl, span_map_fst, span_zero, span_left] using
          colimit.w (span (leftOverlapMap a) (rightOverlapMap a b)) WalkingSpan.Hom.fst)]
    exact hy
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

lemma overlap_isPullback (a b : R) :
    IsPullback (rightOverlapMap a b) (leftOverlapMap a) (ιRight a b) (ιLeft a b) := by
  apply IsOpenImmersion.isPullback
  · exact pushout.condition
  · ext x
    change ιLeft a b x ∈ Set.range (ιRight a b) ↔ x ∈ Set.range (leftOverlapMap a)
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨k, fkL, fkR, z, hzL, _⟩ :=
        (Scheme.IsLocallyDirected.ι_eq_ι_iff
          (span (leftOverlapMap a) (rightOverlapMap a b))).mp hy.symm
      rcases k with (_ | (_ | _))
      · refine ⟨z, ?_⟩
        have hfk : fkL = WalkingSpan.Hom.fst := Subsingleton.elim _ _
        subst fkL
        convert! hzL
      · change WidePushoutShape.Hom (some WalkingPair.left) (some WalkingPair.right) at fkR
        cases fkR
      · change WidePushoutShape.Hom (some WalkingPair.right) (some WalkingPair.left) at fkL
        cases fkL
    · rintro ⟨z, rfl⟩
      refine ⟨rightOverlapMap a b z, ?_⟩
      exact congrArg (fun h : Overlap a ⟶ Model a b => h z) pushout.condition.symm

end PhilipponNodeFactorGluing


set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MvPolynomial MvPolynomial.CrossingQuotient
open AlgebraicGeometry CategoryTheory
namespace PhilipponCrossingPointHom
variable {R : Type u} [CommRing R]
variable {A : Type*} [CommRing A]


lemma mk_C_eq_algebraMap (s : R) (r : R) : mk s (C r) = algebraMap R _ r :=
  (mk s).commutes r

theorem eval₂Hom_rel (s : R) (f : R →+* A) (a b : A) (h : a * b = f s) :
    eval₂Hom f ![a, b] (X 0 * X 1 - C s : MvPolynomial (Fin 2) R) = 0 := by
  rw [map_sub, map_mul, eval₂Hom_X', eval₂Hom_X', eval₂Hom_C]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [h, sub_self]

noncomputable def pointHom (s : R) (f : R →+* A) (a b : A) (h : a * b = f s) :
    CrossingQuotient R s →+* A :=
  Ideal.Quotient.lift (Ideal.span {(X 0 * X 1 - C s : MvPolynomial (Fin 2) R)}) (eval₂Hom f ![a, b])
    (fun p hp => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hp
      rw [map_mul, eval₂Hom_rel s f a b h, mul_zero])

theorem pointHom_mk (s : R) (f : R →+* A) (a b : A) (h : a * b = f s)
    (p : MvPolynomial (Fin 2) R) :
    pointHom s f a b h (mk s p) = eval₂Hom f ![a, b] p := rfl

theorem pointHom_algebraMap (s : R) (f : R →+* A) (a b : A) (h : a * b = f s) (w : R) :
    pointHom s f a b h (algebraMap R _ w) = f w := by
  rw [← mk_C_eq_algebraMap, pointHom_mk, eval₂Hom_C]

theorem pointHom_U (s : R) (f : R →+* A) (a b : A) (h : a * b = f s) :
    pointHom s f a b h (U s) = a := by
  change pointHom s f a b h (mk s (X 0)) = a
  rw [pointHom_mk, eval₂Hom_X']
  rfl

theorem pointHom_V (s : R) (f : R →+* A) (a b : A) (h : a * b = f s) :
    pointHom s f a b h (V s) = b := by
  change pointHom s f a b h (mk s (X 1)) = b
  rw [pointHom_mk, eval₂Hom_X']
  rfl

theorem ringHom_ext {s : R} {f g : CrossingQuotient R s →+* A}
    (hR : ∀ w : R, f (algebraMap R _ w) = g (algebraMap R _ w))
    (hU : f (U s) = g (U s)) (hV : f (V s) = g (V s)) : f = g := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro w
    change f (mk s (C w)) = g (mk s (C w))
    rw [mk_C_eq_algebraMap]
    exact hR w
  · intro j
    fin_cases j
    · exact hU
    · exact hV


lemma specMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom (g.comp f)) =
      Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]


end PhilipponCrossingPointHom

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient
namespace PhilipponNodeFactorSurjective
open PhilipponNodeFactorCharts PhilipponNodeFactorGluing PhilipponCrossingPointHom
variable {R : Type u} [CommRing R]

lemma fieldPoint_lift (a b : R) {K : Type u} [Field K]
    (ψ : CrossingQuotient R (a * b) →+* K) :
    (∃ φ : CrossingQuotient R a →+* K, φ.comp (toLeft a b).toRingHom = ψ) ∨
    ∃ φ : CrossingQuotient R b →+* K, φ.comp (toRight a b).toRingHom = ψ := by
  let ρ := ψ.comp (algebraMap R (CrossingQuotient R (a * b)))
  have hρ (r : R) : ρ r = ψ (algebraMap R _ r) := rfl
  have hab : ψ (U (a * b)) * ψ (V (a * b)) = ρ a * ρ b := by
    calc ψ (U (a * b)) * ψ (V (a * b))
        = ψ (algebraMap R _ (a * b)) := by rw [← map_mul, U_mul_V]
      _ = ρ (a * b) := rfl
      _ = ρ a * ρ b := map_mul ρ a b
  by_cases hu : ψ (U (a * b)) = 0
  · by_cases hb : ρ b = 0
    · right
      have hr : 0 * ψ (V (a * b)) = ρ b := by rw [zero_mul, hb]
      refine ⟨pointHom b ρ 0 (ψ (V (a * b))) hr, ?_⟩
      apply PhilipponCrossingPointHom.ringHom_ext
      · intro r
        change pointHom b ρ _ _ hr (toRight a b (algebraMap R _ r)) = _
        rw [AlgHom.commutes, pointHom_algebraMap, hρ]
      · change pointHom b ρ _ _ hr (toRight a b (U (a * b))) = _
        rw [toRight_U, map_mul, pointHom_U, mul_zero, hu]
      · change pointHom b ρ _ _ hr (toRight a b (V (a * b))) = _
        rw [toRight_V, pointHom_V]
    · left
      have ha : ρ a = 0 := by
        rw [hu, zero_mul] at hab
        exact (mul_eq_zero.mp hab.symm).resolve_right hb
      have hr : ψ (U (a * b)) * (ψ (V (a * b)) / ρ b) = ρ a := by rw [hu, ha, zero_mul]
      refine ⟨pointHom a ρ (ψ (U (a * b))) (ψ (V (a * b)) / ρ b) hr, ?_⟩
      apply PhilipponCrossingPointHom.ringHom_ext
      · intro r
        change pointHom a ρ _ _ hr (toLeft a b (algebraMap R _ r)) = _
        rw [AlgHom.commutes, pointHom_algebraMap, hρ]
      · change pointHom a ρ _ _ hr (toLeft a b (U (a * b))) = _
        rw [toLeft_U, pointHom_U]
      · change pointHom a ρ _ _ hr (toLeft a b (V (a * b))) = _
        rw [toLeft_V, map_mul, pointHom_algebraMap, pointHom_V]
        field_simp
  · left
    have hr : ψ (U (a * b)) * (ρ a / ψ (U (a * b))) = ρ a := by field_simp
    refine ⟨pointHom a ρ (ψ (U (a * b))) (ρ a / ψ (U (a * b))) hr, ?_⟩
    apply PhilipponCrossingPointHom.ringHom_ext
    · intro r
      change pointHom a ρ _ _ hr (toLeft a b (algebraMap R _ r)) = _
      rw [AlgHom.commutes, pointHom_algebraMap, hρ]
    · change pointHom a ρ _ _ hr (toLeft a b (U (a * b))) = _
      rw [toLeft_U, pointHom_U]
    · change pointHom a ρ _ _ hr (toLeft a b (V (a * b))) = _
      rw [toLeft_V, map_mul, pointHom_algebraMap, pointHom_V]
      calc ρ b * (ρ a / ψ (U (a * b))) = (ρ a * ρ b) / ψ (U (a * b)) := by ring
        _ = ψ (V (a * b)) := (div_eq_iff hu).mpr (by
          rw [mul_comm (ψ (V (a * b))) (ψ (U (a * b))), hab])

instance toNode_surjective (a b : R) : Surjective (toNode a b) := by
  constructor
  intro x
  let N := Spec (.of (CrossingQuotient R (a * b)))
  let g := N.fromSpecResidueField x
  let ψ := (Spec.preimage g).hom
  have hψ : Spec.map (CommRingCat.ofHom ψ) = g := Spec.map_preimage g
  rcases fieldPoint_lift a b ψ with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · have h : Spec.map (CommRingCat.ofHom φ) ≫ ιLeft a b ≫ toNode a b = g := by
      rw [ιLeft_toNode, chartMapLeft, ← specMap_comp, hφ, hψ]
    let p : PrimeSpectrum (N.residueField x) := default
    refine ⟨(Spec.map (CommRingCat.ofHom φ) ≫ ιLeft a b) p, ?_⟩
    change (Spec.map (CommRingCat.ofHom φ) ≫ ιLeft a b ≫ toNode a b) p = x
    rw [h]
    exact N.fromSpecResidueField_apply x p
  · have h : Spec.map (CommRingCat.ofHom φ) ≫ ιRight a b ≫ toNode a b = g := by
      rw [ιRight_toNode, chartMapRight, ← specMap_comp, hφ, hψ]
    let p : PrimeSpectrum (N.residueField x) := default
    refine ⟨(Spec.map (CommRingCat.ofHom φ) ≫ ιRight a b) p, ?_⟩
    change (Spec.map (CommRingCat.ofHom φ) ≫ ιRight a b ≫ toNode a b) p = x
    rw [h]
    exact N.fromSpecResidueField_apply x p
end PhilipponNodeFactorSurjective


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PhilipponProjectiveLineCharts
variable (R : Type u) [CommRing R] (i : Fin 2)

abbrev grading := MvPolynomial.homogeneousSubmodule (Fin 2) R
abbrev chartRing := Away (grading R) (MvPolynomial.X i)

noncomputable def specialize :
    MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 1) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun j => if j = i then 1 else MvPolynomial.X (0 : Fin 1))

lemma specialize_X_self : specialize R i (MvPolynomial.X i) = 1 := by
  simp [specialize]

lemma specialize_unit : IsUnit (specialize R i (MvPolynomial.X i)) :=
  isUnit_iff_exists_inv.mpr ⟨1, by rw [specialize_X_self]; simp⟩

noncomputable def fromAway : chartRing R i →+* MvPolynomial (Fin 1) R :=
  (Localization.awayLift (specialize R i) (MvPolynomial.X i)
    (specialize_unit R i)).comp
    (algebraMap (chartRing R i) (Localization.Away (MvPolynomial.X i :
      MvPolynomial (Fin 2) R)))

lemma fromAway_coeff (r : R) :
    fromAway R i (algebraMap R (chartRing R i) r) = MvPolynomial.C r := by
  change Localization.awayLift (specialize R i) _ (specialize_unit R i)
    ((algebraMap R (chartRing R i) r).val) = _
  rw [ProjSpace.val_algebraMap]
  simp only [Localization.awayLift, IsLocalization.Away.lift_eq]
  simp [specialize]

lemma fromAway_ratio (j : Fin 2) :
    fromAway R i (ProjSpace.ratio R 1 i j) = specialize R i (MvPolynomial.X j) := by
  change Localization.awayLift (specialize R i) _ (specialize_unit R i) (ProjSpace.ratio R 1 i j).val = _
  rw [ProjSpace.ratio, Away.val_mk]
  simpa only [one_pow, mul_one] using
    Localization.awayLift_mk (specialize R i) (MvPolynomial.X i)
      (MvPolynomial.X j) 1 (by rw [specialize_X_self]; simp) 1

noncomputable def fromAwayAlg : chartRing R i →ₐ[R] MvPolynomial (Fin 1) R where
  __ := fromAway R i
  commutes' := fromAway_coeff R i

lemma fromAwayAlg_apply (x : chartRing R i) : fromAwayAlg R i x = fromAway R i x := rfl

noncomputable def toAwayAlg : MvPolynomial (Fin 1) R →ₐ[R] chartRing R i :=
  MvPolynomial.aeval (fun _ : Fin 1 => ProjSpace.ratio R 1 i i.rev)

lemma toAwayAlg_X (j : Fin 1) : toAwayAlg R i (MvPolynomial.X j) = ProjSpace.ratio R 1 i i.rev :=
  MvPolynomial.aeval_X _ _

lemma from_to : (fromAwayAlg R i).comp (toAwayAlg R i) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, toAwayAlg_X, fromAwayAlg_apply, fromAway_ratio, AlgHom.id_apply]
  fin_cases i <;> fin_cases j <;> simp [specialize]

lemma to_from : (toAwayAlg R i).comp (fromAwayAlg R i) = AlgHom.id R _ := by
  apply AlgHom.ext_of_adjoin_eq_top (ProjSpace.adjoin_range_ratio R 1 i)
  rintro _ ⟨j, rfl⟩
  change toAwayAlg R i (fromAway R i (ProjSpace.ratio R 1 i j)) = ProjSpace.ratio R 1 i j
  rw [fromAway_ratio]
  fin_cases i <;> fin_cases j <;>
    simp [specialize, toAwayAlg, ProjSpace.ratio_self]

noncomputable def equiv : chartRing R i ≃ₐ[R] MvPolynomial (Fin 1) R :=
  AlgEquiv.ofAlgHom (fromAwayAlg R i) (toAwayAlg R i) (from_to R i) (to_from R i)

/-- The standard affine-space chart in projective space. -/
noncomputable def embedding : Spec (.of (MvPolynomial (Fin 1) R)) ⟶ Proj (grading R) :=
  Spec.map (CommRingCat.ofHom (equiv R i).toRingEquiv.toRingHom) ≫
    Proj.awayι (grading R) (MvPolynomial.X i)
      (ProjSpace.X_mem_one R 1 i) one_pos

instance embedding_isOpenImmersion : IsOpenImmersion (embedding R i) := by
  haveI : IsIso (CommRingCat.ofHom (equiv R i).toRingEquiv.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (equiv R i).bijective
  unfold embedding
  infer_instance

lemma embedding_over : embedding R i ≫ ProjSpace.π R 1 =
    Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin 1) R)) := by
  rw [embedding, Category.assoc, ProjSpace.awayι_comp_π, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (equiv R i).commutes r

end PhilipponProjectiveLineCharts


set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 3000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponProjectiveLineTransition
open PhilipponProjectiveLineCharts
variable {R : Type u} [CommRing R]

lemma chart_ring_ext {A : Type*} [CommRing A] (i : Fin 2)
    {f g : chartRing R i →+* A}
    (hR : ∀ r, f (algebraMap R _ r) = g (algebraMap R _ r))
    (ht : f (ProjSpace.ratio R 1 i i.rev) = g (ProjSpace.ratio R 1 i i.rev)) : f = g := by
  have hpre : f.comp (equiv R i).symm.toRingHom = g.comp (equiv R i).symm.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change f ((equiv R i).symm (algebraMap R _ r)) =
        g ((equiv R i).symm (algebraMap R _ r))
      rw [(equiv R i).symm.commutes]
      exact hR r
    · intro j
      change f (toAwayAlg R i (MvPolynomial.X j)) = g (toAwayAlg R i (MvPolynomial.X j))
      rw [toAwayAlg_X]
      exact ht
  apply RingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := (equiv R i).symm.surjective x
  exact RingHom.congr_fun hpre p

abbrev productRing (R : Type u) [CommRing R] :=
  Away (grading R) (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1)

def restrict₀ (R : Type u) [CommRing R] : chartRing R 0 →+* productRing R :=
  awayMap (grading R) (ProjSpace.X_mem_one R 1 1) rfl

def restrict₁ (R : Type u) [CommRing R] : chartRing R 1 →+* productRing R :=
  awayMap (grading R) (ProjSpace.X_mem_one R 1 0) (mul_comm _ _)

def restrict (i : Fin 2) : chartRing R i →+* productRing R :=
  Fin.cases (restrict₀ R) (Fin.cases (restrict₁ R) (fun j => Fin.elim0 j)) i

variable {A : Type u} [CommRing A] [Algebra R A]

def evalPair (z : A) : MvPolynomial (Fin 2) R →+* A :=
  MvPolynomial.eval₂Hom (algebraMap R A) ![1, z]

@[simp] lemma evalPair_C (z : A) (r : R) : evalPair (R := R) z (MvPolynomial.C r) = algebraMap R A r :=
  MvPolynomial.eval₂Hom_C _ _ _
@[simp] lemma evalPair_X₀ (z : A) : evalPair (R := R) z (MvPolynomial.X 0) = 1 := by simp [evalPair]
@[simp] lemma evalPair_X₁ (z : A) : evalPair (R := R) z (MvPolynomial.X 1) = z := by simp [evalPair]

lemma evalPair_unit (z w : A) (h : z * w = 1) :
    IsUnit (evalPair (R := R) z (MvPolynomial.X 0 * MvPolynomial.X 1)) := by
  apply isUnit_iff_exists_inv.mpr
  exact ⟨w, by simpa using h⟩

def productEval (z w : A) (h : z * w = 1) : productRing R →+* A :=
  (Localization.awayLift (evalPair (R := R) z) (MvPolynomial.X 0 * MvPolynomial.X 1)
    (evalPair_unit (R := R) z w h)).comp
    (algebraMap (productRing R) (Localization.Away (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X 1)))

def chartEval (i : Fin 2) (z : A) : chartRing R i →+* A :=
  (MvPolynomial.aeval (fun _ : Fin 1 => z)).toRingHom.comp (fromAway R i)

lemma chartEval_coeff (i : Fin 2) (z : A) (r : R) :
    chartEval (R := R) i z (algebraMap R _ r) = algebraMap R A r := by
  change MvPolynomial.aeval (fun _ : Fin 1 => z) (fromAway R i (algebraMap R _ r)) = _
  rw [fromAway_coeff, MvPolynomial.aeval_C]

lemma chartEval_ratio (i : Fin 2) (z : A) :
    chartEval (R := R) i z (ProjSpace.ratio R 1 i i.rev) = z := by
  change MvPolynomial.aeval (fun _ : Fin 1 => z) (fromAway R i (ProjSpace.ratio R 1 i i.rev)) = _
  rw [fromAway_ratio]
  fin_cases i <;> simp [specialize]

lemma productEval_restrict_coeff (z w : A) (h : z * w = 1) (i : Fin 2) (r : R) :
    productEval (R := R) z w h (restrict i (algebraMap R (chartRing R i) r)) = algebraMap R A r := by
  fin_cases i
  · change productEval (R := R) z w h (awayMap (grading R) (ProjSpace.X_mem_one R 1 1) rfl
      (fromZeroRingHom (grading R) _ ((ProjSpace.grad0Equiv R 1) r))) = _
    rw [awayMap_fromZeroRingHom]
    change Localization.awayLift (evalPair (R := R) z) _ (evalPair_unit (R := R) z w h)
      (algebraMap (MvPolynomial (Fin 2) R) _ (MvPolynomial.C r)) = _
    rw [IsLocalization.Away.lift_eq, evalPair_C]
  · change productEval (R := R) z w h (awayMap (grading R) (ProjSpace.X_mem_one R 1 0) (mul_comm _ _)
      (fromZeroRingHom (grading R) _ ((ProjSpace.grad0Equiv R 1) r))) = _
    rw [awayMap_fromZeroRingHom]
    change Localization.awayLift (evalPair (R := R) z) _ (evalPair_unit (R := R) z w h)
      (algebraMap (MvPolynomial (Fin 2) R) _ (MvPolynomial.C r)) = _
    rw [IsLocalization.Away.lift_eq, evalPair_C]

lemma productEval_restrict₀_ratio (z w : A) (h : z * w = 1) :
    productEval (R := R) z w h (restrict₀ R (ProjSpace.ratio R 1 0 1)) = z := by
  change Localization.awayLift (evalPair (R := R) z) _ (evalPair_unit (R := R) z w h)
    (awayMap (grading R) (ProjSpace.X_mem_one R 1 1) rfl (ProjSpace.ratio R 1 0 1)).val = _
  rw [ProjSpace.ratio, awayMap_mk, Away.val_mk]
  rw [Localization.awayLift_mk (evalPair (R := R) z) _ _ w (by simpa using h) 1]
  simp [evalPair]
  linear_combination z * h

lemma productEval_restrict₁_ratio (z w : A) (h : z * w = 1) :
    productEval (R := R) z w h (restrict₁ R (ProjSpace.ratio R 1 1 0)) = w := by
  change Localization.awayLift (evalPair (R := R) z) _ (evalPair_unit (R := R) z w h)
    (awayMap (grading R) (ProjSpace.X_mem_one R 1 0) (mul_comm _ _) (ProjSpace.ratio R 1 1 0)).val = _
  rw [ProjSpace.ratio, awayMap_mk, Away.val_mk]
  rw [Localization.awayLift_mk (evalPair (R := R) z) _ _ w (by simpa using h) 1]
  simp [evalPair]

lemma productEval_comp_restrict₀ (z w : A) (h : z * w = 1) :
    (productEval (R := R) z w h).comp (restrict₀ R) = chartEval (R := R) 0 z := by
  apply chart_ring_ext (R := R) 0
  · intro r
    exact (productEval_restrict_coeff (R := R) z w h 0 r).trans (chartEval_coeff (R := R) 0 z r).symm
  · exact (productEval_restrict₀_ratio (R := R) z w h).trans (chartEval_ratio (R := R) 0 z).symm

lemma productEval_comp_restrict₁ (z w : A) (h : z * w = 1) :
    (productEval (R := R) z w h).comp (restrict₁ R) = chartEval (R := R) 1 w := by
  apply chart_ring_ext (R := R) 1
  · intro r
    exact (productEval_restrict_coeff (R := R) z w h 1 r).trans (chartEval_coeff (R := R) 1 w r).symm
  · exact (productEval_restrict₁_ratio (R := R) z w h).trans (chartEval_ratio (R := R) 1 w).symm

def point (i : Fin 2) (z : A) : Spec (.of A) ⟶ Proj (grading R) :=
  Spec.map (CommRingCat.ofHom (chartEval (R := R) i z)) ≫
    Proj.awayι (grading R) (MvPolynomial.X i) (ProjSpace.X_mem_one R 1 i) one_pos

lemma point_zero_eq_point_one (z w : A) (h : z * w = 1) : point (R := R) 0 z = point (R := R) 1 w := by
  dsimp only [point]
  rw [← productEval_comp_restrict₀ (R := R) z w h, ← productEval_comp_restrict₁ (R := R) z w h,
    CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
    Category.assoc, Category.assoc]
  congr 1
  change Spec.map (CommRingCat.ofHom
      (awayMap (grading R) (ProjSpace.X_mem_one R 1 1) rfl)) ≫ _ =
    Spec.map (CommRingCat.ofHom
      (awayMap (grading R) (ProjSpace.X_mem_one R 1 0) (mul_comm _ _))) ≫ _
  rw [Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]

end PhilipponProjectiveLineTransition

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 3000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponProjectiveLinePoints
open PhilipponProjectiveLineCharts PhilipponProjectiveLineTransition
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]

def evalChart (ρ : R →+* A) (i : Fin 2) (z : A) : chartRing R i →+* A :=
  letI := ρ.toAlgebra
  chartEval i z

def point (ρ : R →+* A) (i : Fin 2) (z : A) : Spec (.of A) ⟶ Proj (grading R) :=
  Spec.map (CommRingCat.ofHom (evalChart ρ i z)) ≫
    Proj.awayι (grading R) (MvPolynomial.X i) (ProjSpace.X_mem_one R 1 i) one_pos

lemma evalChart_coeff (ρ : R →+* A) (i : Fin 2) (z : A) (r : R) :
    evalChart ρ i z (algebraMap R _ r) = ρ r := by
  letI := ρ.toAlgebra
  exact chartEval_coeff i z r

lemma evalChart_ratio (ρ : R →+* A) (i : Fin 2) (z : A) :
    evalChart ρ i z (ProjSpace.ratio R 1 i i.rev) = z := by
  letI := ρ.toAlgebra
  exact chartEval_ratio i z

lemma point_over (ρ : R →+* A) (i : Fin 2) (z : A) :
    point ρ i z ≫ ProjSpace.π R 1 = Spec.map (CommRingCat.ofHom ρ) := by
  rw [point, Category.assoc, ProjSpace.awayι_comp_π, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun r => evalChart_coeff ρ i z r)

lemma point_naturality (ρ : R →+* A) (σ : R →+* B) (f : A →+* B)
    (hf : f.comp ρ = σ) (i : Fin 2) (z : A) :
    Spec.map (CommRingCat.ofHom f) ≫ point ρ i z = point σ i (f z) := by
  have h : f.comp (evalChart ρ i z) = evalChart σ i (f z) := by
    apply chart_ring_ext (R := R) i
    · intro r
      change f (evalChart ρ i z (algebraMap R _ r)) = _
      rw [evalChart_coeff, evalChart_coeff]
      exact RingHom.congr_fun hf r
    · change f (evalChart ρ i z (ProjSpace.ratio R 1 i i.rev)) = _
      rw [evalChart_ratio, evalChart_ratio]
  rw [point, point, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

lemma point_zero_eq_point_one (ρ : R →+* A) (z w : A) (h : z * w = 1) :
    point ρ 0 z = point ρ 1 w := by
  letI := ρ.toAlgebra
  exact PhilipponProjectiveLineTransition.point_zero_eq_point_one z w h

lemma point_preimage_basicOpen (ρ : R →+* A) (i j : Fin 2) (z : A) :
    point ρ i z ⁻¹ᵁ Proj.basicOpen (grading R) (MvPolynomial.X j) =
      PrimeSpectrum.basicOpen (if j = i then 1 else z) := by
  rw [point, Scheme.Hom.comp_preimage, Proj.awayι_preimage_basicOpen
    (grading R) (ProjSpace.X_mem_one R 1 i) one_pos (ProjSpace.X_mem_one R 1 j) one_pos]
  have he : Away.isLocalizationElem (ProjSpace.X_mem_one R 1 i) (ProjSpace.X_mem_one R 1 j) =
      ProjSpace.ratio R 1 i j := by
    apply HomogeneousLocalization.val_injective
    simp [Away.isLocalizationElem, ProjSpace.ratio, Away.val_mk]
  rw [he]
  ext x
  change evalChart ρ i z (ProjSpace.ratio R 1 i j) ∉ x.asIdeal ↔ _
  have hvalue : evalChart ρ i z (ProjSpace.ratio R 1 i j) = if j = i then 1 else z := by
    fin_cases i <;> fin_cases j
    · simp [ProjSpace.ratio_self]
    · exact evalChart_ratio ρ 0 z
    · exact evalChart_ratio ρ 1 z
    · simp [ProjSpace.ratio_self]
  rw [hvalue]
  rfl

end PhilipponProjectiveLinePoints

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponNodeFactorProjectiveMap
open PhilipponNodeFactorCharts PhilipponNodeFactorGluing
open PhilipponProjectiveLineCharts PhilipponProjectiveLinePoints
variable {R : Type u} [CommRing R]

abbrev PLine (a b : R) := Proj (grading (CrossingQuotient R (a * b)))

def leftToProj (a b : R) : LeftChart a ⟶ PLine a b :=
  point (toLeft a b).toRingHom 0 (V a)

def rightToProj (a b : R) : RightChart b ⟶ PLine a b :=
  point (toRight a b).toRingHom 1 (U b)

lemma overlap_toProj (a b : R) :
    leftOverlapMap a ≫ leftToProj a b = rightOverlapMap a b ≫ rightToProj a b := by
  let ρ : CrossingQuotient R (a * b) →+* LeftOverlap a :=
    (algebraMap (CrossingQuotient R a) (LeftOverlap a)).comp (toLeft a b).toRingHom
  have hl : (algebraMap (CrossingQuotient R a) (LeftOverlap a)).comp
      (toLeft a b).toRingHom = ρ := rfl
  have hr : (rightToLeftOverlap a b).toRingHom.comp (toRight a b).toRingHom = ρ :=
    (congrArg AlgHom.toRingHom (charts_agree_on_overlap a b)).symm
  rw [rightOverlapMap_eq]
  change Spec.map (CommRingCat.ofHom (algebraMap (CrossingQuotient R a) (LeftOverlap a))) ≫
      point (toLeft a b).toRingHom 0 (V a) =
    Spec.map (CommRingCat.ofHom (rightToLeftOverlap a b).toRingHom) ≫
      point (toRight a b).toRingHom 1 (U b)
  rw [point_naturality _ ρ _ hl, point_naturality _ ρ _ hr]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rightToLeftOverlap, lift_U]
  exact point_zero_eq_point_one ρ _ _ (IsLocalization.Away.mul_invSelf (V a))

def toProj (a b : R) : Model a b ⟶ PLine a b :=
  pushout.desc (leftToProj a b) (rightToProj a b) (overlap_toProj a b)

@[reassoc (attr := simp)] lemma left_toProj (a b : R) :
    ιLeft a b ≫ toProj a b = leftToProj a b := pushout.inl_desc _ _ _
@[reassoc (attr := simp)] lemma right_toProj (a b : R) :
    ιRight a b ≫ toProj a b = rightToProj a b := pushout.inr_desc _ _ _

lemma toProj_over (a b : R) :
    toProj a b ≫ ProjSpace.π (CrossingQuotient R (a * b)) 1 = toNode a b := by
  apply pushout.hom_ext
  · change ιLeft a b ≫ _ = ιLeft a b ≫ _
    rw [left_toProj_assoc, ιLeft_toNode]
    exact point_over (toLeft a b).toRingHom 0 (V a)
  · change ιRight a b ≫ _ = ιRight a b ≫ _
    rw [right_toProj_assoc, ιRight_toNode]
    exact point_over (toRight a b).toRingHom 1 (U b)

end PhilipponNodeFactorProjectiveMap

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponNodeFactorProjectiveEmbedding
open PhilipponNodeFactorCharts PhilipponNodeFactorGluing PhilipponNodeFactorProjectiveMap
open PhilipponProjectiveLineCharts PhilipponProjectiveLinePoints
variable {R : Type u} [CommRing R]

lemma crossing_surj_of_generators {T : Type u} [CommRing T] (a : R)
    (φ : T →+* CrossingQuotient R a)
    (hR : ∀ r, algebraMap R _ r ∈ φ.range) (hU : U a ∈ φ.range) (hV : V a ∈ φ.range) :
    Function.Surjective φ := by
  intro c
  change c ∈ φ.range
  obtain ⟨p, rfl⟩ := mk_surjective a c
  induction p using MvPolynomial.induction_on with
  | C r => exact hR r
  | add p q hp hq =>
    rw [map_add]
    exact φ.range.add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul]
    apply φ.range.mul_mem hp
    fin_cases i
    · exact hU
    · exact hV

lemma left_evalChart_surj (a b : R) :
    Function.Surjective (evalChart (toLeft a b).toRingHom 0 (V a)) := by
  apply crossing_surj_of_generators a
  · intro r
    refine ⟨algebraMap (CrossingQuotient R (a * b)) _ (algebraMap R _ r), ?_⟩
    rw [evalChart_coeff]
    exact (toLeft a b).commutes r
  · exact ⟨algebraMap (CrossingQuotient R (a * b)) _ (U (a * b)), by
      rw [evalChart_coeff]; exact toLeft_U a b⟩
  · exact ⟨ProjSpace.ratio (CrossingQuotient R (a * b)) 1 0 1,
      evalChart_ratio (toLeft a b).toRingHom 0 (V a)⟩

lemma right_evalChart_surj (a b : R) :
    Function.Surjective (evalChart (toRight a b).toRingHom 1 (U b)) := by
  apply crossing_surj_of_generators b
  · intro r
    refine ⟨algebraMap (CrossingQuotient R (a * b)) _ (algebraMap R _ r), ?_⟩
    rw [evalChart_coeff]
    exact (toRight a b).commutes r
  · exact ⟨ProjSpace.ratio (CrossingQuotient R (a * b)) 1 1 0,
      evalChart_ratio (toRight a b).toRingHom 1 (U b)⟩
  · exact ⟨algebraMap (CrossingQuotient R (a * b)) _ (V (a * b)), by
      rw [evalChart_coeff]; exact toRight_V a b⟩

lemma leftOverlap_opensRange (a : R) :
    (leftOverlapMap a).opensRange = PrimeSpectrum.basicOpen (V a) := by
  exact Scheme.Hom.opensRange_localizationAway (R := .of (CrossingQuotient R a)) (V a)

lemma rightOverlap_opensRange (a b : R) :
    (rightOverlapMap a b).opensRange = PrimeSpectrum.basicOpen (U b) := by
  change ((overlapIso a b).hom ≫ Spec.map (CommRingCat.ofHom
    (algebraMap (CrossingQuotient R b) (RightOverlap b)))).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact Scheme.Hom.opensRange_localizationAway (R := .of (CrossingQuotient R b)) (U b)

lemma left_preimage_chart (a b : R) :
    toProj a b ⁻¹ᵁ Proj.basicOpen (grading (CrossingQuotient R (a * b))) (X (0 : Fin 2)) =
      (ιLeft a b).opensRange := by
  ext x
  constructor
  · intro hx
    rcases ι_jointly_surjective a b x with h | ⟨y, rfl⟩
    · exact h
    · have hy : y ∈ PrimeSpectrum.basicOpen (U b) := by
        change y ∈ (ιRight a b ≫ toProj a b) ⁻¹ᵁ _ at hx
        rw [right_toProj] at hx
        change y ∈ point (toRight a b).toRingHom 1 (U b) ⁻¹ᵁ _ at hx
        rwa [point_preimage_basicOpen] at hx
      rw [← rightOverlap_opensRange a b] at hy
      obtain ⟨z, rfl⟩ := hy
      refine ⟨leftOverlapMap a z, ?_⟩
      exact congrArg (fun h : Overlap a ⟶ Model a b => h z) pushout.condition
  · rintro ⟨y, rfl⟩
    change y ∈ (ιLeft a b ≫ toProj a b) ⁻¹ᵁ _
    rw [left_toProj]
    change y ∈ point (toLeft a b).toRingHom 0 (V a) ⁻¹ᵁ _
    rw [point_preimage_basicOpen]
    simp
    trivial

lemma right_preimage_chart (a b : R) :
    toProj a b ⁻¹ᵁ Proj.basicOpen (grading (CrossingQuotient R (a * b))) (X (1 : Fin 2)) =
      (ιRight a b).opensRange := by
  ext x
  constructor
  · intro hx
    rcases ι_jointly_surjective a b x with ⟨y, rfl⟩ | h
    · have hy : y ∈ PrimeSpectrum.basicOpen (V a) := by
        change y ∈ (ιLeft a b ≫ toProj a b) ⁻¹ᵁ _ at hx
        rw [left_toProj] at hx
        change y ∈ point (toLeft a b).toRingHom 0 (V a) ⁻¹ᵁ _ at hx
        rwa [point_preimage_basicOpen] at hx
      rw [← leftOverlap_opensRange a] at hy
      obtain ⟨z, rfl⟩ := hy
      refine ⟨rightOverlapMap a b z, ?_⟩
      exact congrArg (fun h : Overlap a ⟶ Model a b => h z) pushout.condition.symm
    · exact h
  · rintro ⟨y, rfl⟩
    change y ∈ (ιRight a b ≫ toProj a b) ⁻¹ᵁ _
    rw [right_toProj]
    change y ∈ point (toRight a b).toRingHom 1 (U b) ⁻¹ᵁ _
    rw [point_preimage_basicOpen]
    simp
    trivial

lemma left_isPullback (a b : R) :
    IsPullback (Spec.map (CommRingCat.ofHom (evalChart (toLeft a b).toRingHom 0 (V a))))
      (ιLeft a b) (Proj.awayι (grading (CrossingQuotient R (a * b))) (X 0)
        (ProjSpace.X_mem_one _ 1 0) one_pos) (toProj a b) := by
  apply IsOpenImmersion.isPullback
  · exact left_toProj a b
  · rw [Proj.opensRange_awayι]
    exact left_preimage_chart a b

lemma right_isPullback (a b : R) :
    IsPullback (Spec.map (CommRingCat.ofHom (evalChart (toRight a b).toRingHom 1 (U b))))
      (ιRight a b) (Proj.awayι (grading (CrossingQuotient R (a * b))) (X 1)
        (ProjSpace.X_mem_one _ 1 1) one_pos) (toProj a b) := by
  apply IsOpenImmersion.isPullback
  · exact right_toProj a b
  · rw [Proj.opensRange_awayι]
    exact right_preimage_chart a b

instance toProj_isClosedImmersion (a b : R) : IsClosedImmersion (toProj a b) := by
  apply IsZariskiLocalAtTarget.of_openCover
    (P := @IsClosedImmersion) (ProjSpace.affineOpenCover (CrossingQuotient R (a * b)) 1).openCover
  intro i
  change Fin 2 at i
  fin_cases i
  · change IsClosedImmersion (pullback.snd (toProj a b)
      (Proj.awayι (grading (CrossingQuotient R (a * b))) (X 0)
        (ProjSpace.X_mem_one _ 1 0) one_pos))
    rw [← (left_isPullback a b).flip.isoPullback_inv_snd]
    haveI := IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (evalChart (toLeft a b).toRingHom 0 (V a))) (left_evalChart_surj a b)
    infer_instance
  · change IsClosedImmersion (pullback.snd (toProj a b)
      (Proj.awayι (grading (CrossingQuotient R (a * b))) (X 1)
        (ProjSpace.X_mem_one _ 1 1) one_pos))
    rw [← (right_isPullback a b).flip.isoPullback_inv_snd]
    haveI := IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (evalChart (toRight a b).toRingHom 1 (U b))) (right_evalChart_surj a b)
    infer_instance
instance toNode_isProper (a b : R) : IsProper (toNode a b) := by
  rw [← toProj_over a b]
  infer_instance

end PhilipponNodeFactorProjectiveEmbedding


theorem solution {R : Type u} [CommRing R] (a b : R) :
    ∃ (X : Scheme.{u}) (q : X ⟶ Spec (.of (CrossingQuotient R (a * b))))
      (i : Spec (.of (CrossingQuotient R a)) ⟶ X)
      (j : Spec (.of (CrossingQuotient R b)) ⟶ X)
      (α : CrossingQuotient R (a * b) →ₐ[R] CrossingQuotient R a)
      (β : CrossingQuotient R (a * b) →ₐ[R] CrossingQuotient R b)
      (θ : CrossingQuotient R b →ₐ[R] Localization.Away (V a)),
      IsProper q ∧ Surjective q ∧ IsOpenImmersion i ∧ IsOpenImmersion j ∧
      (∀ x : X, (∃ y, i y = x) ∨ ∃ y, j y = x) ∧
      α (U (a * b)) = U a ∧ α (V (a * b)) = algebraMap R _ b * V a ∧
      β (U (a * b)) = algebraMap R _ a * U b ∧ β (V (a * b)) = V b ∧
      θ (U b) = IsLocalization.Away.invSelf (V a) ∧
      θ (V b) = algebraMap R _ b *
        algebraMap (CrossingQuotient R a) (Localization.Away (V a)) (V a) ∧
      i ≫ q = Spec.map (CommRingCat.ofHom α.toRingHom) ∧
      j ≫ q = Spec.map (CommRingCat.ofHom β.toRingHom) ∧
      IsPullback (Spec.map (CommRingCat.ofHom θ.toRingHom))
        (Spec.map (CommRingCat.ofHom
          (algebraMap (CrossingQuotient R a) (Localization.Away (V a))))) j i ∧
      ∃ e : X ⟶ Proj (@MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) (CrossingQuotient R (a * b))
        (@CommRing.toCommSemiring (CrossingQuotient R (a * b)) inferInstance)),
        IsClosedImmersion e ∧ e ≫ ProjSpace.π (CrossingQuotient R (a * b)) 1 = q := by
  refine ⟨PhilipponNodeFactorGluing.Model a b, PhilipponNodeFactorGluing.toNode a b,
    PhilipponNodeFactorGluing.ιLeft a b, PhilipponNodeFactorGluing.ιRight a b,
    PhilipponNodeFactorCharts.toLeft a b, PhilipponNodeFactorCharts.toRight a b,
    PhilipponNodeFactorCharts.rightToLeftOverlap a b,
    inferInstance, inferInstance, inferInstance, inferInstance,
    PhilipponNodeFactorGluing.ι_jointly_surjective a b,
    PhilipponNodeFactorCharts.toLeft_U a b, PhilipponNodeFactorCharts.toLeft_V a b,
    PhilipponNodeFactorCharts.toRight_U a b, PhilipponNodeFactorCharts.toRight_V a b,
    lift_U _ _ _ _, lift_V _ _ _ _,
    PhilipponNodeFactorGluing.ιLeft_toNode a b, PhilipponNodeFactorGluing.ιRight_toNode a b,
    ?_, PhilipponNodeFactorProjectiveMap.toProj a b, inferInstance,
    PhilipponNodeFactorProjectiveMap.toProj_over a b⟩
  rw [← PhilipponNodeFactorGluing.rightOverlapMap_eq]
  exact PhilipponNodeFactorGluing.overlap_isPullback a b

