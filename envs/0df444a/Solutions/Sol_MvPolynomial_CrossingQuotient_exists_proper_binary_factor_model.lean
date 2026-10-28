-- Prove2me | solution 1 for MvPolynomial.CrossingQuotient.exists_proper_binary_factor_model
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-26T21:15:11.666995+00:00
-- url     : https://prove2.me/submissions/d5c4fa4d-672d-4334-b749-b0616a6f02b5

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
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient
open scoped TensorProduct
namespace PhilipponNodeFactorSeparated
open PhilipponNodeFactorCharts PhilipponNodeFactorGluing
variable {R : Type u} [CommRing R]

def toSpec (a b : R) : Model a b ⟶ Spec (.of R) :=
  toNode a b ≫ Spec.map (CommRingCat.ofHom (algebraMap R (CrossingQuotient R (a * b))))

@[reassoc (attr := simp)] lemma left_toSpec (a b : R) :
    ιLeft a b ≫ toSpec a b = Spec.map (CommRingCat.ofHom (algebraMap R (CrossingQuotient R a))) := by
  simp only [toSpec, ιLeft_toNode_assoc, chartMapLeft, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact (toLeft a b).comp_algebraMap

@[reassoc (attr := simp)] lemma right_toSpec (a b : R) :
    ιRight a b ≫ toSpec a b = Spec.map (CommRingCat.ofHom (algebraMap R (CrossingQuotient R b))) := by
  simp only [toSpec, ιRight_toNode_assoc, chartMapRight, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact (toRight a b).comp_algebraMap

set_option backward.isDefEq.respectTransparency false in
def openCover (a b : R) : (Model a b).OpenCover where
  I₀ := Bool
  X i := if i then RightChart b else LeftChart a
  f i := match i with | false => ιLeft a b | true => ιRight a b
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun i => ?_⟩
    · rcases ι_jointly_surjective a b x with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    · cases i <;> infer_instance

lemma isClosedImmersion_mapDesc {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    {X : Scheme.{u}} (i : Spec (.of A) ⟶ X) (j : Spec (.of B) ⟶ X)
    (q : X ⟶ Spec (.of R))
    (hi : i ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (hj : j ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (r₁ : A →ₐ[R] C) (r₂ : B →ₐ[R] C)
    (h : IsPullback (Spec.map (CommRingCat.ofHom r₁.toRingHom))
      (Spec.map (CommRingCat.ofHom r₂.toRingHom)) i j)
    (hφ : Function.Surjective
      (Algebra.TensorProduct.lift r₁ r₂ (fun _ _ => Commute.all _ _) : A ⊗[R] B →ₐ[R] C)) :
    IsClosedImmersion (pullback.mapDesc i j q) := by
  let φ : A ⊗[R] B →ₐ[R] C := Algebra.TensorProduct.lift r₁ r₂ (fun _ _ => Commute.all _ _)
  let f := CommRingCat.ofHom (R := A ⊗[R] B) (S := C) φ.toRingHom
  have hφ' : Function.Surjective f.hom := hφ
  have hcl : IsClosedImmersion (Spec.map f) := IsClosedImmersion.spec_of_surjective f hφ'
  have hleft : Spec.map f ≫ Spec.map (CommRingCat.ofHom (R := A) (S := A ⊗[R] B)
      Algebra.TensorProduct.includeLeftRingHom) = Spec.map (CommRingCat.ofHom r₁.toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact congrArg AlgHom.toRingHom (Algebra.TensorProduct.lift_comp_includeLeft r₁ r₂
      (fun _ _ => Commute.all _ _) : (φ.restrictScalars R).comp Algebra.TensorProduct.includeLeft = r₁)
  have hright : Spec.map f ≫ Spec.map (CommRingCat.ofHom (R := B) (S := A ⊗[R] B)
      (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)))) =
      Spec.map (CommRingCat.ofHom r₂.toRingHom) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact congrArg AlgHom.toRingHom (Algebra.TensorProduct.lift_comp_includeRight r₁ r₂
      (fun _ _ => Commute.all _ _) : φ.comp Algebra.TensorProduct.includeRight = r₂)
  let ε := pullback.congrHom hi hj
  have key : pullback.mapDesc i j q =
      h.isoPullback.inv ≫ Spec.map f ≫
        (pullbackSpecIso R A B).inv ≫ ε.inv := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.comp_id, Category.assoc, Category.assoc, Category.assoc,
        pullback.congrHom_inv, pullback.lift_fst, Category.comp_id, pullbackSpecIso_inv_fst,
        hleft, h.isoPullback_inv_fst]
    · rw [pullback.lift_snd, Category.comp_id, Category.assoc, Category.assoc, Category.assoc,
        pullback.congrHom_inv, pullback.lift_snd, Category.comp_id, pullbackSpecIso_inv_snd,
        hright, h.isoPullback_inv_snd]
  rw [key]
  infer_instance

lemma eq_mul_invSelf_pow {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (x : A) [IsLocalization.Away x B] (z : B) :
    ∃ (n : ℕ) (c : A), z = algebraMap A B c * IsLocalization.Away.invSelf (S := B) x ^ n := by
  obtain ⟨n, c, h⟩ := IsLocalization.Away.surj (S := B) x z
  refine ⟨n, c, ?_⟩
  rw [← h, mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]

lemma surjective_lift_left (a b : R) :
    Function.Surjective (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom R (CrossingQuotient R a) (LeftOverlap a)) (rightToLeftOverlap a b)
      (fun _ _ => Commute.all _ _) :
      CrossingQuotient R a ⊗[R] CrossingQuotient R b →ₐ[R] LeftOverlap a) := by
  intro z
  obtain ⟨n, c, rfl⟩ := eq_mul_invSelf_pow (V a) z
  refine ⟨c ⊗ₜ (U b ^ n), ?_⟩
  rw [Algebra.TensorProduct.lift_tmul, map_pow, rightToLeftOverlap, lift_U]
  rfl

lemma surjective_lift_right (a b : R) :
    Function.Surjective (Algebra.TensorProduct.lift
      (rightToLeftOverlap a b) (IsScalarTower.toAlgHom R (CrossingQuotient R a) (LeftOverlap a))
      (fun _ _ => Commute.all _ _) :
      CrossingQuotient R b ⊗[R] CrossingQuotient R a →ₐ[R] LeftOverlap a) := by
  intro z
  obtain ⟨n, c, rfl⟩ := eq_mul_invSelf_pow (V a) z
  refine ⟨(U b ^ n) ⊗ₜ c, ?_⟩
  rw [Algebra.TensorProduct.lift_tmul, map_pow, rightToLeftOverlap, lift_U, mul_comm]
  rfl

lemma block_self {A : Type u} [CommRing A] [Algebra R A] {X : Scheme.{u}}
    (i : Spec (.of A) ⟶ X) [Mono i] (f : X ⟶ Spec (.of R))
    (hi : i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    IsClosedImmersion (pullback.mapDesc i i f) := by
  apply isClosedImmersion_mapDesc i i f hi hi (AlgHom.id R A) (AlgHom.id R A)
  · have h : Spec.map (CommRingCat.ofHom (AlgHom.id R A).toRingHom) = 𝟙 (Spec (.of A)) := by
      change Spec.map (CommRingCat.ofHom (RingHom.id A)) = _
      rw [CommRingCat.ofHom_id]
      exact Spec.map_id _
    rw [h]
    exact IsKernelPair.id_of_mono i
  · intro c
    exact ⟨c ⊗ₜ 1, by rw [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, map_one, mul_one]⟩

lemma block_left_right (a b : R) :
    IsClosedImmersion (pullback.mapDesc (ιLeft a b) (ιRight a b) (toSpec a b)) := by
  apply isClosedImmersion_mapDesc (ιLeft a b) (ιRight a b) (toSpec a b)
    (left_toSpec a b) (right_toSpec a b)
    (IsScalarTower.toAlgHom R (CrossingQuotient R a) (LeftOverlap a)) (rightToLeftOverlap a b)
  · convert! (overlap_isPullback a b).flip using 1
    exact (rightOverlapMap_eq a b).symm
  · exact surjective_lift_left a b

lemma block_right_left (a b : R) :
    IsClosedImmersion (pullback.mapDesc (ιRight a b) (ιLeft a b) (toSpec a b)) := by
  apply isClosedImmersion_mapDesc (ιRight a b) (ιLeft a b) (toSpec a b)
    (right_toSpec a b) (left_toSpec a b)
    (rightToLeftOverlap a b) (IsScalarTower.toAlgHom R (CrossingQuotient R a) (LeftOverlap a))
  · convert! overlap_isPullback a b using 1
    exact (rightOverlapMap_eq a b).symm
  · exact surjective_lift_right a b

abbrev Qci : AffineTargetMorphismProperty := fun X _ f _ => IsAffine X ∧ Function.Surjective f.appTop

lemma isSeparated_toSpec (a b : R) : IsSeparated (toSpec a b) := by
  haveI : Qci.IsLocal := HasAffineProperty.isLocal_affineProperty @IsClosedImmersion
  haveI : ∀ i, IsAffine ((openCover a b).X i) := fun i => by
    cases i <;> dsimp [openCover] <;> infer_instance
  have hQ : Qci.diagonal (toSpec a b) :=
    AffineTargetMorphismProperty.diagonal_of_openCover_source (Q := Qci) (toSpec a b)
      (openCover a b) (fun i j => ?_)
  · exact ⟨(HasAffineProperty.diagonal_iff (P := @IsClosedImmersion) (f := toSpec a b)).mp hQ⟩
  all_goals
    apply (HasAffineProperty.iff_of_isAffine (P := @IsClosedImmersion)).mp
    cases i <;> cases j
    · exact block_self (ιLeft a b) (toSpec a b) (left_toSpec a b)
    · exact block_left_right a b
    · exact block_right_left a b
    · exact block_self (ιRight a b) (toSpec a b) (right_toSpec a b)

instance model_isSeparated (a b : R) : (Model a b).IsSeparated :=
  (HasAffineProperty.iff_of_isAffine (P := @IsSeparated) (f := toSpec a b)).mp (isSeparated_toSpec a b)

instance toNode_isSeparated (a b : R) : IsSeparated (toNode a b) := inferInstance
end PhilipponNodeFactorSeparated

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient
namespace PhilipponNodeFactorFiniteType
open PhilipponNodeFactorCharts PhilipponNodeFactorGluing PhilipponNodeFactorSeparated
variable {R : Type u} [CommRing R]

instance crossing_finiteType (a : R) : Algebra.FiniteType R (CrossingQuotient R a) := by
  dsimp [CrossingQuotient]
  infer_instance

instance crossing_structure_finiteType (a : R) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R (CrossingQuotient R a)))) := by
  apply HasRingHomProperty.Spec_iff.mpr
  exact RingHom.finiteType_algebraMap.mpr inferInstance

instance model_compactSpace (a b : R) : CompactSpace (Model a b) := by
  haveI : Finite (openCover a b).I₀ := inferInstanceAs (Finite Bool)
  haveI : ∀ i, CompactSpace ((openCover a b).X i) := fun i => by
    cases i
    · change CompactSpace (PrimeSpectrum (CrossingQuotient R a)); infer_instance
    · change CompactSpace (PrimeSpectrum (CrossingQuotient R b)); infer_instance
  exact (openCover a b).compactSpace

instance toSpec_locallyOfFiniteType (a b : R) : LocallyOfFiniteType (toSpec a b) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType) (openCover a b)]
  intro i
  cases i
  · change LocallyOfFiniteType (ιLeft a b ≫ toSpec a b)
    rw [left_toSpec]
    infer_instance
  · change LocallyOfFiniteType (ιRight a b ≫ toSpec a b)
    rw [right_toSpec]
    infer_instance

instance toNode_locallyOfFiniteType (a b : R) : LocallyOfFiniteType (toNode a b) := by
  haveI : LocallyOfFiniteType (toNode a b ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (CrossingQuotient R (a * b))))) :=
    toSpec_locallyOfFiniteType a b
  exact locallyOfFiniteType_of_comp (toNode a b)
    (Spec.map (CommRingCat.ofHom (algebraMap R (CrossingQuotient R (a * b)))))

instance toNode_quasiCompact (a b : R) : QuasiCompact (toNode a b) := inferInstance
end PhilipponNodeFactorFiniteType

set_option autoImplicit false
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 70000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient
namespace PhilipponNodeFactorValuative
open PhilipponNodeFactorCharts PhilipponNodeFactorGluing
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

lemma glue_left (a b : R) {K : Type u} [CommRing K] (ω : LeftOverlap a →+* K) :
    Spec.map (CommRingCat.ofHom (ω.comp (algebraMap (CrossingQuotient R a) (LeftOverlap a)))) ≫
        ιLeft a b =
      Spec.map (CommRingCat.ofHom (ω.comp (rightToLeftOverlap a b).toRingHom)) ≫ ιRight a b := by
  rw [specMap_comp (algebraMap (CrossingQuotient R a) (LeftOverlap a)) ω,
    specMap_comp (rightToLeftOverlap a b).toRingHom ω, Category.assoc, Category.assoc]
  change Spec.map _ ≫ leftOverlapMap a ≫ _ = _
  rw [← rightOverlapMap_eq]
  exact congrArg (fun h : Overlap a ⟶ Model a b => Spec.map (CommRingCat.ofHom ω) ≫ h)
    pushout.condition

lemma overlapToRight_right (a b : R) (z : CrossingQuotient R b) :
    overlapToRightRing a b (rightToLeftOverlap a b z) =
      algebraMap (CrossingQuotient R b) (RightOverlap b) z := by
  rw [← overlapToLeft_algebraMap a b z]
  exact congrArg (fun f : RightOverlap b →ₐ[R] RightOverlap b => f (algebraMap _ _ z))
    (overlap_right_left a b)

lemma glue_right (a b : R) {K : Type u} [CommRing K] (χ : RightOverlap b →+* K) :
    Spec.map (CommRingCat.ofHom (χ.comp (algebraMap (CrossingQuotient R b) (RightOverlap b)))) ≫
        ιRight a b =
      Spec.map (CommRingCat.ofHom (χ.comp (leftToRightOverlap a b).toRingHom)) ≫ ιLeft a b := by
  have hl : (χ.comp (overlapToRightRing a b)).comp
      (algebraMap (CrossingQuotient R a) (LeftOverlap a)) =
      χ.comp (leftToRightOverlap a b).toRingHom := by
    apply RingHom.ext
    intro z
    exact congrArg χ (overlapToRightRing_algebraMap a b z)
  have hr : (χ.comp (overlapToRightRing a b)).comp (rightToLeftOverlap a b).toRingHom =
      χ.comp (algebraMap (CrossingQuotient R b) (RightOverlap b)) := by
    apply RingHom.ext
    intro z
    exact congrArg χ (overlapToRight_right a b z)
  simpa only [hl, hr] using (glue_left a b (χ.comp (overlapToRightRing a b))).symm

section valuation
variable {O K : Type u} [CommRing O] [IsDomain O] [ValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K]

lemma left_extension (a b : R) (φ : CrossingQuotient R a →+* K)
    (ψ : CrossingQuotient R (a * b) →+* O)
    (hcomm : φ.comp (toLeft a b).toRingHom = (algebraMap O K).comp ψ) :
    ∃ l : Spec (.of O) ⟶ Model a b,
      Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ l =
        Spec.map (CommRingCat.ofHom φ) ≫ ιLeft a b := by
  let ρ := ψ.comp (algebraMap R (CrossingQuotient R (a * b)))
  have hinj := IsFractionRing.injective O K
  have hc (z) : φ (toLeft a b z) = algebraMap O K (ψ z) := RingHom.congr_fun hcomm z
  have hσ (r : R) : algebraMap O K (ρ r) = φ (algebraMap R _ r) := by
    change algebraMap O K (ψ (algebraMap R _ r)) = _
    rw [← hc, AlgHom.commutes]
  have hu : φ (U a) = algebraMap O K (ψ (U (a * b))) := by simpa using hc (U (a * b))
  have hv : φ (algebraMap R _ b) * φ (V a) = algebraMap O K (ψ (V (a * b))) := by
    simpa only [toLeft_V, map_mul] using hc (V (a * b))
  by_cases hz : IsLocalization.IsInteger O (φ (V a))
  · obtain ⟨z, hz⟩ := hz
    have hrel : ψ (U (a * b)) * z = ρ a := by
      apply hinj
      rw [map_mul, hz, ← hu, hσ, ← map_mul, U_mul_V]
    let η := pointHom a ρ (ψ (U (a * b))) z hrel
    have hη : (algebraMap O K).comp η = φ := by
      apply ringHom_ext
      · intro r; exact (congrArg (algebraMap O K) (pointHom_algebraMap a ρ _ _ hrel r)).trans (hσ r)
      · exact (congrArg (algebraMap O K) (pointHom_U a ρ _ _ hrel)).trans hu.symm
      · exact (congrArg (algebraMap O K) (pointHom_V a ρ _ _ hrel)).trans hz
    refine ⟨Spec.map (CommRingCat.ofHom η) ≫ ιLeft a b, ?_⟩
    rw [← Category.assoc, ← specMap_comp, hη]
  · have hz0 : φ (V a) ≠ 0 := by
      intro h
      exact hz ⟨0, by rw [map_zero, h]⟩
    obtain ⟨w, hw⟩ : IsLocalization.IsInteger O (φ (V a))⁻¹ :=
      (ValuationRing.isInteger_or_isInteger O (φ (V a))).resolve_left hz
    have hrel : w * ψ (V (a * b)) = ρ b := by
      apply hinj
      rw [map_mul, hw, ← hv, hσ]
      field_simp
    let η := pointHom b ρ w (ψ (V (a * b))) hrel
    have hunit : IsUnit (φ (V a)) := isUnit_iff_ne_zero.mpr hz0
    let ω : LeftOverlap a →+* K := IsLocalization.Away.lift (V a) hunit
    have hωC (c : CrossingQuotient R a) : ω (algebraMap _ _ c) = φ c :=
      IsLocalization.Away.lift_eq _ hunit c
    have hωl : ω.comp (algebraMap (CrossingQuotient R a) (LeftOverlap a)) = φ :=
      IsLocalization.Away.lift_comp (V a) hunit
    have hωinv : ω (IsLocalization.Away.invSelf (V a)) = (φ (V a))⁻¹ := by
      have h : φ (V a) * ω (IsLocalization.Away.invSelf (V a)) = 1 := by
        rw [← hωC, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
      exact (inv_eq_of_mul_eq_one_right h).symm
    have hωr : ω.comp (rightToLeftOverlap a b).toRingHom = (algebraMap O K).comp η := by
      apply ringHom_ext
      · intro r
        change ω (rightToLeftOverlap a b (algebraMap R _ r)) = algebraMap O K (η (algebraMap R _ r))
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R (CrossingQuotient R a) (LeftOverlap a),
          hωC, pointHom_algebraMap, hσ]
      · change ω (rightToLeftOverlap a b (U b)) = algebraMap O K (η (U b))
        rw [rightToLeftOverlap, lift_U, hωinv, pointHom_U, hw]
      · change ω (rightToLeftOverlap a b (V b)) = algebraMap O K (η (V b))
        rw [rightToLeftOverlap, lift_V, map_mul,
          IsScalarTower.algebraMap_apply R (CrossingQuotient R a) (LeftOverlap a),
          hωC, hωC, pointHom_V, hv]
    refine ⟨Spec.map (CommRingCat.ofHom η) ≫ ιRight a b, ?_⟩
    rw [← Category.assoc, ← specMap_comp, ← hωr, ← hωl]
    exact (glue_left a b ω).symm

lemma right_extension (a b : R) (φ : CrossingQuotient R b →+* K)
    (ψ : CrossingQuotient R (a * b) →+* O)
    (hcomm : φ.comp (toRight a b).toRingHom = (algebraMap O K).comp ψ) :
    ∃ l : Spec (.of O) ⟶ Model a b,
      Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ l =
        Spec.map (CommRingCat.ofHom φ) ≫ ιRight a b := by
  let ρ := ψ.comp (algebraMap R (CrossingQuotient R (a * b)))
  have hinj := IsFractionRing.injective O K
  have hc (z) : φ (toRight a b z) = algebraMap O K (ψ z) := RingHom.congr_fun hcomm z
  have hσ (r : R) : algebraMap O K (ρ r) = φ (algebraMap R _ r) := by
    change algebraMap O K (ψ (algebraMap R _ r)) = _
    rw [← hc, AlgHom.commutes]
  have hv : φ (V b) = algebraMap O K (ψ (V (a * b))) := by simpa using hc (V (a * b))
  have hu : φ (algebraMap R _ a) * φ (U b) = algebraMap O K (ψ (U (a * b))) := by
    simpa only [toRight_U, map_mul] using hc (U (a * b))
  by_cases hz : IsLocalization.IsInteger O (φ (U b))
  · obtain ⟨z, hz⟩ := hz
    have hrel : z * ψ (V (a * b)) = ρ b := by
      apply hinj
      rw [map_mul, hz, ← hv, hσ, ← map_mul, U_mul_V]
    let η := pointHom b ρ z (ψ (V (a * b))) hrel
    have hη : (algebraMap O K).comp η = φ := by
      apply ringHom_ext
      · intro r; exact (congrArg (algebraMap O K) (pointHom_algebraMap b ρ _ _ hrel r)).trans (hσ r)
      · exact (congrArg (algebraMap O K) (pointHom_U b ρ _ _ hrel)).trans hz
      · exact (congrArg (algebraMap O K) (pointHom_V b ρ _ _ hrel)).trans hv.symm
    refine ⟨Spec.map (CommRingCat.ofHom η) ≫ ιRight a b, ?_⟩
    rw [← Category.assoc, ← specMap_comp, hη]
  · have hz0 : φ (U b) ≠ 0 := by
      intro h
      exact hz ⟨0, by rw [map_zero, h]⟩
    obtain ⟨w, hw⟩ : IsLocalization.IsInteger O (φ (U b))⁻¹ :=
      (ValuationRing.isInteger_or_isInteger O (φ (U b))).resolve_left hz
    have hrel : ψ (U (a * b)) * w = ρ a := by
      apply hinj
      rw [map_mul, hw, ← hu, hσ]
      field_simp
    let η := pointHom a ρ (ψ (U (a * b))) w hrel
    have hunit : IsUnit (φ (U b)) := isUnit_iff_ne_zero.mpr hz0
    let ω : RightOverlap b →+* K := IsLocalization.Away.lift (U b) hunit
    have hωC (c : CrossingQuotient R b) : ω (algebraMap _ _ c) = φ c :=
      IsLocalization.Away.lift_eq _ hunit c
    have hωr : ω.comp (algebraMap (CrossingQuotient R b) (RightOverlap b)) = φ :=
      IsLocalization.Away.lift_comp (U b) hunit
    have hωinv : ω (IsLocalization.Away.invSelf (U b)) = (φ (U b))⁻¹ := by
      have h : φ (U b) * ω (IsLocalization.Away.invSelf (U b)) = 1 := by
        rw [← hωC, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
      exact (inv_eq_of_mul_eq_one_right h).symm
    have hωl : ω.comp (leftToRightOverlap a b).toRingHom = (algebraMap O K).comp η := by
      apply ringHom_ext
      · intro r
        change ω (leftToRightOverlap a b (algebraMap R _ r)) = algebraMap O K (η (algebraMap R _ r))
        rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R (CrossingQuotient R b) (RightOverlap b),
          hωC, pointHom_algebraMap, hσ]
      · change ω (leftToRightOverlap a b (U a)) = algebraMap O K (η (U a))
        rw [leftToRightOverlap, lift_U, map_mul,
          IsScalarTower.algebraMap_apply R (CrossingQuotient R b) (RightOverlap b),
          hωC, hωC, pointHom_U, hu]
      · change ω (leftToRightOverlap a b (V a)) = algebraMap O K (η (V a))
        rw [leftToRightOverlap, lift_V, hωinv, pointHom_V, hw]
    refine ⟨Spec.map (CommRingCat.ofHom η) ≫ ιLeft a b, ?_⟩
    rw [← Category.assoc, ← specMap_comp, ← hωl, ← hωr]
    exact (glue_right a b ω).symm

end valuation
lemma specMap_cancel {O K : Type u} [CommRing O] [CommRing K] [Algebra O K]
    (hinj : Function.Injective (algebraMap O K))
    {B : CommRingCat.{u}} {f g : Spec (.of O) ⟶ Spec B}
    (h : Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap O K)) ≫ g) : f = g := by
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  congr 1
  ext x
  exact hinj (congrArg (fun k : B ⟶ CommRingCat.of K => k.hom x) h')

lemma hasLift_of_extension (a b : R) (S : ValuativeCommSq (toNode a b))
    (l : Spec (.of S.R) ⟶ Model a b)
    (hl : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ l = S.i₁) :
    S.commSq.HasLift := by
  refine CommSq.HasLift.mk' ⟨l, hl, ?_⟩
  apply specMap_cancel (IsFractionRing.injective S.R S.K)
  rw [← Category.assoc, hl]
  exact S.commSq.w

lemma chart_compatibility (a b : R) (S : ValuativeCommSq (toNode a b))
    {A : Type u} [CommRing A]
    (τ : CrossingQuotient R (a * b) →+* A)
    (i : Spec (.of A) ⟶ Model a b)
    (hi : i ≫ toNode a b = Spec.map (CommRingCat.ofHom τ))
    (g : Spec (.of S.K) ⟶ Spec (.of A)) (hg : g ≫ i = S.i₁) :
    (Spec.preimage g).hom.comp τ = (algebraMap S.R S.K).comp (Spec.preimage S.i₂).hom := by
  have key : Spec.map (CommRingCat.ofHom ((Spec.preimage g).hom.comp τ)) =
      Spec.map (CommRingCat.ofHom ((algebraMap S.R S.K).comp (Spec.preimage S.i₂).hom)) := by
    rw [specMap_comp τ (Spec.preimage g).hom,
      specMap_comp (Spec.preimage S.i₂).hom (algebraMap S.R S.K),
      CommRingCat.ofHom_hom, CommRingCat.ofHom_hom, Spec.map_preimage, Spec.map_preimage,
      ← hi, ← Category.assoc, hg]
    exact S.commSq.w
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)

lemma valuativeCriterion_existence (a b : R) : ValuativeCriterion.Existence (toNode a b) := by
  intro S
  let p₀ : PrimeSpectrum S.K := default
  rcases ι_jointly_surjective a b (S.i₁ p₀) with ⟨y, hy⟩ | ⟨y, hy⟩
  · have hrange : Set.range S.i₁ ⊆ Set.range (ιLeft a b) := by
      rintro _ ⟨p, rfl⟩
      obtain rfl : p = p₀ := Subsingleton.elim (α := PrimeSpectrum S.K) _ _
      exact ⟨y, hy⟩
    let g := IsOpenImmersion.lift (ιLeft a b) S.i₁ hrange
    have hg : g ≫ ιLeft a b = S.i₁ := IsOpenImmersion.lift_fac _ _ _
    have hcomm := chart_compatibility a b S (toLeft a b).toRingHom (ιLeft a b)
      (ιLeft_toNode a b) g hg
    obtain ⟨l, hl⟩ := left_extension a b (Spec.preimage g).hom (Spec.preimage S.i₂).hom hcomm
    apply hasLift_of_extension a b S l
    simpa only [CommRingCat.ofHom_hom, Spec.map_preimage] using hl.trans
      (by simpa only [CommRingCat.ofHom_hom, Spec.map_preimage] using hg)
  · have hrange : Set.range S.i₁ ⊆ Set.range (ιRight a b) := by
      rintro _ ⟨p, rfl⟩
      obtain rfl : p = p₀ := Subsingleton.elim (α := PrimeSpectrum S.K) _ _
      exact ⟨y, hy⟩
    let g := IsOpenImmersion.lift (ιRight a b) S.i₁ hrange
    have hg : g ≫ ιRight a b = S.i₁ := IsOpenImmersion.lift_fac _ _ _
    have hcomm := chart_compatibility a b S (toRight a b).toRingHom (ιRight a b)
      (ιRight_toNode a b) g hg
    obtain ⟨l, hl⟩ := right_extension a b (Spec.preimage g).hom (Spec.preimage S.i₂).hom hcomm
    apply hasLift_of_extension a b S l
    simpa only [CommRingCat.ofHom_hom, Spec.map_preimage] using hl.trans
      (by simpa only [CommRingCat.ofHom_hom, Spec.map_preimage] using hg)

instance toNode_isProper (a b : R) : IsProper (toNode a b) := by
  haveI : UniversallyClosed (toNode a b) :=
    UniversallyClosed.of_valuativeCriterion (toNode a b) (valuativeCriterion_existence a b)
  exact ⟨⟩

end PhilipponNodeFactorValuative


theorem solution {R : Type u} [CommRing R] (a b : R) :
    ∃ (X : Scheme.{u}) (q : X ⟶ Spec (.of (CrossingQuotient R (a * b))))
      (i : Spec (.of (CrossingQuotient R a)) ⟶ X)
      (j : Spec (.of (CrossingQuotient R b)) ⟶ X)
      (α : CrossingQuotient R (a * b) →ₐ[R] CrossingQuotient R a)
      (β : CrossingQuotient R (a * b) →ₐ[R] CrossingQuotient R b)
      (θ : CrossingQuotient R b →ₐ[R] Localization.Away (V a)),
      IsProper q ∧ IsOpenImmersion i ∧ IsOpenImmersion j ∧
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
          (algebraMap (CrossingQuotient R a) (Localization.Away (V a))))) j i := by
  refine ⟨PhilipponNodeFactorGluing.Model a b, PhilipponNodeFactorGluing.toNode a b,
    PhilipponNodeFactorGluing.ιLeft a b, PhilipponNodeFactorGluing.ιRight a b,
    PhilipponNodeFactorCharts.toLeft a b, PhilipponNodeFactorCharts.toRight a b,
    PhilipponNodeFactorCharts.rightToLeftOverlap a b,
    inferInstance, inferInstance, inferInstance,
    PhilipponNodeFactorGluing.ι_jointly_surjective a b,
    PhilipponNodeFactorCharts.toLeft_U a b, PhilipponNodeFactorCharts.toLeft_V a b,
    PhilipponNodeFactorCharts.toRight_U a b, PhilipponNodeFactorCharts.toRight_V a b,
    lift_U _ _ _ _, lift_V _ _ _ _,
    PhilipponNodeFactorGluing.ιLeft_toNode a b, PhilipponNodeFactorGluing.ιRight_toNode a b, ?_⟩
  rw [← PhilipponNodeFactorGluing.rightOverlapMap_eq]
  exact PhilipponNodeFactorGluing.overlap_isPullback a b

