-- Prove2me | solution 1 for MvPolynomial.CrossingQuotient.exists_integral_projective_cartier_modification
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-06T06:01:50.888566+00:00
-- url     : https://prove2.me/submissions/49e82014-0b13-4786-ac91-7471134e2b0f

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_MvPolynomial_CrossingResolution
import Mathlib

universe u v

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace


namespace PhilipponStalkwiseLift

variable {X Y S : Scheme.{u}}

/-- Equality on every source stalk gives equality on a germ-injective scheme.
The proof spreads each stalk equality to a neighborhood and uses an open cover. -/
lemma hom_ext_fromSpecStalk [X.IsGermInjective] (f g : X ⟶ Y)
    (h : ∀ x : X, X.fromSpecStalk x ≫ f = X.fromSpecStalk x ≫ g) : f = g := by
  choose U hxU hU using fun x : X => spread_out_unique_of_isGermInjective' f g (h x)
  have hcover : IsOpenCover U := by
    apply IsOpenCover.mk
    apply top_unique
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x, hxU x⟩
  exact Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover U hcover) f g hU

/-- Stalkwise uniqueness on X also gives uniqueness on every open source over X.
The inverse of the open immersion's stalk isomorphism transports the comparison. -/
lemma unique_on_open [X.IsGermInjective] (sX : X ⟶ S) (sY : Y ⟶ S)
    (huniq : ∀ x : X, ∃! φ : Spec (X.presheaf.stalk x) ⟶ Y,
      φ ≫ sY = X.fromSpecStalk x ≫ sX)
    {W : Scheme.{u}} (p : W ⟶ X) [IsOpenImmersion p]
    (f g : W ⟶ Y) (hf : f ≫ sY = p ≫ sX) (hg : g ≫ sY = p ≫ sX) : f = g := by
  haveI : W.IsGermInjective := fun x =>
    (isGermInjectiveAt_iff_of_isOpenImmersion (f := p)).mp inferInstance
  apply hom_ext_fromSpecStalk
  intro x
  let e := asIso (p.stalkMap x)
  have hover (k : W ⟶ Y) (hk : k ≫ sY = p ≫ sX) :
      (Spec.map e.inv ≫ W.fromSpecStalk x ≫ k) ≫ sY =
        X.fromSpecStalk (p x) ≫ sX := by
    rw [Category.assoc, Category.assoc, hk,
      ← Scheme.SpecMap_stalkMap_fromSpecStalk_assoc,
      ← Spec.map_comp_assoc]
    change Spec.map (e.hom ≫ e.inv) ≫ X.fromSpecStalk (p x) ≫ sX = _
    rw [e.hom_inv_id, Spec.map_id, Category.id_comp]
  obtain ⟨φ, hφ, hφuniq⟩ := huniq (p x)
  have heq := (hφuniq _ (hover f hf)).trans (hφuniq _ (hover g hg)).symm
  exact (cancel_epi (Spec.map e.inv)).mp heq

/-- Stalkwise unique lifts to a locally finite-type target glue to a unique
global lift when the source is germ-injective. In particular this applies
to integral schemes and locally Noetherian schemes. -/
theorem existsUnique_lift [X.IsGermInjective] (sX : X ⟶ S) (sY : Y ⟶ S)
    [LocallyOfFiniteType sY]
    (huniq : ∀ x : X, ∃! φ : Spec (X.presheaf.stalk x) ⟶ Y,
      φ ≫ sY = X.fromSpecStalk x ≫ sX) :
    ∃! f : X ⟶ Y, f ≫ sY = sX := by
  have hlocal : ∀ x : X, ∃ (U : X.Opens) (_hxU : x ∈ U) (f : U.toScheme ⟶ Y),
      f ≫ sY = U.ι ≫ sX := by
    intro x
    obtain ⟨φ, hφ, -⟩ := huniq x
    obtain ⟨U, hxU, f, -, hf⟩ := spread_out_of_isGermInjective' sX sY φ hφ
    exact ⟨U, hxU, f, hf⟩
  choose U hxU f hf using hlocal
  have hcover : IsOpenCover U := by
    apply IsOpenCover.mk
    apply top_unique
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x, hxU x⟩
  let cover := X.openCoverOfIsOpenCover U hcover
  have hcompat : ∀ i j, pullback.fst (cover.f i) (cover.f j) ≫ f i =
      pullback.snd (cover.f i) (cover.f j) ≫ f j := by
    intro i j
    change X at i j
    change pullback.fst (U i).ι (U j).ι ≫ f i =
      pullback.snd (U i).ι (U j).ι ≫ f j
    apply unique_on_open sX sY huniq
      (pullback.fst (U i).ι (U j).ι ≫ (U i).ι)
    · rw [Category.assoc, hf i]
      rfl
    · rw [Category.assoc, hf j]
      exact (pullback.condition_assoc sX).symm
  let F := cover.glueMorphisms f hcompat
  have hF : F ≫ sY = sX := by
    apply Scheme.Cover.hom_ext cover
    intro i
    change cover.f i ≫ cover.glueMorphisms f hcompat ≫ sY = _
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms]
    exact hf i
  refine ⟨F, hF, ?_⟩
  intro g hg
  exact unique_on_open sX sY huniq (𝟙 X) g F (by simpa using hg) (by simpa using hF)

end PhilipponStalkwiseLift

end

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency.types false
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
end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
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

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 300000
open MvPolynomial MvPolynomial.CrossingQuotient


namespace PhilipponNodeCartierLocalLift

variable {A : Type v} [CommRing A]

lemma cancel_regular {r x y : A} (hr : r ∈ nonZeroDivisors A)
    (h : r * x = r * y) : x = y := by
  apply sub_eq_zero.mp
  apply (mem_nonZeroDivisors_iff_left.mp hr) (x - y)
  rw [mul_sub, h, sub_self]

/-- A two-generated effective Cartier ideal in a local ring is generated by one
of its two specified generators. The chosen generator is a non-zero-divisor. -/
lemma regular_generator_or [IsLocalRing A] {u a r : A}
    (hI : Ideal.span ({u, a} : Set A) = Ideal.span ({r} : Set A))
    (hr : r ∈ nonZeroDivisors A) :
    (u ∈ nonZeroDivisors A ∧ u ∣ a) ∨
      (a ∈ nonZeroDivisors A ∧ a ∣ u) := by
  have hu : u ∈ Ideal.span ({r} : Set A) := by
    rw [← hI]
    exact Ideal.subset_span (by simp)
  have ha : a ∈ Ideal.span ({r} : Set A) := by
    rw [← hI]
    exact Ideal.subset_span (by simp)
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hu
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp ha
  have hrI : r ∈ Ideal.span ({u, a} : Set A) := by
    rw [hI]
    exact Ideal.subset_span (by simp)
  obtain ⟨p, q, hpq⟩ := Ideal.mem_span_pair.mp hrI
  have hst : p * s + q * t = 1 := by
    apply cancel_regular hr
    calc
      r * (p * s + q * t) = p * u + q * a := by rw [hs, ht]; ring
      _ = r * 1 := by simpa using hpq
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hst with hps | hqt
  · have hsunit : IsUnit s := isUnit_of_mul_isUnit_right hps
    left
    refine ⟨?_, ?_⟩
    · rw [hs]
      exact mul_mem_nonZeroDivisors.mpr ⟨hr, hsunit.mem_nonZeroDivisors⟩
    · obtain ⟨sunit, rfl⟩ := hsunit
      refine ⟨(sunit⁻¹ : Aˣ) * t, ?_⟩
      rw [hs, ht]
      simp [mul_assoc]
  · have htunit : IsUnit t := isUnit_of_mul_isUnit_right hqt
    right
    refine ⟨?_, ?_⟩
    · rw [ht]
      exact mul_mem_nonZeroDivisors.mpr ⟨hr, htunit.mem_nonZeroDivisors⟩
    · obtain ⟨tunit, rfl⟩ := htunit
      refine ⟨(tunit⁻¹ : Aˣ) * s, ?_⟩
      rw [hs, ht]
      simp [mul_assoc]

variable {R : Type u} [CommRing R]
open PhilipponNodeFactorCharts PhilipponCrossingPointHom

/-- In the chart where the pullback of `u` generates the Cartier ideal,
the map to the left nodal chart exists and is unique. -/
lemma existsUnique_left_lift (a b : R) (ψ : CrossingQuotient R (a * b) →+* A)
    (hu : ψ (U (a * b)) ∈ nonZeroDivisors A)
    (hdiv : ψ (U (a * b)) ∣ ψ (algebraMap R _ a)) :
    ∃! φ : CrossingQuotient R a →+* A,
      φ.comp (toLeft a b).toRingHom = ψ := by
  let ρ := ψ.comp (algebraMap R (CrossingQuotient R (a * b)))
  have hρ (r : R) : ρ r = ψ (algebraMap R _ r) := rfl
  obtain ⟨z, hz⟩ := hdiv
  have hrel : ψ (U (a * b)) * z = ρ a := hz.symm
  have hprod : ψ (U (a * b)) * ψ (V (a * b)) = ρ a * ρ b := by
    rw [← map_mul, U_mul_V, ← hρ, map_mul]
  have hbz : ρ b * z = ψ (V (a * b)) := by
    apply cancel_regular hu
    calc
      ψ (U (a * b)) * (ρ b * z) = (ψ (U (a * b)) * z) * ρ b := by ring
      _ = ψ (U (a * b)) * ψ (V (a * b)) := by rw [hrel, hprod]
  refine ⟨pointHom a ρ (ψ (U (a * b))) z hrel, ?_, ?_⟩
  · apply PhilipponCrossingPointHom.ringHom_ext
    · intro r
      change pointHom a ρ _ _ hrel (toLeft a b (algebraMap R _ r)) = _
      rw [AlgHom.commutes, pointHom_algebraMap, hρ]
    · change pointHom a ρ _ _ hrel (toLeft a b (U (a * b))) = _
      rw [toLeft_U, pointHom_U]
    · change pointHom a ρ _ _ hrel (toLeft a b (V (a * b))) = _
      rw [toLeft_V, map_mul, pointHom_algebraMap, pointHom_V, hbz]
  · intro φ hφ
    have hφR (r : R) : φ (algebraMap R _ r) = ρ r := by
      have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
        f (algebraMap R _ r)) hφ
      change φ (toLeft a b (algebraMap R _ r)) = _ at h
      rw [AlgHom.commutes] at h
      exact h
    have hφU : φ (U a) = ψ (U (a * b)) := by
      have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
        f (U (a * b))) hφ
      change φ (toLeft a b (U (a * b))) = _ at h
      rwa [toLeft_U] at h
    apply PhilipponCrossingPointHom.ringHom_ext
    · intro r
      rw [pointHom_algebraMap]
      exact hφR r
    · rw [pointHom_U]
      exact hφU
    · rw [pointHom_V]
      apply cancel_regular hu
      calc
        ψ (U (a * b)) * φ (V a) = φ (U a) * φ (V a) :=
          congrArg (fun t : A => t * φ (V a)) hφU.symm
        _ = φ (U a * V a) := (map_mul φ _ _).symm
        _ = ρ a := by rw [U_mul_V, hφR]
        _ = ψ (U (a * b)) * z := hrel.symm

/-- In the chart where the pullback of `a` generates the Cartier ideal,
the map to the right nodal chart exists and is unique. -/
lemma existsUnique_right_lift (a b : R) (ψ : CrossingQuotient R (a * b) →+* A)
    (ha : ψ (algebraMap R _ a) ∈ nonZeroDivisors A)
    (hdiv : ψ (algebraMap R _ a) ∣ ψ (U (a * b))) :
    ∃! φ : CrossingQuotient R b →+* A,
      φ.comp (toRight a b).toRingHom = ψ := by
  let ρ := ψ.comp (algebraMap R (CrossingQuotient R (a * b)))
  have hρ (r : R) : ρ r = ψ (algebraMap R _ r) := rfl
  obtain ⟨w, hw⟩ := hdiv
  have hprod : ψ (U (a * b)) * ψ (V (a * b)) = ρ a * ρ b := by
    rw [← map_mul, U_mul_V, ← hρ, map_mul]
  have hrel : w * ψ (V (a * b)) = ρ b := by
    apply cancel_regular ha
    calc
      ψ (algebraMap R _ a) * (w * ψ (V (a * b))) =
          ψ (U (a * b)) * ψ (V (a * b)) := by rw [← mul_assoc, ← hw]
      _ = ψ (algebraMap R _ a) * ρ b := hprod
  refine ⟨pointHom b ρ w (ψ (V (a * b))) hrel, ?_, ?_⟩
  · apply PhilipponCrossingPointHom.ringHom_ext
    · intro r
      change pointHom b ρ _ _ hrel (toRight a b (algebraMap R _ r)) = _
      rw [AlgHom.commutes, pointHom_algebraMap, hρ]
    · change pointHom b ρ _ _ hrel (toRight a b (U (a * b))) = _
      rw [toRight_U, map_mul, pointHom_algebraMap, pointHom_U]
      exact hw.symm
    · change pointHom b ρ _ _ hrel (toRight a b (V (a * b))) = _
      rw [toRight_V, pointHom_V]
  · intro φ hφ
    have hφR (r : R) : φ (algebraMap R _ r) = ρ r := by
      have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
        f (algebraMap R _ r)) hφ
      change φ (toRight a b (algebraMap R _ r)) = _ at h
      rw [AlgHom.commutes] at h
      exact h
    have hφV : φ (V b) = ψ (V (a * b)) := by
      have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
        f (V (a * b))) hφ
      change φ (toRight a b (V (a * b))) = _ at h
      rwa [toRight_V] at h
    have hφU : ρ a * φ (U b) = ψ (U (a * b)) := by
      have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
        f (U (a * b))) hφ
      change φ (toRight a b (U (a * b))) = _ at h
      rwa [toRight_U, map_mul, hφR] at h
    apply PhilipponCrossingPointHom.ringHom_ext
    · intro r
      rw [pointHom_algebraMap]
      exact hφR r
    · rw [pointHom_U]
      apply cancel_regular ha
      calc
        ψ (algebraMap R _ a) * φ (U b) = ψ (U (a * b)) := hφU
        _ = ψ (algebraMap R _ a) * w := hw
    · rw [pointHom_V]
      exact hφV

/-- Effective Cartier pullback of `(u,a)` gives a unique factorization through
at least one of the two specified affine charts of the actual nodal model. -/
theorem exists_unique_chart_lift [IsLocalRing A] (a b : R)
    (ψ : CrossingQuotient R (a * b) →+* A) (r : A)
    (hI : Ideal.span ({ψ (U (a * b)), ψ (algebraMap R _ a)} : Set A) =
      Ideal.span ({r} : Set A)) (hr : r ∈ nonZeroDivisors A) :
    (∃! φ : CrossingQuotient R a →+* A, φ.comp (toLeft a b).toRingHom = ψ) ∨
      (∃! φ : CrossingQuotient R b →+* A, φ.comp (toRight a b).toRingHom = ψ) := by
  rcases regular_generator_or hI hr with ⟨hu, hdiv⟩ | ⟨ha, hdiv⟩
  · exact Or.inl (existsUnique_left_lift a b ψ hu hdiv)
  · exact Or.inr (existsUnique_right_lift a b ψ ha hdiv)

/-- Two affine lifts over a Cartier generator meet in the actual localized
overlap, with both ring-map equations. No reducedness hypothesis is needed. -/
lemma chart_lifts_overlap (a b : R) (ψ : CrossingQuotient R (a * b) →+* A)
    (hu : ψ (U (a * b)) ∈ nonZeroDivisors A)
    (φL : CrossingQuotient R a →+* A) (φR : CrossingQuotient R b →+* A)
    (hL : φL.comp (toLeft a b).toRingHom = ψ)
    (hR : φR.comp (toRight a b).toRingHom = ψ) :
    ∃ ell : LeftOverlap a →+* A,
      ell.comp (algebraMap (CrossingQuotient R a) (LeftOverlap a)) = φL ∧
      ell.comp (rightToLeftOverlap a b).toRingHom = φR := by
  let ρ := ψ.comp (algebraMap R (CrossingQuotient R (a * b)))
  have hφLR (r : R) : φL (algebraMap R _ r) = ρ r := by
    have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
      f (algebraMap R _ r)) hL
    change φL (toLeft a b (algebraMap R _ r)) = _ at h
    rw [AlgHom.commutes] at h
    exact h
  have hφRR (r : R) : φR (algebraMap R _ r) = ρ r := by
    have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
      f (algebraMap R _ r)) hR
    change φR (toRight a b (algebraMap R _ r)) = _ at h
    rw [AlgHom.commutes] at h
    exact h
  have hφLU : φL (U a) = ψ (U (a * b)) := by
    have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
      f (U (a * b))) hL
    change φL (toLeft a b (U (a * b))) = _ at h
    rwa [toLeft_U] at h
  have hleft : ψ (U (a * b)) * φL (V a) = ρ a := by
    calc
      ψ (U (a * b)) * φL (V a) = φL (U a) * φL (V a) :=
        congrArg (fun t : A => t * φL (V a)) hφLU.symm
      _ = φL (U a * V a) := (map_mul φL _ _).symm
      _ = ρ a := by rw [U_mul_V, hφLR]
  have hright : ρ a * φR (U b) = ψ (U (a * b)) := by
    have h := congrArg (fun f : CrossingQuotient R (a * b) →+* A =>
      f (U (a * b))) hR
    change φR (toRight a b (U (a * b))) = _ at h
    rwa [toRight_U, map_mul, hφRR] at h
  have hinv : φL (V a) * φR (U b) = 1 := by
    apply cancel_regular hu
    calc
      ψ (U (a * b)) * (φL (V a) * φR (U b)) =
          (ψ (U (a * b)) * φL (V a)) * φR (U b) := (mul_assoc _ _ _).symm
      _ = ψ (U (a * b)) * 1 := by rw [hleft, hright, mul_one]
  have hz : IsUnit (φL (V a)) := IsUnit.of_mul_eq_one _ hinv
  let ell : LeftOverlap a →+* A := IsLocalization.Away.lift (V a) (g := φL) hz
  have hellL : ell.comp (algebraMap (CrossingQuotient R a) (LeftOverlap a)) = φL := by
    apply RingHom.ext
    intro x
    exact IsLocalization.Away.lift_eq (V a) hz x
  have hcharts :
      (algebraMap (CrossingQuotient R a) (LeftOverlap a)).comp (toLeft a b).toRingHom =
        (rightToLeftOverlap a b).toRingHom.comp (toRight a b).toRingHom :=
    congrArg AlgHom.toRingHom (charts_agree_on_overlap a b)
  have hellR : (ell.comp (rightToLeftOverlap a b).toRingHom).comp
      (toRight a b).toRingHom = ψ := by
    calc
      _ = ell.comp ((rightToLeftOverlap a b).toRingHom.comp (toRight a b).toRingHom) := rfl
      _ = ell.comp ((algebraMap (CrossingQuotient R a) (LeftOverlap a)).comp
          (toLeft a b).toRingHom) := by rw [hcharts]
      _ = φL.comp (toLeft a b).toRingHom := by rw [← RingHom.comp_assoc, hellL]
      _ = ψ := hL
  have ha : ψ (algebraMap R _ a) ∈ nonZeroDivisors A :=
    (mul_mem_nonZeroDivisors.mp (hright.symm ▸ hu)).1
  have hdiv : ψ (algebraMap R _ a) ∣ ψ (U (a * b)) := ⟨φR (U b), hright.symm⟩
  obtain ⟨φ, hφ, huniq⟩ := existsUnique_right_lift a b ψ ha hdiv
  exact ⟨ell, hellL, (huniq _ hellR).trans (huniq _ hR).symm⟩

end PhilipponNodeCartierLocalLift

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
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

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient
open PhilipponNodeFactorCharts PhilipponNodeFactorGluing PhilipponCrossingPointHom


namespace PhilipponNodeCartierModelLift

variable {R A : Type u} [CommRing R] [CommRing A]

/-- A morphism from the spectrum of a local ring to the actual two-chart
model factors through one whole affine chart. -/
lemma factors_through_chart [IsLocalRing A] (a b : R)
    (f : Spec (.of A) ⟶ Model a b) :
    (∃ φ : CrossingQuotient R a →+* A,
      Spec.map (CommRingCat.ofHom φ) ≫ ιLeft a b = f) ∨
    (∃ φ : CrossingQuotient R b →+* A,
      Spec.map (CommRingCat.ofHom φ) ≫ ιRight a b = f) := by
  rcases ι_jointly_surjective a b (f (IsLocalRing.closedPoint A)) with ⟨y, hy⟩ | ⟨y, hy⟩
  · have hrange : Set.range f ⊆ Set.range (ιLeft a b) := by
      rintro _ ⟨x, rfl⟩
      have hclosed : IsLocalRing.closedPoint A ∈ f ⁻¹ᵁ (ιLeft a b).opensRange := ⟨y, hy⟩
      exact (IsLocalRing.specializes_closedPoint x).mem_open
        (f ⁻¹ᵁ (ιLeft a b).opensRange).isOpen hclosed
    let l := IsOpenImmersion.lift (ιLeft a b) f hrange
    refine Or.inl ⟨(Spec.preimage l).hom, ?_⟩
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    exact IsOpenImmersion.lift_fac _ _ _
  · have hrange : Set.range f ⊆ Set.range (ιRight a b) := by
      rintro _ ⟨x, rfl⟩
      have hclosed : IsLocalRing.closedPoint A ∈ f ⁻¹ᵁ (ιRight a b).opensRange := ⟨y, hy⟩
      exact (IsLocalRing.specializes_closedPoint x).mem_open
        (f ⁻¹ᵁ (ιRight a b).opensRange).isOpen hclosed
    let l := IsOpenImmersion.lift (ιRight a b) f hrange
    refine Or.inr ⟨(Spec.preimage l).hom, ?_⟩
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    exact IsOpenImmersion.lift_fac _ _ _

lemma left_compatibility (a b : R) (ψ : CrossingQuotient R (a * b) →+* A)
    (φ : CrossingQuotient R a →+* A)
    (h : (Spec.map (CommRingCat.ofHom φ) ≫ ιLeft a b) ≫ toNode a b =
      Spec.map (CommRingCat.ofHom ψ)) : φ.comp (toLeft a b).toRingHom = ψ := by
  have key : Spec.map (CommRingCat.ofHom (φ.comp (toLeft a b).toRingHom)) =
      Spec.map (CommRingCat.ofHom ψ) := by
    rw [specMap_comp]
    simpa only [Category.assoc, ιLeft_toNode, chartMapLeft] using h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)

lemma right_compatibility (a b : R) (ψ : CrossingQuotient R (a * b) →+* A)
    (φ : CrossingQuotient R b →+* A)
    (h : (Spec.map (CommRingCat.ofHom φ) ≫ ιRight a b) ≫ toNode a b =
      Spec.map (CommRingCat.ofHom ψ)) : φ.comp (toRight a b).toRingHom = ψ := by
  have key : Spec.map (CommRingCat.ofHom (φ.comp (toRight a b).toRingHom)) =
      Spec.map (CommRingCat.ofHom ψ) := by
    rw [specMap_comp]
    simpa only [Category.assoc, ιRight_toNode, chartMapRight] using h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)

/-- The affine lifts constructed from a Cartier generator agree as morphisms
to the actual pushout model, including over nonreduced coefficient rings. -/
lemma chart_lifts_eq (a b : R) (ψ : CrossingQuotient R (a * b) →+* A)
    (hu : ψ (U (a * b)) ∈ nonZeroDivisors A)
    (φL : CrossingQuotient R a →+* A) (φR : CrossingQuotient R b →+* A)
    (hL : φL.comp (toLeft a b).toRingHom = ψ)
    (hR : φR.comp (toRight a b).toRingHom = ψ) :
    Spec.map (CommRingCat.ofHom φL) ≫ ιLeft a b =
      Spec.map (CommRingCat.ofHom φR) ≫ ιRight a b := by
  obtain ⟨ell, hellL, hellR⟩ :=
    PhilipponNodeCartierLocalLift.chart_lifts_overlap a b ψ hu φL φR hL hR
  rw [← hellL, ← hellR,
    specMap_comp (algebraMap (CrossingQuotient R a) (LeftOverlap a)) ell,
    specMap_comp (rightToLeftOverlap a b).toRingHom ell,
    Category.assoc, Category.assoc]
  change Spec.map _ ≫ leftOverlapMap a ≫ _ = _
  rw [← rightOverlapMap_eq]
  exact congrArg (fun h : Overlap a ⟶ Model a b =>
    Spec.map (CommRingCat.ofHom ell) ≫ h) pushout.condition

/-- The actual binary nodal model has the Cartier lifting property on spectra
of arbitrary local rings. The map is unique as a map to the whole model. -/
theorem existsUnique_model_lift [IsLocalRing A] (a b : R)
    (ψ : CrossingQuotient R (a * b) →+* A) (r : A)
    (hI : Ideal.span ({ψ (U (a * b)), ψ (algebraMap R _ a)} : Set A) =
      Ideal.span ({r} : Set A)) (hr : r ∈ nonZeroDivisors A) :
    ∃! f : Spec (.of A) ⟶ Model a b,
      f ≫ toNode a b = Spec.map (CommRingCat.ofHom ψ) := by
  rcases PhilipponNodeCartierLocalLift.regular_generator_or hI hr with
      ⟨hu, hdiv⟩ | ⟨ha, hdiv⟩
  · obtain ⟨φL, hL, huniq⟩ :=
      PhilipponNodeCartierLocalLift.existsUnique_left_lift a b ψ hu hdiv
    refine ⟨Spec.map (CommRingCat.ofHom φL) ≫ ιLeft a b, ?_, ?_⟩
    · change (Spec.map (CommRingCat.ofHom φL) ≫ ιLeft a b) ≫ toNode a b = _
      rw [Category.assoc, ιLeft_toNode, chartMapLeft, ← specMap_comp, hL]
    · intro f hf
      rcases factors_through_chart a b f with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
      · have hcomp := left_compatibility a b ψ φ (by rw [hφ]; exact hf)
        have heq := huniq φ hcomp
        exact hφ.symm.trans (congrArg
          (fun k => Spec.map (CommRingCat.ofHom k) ≫ ιLeft a b) heq)
      · have hcomp := right_compatibility a b ψ φ (by rw [hφ]; exact hf)
        exact hφ.symm.trans (chart_lifts_eq a b ψ hu φL φ hL hcomp).symm
  · obtain ⟨φR, hR, huniq⟩ :=
      PhilipponNodeCartierLocalLift.existsUnique_right_lift a b ψ ha hdiv
    refine ⟨Spec.map (CommRingCat.ofHom φR) ≫ ιRight a b, ?_, ?_⟩
    · change (Spec.map (CommRingCat.ofHom φR) ≫ ιRight a b) ≫ toNode a b = _
      rw [Category.assoc, ιRight_toNode, chartMapRight, ← specMap_comp, hR]
    · intro f hf
      rcases factors_through_chart a b f with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
      · have hcomp := left_compatibility a b ψ φ (by rw [hφ]; exact hf)
        have hφa : φ (algebraMap R _ a) = ψ (algebraMap R _ a) := by
          have h := congrArg (fun k : CrossingQuotient R (a * b) →+* A =>
            k (algebraMap R _ a)) hcomp
          change φ (toLeft a b (algebraMap R _ a)) = _ at h
          rwa [AlgHom.commutes] at h
        have hφU : φ (U a) = ψ (U (a * b)) := by
          have h := congrArg (fun k : CrossingQuotient R (a * b) →+* A =>
            k (U (a * b))) hcomp
          change φ (toLeft a b (U (a * b))) = _ at h
          rwa [toLeft_U] at h
        have hproduct : ψ (U (a * b)) * φ (V a) = ψ (algebraMap R _ a) := by
          calc
            _ = φ (U a) * φ (V a) := congrArg (fun t : A => t * φ (V a)) hφU.symm
            _ = φ (U a * V a) := (map_mul φ _ _).symm
            _ = ψ (algebraMap R _ a) := by rw [U_mul_V, hφa]
        have hu : ψ (U (a * b)) ∈ nonZeroDivisors A :=
          (mul_mem_nonZeroDivisors.mp (hproduct.symm ▸ ha)).1
        exact hφ.symm.trans (chart_lifts_eq a b ψ hu φ φR hcomp hR)
      · have hcomp := right_compatibility a b ψ φ (by rw [hφ]; exact hf)
        have heq := huniq φ hcomp
        exact hφ.symm.trans (congrArg
          (fun k => Spec.map (CommRingCat.ofHom k) ≫ ιRight a b) heq)

end PhilipponNodeCartierModelLift

end

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
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
end

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
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
end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient
open PhilipponNodeFactorGluing


namespace PhilipponNodeCartierGlobalLift

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The actual coefficient homomorphism of the point induced on a source stalk. -/
abbrev stalkHom (a b : R)
    (f : X ⟶ Spec (.of (CrossingQuotient R (a * b)))) (x : X) :
    CrossingQuotient R (a * b) →+* X.presheaf.stalk x :=
  (Spec.preimage (X.fromSpecStalk x ≫ f)).hom

/-- Global Cartier factorization through the actual binary nodal model.
The hypothesis is the stalkwise effective Cartier condition on the
pullback of the specified finitely generated ideal `(u,a)`. -/
theorem existsUnique_lift [X.IsGermInjective] (a b : R)
    (f : X ⟶ Spec (.of (CrossingQuotient R (a * b))))
    (hCartier : ∀ x : X, ∃ r : X.presheaf.stalk x,
      Ideal.span ({stalkHom a b f x (U (a * b)),
        stalkHom a b f x (algebraMap R _ a)} : Set (X.presheaf.stalk x)) =
        Ideal.span ({r} : Set (X.presheaf.stalk x)) ∧
      r ∈ nonZeroDivisors (X.presheaf.stalk x)) :
    ∃! l : X ⟶ Model a b, l ≫ toNode a b = f := by
  apply PhilipponStalkwiseLift.existsUnique_lift f (toNode a b)
  intro x
  obtain ⟨r, hI, hr⟩ := hCartier x
  have h := PhilipponNodeCartierModelLift.existsUnique_model_lift a b
    (stalkHom a b f x) r hI hr
  simpa only [stalkHom, CommRingCat.ofHom_hom, Spec.map_preimage,
    CommRingCat.of_carrier] using h

end PhilipponNodeCartierGlobalLift

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient
open PhilipponNodeFactorCharts PhilipponNodeFactorGluing PhilipponNodeCartierGlobalLift


namespace PhilipponNodeCartierCenter

variable {R : Type u} [CommRing R] {X W : Scheme.{u}}

/-- Stalkwise effective Cartier condition on the pullback of `(u,a)`. -/
def At (a b : R) (f : X ⟶ Spec (.of (CrossingQuotient R (a * b)))) (x : X) : Prop :=
  ∃ r : X.presheaf.stalk x,
    Ideal.span ({stalkHom a b f x (U (a * b)),
      stalkHom a b f x (algebraMap R _ a)} : Set (X.presheaf.stalk x)) =
      Ideal.span ({r} : Set (X.presheaf.stalk x)) ∧
    r ∈ nonZeroDivisors (X.presheaf.stalk x)

lemma stalkHom_comp (a b : R)
    (f : X ⟶ Spec (.of (CrossingQuotient R (a * b)))) (p : W ⟶ X) (x : W) :
    (p.stalkMap x).hom.comp (stalkHom a b f (p x)) = stalkHom a b (p ≫ f) x := by
  have key : Spec.map (CommRingCat.ofHom
      ((p.stalkMap x).hom.comp (stalkHom a b f (p x)))) =
      Spec.map (CommRingCat.ofHom (stalkHom a b (p ≫ f) x)) := by
    rw [PhilipponCrossingPointHom.specMap_comp]
    simp only [stalkHom, CommRingCat.ofHom_hom, Spec.map_preimage]
    rw [← Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk, Category.assoc]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)

lemma of_open (a b : R)
    (f : X ⟶ Spec (.of (CrossingQuotient R (a * b))))
    (p : W ⟶ X) [IsOpenImmersion p] (x : W) (h : At a b (p ≫ f) x) :
    At a b f (p x) := by
  obtain ⟨r, hI, hr⟩ := h
  let e := (asIso (p.stalkMap x)).commRingCatIsoToRingEquiv
  have hψ (z : CrossingQuotient R (a * b)) :
      e (stalkHom a b f (p x) z) = stalkHom a b (p ≫ f) x z :=
    DFunLike.congr_fun (stalkHom_comp a b f p x) z
  refine ⟨e.symm r, ?_, ?_⟩
  · have hm := congrArg (Ideal.map e.symm.toRingHom) hI
    simp only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton] at hm
    change Ideal.span {e.symm (stalkHom a b (p ≫ f) x (U (a * b))),
      e.symm (stalkHom a b (p ≫ f) x (algebraMap R _ a))} =
      Ideal.span {e.symm r} at hm
    simpa only [← hψ, RingEquiv.symm_apply_apply] using hm
  · rw [← MulEquivClass.map_nonZeroDivisors e.symm]
    exact ⟨r, hr, rfl⟩

lemma regular_map_of_flat {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Flat) {r : A} (hr : r ∈ nonZeroDivisors A) :
    φ r ∈ nonZeroDivisors B := by
  letI := φ.toAlgebra
  haveI : Module.Flat A B := hφ
  rw [mem_nonZeroDivisors_iff_left]
  intro x hx
  apply (Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B) hr)
  simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_zero] using hx

/-- The actual Cartier center is preserved by flat source base change. -/
lemma pullback_of_flat (a b : R)
    (f : X ⟶ Spec (.of (CrossingQuotient R (a * b))))
    (p : W ⟶ X) [Flat p] (x : W) (h : At a b f (p x)) :
    At a b (p ≫ f) x := by
  obtain ⟨r, hI, hr⟩ := h
  let φ : X.presheaf.stalk (p x) →+* W.presheaf.stalk x := (p.stalkMap x).hom
  have hψ (z : CrossingQuotient R (a * b)) :
      φ (stalkHom a b f (p x) z) = stalkHom a b (p ≫ f) x z :=
    DFunLike.congr_fun (stalkHom_comp a b f p x) z
  refine ⟨φ r, ?_, ?_⟩
  · have hm := congrArg (Ideal.map φ) hI
    simpa only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton, hψ] using hm
  · exact regular_map_of_flat φ (((Flat.iff_flat_stalkMap p).mp inferInstance) x) hr

set_option backward.isDefEq.respectTransparency false in
lemma stalkHom_SpecMap (a b : R) {A : Type u} [CommRing A]
    (φ : CrossingQuotient R (a * b) →+* A) (x : PrimeSpectrum A) :
    stalkHom a b (Spec.map (CommRingCat.ofHom φ)) x =
      (StructureSheaf.toStalk A x).hom.comp φ := by
  change (Spec.preimage ((Spec (.of A)).fromSpecStalk x ≫
    Spec.map (CommRingCat.ofHom φ))).hom = _
  rw [Spec.fromSpecStalk_eq', ← Spec.map_comp, Spec.preimage_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma at_specMap_of_regular_generator (a b : R) {A : Type u} [CommRing A]
    (φ : CrossingQuotient R (a * b) →+* A) (r : A)
    (hI : Ideal.span ({φ (U (a * b)), φ (algebraMap R _ a)} : Set A) =
      Ideal.span ({r} : Set A)) (hr : r ∈ nonZeroDivisors A) (x : PrimeSpectrum A) :
    At a b (Spec.map (CommRingCat.ofHom φ)) x := by
  let ρ : A →+* (Spec (.of A)).presheaf.stalk x := (StructureSheaf.toStalk A x).hom
  refine ⟨ρ r, ?_, ?_⟩
  · rw [stalkHom_SpecMap]
    change Ideal.span {ρ (φ (U (a * b))), ρ (φ (algebraMap R _ a))} =
      Ideal.span {ρ r}
    have hm := congrArg (Ideal.map ρ) hI
    simpa only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton,
      RingHom.comp_apply] using hm
  · change algebraMap A ((Spec.structureSheaf A).presheaf.stalk x) r ∈
      nonZeroDivisors ((Spec.structureSheaf A).presheaf.stalk x)
    exact IsLocalization.nonZeroDivisors_le_comap x.asIdeal.primeCompl
      ((Spec.structureSheaf A).presheaf.stalk x) hr

lemma on_left (a b : R) (hu : U a ∈ nonZeroDivisors (CrossingQuotient R a))
    (x : LeftChart a) : At a b (chartMapLeft a b) x := by
  apply at_specMap_of_regular_generator a b (toLeft a b).toRingHom (U a) _ hu x
  change Ideal.span {toLeft a b (U (a * b)), toLeft a b (algebraMap R _ a)} = _
  rw [toLeft_U, AlgHom.commutes]
  exact Ideal.span_pair_eq_span_left_iff_dvd.mpr ⟨V a, (U_mul_V a).symm⟩

lemma on_right (a b : R)
    (ha : algebraMap R (CrossingQuotient R b) a ∈ nonZeroDivisors (CrossingQuotient R b))
    (x : RightChart b) : At a b (chartMapRight a b) x := by
  apply at_specMap_of_regular_generator a b (toRight a b).toRingHom
    (algebraMap R (CrossingQuotient R b) a) _ ha x
  change Ideal.span {toRight a b (U (a * b)), toRight a b (algebraMap R _ a)} = _
  rw [toRight_U, AlgHom.commutes]
  exact Ideal.span_pair_eq_span_right_iff_dvd.mpr ⟨U b, rfl⟩

theorem on_model (a b : R)
    (hu : U a ∈ nonZeroDivisors (CrossingQuotient R a))
    (ha : algebraMap R (CrossingQuotient R b) a ∈ nonZeroDivisors (CrossingQuotient R b)) :
    ∀ x : Model a b, At a b (toNode a b) x := by
  intro x
  rcases ι_jointly_surjective a b x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · apply of_open a b (toNode a b) (ιLeft a b) y
    simpa only [ιLeft_toNode] using on_left a b hu y
  · apply of_open a b (toNode a b) (ιRight a b) y
    simpa only [ιRight_toNode] using on_right a b ha y

end PhilipponNodeCartierCenter

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial MvPolynomial.CrossingQuotient


namespace PhilipponCrossingRegular

variable {R : Type u} [CommRing R]

lemma C_regular {σ : Type*} {a : R} (ha : a ∈ nonZeroDivisors R) :
    C a ∈ nonZeroDivisors (MvPolynomial σ R) := by
  rw [mem_nonZeroDivisors_iff_left]
  intro p hp
  ext m
  apply (mem_nonZeroDivisors_iff_left.mp ha)
  simpa only [coeff_C_mul, coeff_zero] using congrArg (coeff m) hp

/-- The nodal relation is regular over any coefficient ring, including a
quotient coefficient ring with zero divisors. -/
lemma relation_regular (t : R) :
    (X 0 * X 1 - C t : MvPolynomial (Fin 2) R) ∈
      nonZeroDivisors (MvPolynomial (Fin 2) R) := by
  nontriviality R
  let e := MvPolynomial.finSuccEquiv R 1
  have he : e (X 0 * X 1 - C t) =
      Polynomial.C (X (0 : Fin 1)) * Polynomial.X + Polynomial.C (-C t) := by
    simp only [e, map_sub, map_mul, finSuccEquiv_X_zero,
      show (1 : Fin 2) = (0 : Fin 1).succ from rfl, finSuccEquiv_X_succ]
    rw [finSuccEquiv_apply, eval₂Hom_C]
    simp only [RingHom.comp_apply, map_neg]
    ring
  have hreg : e (X 0 * X 1 - C t) ∈
      nonZeroDivisors (Polynomial (MvPolynomial (Fin 1) R)) := by
    rw [he]
    apply Polynomial.mem_nonZeroDivisors_of_leadingCoeff
    rw [Polynomial.leadingCoeff_linear (MvPolynomial.X_ne_zero (0 : Fin 1))]
    exact (MvPolynomial.isRegular_X).mem_nonZeroDivisors
  rw [mem_nonZeroDivisors_iff_left]
  intro p hp
  apply e.injective
  apply (mem_nonZeroDivisors_iff_left.mp hreg)
  rw [← map_mul, hp, map_zero]

lemma coefficient_regular_of_kernel (t : R) {a : R} (ha : a ∈ nonZeroDivisors R)
    {S : Type u} [CommRing S] (ρ : R →+* S) (hρa : ρ a = 0)
    (hker : ∀ z : R, ρ z = 0 → a ∣ z) :
    algebraMap R (CrossingQuotient R t) a ∈ nonZeroDivisors (CrossingQuotient R t) := by
  rw [mem_nonZeroDivisors_iff_left]
  intro x hx
  obtain ⟨p, rfl⟩ := mk_surjective t x
  have hmem : C a * p ∈ Ideal.span ({X 0 * X 1 - C t} : Set (MvPolynomial (Fin 2) R)) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change mk t (C a * p) = 0
    rw [map_mul, show mk t (C a) = algebraMap R _ a from (mk t).commutes a]
    exact hx
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hmem
  let f : MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 2) S := MvPolynomial.map ρ
  have hfa : f (C a : MvPolynomial (Fin 2) R) = 0 := by
    simp only [f, MvPolynomial.map_C, hρa, map_zero]
  have hfrel : f (X 0 * X 1 - C t) =
      (X 0 * X 1 - C (ρ t) : MvPolynomial (Fin 2) S) := by
    simp only [map_sub, map_mul, f, MvPolynomial.map_X, MvPolynomial.map_C]
  have hfq : f q = 0 := by
    have h := congrArg f hq
    have hz : (X 0 * X 1 - C (ρ t) : MvPolynomial (Fin 2) S) * f q = 0 := by
      simpa only [map_mul, hfrel, hfa, zero_mul] using h.symm
    exact (mem_nonZeroDivisors_iff_left.mp (relation_regular (ρ t))) (f q) hz
  have hdiv : C a ∣ q := by
    apply (MvPolynomial.C_dvd_iff_dvd_coeff a q).mpr
    intro m
    apply hker
    have h := congrArg (coeff m) hfq
    simpa only [f, MvPolynomial.coeff_map, coeff_zero] using h
  obtain ⟨k, hk⟩ := hdiv
  have hp : p = (X 0 * X 1 - C t) * k := by
    apply sub_eq_zero.mp
    apply (mem_nonZeroDivisors_iff_left.mp (C_regular (σ := Fin 2) ha))
    calc
      C a * (p - (X 0 * X 1 - C t) * k) =
          C a * p - (X 0 * X 1 - C t) * (C a * k) := by ring
      _ = 0 := by rw [← hk, ← hq, sub_self]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.mem_span_singleton.mpr ⟨k, hp⟩

/-- A regular coefficient stays regular in the nodal quotient. -/
theorem coefficient_regular (t : R) {a : R} (ha : a ∈ nonZeroDivisors R) :
    algebraMap R (CrossingQuotient R t) a ∈ nonZeroDivisors (CrossingQuotient R t) := by
  apply coefficient_regular_of_kernel t ha (Ideal.Quotient.mk (Ideal.span {a}))
  · exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  · intro z hz
    exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)

theorem U_regular (t : R) (ht : t ∈ nonZeroDivisors R) :
    U t ∈ nonZeroDivisors (CrossingQuotient R t) := by
  have h := coefficient_regular t ht
  rw [← U_mul_V] at h
  exact (mul_mem_nonZeroDivisors.mp h).1

theorem V_regular (t : R) (ht : t ∈ nonZeroDivisors R) :
    V t ∈ nonZeroDivisors (CrossingQuotient R t) := by
  have h := coefficient_regular t ht
  rw [← U_mul_V] at h
  exact (mul_mem_nonZeroDivisors.mp h).2

end PhilipponCrossingRegular

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient
open PhilipponNodeFactorGluing


namespace PhilipponNodeCartierFactorization

variable {R : Type u} [CommRing R]

/-- The actual two-chart nodal model makes `(u,a)` an effective Cartier ideal
whenever `a` is regular in the coefficient ring; no assumption on `b` is needed. -/
theorem center_cartier (a b : R) (ha : a ∈ nonZeroDivisors R) :
    ∀ x : Model a b, PhilipponNodeCartierCenter.At a b (toNode a b) x :=
  PhilipponNodeCartierCenter.on_model a b (PhilipponCrossingRegular.U_regular a ha)
    (PhilipponCrossingRegular.coefficient_regular b ha)

/-- The Cartier factorization through the actual model is unique on the
whole source, hence independent of affine-chart choices. -/
theorem existsUnique_lift {X : Scheme.{u}} [X.IsGermInjective] (a b : R)
    (f : X ⟶ Spec (.of (CrossingQuotient R (a * b))))
    (h : ∀ x : X, PhilipponNodeCartierCenter.At a b f x) :
    ∃! l : X ⟶ Model a b, l ≫ toNode a b = f :=
  PhilipponNodeCartierGlobalLift.existsUnique_lift a b f h

end PhilipponNodeCartierFactorization

end

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open MvPolynomial MvPolynomial.CrossingQuotient
namespace PhilipponNodeFactorInvertU
open PhilipponNodeFactorCharts
variable {R : Type u} [CommRing R]
abbrev UChart (c : R) := Localization.Away (U c)

lemma chart_ext_of_unit_U {c : R} {A : Type*} [CommRing A] [Algebra R A]
    {f g : CrossingQuotient R c →ₐ[R] A} (hU : f (U c) = g (U c))
    (hunit : IsUnit (f (U c))) : f = g := by
  apply chart_ext hU
  apply hunit.mul_left_cancel
  calc f (U c) * f (V c) = f (algebraMap R _ c) := by rw [← map_mul, U_mul_V]
    _ = g (algebraMap R _ c) := by rw [f.commutes, g.commutes]
    _ = g (U c) * g (V c) := by rw [← map_mul, U_mul_V]
    _ = f (U c) * g (V c) := by rw [hU]

def inverseChart (a b : R) : CrossingQuotient R a →ₐ[R] UChart (a * b) :=
  lift a (algebraMap (CrossingQuotient R (a * b)) _ (U (a * b)))
    (algebraMap R _ a * IsLocalization.Away.invSelf (U (a * b))) (by
      rw [mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one])

lemma forward_isUnit (a b : R) : IsUnit
    (((IsScalarTower.toAlgHom R (CrossingQuotient R a) (UChart a)).comp (toLeft a b)).toRingHom
      (U (a * b))) := by
  change IsUnit (algebraMap (CrossingQuotient R a) (UChart a) (toLeft a b (U (a * b))))
  rw [toLeft_U]
  exact IsLocalization.Away.algebraMap_isUnit (U a)

lemma backward_isUnit (a b : R) : IsUnit ((inverseChart a b).toRingHom (U a)) := by
  change IsUnit (inverseChart a b (U a))
  rw [inverseChart, lift_U]
  exact IsLocalization.Away.algebraMap_isUnit (U (a * b))

def forwardRing (a b : R) : UChart (a * b) →+* UChart a :=
  IsLocalization.Away.lift (U (a * b)) (forward_isUnit a b)

def backwardRing (a b : R) : UChart a →+* UChart (a * b) :=
  IsLocalization.Away.lift (U a) (backward_isUnit a b)

lemma forwardRing_algebraMap (a b : R) (x : CrossingQuotient R (a * b)) :
    forwardRing a b (algebraMap _ _ x) = algebraMap (CrossingQuotient R a) (UChart a) (toLeft a b x) :=
  IsLocalization.Away.lift_eq _ (forward_isUnit a b) x
lemma backwardRing_algebraMap (a b : R) (x : CrossingQuotient R a) :
    backwardRing a b (algebraMap _ _ x) = inverseChart a b x :=
  IsLocalization.Away.lift_eq _ (backward_isUnit a b) x

def forward (a b : R) : UChart (a * b) →ₐ[R] UChart a :=
  { forwardRing a b with
    commutes' := fun r => by
      change forwardRing a b (algebraMap R (UChart (a * b)) r) = _
      rw [IsScalarTower.algebraMap_apply R (CrossingQuotient R (a * b)) (UChart (a * b)) r,
        forwardRing_algebraMap, AlgHom.commutes,
        ← IsScalarTower.algebraMap_apply R (CrossingQuotient R a) (UChart a) r] }

def backward (a b : R) : UChart a →ₐ[R] UChart (a * b) :=
  { backwardRing a b with
    commutes' := fun r => by
      change backwardRing a b (algebraMap R (UChart a) r) = _
      rw [IsScalarTower.algebraMap_apply R (CrossingQuotient R a) (UChart a) r,
        backwardRing_algebraMap]
      exact (inverseChart a b).commutes r }

@[simp] lemma forward_algebraMap (a b : R) (x : CrossingQuotient R (a * b)) :
    forward a b (algebraMap _ _ x) = algebraMap (CrossingQuotient R a) (UChart a) (toLeft a b x) :=
  forwardRing_algebraMap a b x
@[simp] lemma backward_algebraMap (a b : R) (x : CrossingQuotient R a) :
    backward a b (algebraMap _ _ x) = inverseChart a b x :=
  backwardRing_algebraMap a b x

lemma backward_forward (a b : R) : (backward a b).comp (forward a b) = AlgHom.id R (UChart (a * b)) := by
  have h : ((backward a b).comp (forward a b)).comp
      (IsScalarTower.toAlgHom R (CrossingQuotient R (a * b)) (UChart (a * b))) =
      IsScalarTower.toAlgHom R (CrossingQuotient R (a * b)) (UChart (a * b)) := by
    apply chart_ext_of_unit_U
    · simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', forward_algebraMap,
        toLeft_U, backward_algebraMap, inverseChart, lift_U]
    · change IsUnit (backward a b (forward a b (algebraMap _ _ (U (a * b)))))
      rw [forward_algebraMap, toLeft_U, backward_algebraMap, inverseChart, lift_U]
      exact IsLocalization.Away.algebraMap_isUnit (U (a * b))
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (U (a * b))) (S := UChart (a * b))
  exact RingHom.ext (fun x => congrArg (fun f : CrossingQuotient R (a * b) →ₐ[R] UChart (a * b) => f x) h)

lemma forward_backward (a b : R) : (forward a b).comp (backward a b) = AlgHom.id R (UChart a) := by
  have h : ((forward a b).comp (backward a b)).comp
      (IsScalarTower.toAlgHom R (CrossingQuotient R a) (UChart a)) =
      IsScalarTower.toAlgHom R (CrossingQuotient R a) (UChart a) := by
    apply chart_ext_of_unit_U
    · simp only [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', backward_algebraMap,
        inverseChart, lift_U, forward_algebraMap, toLeft_U]
    · change IsUnit (forward a b (backward a b (algebraMap _ _ (U a))))
      rw [backward_algebraMap, inverseChart, lift_U, forward_algebraMap, toLeft_U]
      exact IsLocalization.Away.algebraMap_isUnit (U a)
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (U a)) (S := UChart a)
  exact RingHom.ext (fun x => congrArg (fun f : CrossingQuotient R a →ₐ[R] UChart a => f x) h)

def equiv (a b : R) : UChart (a * b) ≃ₐ[R] UChart a :=
  AlgEquiv.ofAlgHom (forward a b) (backward a b) (forward_backward a b) (backward_forward a b)
end PhilipponNodeFactorInvertU
end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 10000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open MvPolynomial MvPolynomial.CrossingQuotient
open AlgebraicGeometry CategoryTheory

namespace PhilipponUnitNode
variable (R : Type u) [CommRing R]

abbrev L := Localization.Away (Polynomial.X : Polynomial R)

def coeff : R →+* L R :=
  (algebraMap (Polynomial R) (L R)).comp Polynomial.C

def toLoc : CrossingQuotient R 1 →+* L R :=
  PhilipponCrossingPointHom.pointHom 1 (coeff R)
    (algebraMap (Polynomial R) (L R) Polynomial.X)
    (IsLocalization.Away.invSelf Polynomial.X) (by
      rw [IsLocalization.Away.mul_invSelf, map_one])

lemma U_unit : IsUnit (U (1 : R)) :=
  IsUnit.of_mul_eq_one_right (V (1 : R)) (by rw [mul_comm, U_mul_V, map_one])

def polyMap : Polynomial R →+* CrossingQuotient R 1 :=
  Polynomial.eval₂RingHom (algebraMap R _) (U (1 : R))

def fromLoc : L R →+* CrossingQuotient R 1 :=
  IsLocalization.Away.lift Polynomial.X
    (show IsUnit (polyMap R Polynomial.X) by simpa [polyMap] using U_unit R)

lemma fromLoc_algebraMap (p : Polynomial R) :
    fromLoc R (algebraMap (Polynomial R) (L R) p) = polyMap R p :=
  IsLocalization.Away.lift_eq _ _ p

@[simp] lemma fromLoc_coeff (r : R) :
    fromLoc R (coeff R r) = algebraMap R _ r := by
  change fromLoc R (algebraMap (Polynomial R) (L R) (Polynomial.C r)) = _
  rw [fromLoc_algebraMap]
  simp [polyMap]

@[simp] lemma fromLoc_X :
    fromLoc R (algebraMap (Polynomial R) (L R) Polynomial.X) = U (1 : R) := by
  rw [fromLoc_algebraMap]
  simp [polyMap]

@[simp] lemma toLoc_coeff (r : R) :
    toLoc R (algebraMap R _ r) = coeff R r :=
  PhilipponCrossingPointHom.pointHom_algebraMap _ _ _ _ _ _

@[simp] lemma toLoc_U :
    toLoc R (U (1 : R)) = algebraMap (Polynomial R) (L R) Polynomial.X :=
  PhilipponCrossingPointHom.pointHom_U _ _ _ _ _

@[simp] lemma toLoc_V :
    toLoc R (V (1 : R)) = IsLocalization.Away.invSelf (Polynomial.X : Polynomial R) :=
  PhilipponCrossingPointHom.pointHom_V _ _ _ _ _

lemma from_to : (fromLoc R).comp (toLoc R) = RingHom.id _ := by
  apply PhilipponCrossingPointHom.ringHom_ext
  · intro r
    simp
  · simp
  · change fromLoc R (toLoc R (V (1 : R))) = V (1 : R)
    apply (U_unit R).mul_left_cancel
    calc U (1 : R) * fromLoc R (toLoc R (V (1 : R))) =
        fromLoc R (toLoc R (U (1 : R))) * fromLoc R (toLoc R (V (1 : R))) := by simp
      _ = fromLoc R (toLoc R (U (1 : R) * V (1 : R))) := by rw [map_mul, map_mul]
      _ = 1 := by simp only [U_mul_V, map_one]
      _ = U (1 : R) * V (1 : R) := by simpa using (U_mul_V (1 : R)).symm

lemma to_from : (toLoc R).comp (fromLoc R) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial R)) (S := L R)
  apply Polynomial.ringHom_ext
  · intro r
    change toLoc R (fromLoc R (coeff R r)) = coeff R r
    simp
  · change toLoc R (fromLoc R (algebraMap (Polynomial R) (L R) Polynomial.X)) = _
    simp

def equiv : CrossingQuotient R 1 ≃+* L R :=
  RingEquiv.ofRingHom (toLoc R) (fromLoc R) (to_from R) (from_to R)

def specIso : Spec (.of (CrossingQuotient R 1)) ≅ Spec (.of (L R)) :=
  Scheme.Spec.mapIso (equiv R).symm.toCommRingCatIso.op

lemma specIso_over :
    (specIso R).hom ≫ Spec.map (CommRingCat.ofHom (coeff R)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (CrossingQuotient R 1))) := by
  change Spec.map (CommRingCat.ofHom (fromLoc R)) ≫ _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (fromLoc_coeff R))

instance loc_smooth : Smooth (Spec.map (CommRingCat.ofHom (coeff R))) := by
  have : Algebra.Smooth R (Polynomial R) := ⟨inferInstance, inferInstance⟩
  have : Smooth (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R) (L R)))) :=
    IsOpenImmersion.of_isLocalization Polynomial.X
  dsimp only [coeff]
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  infer_instance

instance node_smooth : Smooth (Spec.map (CommRingCat.ofHom
    (algebraMap R (CrossingQuotient R 1)))) := by
  rw [← specIso_over]
  infer_instance

variable [IsDomain R]

instance loc_domain : IsDomain (L R) :=
  IsLocalization.Away.isDomain _ (Polynomial.X_ne_zero (R := R))

instance node_domain : IsDomain (CrossingQuotient R 1) :=
  MulEquiv.isDomain (L R) (equiv R).toMulEquiv

end PhilipponUnitNode

end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open MvPolynomial MvPolynomial.CrossingQuotient


namespace PhilipponCrossingDomain

variable {R : Type u} [CommRing R] [IsDomain R]
open PhilipponNodeFactorInvertU

def chartCongr {s t : R} (h : s = t) : UChart s ≃ₐ[R] UChart t := by
  subst t
  exact AlgEquiv.refl

/-- Every nonzero nodal equation over a coefficient domain has an integral
coordinate ring, by embedding in its Laurent U-chart. -/
theorem isDomain (t : R) (ht : t ≠ 0) : IsDomain (CrossingQuotient R t) := by
  haveI : IsDomain (UChart (1 : R)) := IsLocalization.Away.isDomain _
    (PhilipponUnitNode.U_unit R).ne_zero
  let e : UChart t ≃ₐ[R] UChart (1 : R) :=
    (chartCongr (one_mul t).symm).trans (PhilipponNodeFactorInvertU.equiv (1 : R) t)
  haveI : IsDomain (UChart t) := MulEquiv.isDomain (UChart (1 : R)) e.toMulEquiv
  have hU : U t ∈ nonZeroDivisors (CrossingQuotient R t) :=
    PhilipponCrossingRegular.U_regular t (mem_nonZeroDivisors_iff_ne_zero.mpr ht)
  have hinj := IsLocalization.injective (UChart t) (Submonoid.powers_le.mpr hU)
  exact Function.Injective.isDomain (algebraMap (CrossingQuotient R t) (UChart t)) hinj

end PhilipponCrossingDomain

end

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace PhilipponTwoOpenChartIntegral
variable {L R X : Scheme.{u}} (i : L ⟶ X) (j : R ⟶ X)
  [IsOpenImmersion i] [IsOpenImmersion j]
  (hcover : ∀ x : X, (∃ y, i y = x) ∨ ∃ y, j y = x)

def cover : X.OpenCover where
  I₀ := Bool
  X b := if b then R else L
  f b := match b with | false => i | true => j
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun b => ?_⟩
    · rcases hcover x with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    · cases b <;> infer_instance

include i j hcover

lemma smooth_of_charts {T : Scheme.{u}} (p : X ⟶ T) [Smooth (i ≫ p)] [Smooth (j ≫ p)] :
    Smooth p := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth) (cover i j hcover)]
  intro b
  change Bool at b
  cases b
  · exact inferInstanceAs (Smooth (i ≫ p))
  · exact inferInstanceAs (Smooth (j ≫ p))

lemma reduced_of_charts [IsReduced L] [IsReduced R] : IsReduced X := by
  haveI : ∀ b, IsReduced ((cover i j hcover).X b) := fun b => by
    change Bool at b
    cases b <;> dsimp [cover] <;> infer_instance
  exact IsReduced.of_openCover X (cover i j hcover)

lemma dense_left [IrreducibleSpace R] {O : Scheme.{u}} [Nonempty O]
    (l : O ⟶ L) (r : O ⟶ R) [IsOpenImmersion r] (hglue : l ≫ i = r ≫ j) :
    DenseRange i := by
  have hd : DenseRange r :=
    IsOpenMap.denseRange_of_isPreirreducibleSpace r r.isOpenEmbedding.isOpenMap
  have hr : Set.range j ⊆ closure (Set.range i) := by
    rintro _ ⟨y, rfl⟩
    apply (closure_minimal ?_ (isClosed_closure.preimage j.continuous)) (hd y)
    rintro _ ⟨z, rfl⟩
    have h := congrArg (fun f : O ⟶ X => f z) hglue
    change i (l z) = j (r z) at h
    change j (r z) ∈ closure (Set.range i)
    rw [← h]
    exact subset_closure ⟨_, rfl⟩
  intro x
  rcases hcover x with h | h
  · exact subset_closure h
  · exact hr h

lemma integral_of_charts [IsIntegral L] [IsIntegral R] {O : Scheme.{u}} [Nonempty O]
    (l : O ⟶ L) (r : O ⟶ R) [IsOpenImmersion r] (hglue : l ≫ i = r ≫ j) :
    IsIntegral X := by
  have hd := dense_left i j hcover l r hglue
  haveI : IsReduced X := reduced_of_charts i j hcover
  haveI : IrreducibleSpace X := by
    apply (irreducibleSpace_def X).mpr
    have h : IsIrreducible (Set.range i) := by
      simpa only [Set.image_univ] using
        (IrreducibleSpace.isIrreducible_univ L).image i i.continuous.continuousOn
    change IsIrreducible (Set.univ : Set X)
    rw [← hd.closure_range]
    exact h.closure
  exact isIntegral_of_irreducibleSpace_of_isReduced X
end PhilipponTwoOpenChartIntegral
end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient
open PhilipponNodeFactorCharts PhilipponNodeFactorGluing


namespace PhilipponNodeCartierCanonical

variable {R : Type u} [CommRing R] [IsDomain R]

theorem model_integral (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    IsIntegral (Model a b) := by
  haveI : IsDomain (CrossingQuotient R a) := PhilipponCrossingDomain.isDomain a ha
  haveI : IsDomain (CrossingQuotient R b) := PhilipponCrossingDomain.isDomain b hb
  haveI : IsDomain (LeftOverlap a) := IsLocalization.Away.isDomain _
    (nonZeroDivisors.ne_zero (PhilipponCrossingRegular.V_regular a
      (mem_nonZeroDivisors_iff_ne_zero.mpr ha)))
  haveI : Nonempty (Overlap a) := inferInstanceAs (Nonempty (PrimeSpectrum (LeftOverlap a)))
  exact PhilipponTwoOpenChartIntegral.integral_of_charts (ιLeft a b) (ιRight a b)
    (ι_jointly_surjective a b) (leftOverlapMap a) (rightOverlapMap a b) pushout.condition

/-- The actual integral nodal modification has no nontrivial endomorphism
over its node. This is the uniqueness needed for comparison cocycles. -/
theorem endomorphism_eq_id (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Model a b ⟶ Model a b) (hh : h ≫ toNode a b = toNode a b) : h = 𝟙 _ := by
  haveI : IsIntegral (Model a b) := model_integral a b ha hb
  obtain ⟨l, hl, huniq⟩ := PhilipponNodeCartierFactorization.existsUnique_lift a b
    (toNode a b) (PhilipponNodeCartierFactorization.center_cartier a b
      (mem_nonZeroDivisors_iff_ne_zero.mpr ha))
  exact (huniq h hh).trans (huniq (𝟙 _) (by simp)).symm

/-- Compatible Cartier centers determine a unique comparison isomorphism
between actual integral nodal modifications over an isomorphism of nodes. -/
theorem existsUnique_comparison {S : Type u} [CommRing S] [IsDomain S]
    (a b : R) (c d : S) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (e : Spec (.of (CrossingQuotient R (a * b))) ≅
      Spec (.of (CrossingQuotient S (c * d))))
    (h12 : ∀ x : Model a b, PhilipponNodeCartierCenter.At c d (toNode a b ≫ e.hom) x)
    (h21 : ∀ x : Model c d, PhilipponNodeCartierCenter.At a b (toNode c d ≫ e.inv) x) :
    ∃! E : Model a b ≅ Model c d, E.hom ≫ toNode c d = toNode a b ≫ e.hom := by
  haveI : IsIntegral (Model a b) := model_integral a b ha hb
  haveI : IsIntegral (Model c d) := model_integral c d hc hd
  obtain ⟨l12, hl12, huniq12⟩ := PhilipponNodeCartierFactorization.existsUnique_lift c d
    (toNode a b ≫ e.hom) h12
  obtain ⟨l21, hl21, huniq21⟩ := PhilipponNodeCartierFactorization.existsUnique_lift a b
    (toNode c d ≫ e.inv) h21
  have hleft : l12 ≫ l21 = 𝟙 _ := by
    apply endomorphism_eq_id a b ha hb
    rw [Category.assoc, hl21, ← Category.assoc, hl12, Category.assoc,
      e.hom_inv_id, Category.comp_id]
  have hright : l21 ≫ l12 = 𝟙 _ := by
    apply endomorphism_eq_id c d hc hd
    rw [Category.assoc, hl12, ← Category.assoc, hl21, Category.assoc,
      e.inv_hom_id, Category.comp_id]
  refine ⟨{hom := l12, inv := l21, hom_inv_id := hleft, inv_hom_id := hright}, hl12, ?_⟩
  intro E hE
  apply Iso.ext
  exact huniq12 E.hom hE

end PhilipponNodeCartierCanonical

end

noncomputable section

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

end

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 3000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
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
end

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 3000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
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
end

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
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
end

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
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
end

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
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

end

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient
namespace PhilipponNodeFactorOpenIso
open PhilipponNodeFactorCharts PhilipponNodeFactorGluing PhilipponNodeFactorInvertU
variable {R : Type u} [CommRing R]

def sourceOpen (a b : R) : Spec (.of (UChart a)) ⟶ Model a b :=
  Spec.map (CommRingCat.ofHom (algebraMap (CrossingQuotient R a) (UChart a))) ≫ ιLeft a b

def targetOpen (a b : R) : Spec (.of (UChart (a * b))) ⟶ Spec (.of (CrossingQuotient R (a * b))) :=
  Spec.map (CommRingCat.ofHom (algebraMap (CrossingQuotient R (a * b)) (UChart (a * b))))

def comparison (a b : R) : Spec (.of (UChart a)) ⟶ Spec (.of (UChart (a * b))) :=
  Spec.map (CommRingCat.ofHom (forwardRing a b))

instance sourceOpen_isOpenImmersion (a b : R) : IsOpenImmersion (sourceOpen a b) := by
  haveI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (CrossingQuotient R a) (UChart a)))) :=
    IsOpenImmersion.of_isLocalization (U a)
  unfold sourceOpen
  infer_instance

instance targetOpen_isOpenImmersion (a b : R) : IsOpenImmersion (targetOpen a b) :=
  IsOpenImmersion.of_isLocalization (U (a * b))

instance comparison_isIso (a b : R) : IsIso (comparison a b) := by
  haveI : IsIso (CommRingCat.ofHom (forwardRing a b)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (equiv a b).bijective
  unfold comparison
  infer_instance

lemma square (a b : R) : sourceOpen a b ≫ toNode a b = comparison a b ≫ targetOpen a b := by
  rw [sourceOpen, Category.assoc, ιLeft_toNode, chartMapLeft]
  dsimp only [comparison, targetOpen]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (fun z => (forwardRing_algebraMap a b z).symm))

lemma targetOpen_opensRange (a b : R) :
    (targetOpen a b).opensRange = PrimeSpectrum.basicOpen (U (a * b)) :=
  Scheme.Hom.opensRange_localizationAway (R := .of (CrossingQuotient R (a * b))) (U (a * b))

lemma rightOverlap_opensRange (a b : R) :
    (rightOverlapMap a b).opensRange = PrimeSpectrum.basicOpen (U b) := by
  change ((overlapIso a b).hom ≫ Spec.map (CommRingCat.ofHom
    (algebraMap (CrossingQuotient R b) (RightOverlap b)))).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact Scheme.Hom.opensRange_localizationAway (R := .of (CrossingQuotient R b)) (U b)

lemma preimage_targetOpen (a b : R) :
    toNode a b ⁻¹ᵁ (targetOpen a b).opensRange = (sourceOpen a b).opensRange := by
  have hleft (y : LeftChart a) :
      toNode a b (ιLeft a b y) ∈ (targetOpen a b).opensRange →
        ιLeft a b y ∈ (sourceOpen a b).opensRange := by
    intro hy
    change y ∈ (ιLeft a b ≫ toNode a b) ⁻¹ᵁ (targetOpen a b).opensRange at hy
    rw [ιLeft_toNode, targetOpen_opensRange] at hy
    change toLeft a b (U (a * b)) ∉ y.asIdeal at hy
    rw [toLeft_U] at hy
    have hmem : y ∈ (Spec.map (CommRingCat.ofHom
        (algebraMap (CrossingQuotient R a) (UChart a)))).opensRange := by
      rw [Scheme.Hom.opensRange_localizationAway (R := .of (CrossingQuotient R a)) (U a)]
      exact hy
    obtain ⟨z, hz⟩ := hmem
    refine ⟨z, ?_⟩
    change ιLeft a b (Spec.map (CommRingCat.ofHom
      (algebraMap (CrossingQuotient R a) (UChart a))) z) = ιLeft a b y
    exact congrArg (ιLeft a b) hz
  ext x
  constructor
  · intro hx
    rcases ι_jointly_surjective a b x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact hleft y hx
    · have hy : U b ∉ y.asIdeal := by
        change y ∈ (ιRight a b ≫ toNode a b) ⁻¹ᵁ (targetOpen a b).opensRange at hx
        rw [ιRight_toNode, targetOpen_opensRange] at hx
        change toRight a b (U (a * b)) ∉ y.asIdeal at hx
        rw [toRight_U] at hx
        intro h
        exact hx (y.asIdeal.mul_mem_left _ h)
      have hy' : y ∈ (rightOverlapMap a b).opensRange := by
        rw [rightOverlap_opensRange]
        exact hy
      obtain ⟨z, rfl⟩ := hy'
      have heq : ιRight a b (rightOverlapMap a b z) = ιLeft a b (leftOverlapMap a z) :=
        congrArg (fun f : Overlap a ⟶ Model a b => f z) pushout.condition.symm
      rw [heq] at hx ⊢
      exact hleft _ hx
  · rintro ⟨z, rfl⟩
    refine ⟨comparison a b z, ?_⟩
    exact congrArg (fun f : Spec (.of (UChart a)) ⟶ Spec (.of (CrossingQuotient R (a * b))) => f z)
      (square a b).symm

lemma isPullback (a b : R) :
    IsPullback (comparison a b) (sourceOpen a b) (targetOpen a b) (toNode a b) := by
  exact IsOpenImmersion.isPullback _ _ _ _ (square a b) (preimage_targetOpen a b)

instance pullback_isIso (a b : R) : IsIso (pullback.snd (toNode a b) (targetOpen a b)) := by
  rw [← (isPullback a b).flip.isoPullback_inv_snd]
  infer_instance

lemma isIso_morphismRestrict (a b : R) :
    IsIso (toNode a b ∣_ PrimeSpectrum.basicOpen (U (a * b))) := by
  rw [← targetOpen_opensRange a b]
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictOpensRange (toNode a b) (targetOpen a b))).mpr inferInstance
end PhilipponNodeFactorOpenIso
end

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 40000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient
attribute [local instance] MvPolynomial.gradedAlgebra


namespace PhilipponNodeCartierProjective

theorem exists_projective_modification {R : Type u} [CommRing R] [IsDomain R]
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    let N : Scheme.{u} := Spec (.of (CrossingQuotient R (a * b)))
    let Cartier : ∀ X : Scheme.{u}, (X ⟶ N) → Prop := fun X f =>
      ∀ x : X, ∃ r : X.presheaf.stalk x,
        Ideal.span ({(Spec.preimage (X.fromSpecStalk x ≫ f)).hom (U (a * b)),
          (Spec.preimage (X.fromSpecStalk x ≫ f)).hom (algebraMap R _ a)} :
          Set (X.presheaf.stalk x)) = Ideal.span ({r} : Set (X.presheaf.stalk x)) ∧
        r ∈ nonZeroDivisors (X.presheaf.stalk x)
    ∃ (Y : Scheme.{u}) (q : Y ⟶ N),
      IsIntegral Y ∧ IsProper q ∧ Surjective q ∧
      IsIso (q ∣_ PrimeSpectrum.basicOpen (U (a * b))) ∧
      (∃ e : Y ⟶ Proj (@MvPolynomial.homogeneousSubmodule (Fin (1 + 1))
          (CrossingQuotient R (a * b))
          (@CommRing.toCommSemiring (CrossingQuotient R (a * b)) inferInstance)),
        IsClosedImmersion e ∧ e ≫ ProjSpace.π (CrossingQuotient R (a * b)) 1 = q) ∧
      Cartier Y q ∧
      (∀ (X : Scheme.{u}) [X.IsGermInjective] (f : X ⟶ N),
        Cartier X f → ∃! l : X ⟶ Y, l ≫ q = f) := by
  dsimp only
  refine ⟨PhilipponNodeFactorGluing.Model a b, PhilipponNodeFactorGluing.toNode a b,
    PhilipponNodeCartierCanonical.model_integral a b ha hb,
    inferInstance, inferInstance,
    PhilipponNodeFactorOpenIso.isIso_morphismRestrict a b,
    ⟨PhilipponNodeFactorProjectiveMap.toProj a b, inferInstance,
      PhilipponNodeFactorProjectiveMap.toProj_over a b⟩,
    PhilipponNodeCartierFactorization.center_cartier a b
      (mem_nonZeroDivisors_iff_ne_zero.mpr ha), ?_⟩
  intro X hX f hf
  exact PhilipponNodeCartierFactorization.existsUnique_lift a b f hf

end PhilipponNodeCartierProjective

end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient
attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution {R : Type u} [CommRing R] [IsDomain R]
    (a b : R) (ha : a ≠ 0) (hb : b ≠ 0) :
    let N : Scheme.{u} := Spec (.of (CrossingQuotient R (a * b)))
    let Cartier : ∀ X : Scheme.{u}, (X ⟶ N) → Prop := fun X f =>
      ∀ x : X, ∃ r : X.presheaf.stalk x,
        Ideal.span ({(Spec.preimage (X.fromSpecStalk x ≫ f)).hom (U (a * b)),
          (Spec.preimage (X.fromSpecStalk x ≫ f)).hom (algebraMap R _ a)} :
          Set (X.presheaf.stalk x)) = Ideal.span ({r} : Set (X.presheaf.stalk x)) ∧
        r ∈ nonZeroDivisors (X.presheaf.stalk x)
    ∃ (Y : Scheme.{u}) (q : Y ⟶ N),
      IsIntegral Y ∧ IsProper q ∧ Surjective q ∧
      IsIso (q ∣_ PrimeSpectrum.basicOpen (U (a * b))) ∧
      (∃ e : Y ⟶ Proj (@MvPolynomial.homogeneousSubmodule (Fin (1 + 1))
          (CrossingQuotient R (a * b))
          (@CommRing.toCommSemiring (CrossingQuotient R (a * b)) inferInstance)),
        IsClosedImmersion e ∧ e ≫ ProjSpace.π (CrossingQuotient R (a * b)) 1 = q) ∧
      Cartier Y q ∧
      (∀ (X : Scheme.{u}) [X.IsGermInjective] (f : X ⟶ N),
        Cartier X f → ∃! l : X ⟶ Y, l ≫ q = f) := by
  exact PhilipponNodeCartierProjective.exists_projective_modification a b ha hb
