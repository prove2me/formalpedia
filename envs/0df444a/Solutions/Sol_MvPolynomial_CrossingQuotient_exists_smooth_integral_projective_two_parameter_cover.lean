-- Prove2me | solution 1 for MvPolynomial.CrossingQuotient.exists_smooth_integral_projective_two_parameter_cover
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-28T17:20:30.24948+00:00
-- url     : https://prove2.me/submissions/0c3ed4c5-906e-4abe-903a-ddf7e155d003

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_MvPolynomial_CrossingResolution
import Mathlib
import Theorems.Thm_MvPolynomial_CrossingQuotient_exists_projective_surjective_binary_factor_model

universe u
noncomputable section

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
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MvPolynomial MvPolynomial.CrossingQuotient
namespace PhilipponNodePolynomialParameter
variable (B : Type u) [CommRing B]
abbrev Node := CrossingQuotient (Polynomial B) Polynomial.X

def coeff : B →+* Node B :=
  (algebraMap (Polynomial B) (Node B)).comp Polynomial.C

def substitution : Polynomial B →+* MvPolynomial (Fin 2) B :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 0 * MvPolynomial.X 1)

def toPoly : Node B →+* MvPolynomial (Fin 2) B :=
  PhilipponCrossingPointHom.pointHom Polynomial.X (substitution B)
    (MvPolynomial.X 0) (MvPolynomial.X 1) (by simp [substitution])

def fromPoly : MvPolynomial (Fin 2) B →+* Node B :=
  MvPolynomial.eval₂Hom (coeff B) ![U (Polynomial.X : Polynomial B), V (Polynomial.X : Polynomial B)]

@[simp] lemma fromPoly_C (r : B) : fromPoly B (MvPolynomial.C r) = coeff B r :=
  MvPolynomial.eval₂Hom_C _ _ _
@[simp] lemma fromPoly_X₀ : fromPoly B (MvPolynomial.X 0) = U (Polynomial.X : Polynomial B) := by
  simp [fromPoly]
@[simp] lemma fromPoly_X₁ : fromPoly B (MvPolynomial.X 1) = V (Polynomial.X : Polynomial B) := by
  simp [fromPoly]

@[simp] lemma toPoly_coeff (p : Polynomial B) :
    toPoly B (algebraMap (Polynomial B) (Node B) p) = substitution B p :=
  PhilipponCrossingPointHom.pointHom_algebraMap _ _ _ _ _ _
@[simp] lemma toPoly_U : toPoly B (U (Polynomial.X : Polynomial B)) = MvPolynomial.X 0 :=
  PhilipponCrossingPointHom.pointHom_U _ _ _ _ _
@[simp] lemma toPoly_V : toPoly B (V (Polynomial.X : Polynomial B)) = MvPolynomial.X 1 :=
  PhilipponCrossingPointHom.pointHom_V _ _ _ _ _

lemma fromPoly_substitution :
    (fromPoly B).comp (substitution B) = algebraMap (Polynomial B) (Node B) := by
  apply Polynomial.ringHom_ext
  · intro r
    change fromPoly B ((Polynomial.C r).eval₂ MvPolynomial.C (MvPolynomial.X 0 * MvPolynomial.X 1)) = _
    rw [Polynomial.eval₂_C, fromPoly_C]
    rfl
  · change fromPoly B ((Polynomial.X : Polynomial B).eval₂ MvPolynomial.C
      (MvPolynomial.X 0 * MvPolynomial.X 1)) = _
    rw [Polynomial.eval₂_X, map_mul, fromPoly_X₀, fromPoly_X₁, U_mul_V]

lemma from_to : (fromPoly B).comp (toPoly B) = RingHom.id (Node B) := by
  apply PhilipponCrossingPointHom.ringHom_ext
  · intro p
    change fromPoly B (toPoly B (algebraMap (Polynomial B) (Node B) p)) = _
    rw [toPoly_coeff]
    exact RingHom.congr_fun (fromPoly_substitution B) p
  · change fromPoly B (toPoly B (U (Polynomial.X : Polynomial B))) = _
    rw [toPoly_U, fromPoly_X₀]
    rfl
  · change fromPoly B (toPoly B (V (Polynomial.X : Polynomial B))) = _
    rw [toPoly_V, fromPoly_X₁]
    rfl

lemma to_from : (toPoly B).comp (fromPoly B) = RingHom.id (MvPolynomial (Fin 2) B) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    change toPoly B (fromPoly B (MvPolynomial.C r)) = _
    rw [fromPoly_C]
    change toPoly B (algebraMap (Polynomial B) (Node B) (Polynomial.C r)) = _
    rw [toPoly_coeff]
    simp [substitution]
  · intro i
    fin_cases i
    · change toPoly B (fromPoly B (MvPolynomial.X 0)) = _
      rw [fromPoly_X₀, toPoly_U]
      rfl
    · change toPoly B (fromPoly B (MvPolynomial.X 1)) = _
      rw [fromPoly_X₁, toPoly_V]
      rfl

def equiv : Node B ≃+* MvPolynomial (Fin 2) B :=
  RingEquiv.ofRingHom (toPoly B) (fromPoly B) (to_from B) (from_to B)
end PhilipponNodePolynomialParameter

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory
open MvPolynomial MvPolynomial.CrossingQuotient
namespace PhilipponNodePolynomialParameterSmooth
open PhilipponNodePolynomialParameter
variable (B : Type u) [CommRing B]

def specIso : Spec (.of (Node B)) ≅ Spec (.of (MvPolynomial (Fin 2) B)) :=
  Scheme.Spec.mapIso (equiv B).symm.toCommRingCatIso.op

lemma specIso_over : (specIso B).hom ≫
    Spec.map (CommRingCat.ofHom (MvPolynomial.C : B →+* MvPolynomial (Fin 2) B)) =
    Spec.map (CommRingCat.ofHom (coeff B)) := by
  change Spec.map (CommRingCat.ofHom (fromPoly B)) ≫ _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (fun r => fromPoly_C B r))

instance smooth_coeff : Smooth (Spec.map (CommRingCat.ofHom (coeff B))) := by
  haveI : Algebra.Smooth B (MvPolynomial (Fin 2) B) := ⟨inferInstance, inferInstance⟩
  haveI : Smooth (Spec.map (CommRingCat.ofHom (MvPolynomial.C : B →+* MvPolynomial (Fin 2) B))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  rw [← specIso_over B]
  infer_instance

lemma smooth_of_smooth_base {T : Scheme.{u}} (p : Spec (.of B) ⟶ T) [Smooth p] :
    Smooth (Spec.map (CommRingCat.ofHom (coeff B)) ≫ p) := inferInstance
end PhilipponNodePolynomialParameterSmooth

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MvPolynomial MvPolynomial.CrossingQuotient
namespace PhilipponNodePolynomialBaseChange
open PhilipponCrossingPointHom
variable (B : Type u) [CommRing B] (b : B)
abbrev NodePoly := CrossingQuotient (Polynomial B) (Polynomial.C b)

def coeff : B →+* NodePoly B b :=
  (algebraMap (Polynomial B) (NodePoly B b)).comp Polynomial.C

def baseMap : CrossingQuotient B b →+* NodePoly B b :=
  pointHom b (coeff B b) (U (Polynomial.C b)) (V (Polynomial.C b)) (U_mul_V _)

def coefficientMap : Polynomial B →+* Polynomial (CrossingQuotient B b) :=
  Polynomial.mapRingHom (algebraMap B (CrossingQuotient B b))

@[simp] lemma coefficientMap_C (r : B) : coefficientMap B b (Polynomial.C r) =
    Polynomial.C (algebraMap B (CrossingQuotient B b) r) := by
  simp [coefficientMap, Polynomial.coe_mapRingHom]

@[simp] lemma coefficientMap_X : coefficientMap B b Polynomial.X = Polynomial.X := by
  simp [coefficientMap, Polynomial.coe_mapRingHom]

def toPoly : NodePoly B b →+* Polynomial (CrossingQuotient B b) :=
  pointHom (Polynomial.C b) (coefficientMap B b) (Polynomial.C (U b)) (Polynomial.C (V b)) (by
    rw [← map_mul, U_mul_V, coefficientMap_C])

def fromPoly : Polynomial (CrossingQuotient B b) →+* NodePoly B b :=
  Polynomial.eval₂RingHom (baseMap B b) (algebraMap (Polynomial B) (NodePoly B b) Polynomial.X)

@[simp] lemma baseMap_coeff (r : B) :
    baseMap B b (algebraMap B _ r) = coeff B b r := pointHom_algebraMap _ _ _ _ _ _
@[simp] lemma baseMap_U : baseMap B b (U b) = U (Polynomial.C b) := pointHom_U _ _ _ _ _
@[simp] lemma baseMap_V : baseMap B b (V b) = V (Polynomial.C b) := pointHom_V _ _ _ _ _
@[simp] lemma toPoly_coeff (p : Polynomial B) :
    toPoly B b (algebraMap (Polynomial B) (NodePoly B b) p) = coefficientMap B b p :=
  pointHom_algebraMap _ _ _ _ _ _
@[simp] lemma toPoly_U : toPoly B b (U (Polynomial.C b)) = Polynomial.C (U b) := pointHom_U _ _ _ _ _
@[simp] lemma toPoly_V : toPoly B b (V (Polynomial.C b)) = Polynomial.C (V b) := pointHom_V _ _ _ _ _
@[simp] lemma fromPoly_C (c : CrossingQuotient B b) : fromPoly B b (Polynomial.C c) = baseMap B b c := by
  change (Polynomial.C c).eval₂ (baseMap B b) _ = _
  rw [Polynomial.eval₂_C]
@[simp] lemma fromPoly_X : fromPoly B b Polynomial.X =
    algebraMap (Polynomial B) (NodePoly B b) Polynomial.X := by
  change Polynomial.X.eval₂ (baseMap B b) _ = _
  rw [Polynomial.eval₂_X]

lemma fromPoly_coefficientMap :
    (fromPoly B b).comp (coefficientMap B b) = algebraMap (Polynomial B) (NodePoly B b) := by
  apply Polynomial.ringHom_ext
  · intro r
    change fromPoly B b (coefficientMap B b (Polynomial.C r)) = _
    rw [coefficientMap_C, fromPoly_C, baseMap_coeff]
    rfl
  · change fromPoly B b (coefficientMap B b Polynomial.X) = _
    rw [coefficientMap_X]
    exact fromPoly_X B b

lemma toPoly_baseMap : (toPoly B b).comp (baseMap B b) =
    (@Polynomial.C (CrossingQuotient B b)
      (inferInstance : CommRing (CrossingQuotient B b)).toRing.toSemiring) := by
  apply PhilipponCrossingPointHom.ringHom_ext (R := B)
    (A := Polynomial (CrossingQuotient B b)) (s := b)
  · intro r
    change toPoly B b (baseMap B b (algebraMap B _ r)) = _
    rw [baseMap_coeff]
    change toPoly B b (algebraMap (Polynomial B) (NodePoly B b) (Polynomial.C r)) = _
    rw [toPoly_coeff]
    exact coefficientMap_C B b r
  · change toPoly B b (baseMap B b (U b)) = _
    rw [baseMap_U, toPoly_U]
  · change toPoly B b (baseMap B b (V b)) = _
    rw [baseMap_V, toPoly_V]

lemma from_to : (fromPoly B b).comp (toPoly B b) = RingHom.id (NodePoly B b) := by
  apply PhilipponCrossingPointHom.ringHom_ext
  · intro p
    change fromPoly B b (toPoly B b (algebraMap (Polynomial B) (NodePoly B b) p)) = _
    rw [toPoly_coeff]
    exact RingHom.congr_fun (fromPoly_coefficientMap B b) p
  · change fromPoly B b (toPoly B b (U (Polynomial.C b))) = _
    rw [toPoly_U, fromPoly_C, baseMap_U]
    rfl
  · change fromPoly B b (toPoly B b (V (Polynomial.C b))) = _
    rw [toPoly_V, fromPoly_C, baseMap_V]
    rfl

lemma to_from : (toPoly B b).comp (fromPoly B b) =
    RingHom.id (Polynomial (CrossingQuotient B b)) := by
  apply Polynomial.ringHom_ext
  · intro c
    change toPoly B b (fromPoly B b (Polynomial.C c)) = _
    rw [fromPoly_C]
    exact RingHom.congr_fun (toPoly_baseMap B b) c
  · change toPoly B b (fromPoly B b Polynomial.X) = _
    rw [fromPoly_X, toPoly_coeff]
    exact coefficientMap_X B b

def equiv : NodePoly B b ≃+* Polynomial (CrossingQuotient B b) :=
  RingEquiv.ofRingHom (toPoly B b) (fromPoly B b) (to_from B b) (from_to B b)
end PhilipponNodePolynomialBaseChange

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory
open MvPolynomial MvPolynomial.CrossingQuotient
namespace PhilipponNodePolynomialBaseChangeSmooth
open PhilipponNodePolynomialBaseChange
variable (B : Type u) [CommRing B] (b : B)

def specIso : Spec (.of (NodePoly B b)) ≅ Spec (.of (Polynomial (CrossingQuotient B b))) :=
  Scheme.Spec.mapIso (equiv B b).symm.toCommRingCatIso.op

lemma specIso_over : (specIso B b).hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap (CrossingQuotient B b) (Polynomial (CrossingQuotient B b)))) =
    Spec.map (CommRingCat.ofHom (baseMap B b)) := by
  change Spec.map (CommRingCat.ofHom (R := Polynomial (CrossingQuotient B b))
    (S := NodePoly B b) (fromPoly B b)) ≫ _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (fun c => fromPoly_C B b c))

instance smooth_baseMap : Smooth (Spec.map (CommRingCat.ofHom (baseMap B b))) := by
  haveI : Algebra.Smooth (CrossingQuotient B b) (Polynomial (CrossingQuotient B b)) :=
    ⟨inferInstance, inferInstance⟩
  haveI : Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap (CrossingQuotient B b) (Polynomial (CrossingQuotient B b))))) := by
    apply HasRingHomProperty.Spec_iff.mpr
    exact RingHom.smooth_algebraMap.mpr
      (inferInstance : Algebra.Smooth (CrossingQuotient B b) (Polynomial (CrossingQuotient B b)))
  rw [← specIso_over B b]
  infer_instance

lemma smooth_of_smooth_node {T : Scheme.{u}}
    (p : Spec (.of (CrossingQuotient B b)) ⟶ T) [Smooth p] :
    Smooth (Spec.map (CommRingCat.ofHom (baseMap B b)) ≫ p) := inferInstance
end PhilipponNodePolynomialBaseChangeSmooth

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
noncomputable section
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

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient
namespace PhilipponTwoParameterNodeCharts
variable (K : Type u) [CommRing K]
abbrev Base := Polynomial (Polynomial K)
abbrev a : Base K := Polynomial.X
abbrev b : Base K := Polynomial.C Polynomial.X

def baseCoeff : K →+* Base K := Polynomial.C.comp Polynomial.C

def totalCoeff (c : Base K) : K →+* CrossingQuotient (Base K) c :=
  (algebraMap (Base K) (CrossingQuotient (Base K) c)).comp (baseCoeff K)

lemma left_coeff_eq : totalCoeff K (a K) =
    (PhilipponNodePolynomialParameter.coeff (Polynomial K)).comp Polynomial.C := rfl

lemma right_coeff_eq : totalCoeff K (b K) =
    (PhilipponNodePolynomialBaseChange.baseMap (Polynomial K) Polynomial.X).comp
      (PhilipponNodePolynomialParameter.coeff K) := by
  apply RingHom.ext
  intro r
  change totalCoeff K (b K) r =
    PhilipponNodePolynomialBaseChange.baseMap (Polynomial K) Polynomial.X
      (algebraMap (Polynomial K) (PhilipponNodePolynomialParameter.Node K) (Polynomial.C r))
  rw [PhilipponNodePolynomialBaseChange.baseMap_coeff]
  rfl

instance left_smooth : Smooth (Spec.map (CommRingCat.ofHom (totalCoeff K (a K)))) := by
  haveI : Algebra.Smooth K (Polynomial K) := ⟨inferInstance, inferInstance⟩
  haveI : Smooth (Spec.map (CommRingCat.ofHom (Polynomial.C : K →+* Polynomial K))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  rw [left_coeff_eq, CommRingCat.ofHom_comp, Spec.map_comp]
  infer_instance

instance right_smooth : Smooth (Spec.map (CommRingCat.ofHom (totalCoeff K (b K)))) := by
  rw [right_coeff_eq, CommRingCat.ofHom_comp, Spec.map_comp]
  infer_instance


variable [IsDomain K]

instance inner_domain : IsDomain (PhilipponNodePolynomialParameter.Node K) :=
  MulEquiv.isDomain (MvPolynomial (Fin 2) K) (PhilipponNodePolynomialParameter.equiv K).toMulEquiv

instance left_domain : IsDomain (CrossingQuotient (Base K) (a K)) :=
  MulEquiv.isDomain (MvPolynomial (Fin 2) (Polynomial K))
    (PhilipponNodePolynomialParameter.equiv (Polynomial K)).toMulEquiv

instance right_domain : IsDomain (CrossingQuotient (Base K) (b K)) :=
  MulEquiv.isDomain (Polynomial (PhilipponNodePolynomialParameter.Node K))
    (PhilipponNodePolynomialBaseChange.equiv (Polynomial K) Polynomial.X).toMulEquiv

lemma left_V_ne_zero : V (a K) ≠ 0 := by
  intro h
  have h' := congrArg (PhilipponNodePolynomialParameter.toPoly (Polynomial K)) h
  rw [PhilipponNodePolynomialParameter.toPoly_V, map_zero] at h'
  exact (MvPolynomial.X_ne_zero (R := Polynomial K) (1 : Fin 2)) h'

instance overlap_domain : IsDomain (Localization.Away (V (a K))) :=
  IsLocalization.Away.isDomain (Localization.Away (V (a K))) (left_V_ne_zero K)


end PhilipponTwoParameterNodeCharts


set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponTwoParameterNodeCover
open PhilipponTwoParameterNodeCharts
variable (K : Type u) [CommRing K] [IsDomain K]

theorem exists_cover :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of (CrossingQuotient (Base K) (a K * b K)))),
      IsIntegral Y ∧ IsProper q ∧ Surjective q ∧
      Smooth (q ≫ Spec.map (CommRingCat.ofHom (totalCoeff K (a K * b K)))) ∧
      ∃ e : Y ⟶ Proj (@MvPolynomial.homogeneousSubmodule (Fin (1 + 1))
        (CrossingQuotient (Base K) (a K * b K))
        (@CommRing.toCommSemiring (CrossingQuotient (Base K) (a K * b K)) inferInstance)),
        IsClosedImmersion e ∧ e ≫ ProjSpace.π (CrossingQuotient (Base K) (a K * b K)) 1 = q := by
  obtain ⟨Y, q, i, j, α, β, θ, hq, hqs, hi, hj, hcover,
    _, _, _, _, _, _, hiq, hjq, hpb, e, he, heq⟩ :=
    MvPolynomial.CrossingQuotient.exists_projective_surjective_binary_factor_model (a K) (b K)
  haveI : IsOpenImmersion i := hi
  haveI : IsOpenImmersion j := hj
  let p := q ≫ Spec.map (CommRingCat.ofHom (totalCoeff K (a K * b K)))
  have hip : i ≫ p = Spec.map (CommRingCat.ofHom (totalCoeff K (a K))) := by
    rw [show i ≫ p = (i ≫ q) ≫ _ from (Category.assoc _ _ _).symm, hiq,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change α (algebraMap (Base K) _ (baseCoeff K r)) = _
    exact α.commutes _
  have hjp : j ≫ p = Spec.map (CommRingCat.ofHom (totalCoeff K (b K))) := by
    rw [show j ≫ p = (j ≫ q) ≫ _ from (Category.assoc _ _ _).symm, hjq,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change β (algebraMap (Base K) _ (baseCoeff K r)) = _
    exact β.commutes _
  haveI : Smooth (i ≫ p) := by rw [hip]; infer_instance
  haveI : Smooth (j ≫ p) := by rw [hjp]; infer_instance
  have hsm : Smooth p := PhilipponTwoOpenChartIntegral.smooth_of_charts i j hcover p
  haveI : Nonempty (Spec (.of (Localization.Away (V (a K))))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (Localization.Away (V (a K)))))
  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom θ.toRingHom)) :=
    MorphismProperty.of_isPullback hpb.flip hi
  have hint : IsIntegral Y := PhilipponTwoOpenChartIntegral.integral_of_charts i j hcover
    (Spec.map (CommRingCat.ofHom (algebraMap (CrossingQuotient (Base K) (a K))
      (Localization.Away (V (a K))))))
    (Spec.map (CommRingCat.ofHom θ.toRingHom)) hpb.w.symm
  exact ⟨Y, q, hint, hq, hqs, hsm, e, he, heq⟩
end PhilipponTwoParameterNodeCover

theorem solution (K : Type u) [CommRing K] [IsDomain K] :
    let R := Polynomial (Polynomial K)
    let s : R := Polynomial.X
    let t : R := Polynomial.C Polynomial.X
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of (CrossingQuotient R (s * t)))),
      IsIntegral Y ∧ IsProper q ∧ Surjective q ∧
      Smooth (q ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap R (CrossingQuotient R (s * t))).comp
          ((Polynomial.C : Polynomial K →+* R).comp
            (Polynomial.C : K →+* Polynomial K))))) ∧
      ∃ e : Y ⟶ Proj (@MvPolynomial.homogeneousSubmodule (Fin (1 + 1))
        (CrossingQuotient R (s * t))
        (@CommRing.toCommSemiring (CrossingQuotient R (s * t)) inferInstance)),
        IsClosedImmersion e ∧ e ≫ ProjSpace.π (CrossingQuotient R (s * t)) 1 = q := by
  exact PhilipponTwoParameterNodeCover.exists_cover K
