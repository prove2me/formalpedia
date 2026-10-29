-- Prove2me | solution 1 for MvPolynomial.CrossingQuotient.exists_smooth_integral_proper_cover_of_monomial
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-29T01:41:33.713976+00:00
-- url     : https://prove2.me/submissions/4a168076-3937-4e17-bceb-ad5a8fa7e75e

import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_MvPolynomial_CrossingResolution
import Mathlib

universe u

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
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 10000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial MvPolynomial.CrossingQuotient

namespace PhilipponCrossingCoefficientEquiv
variable {R S : Type u} [CommRing R] [CommRing S]

def forward (e : R ≃+* S) (t : R) (s : S) (he : e t = s) :
    CrossingQuotient R t →+* CrossingQuotient S s :=
  PhilipponCrossingPointHom.pointHom t ((algebraMap S (CrossingQuotient S s)).comp e.toRingHom)
    (U s) (V s) (by
      rw [U_mul_V]
      exact congrArg (algebraMap S (CrossingQuotient S s)) he.symm)

def backward (e : R ≃+* S) (t : R) (s : S) (he : e t = s) :
    CrossingQuotient S s →+* CrossingQuotient R t :=
  PhilipponCrossingPointHom.pointHom s ((algebraMap R (CrossingQuotient R t)).comp e.symm.toRingHom)
    (U t) (V t) (by
      rw [U_mul_V]
      apply congrArg (algebraMap R (CrossingQuotient R t))
      exact (e.symm_apply_apply t).symm.trans (congrArg e.symm he))

@[simp] lemma forward_coeff (e : R ≃+* S) (t : R) (s : S) (he : e t = s) (r : R) :
    forward e t s he (algebraMap R _ r) = algebraMap S _ (e r) :=
  PhilipponCrossingPointHom.pointHom_algebraMap _ _ _ _ _ _

@[simp] lemma backward_coeff (e : R ≃+* S) (t : R) (s : S) (he : e t = s) (r : S) :
    backward e t s he (algebraMap S _ r) = algebraMap R _ (e.symm r) :=
  PhilipponCrossingPointHom.pointHom_algebraMap _ _ _ _ _ _

@[simp] lemma forward_U (e : R ≃+* S) (t : R) (s : S) (he : e t = s) :
    forward e t s he (U t) = U s :=
  PhilipponCrossingPointHom.pointHom_U _ _ _ _ _

@[simp] lemma forward_V (e : R ≃+* S) (t : R) (s : S) (he : e t = s) :
    forward e t s he (V t) = V s :=
  PhilipponCrossingPointHom.pointHom_V _ _ _ _ _

@[simp] lemma backward_U (e : R ≃+* S) (t : R) (s : S) (he : e t = s) :
    backward e t s he (U s) = U t :=
  PhilipponCrossingPointHom.pointHom_U _ _ _ _ _

@[simp] lemma backward_V (e : R ≃+* S) (t : R) (s : S) (he : e t = s) :
    backward e t s he (V s) = V t :=
  PhilipponCrossingPointHom.pointHom_V _ _ _ _ _

lemma backward_forward (e : R ≃+* S) (t : R) (s : S) (he : e t = s) :
    (backward e t s he).comp (forward e t s he) = RingHom.id _ := by
  apply PhilipponCrossingPointHom.ringHom_ext
  · intro r
    simp
  · simp
  · simp

lemma forward_backward (e : R ≃+* S) (t : R) (s : S) (he : e t = s) :
    (forward e t s he).comp (backward e t s he) = RingHom.id _ := by
  apply PhilipponCrossingPointHom.ringHom_ext
  · intro r
    simp
  · simp
  · simp

def equiv (e : R ≃+* S) (t : R) (s : S) (he : e t = s) :
    CrossingQuotient R t ≃+* CrossingQuotient S s :=
  RingEquiv.ofRingHom (forward e t s he) (backward e t s he)
    (forward_backward e t s he) (backward_forward e t s he)

@[simp] lemma equiv_coeff (e : R ≃+* S) (t : R) (s : S) (he : e t = s) (r : R) :
    equiv e t s he (algebraMap R _ r) = algebraMap S _ (e r) := forward_coeff e t s he r

@[simp] lemma equiv_symm_coeff (e : R ≃+* S) (t : R) (s : S) (he : e t = s) (r : S) :
    (equiv e t s he).symm (algebraMap S _ r) = algebraMap R _ (e.symm r) := backward_coeff e t s he r

@[simp] lemma equiv_U (e : R ≃+* S) (t : R) (s : S) (he : e t = s) :
    equiv e t s he (U t) = U s := forward_U e t s he

@[simp] lemma equiv_V (e : R ≃+* S) (t : R) (s : S) (he : e t = s) :
    equiv e t s he (V t) = V s := forward_V e t s he

end PhilipponCrossingCoefficientEquiv

end


noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency.types false
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
end


noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 5000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
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
end


noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponOpenSpanGluing

variable {O L R : Scheme.{u}} (l : O ⟶ L) (r : O ⟶ R)
  [IsOpenImmersion l] [IsOpenImmersion r]

abbrev Model : Scheme.{u} := pushout l r

def inl : L ⟶ Model l r := pushout.inl l r
def inr : R ⟶ Model l r := pushout.inr l r

instance inl_isOpenImmersion : IsOpenImmersion (inl l r) := by
  exact inferInstanceAs (IsOpenImmersion (colimit.ι (span l r) WalkingSpan.left))

instance inr_isOpenImmersion : IsOpenImmersion (inr l r) := by
  exact inferInstanceAs (IsOpenImmersion (colimit.ι (span l r) WalkingSpan.right))

@[reassoc]
lemma condition : l ≫ inl l r = r ≫ inr l r := pushout.condition

theorem jointly_surjective (x : Model l r) :
    (∃ y, inl l r y = x) ∨ ∃ y, inr l r y = x := by
  obtain ⟨j, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span l r) x
  rcases j with (_ | (_ | _))
  · left
    refine ⟨l y, ?_⟩
    change (l ≫ inl l r) y = x
    rw [show l ≫ inl l r = colimit.ι (span l r) WalkingSpan.zero from
      (by simpa only [inl, pushout.inl, span_map_fst, span_zero, span_left] using
        colimit.w (span l r) WalkingSpan.Hom.fst)]
    exact hy
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩

theorem overlap_isPullback : IsPullback r l (inr l r) (inl l r) := by
  apply IsOpenImmersion.isPullback
  · exact condition l r
  · ext x
    change inl l r x ∈ Set.range (inr l r) ↔ x ∈ Set.range l
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨k, fkL, fkR, z, hzL, _⟩ :=
        (Scheme.IsLocallyDirected.ι_eq_ι_iff (span l r)).mp hy.symm
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
      refine ⟨r z, ?_⟩
      exact congrArg (fun h : O ⟶ Model l r => h z) (condition l r).symm

end PhilipponOpenSpanGluing

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
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponOpenModification

theorem cartesian_restrictions
    {O L R X Y Z : Scheme.{u}}
    (l : O ⟶ L) (r : O ⟶ R) (i : L ⟶ X) (j : R ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j]
    (hX : IsPullback l r i j)
    (q : Y ⟶ R) (o : O ⟶ Y) (hO : IsPullback (𝟙 O) o r q)
    (iL : L ⟶ Z) (iY : Y ⟶ Z) [IsOpenImmersion iL] [IsOpenImmersion iY]
    (f : Z ⟶ X) (hL : iL ≫ f = i) (hY : iY ≫ f = q ≫ j)
    (hglue : l ≫ iL = o ≫ iY)
    (hcover : ∀ z : Z, (∃ x, iL x = z) ∨ ∃ y, iY y = z) :
    IsPullback (𝟙 L) iL i f ∧ IsPullback q iY j f := by
  have hpreL : f ⁻¹ᵁ i.opensRange = iL.opensRange := by
    ext z
    change (∃ x, i x = f z) ↔ ∃ x, iL x = z
    constructor
    · rintro ⟨x, hx⟩
      rcases hcover z with ⟨x', rfl⟩ | ⟨y, rfl⟩
      · exact ⟨x', rfl⟩
      · have hxy : i x = j (q y) := by
          simpa only [← Scheme.Hom.comp_apply, hY] using hx
        obtain ⟨ω, _, hrω⟩ := Scheme.exists_preimage_of_isPullback hX x (q y) hxy
        obtain ⟨ω', hid, hoω⟩ := Scheme.exists_preimage_of_isPullback hO ω y hrω
        have heq : ω' = ω := by simpa using hid
        have hoy : o ω = y := heq ▸ hoω
        refine ⟨l ω, ?_⟩
        change (l ≫ iL) ω = iY y
        rw [hglue]
        change iY (o ω) = iY y
        rw [hoy]
    · rintro ⟨x, rfl⟩
      refine ⟨x, ?_⟩
      change i x = (iL ≫ f) x
      rw [hL]
  have hpreR : f ⁻¹ᵁ j.opensRange = iY.opensRange := by
    ext z
    change (∃ x, j x = f z) ↔ ∃ y, iY y = z
    constructor
    · rintro ⟨x, hx⟩
      rcases hcover z with ⟨x', rfl⟩ | ⟨y, rfl⟩
      · have hxy : i x' = j x := by
          simpa only [← Scheme.Hom.comp_apply, hL] using hx.symm
        obtain ⟨ω, hlω, _⟩ := Scheme.exists_preimage_of_isPullback hX x' x hxy
        refine ⟨o ω, ?_⟩
        change (o ≫ iY) ω = iL x'
        rw [← hglue]
        change iL (l ω) = iL x'
        rw [hlω]
      · exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      refine ⟨q y, ?_⟩
      change (q ≫ j) y = (iY ≫ f) y
      rw [hY]
  exact ⟨IsOpenImmersion.isPullback (𝟙 L) iL i f (by simpa using hL) hpreL,
    IsOpenImmersion.isPullback q iY j f hY hpreR⟩

theorem proper_of_cartesian_charts
    {L R X Y Z : Scheme.{u}} (i : L ⟶ X) (j : R ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j]
    (hcover : ∀ x : X, (∃ y, i y = x) ∨ ∃ y, j y = x)
    (q : Y ⟶ R) [IsProper q] (f : Z ⟶ X)
    (iL : L ⟶ Z) (iY : Y ⟶ Z)
    (hL : IsPullback (𝟙 L) iL i f) (hY : IsPullback q iY j f) :
    IsProper f := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsProper) (f := f)
    (PhilipponTwoOpenChartIntegral.cover i j hcover)
  intro b
  change Bool at b
  cases b
  · change IsProper (pullback.snd f i)
    rw [← hL.flip.isoPullback_inv_snd]
    infer_instance
  · change IsProper (pullback.snd f j)
    rw [← hY.flip.isoPullback_inv_snd]
    infer_instance

theorem surjective_of_charts
    {L R X Y Z : Scheme.{u}} (i : L ⟶ X) (j : R ⟶ X)
    (hcover : ∀ x : X, (∃ y, i y = x) ∨ ∃ y, j y = x)
    (q : Y ⟶ R) [Surjective q] (f : Z ⟶ X)
    (iL : L ⟶ Z) (iY : Y ⟶ Z)
    (hL : iL ≫ f = i) (hY : iY ≫ f = q ≫ j) :
    Surjective f := by
  constructor
  intro x
  rcases hcover x with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · refine ⟨iL a, ?_⟩
    change (iL ≫ f) a = i a
    rw [hL]
  · obtain ⟨y, rfl⟩ := q.surjective b
    refine ⟨iY y, ?_⟩
    change (iY ≫ f) y = (q ≫ j) y
    rw [hY]

theorem exists_extension
    {O L R X Y : Scheme.{u}}
    (l : O ⟶ L) (r : O ⟶ R) (i : L ⟶ X) (j : R ⟶ X)
    [IsOpenImmersion l] [IsOpenImmersion r]
    [IsOpenImmersion i] [IsOpenImmersion j]
    (hX : IsPullback l r i j)
    (hcover : ∀ x : X, (∃ y, i y = x) ∨ ∃ y, j y = x)
    (q : Y ⟶ R) [IsProper q] [Surjective q]
    (o : O ⟶ Y) (hO : IsPullback (𝟙 O) o r q) :
    ∃ (Z : Scheme.{u}) (f : Z ⟶ X) (iL : L ⟶ Z) (iY : Y ⟶ Z),
      IsOpenImmersion iL ∧ IsOpenImmersion iY ∧
      (∀ z : Z, (∃ x, iL x = z) ∨ ∃ y, iY y = z) ∧
      IsPullback (𝟙 L) iL i f ∧ IsPullback q iY j f ∧
      iL ≫ f = i ∧ iY ≫ f = q ≫ j ∧ l ≫ iL = o ≫ iY ∧
      IsProper f ∧ Surjective f := by
  have : IsOpenImmersion o := MorphismProperty.of_isPullback hO inferInstance
  let Z := PhilipponOpenSpanGluing.Model l o
  let iL : L ⟶ Z := PhilipponOpenSpanGluing.inl l o
  let iY : Y ⟶ Z := PhilipponOpenSpanGluing.inr l o
  have : IsOpenImmersion iL := inferInstanceAs (IsOpenImmersion (PhilipponOpenSpanGluing.inl l o))
  have : IsOpenImmersion iY := inferInstanceAs (IsOpenImmersion (PhilipponOpenSpanGluing.inr l o))
  have hoq : o ≫ q = r := by simpa using hO.w.symm
  have hcomm : l ≫ i = o ≫ (q ≫ j) := by rw [← Category.assoc, hoq, ← hX.w]
  let f : Z ⟶ X := pushout.desc i (q ≫ j) hcomm
  have hL : iL ≫ f = i := pushout.inl_desc _ _ _
  have hY : iY ≫ f = q ≫ j := pushout.inr_desc _ _ _
  have hglue : l ≫ iL = o ≫ iY := PhilipponOpenSpanGluing.condition l o
  have hcoverZ : ∀ z : Z, (∃ x, iL x = z) ∨ ∃ y, iY y = z :=
    PhilipponOpenSpanGluing.jointly_surjective l o
  obtain ⟨hleft, hright⟩ := cartesian_restrictions l r i j hX q o hO iL iY f hL hY hglue hcoverZ
  have hproper := proper_of_cartesian_charts i j hcover q f iL iY hleft hright
  have hsurj := surjective_of_charts i j hcover q f iL iY hL hY
  exact ⟨Z, f, iL, iY, inferInstance, inferInstance, hcoverZ, hleft, hright,
    hL, hY, hglue, hproper, hsurj⟩

theorem exists_smooth_integral_extension
    {O L R X Y T : Scheme.{u}} [Nonempty O] [IsIntegral L] [IsIntegral Y]
    (l : O ⟶ L) (r : O ⟶ R) (i : L ⟶ X) (j : R ⟶ X)
    [IsOpenImmersion l] [IsOpenImmersion r]
    [IsOpenImmersion i] [IsOpenImmersion j]
    (hX : IsPullback l r i j)
    (hcover : ∀ x : X, (∃ y, i y = x) ∨ ∃ y, j y = x)
    (q : Y ⟶ R) [IsProper q] [Surjective q]
    (o : O ⟶ Y) (hO : IsPullback (𝟙 O) o r q)
    (π : X ⟶ T) [Smooth (i ≫ π)] [Smooth ((q ≫ j) ≫ π)] :
    ∃ (Z : Scheme.{u}) (f : Z ⟶ X),
      IsIntegral Z ∧ IsProper f ∧ Surjective f ∧ Smooth (f ≫ π) := by
  obtain ⟨Z, f, iL, iY, hiL, hiY, hcoverZ, _hleft, _hright,
    hL, hY, hglue, hf, hsurj⟩ := exists_extension l r i j hX hcover q o hO
  have : IsOpenImmersion iL := hiL
  have : IsOpenImmersion iY := hiY
  have : IsOpenImmersion o := MorphismProperty.of_isPullback hO inferInstance
  have hInt : IsIntegral Z :=
    PhilipponTwoOpenChartIntegral.integral_of_charts iL iY hcoverZ l o hglue
  have : Smooth (iL ≫ (f ≫ π)) := by
    simpa only [← Category.assoc, hL] using inferInstanceAs (Smooth (i ≫ π))
  have : Smooth (iY ≫ (f ≫ π)) := by
    simpa only [← Category.assoc, hY] using inferInstanceAs (Smooth ((q ≫ j) ≫ π))
  have hsmooth : Smooth (f ≫ π) :=
    PhilipponTwoOpenChartIntegral.smooth_of_charts iL iY hcoverZ (f ≫ π)
  exact ⟨Z, f, hInt, hf, hsurj, hsmooth⟩

end PhilipponOpenModification

end


noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace PhilipponOpenModificationIso

theorem pullback_isIso_of_restrict
    {Y R O : Scheme.{u}} (q : Y ⟶ R) (r : O ⟶ R) [IsOpenImmersion r]
    [IsIso (q ∣_ r.opensRange)] : IsIso (pullback.snd q r) :=
  ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictOpensRange q r)).mp inferInstance

theorem restrict_isIso_of_pullback
    {P Y R O : Scheme.{u}} (q : Y ⟶ R) (r : O ⟶ R) [IsOpenImmersion r]
    (fst : P ⟶ Y) (snd : P ⟶ O) (h : IsPullback fst snd q r) [IsIso snd] :
    IsIso (q ∣_ r.opensRange) := by
  have : IsIso (pullback.snd q r) := by
    rw [← h.isoPullback_inv_snd]
    infer_instance
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictOpensRange q r)).mpr inferInstance

theorem exists_open_lift
    {Y R O : Scheme.{u}} (q : Y ⟶ R) (r : O ⟶ R) [IsOpenImmersion r]
    [IsIso (q ∣_ r.opensRange)] :
    ∃ o : O ⟶ Y, IsOpenImmersion o ∧ o ≫ q = r ∧ IsPullback (𝟙 O) o r q := by
  have : IsIso (pullback.snd q r) := pullback_isIso_of_restrict q r
  let e : O ≅ pullback q r := (asIso (pullback.snd q r)).symm
  let o : O ⟶ Y := e.hom ≫ pullback.fst q r
  have hoq : o ≫ q = r := by
    dsimp only [o]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    simp [e]
  have hpb : IsPullback o (𝟙 O) q r :=
    IsPullback.of_iso_pullback ⟨by simpa using hoq⟩ e rfl (by simp [e])
  have : IsOpenImmersion o := MorphismProperty.of_isPullback hpb.flip inferInstance
  exact ⟨o, inferInstance, hoq, hpb.flip⟩

theorem isIso_restrict_comp
    {Z Y X : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X) (U : X.Opens)
    [IsIso (g ∣_ U)] [IsIso (f ∣_ g ⁻¹ᵁ U)] : IsIso ((f ≫ g) ∣_ U) := by
  rw [morphismRestrict_comp]
  exact inferInstanceAs (IsIso ((f ∣_ (g ⁻¹ᵁ U)) ≫ (g ∣_ U)))

theorem isIso_restrict_of_le
    {Y X : Scheme.{u}} (f : Y ⟶ X) {U V : X.Opens} (hUV : U ≤ V)
    [IsIso (f ∣_ V)] : IsIso (f ∣_ U) := by
  have heq : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U := by
    simpa only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      using inf_eq_right.mpr hUV
  have hiso : IsIso (f ∣_ V.ι ''ᵁ (V.ι ⁻¹ᵁ U)) :=
    ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U))).mp inferInstance
  rw [heq] at hiso
  exact hiso

theorem exists_extension
    {O L R X Y : Scheme.{u}}
    (l : O ⟶ L) (r : O ⟶ R) (i : L ⟶ X) (j : R ⟶ X)
    [IsOpenImmersion l] [IsOpenImmersion r]
    [IsOpenImmersion i] [IsOpenImmersion j]
    (hX : IsPullback l r i j)
    (hcover : ∀ x : X, (∃ y, i y = x) ∨ ∃ y, j y = x)
    (q : Y ⟶ R) [IsProper q] [Surjective q]
    [IsIso (q ∣_ r.opensRange)] :
    ∃ (Z : Scheme.{u}) (f : Z ⟶ X) (iL : L ⟶ Z) (iY : Y ⟶ Z),
      IsOpenImmersion iL ∧ IsOpenImmersion iY ∧
      (∀ z : Z, (∃ x, iL x = z) ∨ ∃ y, iY y = z) ∧
      IsPullback (𝟙 L) iL i f ∧ IsPullback q iY j f ∧
      iL ≫ f = i ∧ iY ≫ f = q ≫ j ∧
      IsProper f ∧ Surjective f ∧ IsIso (f ∣_ i.opensRange) := by
  obtain ⟨o, _, _, hO⟩ := exists_open_lift q r
  obtain ⟨Z, f, iL, iY, hiL, hiY, hcoverZ, hleft, hright, hL, hY, _, hf, hsurj⟩ :=
    PhilipponOpenModification.exists_extension l r i j hX hcover q o hO
  have hiso : IsIso (f ∣_ i.opensRange) :=
    restrict_isIso_of_pullback f i iL (𝟙 L) hleft.flip
  exact ⟨Z, f, iL, iY, hiL, hiY, hcoverZ, hleft, hright, hL, hY, hf, hsurj, hiso⟩

end PhilipponOpenModificationIso

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
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient

namespace PhilipponSmoothNodeFactorization
open PhilipponNodeFactorCharts PhilipponNodeFactorGluing
variable {K R : Type u} [CommRing K] [CommRing R]

abbrev Node (c : R) : Scheme.{u} := Spec (.of (CrossingQuotient R c))

def coeff (ρ : K →+* R) (c : R) : K →+* CrossingQuotient R c :=
  (algebraMap R (CrossingQuotient R c)).comp ρ

def projection (ρ : K →+* R) (c : R) : Node c ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (coeff ρ c))

lemma left_over (ρ : K →+* R) (a b : R) :
    chartMapLeft a b ≫ projection ρ (a * b) = projection ρ a := by
  dsimp only [chartMapLeft, projection]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext fun c => (toLeft a b).commutes (ρ c)

lemma right_over (ρ : K →+* R) (a b : R) :
    chartMapRight a b ≫ projection ρ (a * b) = projection ρ b := by
  dsimp only [chartMapRight, projection]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext fun c => (toRight a b).commutes (ρ c)

theorem step (ρ : K →+* R) (a b : R)
    [IsIntegral (LeftChart a)] [Nonempty (Overlap a)] [Smooth (projection ρ a)] {Y : Scheme.{u}} [IsIntegral Y]
    (q : Y ⟶ Node b) [IsProper q] [Surjective q]
    [IsIso (q ∣_ PrimeSpectrum.basicOpen (U b))]
    (hsm : Smooth (q ≫ projection ρ b)) :
    ∃ (Z : Scheme.{u}) (p : Z ⟶ Node (a * b)),
      IsIntegral Z ∧ IsProper p ∧ Surjective p ∧
      Smooth (p ≫ projection ρ (a * b)) ∧
      IsIso (p ∣_ PrimeSpectrum.basicOpen (U (a * b))) := by
  let g := toNode a b
  have : IsIso (q ∣_ (rightOverlapMap a b).opensRange) := by
    rw [PhilipponNodeFactorOpenIso.rightOverlap_opensRange]
    infer_instance
  obtain ⟨o, ho, _, hO⟩ :=
    PhilipponOpenModificationIso.exists_open_lift q (rightOverlapMap a b)
  have : IsOpenImmersion o := ho
  obtain ⟨Z, f, iL, iY, hiL, hiY, hcoverZ, hleft, _hright, hL, hY, hglue, hf, hsurj⟩ :=
    PhilipponOpenModification.exists_extension (leftOverlapMap a) (rightOverlapMap a b)
      (ιLeft a b) (ιRight a b) (overlap_isPullback a b).flip
      (ι_jointly_surjective a b) q o hO
  have : IsOpenImmersion iL := hiL
  have : IsOpenImmersion iY := hiY
  have : IsProper f := hf
  have : Surjective f := hsurj
  have hInt : IsIntegral Z :=
    PhilipponTwoOpenChartIntegral.integral_of_charts iL iY hcoverZ (leftOverlapMap a) o hglue
  let p : Z ⟶ Node (a * b) := f ≫ g
  let πM := g ≫ projection ρ (a * b)
  have hπL : ιLeft a b ≫ πM = projection ρ a := by
    dsimp only [πM, g]
    rw [← Category.assoc, ιLeft_toNode, left_over]
  have hπR : ιRight a b ≫ πM = projection ρ b := by
    dsimp only [πM, g]
    rw [← Category.assoc, ιRight_toNode, right_over]
  have : Smooth (iL ≫ (f ≫ πM)) := by
    rw [← Category.assoc, hL, hπL]
    exact inferInstanceAs (Smooth (projection ρ a))
  have : Smooth (iY ≫ (f ≫ πM)) := by
    rw [← Category.assoc, hY, Category.assoc, hπR]
    exact hsm
  have hsmooth : Smooth (p ≫ projection ρ (a * b)) := by
    simpa only [p, πM, Category.assoc] using
      PhilipponTwoOpenChartIntegral.smooth_of_charts iL iY hcoverZ (f ≫ πM)
  have : IsIso (f ∣_ (ιLeft a b).opensRange) :=
    PhilipponOpenModificationIso.restrict_isIso_of_pullback f (ιLeft a b) iL (𝟙 _) hleft.flip
  have hsub : g ⁻¹ᵁ PrimeSpectrum.basicOpen (U (a * b)) ≤ (ιLeft a b).opensRange := by
    dsimp only [g]
    rw [← PhilipponNodeFactorOpenIso.targetOpen_opensRange a b,
      PhilipponNodeFactorOpenIso.preimage_targetOpen]
    rintro x ⟨z, rfl⟩
    refine ⟨Spec.map (CommRingCat.ofHom
      (algebraMap (CrossingQuotient R a) (Localization.Away (U a)))) z, ?_⟩
    rfl
  have : IsIso (f ∣_ g ⁻¹ᵁ PrimeSpectrum.basicOpen (U (a * b))) :=
    PhilipponOpenModificationIso.isIso_restrict_of_le f hsub
  have : IsIso (g ∣_ PrimeSpectrum.basicOpen (U (a * b))) :=
    PhilipponNodeFactorOpenIso.isIso_morphismRestrict a b
  have hiso : IsIso (p ∣_ PrimeSpectrum.basicOpen (U (a * b))) :=
    PhilipponOpenModificationIso.isIso_restrict_comp f g _
  exact ⟨Z, p, hInt, inferInstance, inferInstance, hsmooth, hiso⟩


end PhilipponSmoothNodeFactorization
end


noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 20000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient

namespace PhilipponPolynomialVariableNode
variable (K : Type u) [CommRing K] (σ : Type u)

abbrev Others (i : σ) := {j : σ // j ≠ i}
abbrev B (i : σ) := MvPolynomial (Others σ i) K

def split (i : σ) : MvPolynomial σ K ≃ₐ[K] Polynomial (B K σ i) := by
  classical
  exact (MvPolynomial.renameEquiv K (Equiv.optionSubtypeNe i).symm).trans
    (MvPolynomial.optionEquivLeft K (Others σ i))

lemma split_X (i : σ) : split K σ i (X i) = Polynomial.X := by
  classical
  simp [split]

lemma split_C (i : σ) (r : K) : split K σ i (C r) = Polynomial.C (C r) := by
  change split K σ i (algebraMap K (MvPolynomial σ K) r) =
    algebraMap K (Polynomial (B K σ i)) r
  exact (split K σ i).commutes r

def nodeEquiv (i : σ) :
    CrossingQuotient (MvPolynomial σ K) (X i) ≃+* PhilipponNodePolynomialParameter.Node (B K σ i) :=
  PhilipponCrossingCoefficientEquiv.equiv (split K σ i).toRingEquiv
    (X i) Polynomial.X (split_X K σ i)

lemma nodeEquiv_coeff (i : σ) (r : K) :
    nodeEquiv K σ i (algebraMap (MvPolynomial σ K) _ (C r)) =
      algebraMap (Polynomial (B K σ i)) _ (Polynomial.C (C r)) := by
  rw [nodeEquiv, PhilipponCrossingCoefficientEquiv.equiv_coeff]
  exact congrArg (algebraMap (Polynomial (B K σ i))
    (PhilipponNodePolynomialParameter.Node (B K σ i))) (split_C K σ i r)

def targetCoeff (i : σ) : K →+* PhilipponNodePolynomialParameter.Node (B K σ i) :=
  (PhilipponNodePolynomialParameter.coeff (B K σ i)).comp (MvPolynomial.C : K →+* B K σ i)

lemma nodeEquiv_symm_coeff (i : σ) (r : K) :
    (nodeEquiv K σ i).symm (targetCoeff K σ i r) =
      algebraMap (MvPolynomial σ K) _ (C r) := by
  apply (nodeEquiv K σ i).injective
  rw [RingEquiv.apply_symm_apply, nodeEquiv_coeff]
  rfl

def specIso (i : σ) :
    Spec (.of (CrossingQuotient (MvPolynomial σ K) (X i))) ≅
      Spec (.of (PhilipponNodePolynomialParameter.Node (B K σ i))) :=
  Scheme.Spec.mapIso (nodeEquiv K σ i).symm.toCommRingCatIso.op

lemma specIso_over (i : σ) :
    (specIso K σ i).hom ≫ Spec.map (CommRingCat.ofHom (targetCoeff K σ i)) =
      PhilipponSmoothNodeFactorization.projection (MvPolynomial.C : K →+* MvPolynomial σ K) (X i) := by
  change Spec.map (CommRingCat.ofHom (nodeEquiv K σ i).symm.toRingHom) ≫ _ = _
  dsimp only [PhilipponSmoothNodeFactorization.projection]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (nodeEquiv_symm_coeff K σ i)

theorem target_smooth [Finite σ] (i : σ) :
    Smooth (Spec.map (CommRingCat.ofHom (targetCoeff K σ i))) := by
  have : Algebra.Smooth K (B K σ i) := ⟨inferInstance, inferInstance⟩
  have : Smooth (Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* B K σ i))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  dsimp only [targetCoeff]
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  infer_instance

instance node_smooth [Finite σ] (i : σ) :
    Smooth (PhilipponSmoothNodeFactorization.projection
      (MvPolynomial.C : K →+* MvPolynomial σ K) (X i)) := by
  have := target_smooth K σ i
  rw [← specIso_over]
  infer_instance

variable [IsDomain K]

instance node_domain (i : σ) : IsDomain (CrossingQuotient (MvPolynomial σ K) (X i)) :=
  MulEquiv.isDomain (MvPolynomial (Fin 2) (B K σ i))
    ((nodeEquiv K σ i).trans (PhilipponNodePolynomialParameter.equiv (B K σ i))).toMulEquiv

lemma V_ne_zero (i : σ) : V (X i : MvPolynomial σ K) ≠ 0 := by
  intro h
  have h' := congrArg (nodeEquiv K σ i) h
  rw [nodeEquiv, PhilipponCrossingCoefficientEquiv.equiv_V, map_zero] at h'
  have h'' := congrArg (PhilipponNodePolynomialParameter.toPoly (B K σ i)) h'
  rw [PhilipponNodePolynomialParameter.toPoly_V, map_zero] at h''
  exact MvPolynomial.X_ne_zero (1 : Fin 2) h''

instance overlap_domain (i : σ) :
    IsDomain (Localization.Away (V (X i : MvPolynomial σ K))) :=
  IsLocalization.Away.isDomain _ (V_ne_zero K σ i)

end PhilipponPolynomialVariableNode

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
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient

namespace PhilipponMonomialNodeCover
variable (K : Type u) [CommRing K] [IsDomain K] (σ : Type u) [Finite σ]

abbrev R := MvPolynomial σ K

def product (word : List σ) : R K σ := (word.map MvPolynomial.X).prod

instance polynomial_smooth : Smooth (Spec.map (CommRingCat.ofHom
    (MvPolynomial.C : K →+* R K σ))) := by
  have : Algebra.Smooth K (R K σ) := ⟨inferInstance, inferInstance⟩
  exact HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)

instance unit_smooth : Smooth (PhilipponSmoothNodeFactorization.projection
    (MvPolynomial.C : K →+* R K σ) 1) := by
  dsimp only [PhilipponSmoothNodeFactorization.projection, PhilipponSmoothNodeFactorization.coeff]
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  infer_instance

theorem exists_cover (word : List σ) :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ PhilipponSmoothNodeFactorization.Node (product K σ word)),
      IsIntegral Y ∧ IsProper q ∧ Surjective q ∧
      Smooth (q ≫ PhilipponSmoothNodeFactorization.projection
        (MvPolynomial.C : K →+* R K σ) (product K σ word)) ∧
      IsIso (q ∣_ PrimeSpectrum.basicOpen (U (product K σ word))) := by
  induction word with
  | nil =>
    change ∃ (Y : Scheme.{u}) (q : Y ⟶ PhilipponSmoothNodeFactorization.Node (1 : R K σ)),
      IsIntegral Y ∧ IsProper q ∧ Surjective q ∧
      Smooth (q ≫ PhilipponSmoothNodeFactorization.projection
        (MvPolynomial.C : K →+* R K σ) 1) ∧
      IsIso (q ∣_ PrimeSpectrum.basicOpen (U (1 : R K σ)))
    refine ⟨PhilipponSmoothNodeFactorization.Node (1 : R K σ), 𝟙 _,
      inferInstance, inferInstance, inferInstance, ?_, inferInstance⟩
    simpa only [Category.id_comp] using inferInstanceAs (Smooth
      (PhilipponSmoothNodeFactorization.projection (MvPolynomial.C : K →+* R K σ) 1))
  | cons i word ih =>
    obtain ⟨Y, q, hY, hq, hqs, hsm, hi⟩ := ih
    have : IsIntegral Y := hY
    have : IsProper q := hq
    have : Surjective q := hqs
    have : IsIso (q ∣_ PrimeSpectrum.basicOpen (U (product K σ word))) := hi
    have : Nonempty (PhilipponNodeFactorGluing.Overlap (X i : R K σ)) :=
      inferInstanceAs (Nonempty (PrimeSpectrum (Localization.Away (V (X i : R K σ)))))
    have hprod : product K σ (i :: word) = X i * product K σ word := by
      simp [product]
    rw [hprod]
    exact PhilipponSmoothNodeFactorization.step (MvPolynomial.C : K →+* R K σ)
      (X i) (product K σ word) q hsm

def exponentWord (d : σ →₀ ℕ) : List σ := by
  classical
  exact d.support.toList.flatMap fun i => List.replicate (d i) i

lemma product_replicates (d : σ →₀ ℕ) (s : List σ) :
    product K σ (s.flatMap fun i => List.replicate (d i) i) =
      (s.map fun i => (X i : R K σ) ^ d i).prod := by
  induction s with
  | nil => simp [product]
  | cons i s ih =>
    have h : product K σ ((i :: s).flatMap fun j => List.replicate (d j) j) =
        (X i : R K σ) ^ d i * product K σ (s.flatMap fun j => List.replicate (d j) j) := by
      simp [product, List.prod_replicate]
    rw [h, ih]
    rfl

lemma product_exponentWord (d : σ →₀ ℕ) :
    product K σ (exponentWord σ d) = MvPolynomial.monomial d (1 : K) := by
  classical
  dsimp only [exponentWord]
  rw [product_replicates, Finset.prod_map_toList]
  exact MvPolynomial.prod_X_pow_eq_monomial

theorem exists_monomial_cover (d : σ →₀ ℕ) :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ PhilipponSmoothNodeFactorization.Node (monomial d (1 : K))),
      IsIntegral Y ∧ IsProper q ∧ Surjective q ∧
      Smooth (q ≫ PhilipponSmoothNodeFactorization.projection
        (MvPolynomial.C : K →+* R K σ) (monomial d (1 : K))) ∧
      IsIso (q ∣_ PrimeSpectrum.basicOpen (U (monomial d (1 : K)))) := by
  have h := exists_cover K σ (exponentWord σ d)
  rw [product_exponentWord] at h
  exact h

end PhilipponMonomialNodeCover

end


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MvPolynomial MvPolynomial.CrossingQuotient

theorem solution
    (K : Type u) [CommRing K] [IsDomain K] (σ : Type u) [Finite σ] (d : σ →₀ ℕ) :
    let R := MvPolynomial σ K
    let c : R := MvPolynomial.monomial d 1
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of (CrossingQuotient R c))),
      IsIntegral Y ∧ IsProper q ∧ Surjective q ∧
      Smooth (q ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap R (CrossingQuotient R c)).comp (MvPolynomial.C : K →+* R)))) ∧
      IsIso (q ∣_ PrimeSpectrum.basicOpen (U c)) := by
  exact PhilipponMonomialNodeCover.exists_monomial_cover K σ d
