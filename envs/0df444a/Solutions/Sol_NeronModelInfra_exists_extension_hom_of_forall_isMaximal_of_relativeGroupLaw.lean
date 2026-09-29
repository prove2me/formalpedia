-- Prove2me | solution 1 for NeronModelInfra.exists_extension_hom_of_forall_isMaximal_of_relativeGroupLaw
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/3b68de17-7288-5c3d-86ef-10a521e404ce

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_NeronModelInfra_existsUnique_extension_of_exists_isLocalization_atPrime
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_comp_mul_eq_mul_comp_of_genericFibre
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NeronModelInfra_exists_extension_hom_of_forall_isMaximal_of_relativeGroupLaw

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    {G : Scheme.{0}} (g : G ⟶ Spec (CommRingCat.of ℤ)) [IsSeparated g] [LocallyOfFiniteType g] [Flat g]
    (L : RelativeGroupLaw ℤ g)
    (φη : SchemeHomOver (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))
      (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))))
    (hhom : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℚ))
        (x y : SchemeHomOver s (pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))))),
      NeronModelInfra.schemeHomOverComp
          ((L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))).mul s x y) φη =
        (L.baseChange (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))).mul s
          (NeronModelInfra.schemeHomOverComp x φη) (NeronModelInfra.schemeHomOverComp y φη))

    {ι' : Type} (a b : ι' → (Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ G))
    (hab : ∀ (i : ι') (z zt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
        pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))),
      z ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) = a i →
      zt ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) = b i →
      zt = z ≫ φη.1)
    (ha : ∀ i : ι', a i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))
    (hb : ∀ i : ι', b i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))))

    (h : ∀ (𝔪 : Ideal ℤ) [𝔪.IsMaximal], ∃ (A : Type) (_ : CommRing A) (_ : Algebra ℤ A)
        (_ : IsLocalization.AtPrime A 𝔪) (_ : Algebra A ℚ) (_ : IsScalarTower ℤ A ℚ)
        (gA : pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))) ⟶ G),
        gA ≫ g = pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))) ≫ g ∧
        ∀ j : pullback g (specGenericFibreInclusion ℤ ℚ) ⟶
            pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))),
          j ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))) =
            pullback.fst g (specGenericFibreInclusion ℤ ℚ) →
          j ≫ gA = φη.1 ≫ pullback.fst g (specGenericFibreInclusion ℤ ℚ)) :
    ∃ φ : SchemeHomOver g g,
      pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) ≫ φ.1 =
        φη.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) ∧
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℤ)) (x y : SchemeHomOver s g),
        NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
          L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ i : ι', b i = a i ≫ φ.1  := by

  have h' : ∀ (𝔪 : Ideal ℤ) [𝔪.IsMaximal], ∃ (A : Type) (_ : CommRing A) (iAlg : Algebra ℤ A)
      (_ : IsLocalization.AtPrime A 𝔪) (iAlgQ : Algebra A ℚ)
      (_ : @IsScalarTower ℤ A ℚ (@Algebra.toSMul ℤ A _ _ iAlg) (@Algebra.toSMul A ℚ _ _ iAlgQ)
        (@Algebra.toSMul ℤ ℚ _ _ (Ring.toIntAlgebra ℚ)))
      (gA : pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))) ⟶ G),
      gA ≫ g = pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))) ≫ g ∧
      ∀ j : pullback g (specGenericFibreInclusion ℤ ℚ) ⟶
          pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))),
        j ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ A))) =
          pullback.fst g (specGenericFibreInclusion ℤ ℚ) →
        j ≫ gA = φη.1 ≫ pullback.fst g (specGenericFibreInclusion ℤ ℚ) := by
    intro 𝔪 _
    obtain ⟨A, iA, iAlg, iLoc, iAlgQ, hst, gA, h1, h2⟩ := h 𝔪
    refine ⟨A, iA, iAlg, iLoc, iAlgQ,
      @IsScalarTower.mk ℤ A ℚ (@Algebra.toSMul ℤ A _ _ iAlg) (@Algebra.toSMul A ℚ _ _ iAlgQ)
        (@Algebra.toSMul ℤ ℚ _ _ (Ring.toIntAlgebra ℚ)) (fun r a q => ?_), gA, h1, h2⟩
    have := hst.smul_assoc r a q
    rw [zsmul_eq_mul, zsmul_eq_mul] at this
    have e1 : @algebraMap ℤ A _ _ iAlg r = r := eq_intCast _ r
    have e2 : algebraMap ℤ ℚ r = r := eq_intCast _ r
    have l1 : @HSMul.hSMul ℤ A A (@instHSMul ℤ A (@Algebra.toSMul ℤ A _ _ iAlg)) r a = (r : A) * a := by
      rw [@Algebra.smul_def ℤ A _ _ iAlg, e1]
    have l2 : ∀ t : ℚ, @HSMul.hSMul ℤ ℚ ℚ (@instHSMul ℤ ℚ (@Algebra.toSMul ℤ ℚ _ _ (Ring.toIntAlgebra ℚ))) r t =
        (r : ℚ) * t := fun t => by
      rw [Algebra.smul_def, e2]
    rw [l1, l2]
    exact this

  obtain ⟨φ, hφ, -⟩ :=
    NeronModelInfra.existsUnique_extension_of_exists_isLocalization_atPrime (R := ℤ) ℚ g g φη h'

  have hsq' : pullback.fst g (specGenericFibreInclusion ℤ ℚ) ≫ φ.1 =
      φη.1 ≫ pullback.fst g (specGenericFibreInclusion ℤ ℚ) := by
    have h1 : (genericFibreRestrict ℤ ℚ g g φ).1 ≫ pullback.fst g (specGenericFibreInclusion ℤ ℚ) =
        pullback.fst g (specGenericFibreInclusion ℤ ℚ) ≫ φ.1 := genericFibreRestrict_coe_comp_fst g g φ
    rw [hφ] at h1
    exact h1.symm
  have hsq : pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) ≫ φ.1 =
      φη.1 ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) := hsq'
  refine ⟨φ, hsq, ?_, ?_⟩
  ·
    intro T s x y
    apply Subtype.ext
    rw [NeronModelInfra.schemeHomOverComp_coe]
    refine RelativeGroupLaw.comp_mul_eq_mul_comp_of_genericFibre ℤ ℚ L L φ ?_ s x y
    intro S s' x' y'

    set X := RelativeGroupLaw.baseChangePointOfBase (specGenericFibreInclusion ℤ ℚ) x' with hX
    set Y := RelativeGroupLaw.baseChangePointOfBase (specGenericFibreInclusion ℤ ℚ) y' with hY
    have e1 : x' = RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion ℤ ℚ) X :=
      (RelativeGroupLaw.baseChangePointToBase_ofBase _ x').symm
    have e2 : y' = RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion ℤ ℚ) Y :=
      (RelativeGroupLaw.baseChangePointToBase_ofBase _ y').symm
    have eX : RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion ℤ ℚ)
        (NeronModelInfra.schemeHomOverComp X φη) =
        (⟨x'.1 ≫ φ.1, by rw [Category.assoc, φ.2, x'.2]⟩ :
          SchemeHomOver (s' ≫ specGenericFibreInclusion ℤ ℚ) g) := by
      apply Subtype.ext
      change (NeronModelInfra.schemeHomOverComp X φη).1 ≫ pullback.fst g (specGenericFibreInclusion ℤ ℚ) =
        x'.1 ≫ φ.1
      rw [NeronModelInfra.schemeHomOverComp_coe, e1, RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc,
        Category.assoc]
      congr 1
      exact hsq'.symm
    have eY : RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion ℤ ℚ)
        (NeronModelInfra.schemeHomOverComp Y φη) =
        (⟨y'.1 ≫ φ.1, by rw [Category.assoc, φ.2, y'.2]⟩ :
          SchemeHomOver (s' ≫ specGenericFibreInclusion ℤ ℚ) g) := by
      apply Subtype.ext
      change (NeronModelInfra.schemeHomOverComp Y φη).1 ≫ pullback.fst g (specGenericFibreInclusion ℤ ℚ) =
        y'.1 ≫ φ.1
      rw [NeronModelInfra.schemeHomOverComp_coe, e2, RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc,
        Category.assoc]
      congr 1
      exact hsq'.symm
    have hh : NeronModelInfra.schemeHomOverComp
        ((L.baseChange (specGenericFibreInclusion ℤ ℚ)).mul s' X Y) φη =
        (L.baseChange (specGenericFibreInclusion ℤ ℚ)).mul s'
          (NeronModelInfra.schemeHomOverComp X φη) (NeronModelInfra.schemeHomOverComp Y φη) :=
      hhom s' X Y
    calc (L.mul (s' ≫ specGenericFibreInclusion ℤ ℚ) x' y').1 ≫ φ.1
        = (RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion ℤ ℚ)
            ((L.baseChange (specGenericFibreInclusion ℤ ℚ)).mul s' X Y)).1 ≫ φ.1 := by
          rw [e1, e2, RelativeGroupLaw.baseChangePointToBase_mul]
      _ = ((L.baseChange (specGenericFibreInclusion ℤ ℚ)).mul s' X Y).1 ≫
            (φη.1 ≫ pullback.fst g (specGenericFibreInclusion ℤ ℚ)) := by
          rw [RelativeGroupLaw.baseChangePointToBase_coe, Category.assoc]
          congr 1
      _ = (NeronModelInfra.schemeHomOverComp ((L.baseChange (specGenericFibreInclusion ℤ ℚ)).mul s' X Y) φη).1 ≫
            pullback.fst g (specGenericFibreInclusion ℤ ℚ) := by
          rw [NeronModelInfra.schemeHomOverComp_coe, Category.assoc]
      _ = (RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion ℤ ℚ)
            ((L.baseChange (specGenericFibreInclusion ℤ ℚ)).mul s'
              (NeronModelInfra.schemeHomOverComp X φη) (NeronModelInfra.schemeHomOverComp Y φη))).1 := by
          rw [hh]
          rfl
      _ = (L.mul (s' ≫ specGenericFibreInclusion ℤ ℚ)
            (RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion ℤ ℚ)
              (NeronModelInfra.schemeHomOverComp X φη))
            (RelativeGroupLaw.baseChangePointToBase (specGenericFibreInclusion ℤ ℚ)
              (NeronModelInfra.schemeHomOverComp Y φη))).1 := by
          rw [RelativeGroupLaw.baseChangePointToBase_mul]
      _ = _ := by rw [eX, eY]
  ·
    intro i
    let sQ : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of ℚ) :=
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))
    have hsQ : sQ ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)) =
        Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ))) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
    let z : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
        pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) :=
      pullback.lift (a i) sQ (by rw [ha i, hsQ])
    let zt : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
        pullback g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) :=
      pullback.lift (b i) sQ (by rw [hb i, hsQ])
    have hz : z ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) = a i := pullback.lift_fst _ _ _
    have hzt : zt ≫ pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ))) = b i :=
      pullback.lift_fst _ _ _
    have h1 := hab i z zt hz hzt
    rw [← hzt, h1, Category.assoc, ← hsq, ← Category.assoc, hz]

end S_NeronModelInfra_exists_extension_hom_of_forall_isMaximal_of_relativeGroupLaw
end P2MW
export P2MW.S_NeronModelInfra_exists_extension_hom_of_forall_isMaximal_of_relativeGroupLaw (solution)
