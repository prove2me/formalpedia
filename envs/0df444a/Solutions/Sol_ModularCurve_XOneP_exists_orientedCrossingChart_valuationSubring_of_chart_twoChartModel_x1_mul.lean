-- Prove2me | solution 1 for ModularCurve.XOneP.exists_orientedCrossingChart_valuationSubring_of_chart_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/22e64854-c9cd-510c-a4d2-e4517e475e50

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_WeilDatum
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Theorems.Thm_MvPolynomial_CrossingQuotient_exists_algEquiv_tensorProduct_apply_U_and_apply_V
import Theorems.Thm_ValuationSubring_eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_orientedCrossingChart_valuationSubring_of_chart_twoChartModel_x1_mul

p2m_attr_erase "instance" "IsScalarTower.of_algHom"
attribute [scoped instance 10000] SubalgebraClass.toAlgebra

set_option autoImplicit false

p2m_open "MvPolynomial CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

open IsLocalRing
open TensorProduct

private theorem map_stalkMap_maximalIdeal_eq_of_formallyUnramified
    {X Y : Scheme.{0}} (f : X ⟶ Y) (x : X)
    (hft : (f.stalkMap x).hom.EssFiniteType) (hfu : (f.stalkMap x).hom.FormallyUnramified) :
    Ideal.map (f.stalkMap x).hom (maximalIdeal (Y.presheaf.stalk (f.base x))) = maximalIdeal (X.presheaf.stalk x) := by
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact hft
  have : Algebra.FormallyUnramified (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := by
    rw [← RingHom.formallyUnramified_algebraMap, RingHom.algebraMap_toAlgebra]
    exact hfu
  exact Algebra.FormallyUnramified.map_maximalIdeal

namespace R4Alg

theorem crossing_bc (O : Type) [CommRing O] (A : Type) [CommRing A] [Algebra O A] (tO : O) (tA : A)
    (ht : algebraMap O A tO = tA) :
    ∃ (φ : CrossingQuotient A tA →+* CrossingQuotient O tO ⊗[O] A) (ψ : CrossingQuotient O tO ⊗[O] A →+* CrossingQuotient A tA),
      φ.comp ψ = RingHom.id _ ∧ ψ.comp φ = RingHom.id _ ∧
      φ (CrossingQuotient.U tA) = Algebra.TensorProduct.includeLeftRingHom (CrossingQuotient.U tO) ∧
      φ (CrossingQuotient.V tA) = Algebra.TensorProduct.includeLeftRingHom (CrossingQuotient.V tO) ∧
      (∀ a : A, ψ ((1 : CrossingQuotient O tO) ⊗ₜ[O] a) = algebraMap A (CrossingQuotient A tA) a) ∧
      φ.comp (algebraMap A (CrossingQuotient A tA)) =
        AlgHom.toRingHom (Algebra.TensorProduct.includeRight (R := O) (A := CrossingQuotient O tO) (B := A)) ∧
      (∀ o : O, ψ (algebraMap O (CrossingQuotient O tO) o ⊗ₜ[O] (1 : A)) = algebraMap O (CrossingQuotient A tA) o) := by
  obtain ⟨ecq, hecqU, hecqV⟩ := MvPolynomial.CrossingQuotient.exists_algEquiv_tensorProduct_apply_U_and_apply_V O tO A tA ht
  let φ : CrossingQuotient A tA →+* CrossingQuotient O tO ⊗[O] A :=
    (Algebra.TensorProduct.comm O A (CrossingQuotient O tO)).toRingEquiv.toRingHom.comp ecq.toRingEquiv.toRingHom
  let ψ : CrossingQuotient O tO ⊗[O] A →+* CrossingQuotient A tA :=
    ecq.symm.toRingEquiv.toRingHom.comp (Algebra.TensorProduct.comm O A (CrossingQuotient O tO)).symm.toRingEquiv.toRingHom
  have hψR : ∀ a : A, ψ ((1 : CrossingQuotient O tO) ⊗ₜ[O] a) = algebraMap A (CrossingQuotient A tA) a := by
    intro a
    show ecq.symm ((Algebra.TensorProduct.comm O A (CrossingQuotient O tO)).symm (1 ⊗ₜ a)) = _
    rw [Algebra.TensorProduct.comm_symm_tmul,
      show (a ⊗ₜ[O] (1 : CrossingQuotient O tO) : A ⊗[O] CrossingQuotient O tO) = algebraMap A (A ⊗[O] CrossingQuotient O tO) a by
        rw [Algebra.TensorProduct.algebraMap_apply]; rfl,
      AlgEquiv.commutes]
  refine ⟨φ, ψ, ?_, ?_, ?_, ?_, hψR, ?_, ?_⟩
  · refine RingHom.ext fun x => ?_
    show (Algebra.TensorProduct.comm O A (CrossingQuotient O tO)) (ecq (ecq.symm ((Algebra.TensorProduct.comm O A (CrossingQuotient O tO)).symm x))) = x
    rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  · refine RingHom.ext fun x => ?_
    show ecq.symm ((Algebra.TensorProduct.comm O A (CrossingQuotient O tO)).symm ((Algebra.TensorProduct.comm O A (CrossingQuotient O tO)) (ecq x))) = x
    rw [AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]
  · show (Algebra.TensorProduct.comm O A (CrossingQuotient O tO)) (ecq (CrossingQuotient.U tA)) = _
    rw [hecqU, Algebra.TensorProduct.comm_tmul]; rfl
  · show (Algebra.TensorProduct.comm O A (CrossingQuotient O tO)) (ecq (CrossingQuotient.V tA)) = _
    rw [hecqV, Algebra.TensorProduct.comm_tmul]; rfl
  · ext a
    show (Algebra.TensorProduct.comm O A (CrossingQuotient O tO)) (ecq (algebraMap A _ a)) = 1 ⊗ₜ a
    rw [ecq.commutes, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.comm_tmul]; rfl
  · intro o
    have h1 : (algebraMap O (CrossingQuotient O tO) o ⊗ₜ[O] (1 : A)) = (1 : CrossingQuotient O tO) ⊗ₜ[O] algebraMap O A o := by
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one]
    rw [h1, hψR, ← IsScalarTower.algebraMap_apply]

theorem equivariance (O : Type) [CommRing O] (A : Type) [CommRing A] [Algebra O A] (tO : O) (tA : A)
    (ψ : CrossingQuotient O tO ⊗[O] A →+* CrossingQuotient A tA)
    (hψO : ∀ o : O, ψ (algebraMap O (CrossingQuotient O tO) o ⊗ₜ[O] (1 : A)) = algebraMap O (CrossingQuotient A tA) o)
    (hψU : ψ (Algebra.TensorProduct.includeLeftRingHom (CrossingQuotient.U tO)) = CrossingQuotient.U tA)
    (hψV : ψ (Algebra.TensorProduct.includeLeftRingHom (CrossingQuotient.V tO)) = CrossingQuotient.V tA)
    (hψR : ∀ a : A, ψ ((1 : CrossingQuotient O tO) ⊗ₜ[O] a) = algebraMap A (CrossingQuotient A tA) a)
    (σ : A →+* A) (hσ : ∀ o : O, σ (algebraMap O A o) = algebraMap O A o)
    (x' y' : A) (hxy : x' * y' = algebraMap A A tA) (hxy' : σ x' * σ y' = algebraMap A A tA) :
    σ.comp ((CrossingQuotient.lift (t := tA) x' y' hxy).toRingHom.comp (ψ.comp
        (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := CrossingQuotient O tO) (B := A)))) =
      (CrossingQuotient.lift (t := tA) (σ x') (σ y') hxy').toRingHom.comp (ψ.comp
        (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := CrossingQuotient O tO) (B := A))) ∧
    (CrossingQuotient.lift (t := tA) (σ x') (σ y') hxy').toRingHom.comp (ψ.comp
        (AlgHom.toRingHom (Algebra.TensorProduct.includeRight (R := O) (A := CrossingQuotient O tO) (B := A)))) = RingHom.id _ := by
  let σo : A →ₐ[O] A := { σ with commutes' := hσ }
  let ψo : CrossingQuotient O tO ⊗[O] A →ₐ[O] CrossingQuotient A tA :=
    { ψ with commutes' := fun o => by change ψ (algebraMap O _ o) = algebraMap O _ o; rw [Algebra.TensorProduct.algebraMap_apply]; exact hψO o }
  let Lo : CrossingQuotient A tA →ₐ[O] A := (CrossingQuotient.lift (t := tA) x' y' hxy).restrictScalars O
  let Lo' : CrossingQuotient A tA →ₐ[O] A := (CrossingQuotient.lift (t := tA) (σ x') (σ y') hxy').restrictScalars O
  have key : σo.comp (Lo.comp (ψo.comp (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := CrossingQuotient O tO) (B := A)))) =
      Lo'.comp (ψo.comp (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := CrossingQuotient O tO) (B := A))) := by
    apply CrossingQuotient.algHom_ext_chart
    · show σ (CrossingQuotient.lift _ x' y' hxy (ψ (Algebra.TensorProduct.includeLeftRingHom (CrossingQuotient.U tO)))) =
        CrossingQuotient.lift _ (σ x') (σ y') hxy' (ψ (Algebra.TensorProduct.includeLeftRingHom (CrossingQuotient.U tO)))
      rw [hψU, CrossingQuotient.lift_U, CrossingQuotient.lift_U]
    · show σ (CrossingQuotient.lift _ x' y' hxy (ψ (Algebra.TensorProduct.includeLeftRingHom (CrossingQuotient.V tO)))) =
        CrossingQuotient.lift _ (σ x') (σ y') hxy' (ψ (Algebra.TensorProduct.includeLeftRingHom (CrossingQuotient.V tO)))
      rw [hψV, CrossingQuotient.lift_V, CrossingQuotient.lift_V]
  refine ⟨congrArg AlgHom.toRingHom key, ?_⟩
  refine RingHom.ext fun a => ?_
  show CrossingQuotient.lift _ (σ x') (σ y') hxy' (ψ ((1 : CrossingQuotient O tO) ⊗ₜ[O] a)) = a
  rw [hψR, AlgHom.commutes]; rfl

theorem equivariance_geom
    {T B : Scheme.{0}} (cB : T ⟶ B)
    (O : Type) [CommRing O] (A : Type) [CommRing A] [Algebra O A]
    (ρA : Spec (CommRingCat.of A) ⟶ B) (ρO' : Spec (CommRingCat.of O) ⟶ B)
    (tO : O) (tA : A)
    (φ : CrossingQuotient A tA →+* CrossingQuotient O tO ⊗[O] A) (ψ : CrossingQuotient O tO ⊗[O] A →+* CrossingQuotient A tA)
    (hφψ : φ.comp ψ = RingHom.id _) (hψφ : ψ.comp φ = RingHom.id _)
    (hφU : φ (CrossingQuotient.U tA) = Algebra.TensorProduct.includeLeftRingHom (CrossingQuotient.U tO))
    (hφV : φ (CrossingQuotient.V tA) = Algebra.TensorProduct.includeLeftRingHom (CrossingQuotient.V tO))
    (hψR : ∀ a : A, ψ ((1 : CrossingQuotient O tO) ⊗ₜ[O] a) = algebraMap A (CrossingQuotient A tA) a)
    (hψO : ∀ o : O, ψ (algebraMap O (CrossingQuotient O tO) o ⊗ₜ[O] (1 : A)) = algebraMap O (CrossingQuotient A tA) o)
    (pr : pullback cB ρA ⟶ pullback cB ρO')
    (hpr₁ : pr ≫ pullback.fst _ _ = pullback.fst _ _)
    (hpr₂ : pr ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap O A)))
    (U₀ : (pullback cB ρO').Opens) (U : (pullback cB ρA).Opens)
    (g₁ : (U : Scheme.{0}) ⟶ (U₀ : Scheme.{0})) (hg₁ : g₁ ≫ U₀.ι = U.ι ≫ pr)
    (f₀ : (U₀ : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme tO)
    (h : (U : Scheme.{0}) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O tO))))
      (Spec.map (CommRingCat.ofHom (algebraMap O A))))
    (hh₁ : h ≫ pullback.fst _ _ = g₁ ≫ f₀) (hh₂ : h ≫ pullback.snd _ _ = U.ι ≫ pullback.snd _ _)
    (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme tA)
    (hf' : f = (h ≫ (pullbackSpecIso O (CrossingQuotient O tO) A).hom) ≫ Spec.map (CommRingCat.ofHom φ))
    (σ : A →+* A) (hσ : ∀ o : O, σ (algebraMap O A o) = algebraMap O A o)
    (x' y' : A) (hxy : x' * y' = algebraMap A A tA) (hxy' : σ x' * σ y' = algebraMap A A tA)
    (sU sU' : Spec (CommRingCat.of A) ⟶ (U : Scheme.{0}))
    (hsU : sU ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _) (hsU' : sU' ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _)
    (hsU'₁ : sU' ≫ U.ι ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom σ) ≫ sU ≫ U.ι ≫ pullback.fst _ _)
    (hfs : sU ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := tA) x' y' hxy).toRingHom)) :
    sU' ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := tA) (σ x') (σ y') hxy').toRingHom) := by
  let sφ : Spec (CommRingCat.of (CrossingQuotient O tO ⊗[O] A)) ⟶ CrossingQuotient.crossingScheme tA := Spec.map (CommRingCat.ofHom φ)
  let sψ : CrossingQuotient.crossingScheme tA ⟶ Spec (CommRingCat.of (CrossingQuotient O tO ⊗[O] A)) := Spec.map (CommRingCat.ofHom ψ)
  have hσι : σ.comp (algebraMap O A) = algebraMap O A := RingHom.ext hσ

  have hφψ' : sφ ≫ sψ = 𝟙 _ := by
    simp only [sφ, sψ, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφψ, CommRingCat.ofHom_id, Spec.map_id]
  have hψφ' : sψ ≫ sφ = 𝟙 _ := by
    simp only [sφ, sψ, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψφ, CommRingCat.ofHom_id, Spec.map_id]

  have hsec : sU' ≫ g₁ = Spec.map (CommRingCat.ofHom σ) ≫ sU ≫ g₁ := by
    apply (cancel_mono U₀.ι).mp
    simp only [Category.assoc, hg₁]
    apply pullback.hom_ext
    · simp only [Category.assoc, hpr₁]
      exact hsU'₁
    · simp only [Category.assoc, hpr₂]
      rw [reassoc_of% hsU', reassoc_of% hsU, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hσι]

  have hsUh : sU ≫ h = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := tA) x' y' hxy).toRingHom) ≫ sψ ≫ (pullbackSpecIso O (CrossingQuotient O tO) A).inv := by
    have e5 := congrArg (· ≫ sψ ≫ (pullbackSpecIso O (CrossingQuotient O tO) A).inv) hfs
    simp only [hf', Category.assoc] at e5
    rw [reassoc_of% hφψ', Iso.hom_inv_id, Category.comp_id] at e5
    exact e5

  have hψU : ψ (Algebra.TensorProduct.includeLeftRingHom (CrossingQuotient.U tO)) = CrossingQuotient.U tA := by
    rw [← hφU]; exact congrFun (congrArg DFunLike.coe hψφ) _
  have hψV : ψ (Algebra.TensorProduct.includeLeftRingHom (CrossingQuotient.V tO)) = CrossingQuotient.V tA := by
    rw [← hφV]; exact congrFun (congrArg DFunLike.coe hψφ) _

  obtain ⟨keyR, keyR₂⟩ := R4Alg.equivariance O A tO tA ψ hψO hψU hψV hψR σ hσ x' y' hxy hxy'

  have hsU'h : sU' ≫ h = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := tA) (σ x') (σ y') hxy').toRingHom) ≫ sψ ≫ (pullbackSpecIso O (CrossingQuotient O tO) A).inv := by
    apply pullback.hom_ext
    · rw [Category.assoc, hh₁, ← Category.assoc, hsec, Category.assoc, Category.assoc, ← hh₁, reassoc_of% hsUh]
      simp only [sψ, Category.assoc]
      erw [pullbackSpecIso_inv_fst]
      simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [keyR]
    · rw [Category.assoc, hh₂, hsU']
      simp only [sψ, Category.assoc]
      erw [pullbackSpecIso_inv_snd]
      simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [← Spec.map_id, ← CommRingCat.ofHom_id]
      congr 2
      refine (RingHom.ext fun a => ?_).symm
      show CrossingQuotient.lift _ (σ x') (σ y') hxy' (ψ ((1 : CrossingQuotient O tO) ⊗ₜ[O] a)) = a
      rw [hψR, AlgHom.commutes]; rfl

  rw [hf']
  simp only [Category.assoc]
  rw [reassoc_of% hsU'h]
  simp only [Iso.inv_hom_id_assoc]
  rw [hψφ', Category.comp_id]

end R4Alg

private theorem residueFieldMap_surjective_of_isClosedImmersion {X Y : Scheme.{0}} (g : X ⟶ Y)
    [IsClosedImmersion g] (x : X) : Function.Surjective (g.residueFieldMap x).hom := by
  have hc : Function.Surjective ((Y.residue (g.base x)) ≫ g.residueFieldMap x).hom := by
    rw [Scheme.residue_residueFieldMap]
    exact (X.residue_surjective x).comp (g.stalkMap_surjective x)
  rw [CommRingCat.hom_comp, RingHom.coe_comp] at hc
  exact Function.Surjective.of_comp hc

private theorem residueFieldMap_surjective_of_comp {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z) (x : X)
    (hab : Function.Surjective ((a ≫ b).residueFieldMap x).hom) :
    Function.Surjective (a.residueFieldMap x).hom := by
  rw [Scheme.residueFieldMap_comp] at hab
  intro c
  obtain ⟨d, hd⟩ := hab c
  exact ⟨(b.residueFieldMap (a.base x)).hom d, hd⟩

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ) (hπk : Function.Surjective πk)

    (bc : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom πk))

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ρO : A →+* O)
    (ι : O →+* ↥Pl) (hι : ι.comp ρO = ρ) (hιinj : Function.Injective ι)
    (hιloc : ∀ o : O, ι o ∈ IsLocalRing.maximalIdeal ↥Pl ↔ o ∈ IsLocalRing.maximalIdeal O)
    (hιsurj : Function.Surjective (fun o : O => πk (ι o)))
    (hιfix : ∀ τ : ↥(Pl.decompositionSubgroup ℚ), τ ∈ Pl.inertiaSubgroup ℚ →
      (∀ l : L, (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
      ∀ o : O, τ • (ι o) = ι o)

    (bcO : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)))
    (hbcO₁ : bcO ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbcO₂ : bcO ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (πk.comp ι)))

    (ν : ↥(pullback i₁.1 i₂.1))
    (e : ℕ) (he : 1 ≤ e) (U₀ : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))).Opens)
    (hxU₀ : (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bcO).base ν ∈ U₀)
    (f₀ : (U₀ : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme ((ρO ϖ) ^ e))
    (hover₀ : f₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O ((ρO ϖ) ^ e)))) = U₀.ι ≫ pullback.snd _ _)
    (hfib₀ : (∀ y : ↥(U₀ : Scheme.{0}),
            (CrossingQuotient.U ((ρO ϖ) ^ e) ∈ (f₀.base y).asIdeal ∧ CrossingQuotient.V ((ρO ϖ) ^ e) ∈ (f₀.base y).asIdeal) ↔
            U₀.ι.base y = (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bcO).base ν))
    (hpt₀ : (∀ y : ↥(U₀ : Scheme.{0}), U₀.ι.base y = (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bcO).base ν →
            (f₀.stalkMap y).hom.Flat ∧
            Ideal.map (f₀.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
            IsIso (f₀.residueFieldMap y)))
    (het₀ : (∀ y : ↥(U₀ : Scheme.{0}), U₀.ι.base y = (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bcO).base ν →
            ∃ V : (U₀ : Scheme.{0}).Opens, y ∈ V ∧ Etale (V.ι ≫ f₀)))
    (hor₁ : (∀ y : ↥(U₀ : Scheme.{0}), CrossingQuotient.V ((ρO ϖ) ^ e) ∈ (f₀.base y).asIdeal → U₀.ι.base y ∈ Set.range (i₁.1 ≫ bcO).base))
    (hor₂ : (∀ y : ↥(U₀ : Scheme.{0}), CrossingQuotient.U ((ρO ϖ) ^ e) ∈ (f₀.base y).asIdeal → U₀.ι.base y ∈ Set.range (i₂.1 ≫ bcO).base))
    (hor₃ : (∀ y : ↥(U₀ : Scheme.{0}), U₀.ι.base y ∈ Set.range (i₁.1 ≫ bcO).base → CrossingQuotient.V ((ρO ϖ) ^ e) ∈ (f₀.base y).asIdeal))
    (hor₄ : (∀ y : ↥(U₀ : Scheme.{0}), U₀.ι.base y ∈ Set.range (i₂.1 ≫ bcO).base → CrossingQuotient.U ((ρO ϖ) ^ e) ∈ (f₀.base y).asIdeal))
    :
      ∃ (U : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ))).Opens)
        (_ : (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base ν ∈ U)
        (f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme ((ρ ϖ) ^ e)),

        f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥Pl (CrossingQuotient ↥Pl ((ρ ϖ) ^ e)))) =
            U.ι ≫ pullback.snd _ _ ∧

        (∀ y : ↥(U : Scheme.{0}),
            (CrossingQuotient.U ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal ∧
              CrossingQuotient.V ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal) ↔
            U.ι.base y = (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base ν) ∧

        (∀ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base ν →
            (f.stalkMap y).hom.Flat ∧
            Ideal.map (f.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
            IsIso (f.residueFieldMap y)) ∧

        (∃ W : (U : Scheme.{0}).Opens,
          (∃ y : ↥(U : Scheme.{0}), U.ι.base y = (pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base ν ∧ y ∈ W) ∧
          AlgebraicGeometry.Etale (W.ι ≫ f)) ∧

        (∀ (τ : ↥(Pl.decompositionSubgroup ℚ)), τ ∈ Pl.inertiaSubgroup ℚ →
          (∀ l : L, (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (algebraMap L (AlgebraicClosure ℚ) l) = algebraMap L (AlgebraicClosure ℚ) l) →
          ∀ (x' y' : ↥Pl) (hxy : x' * y' = algebraMap ↥Pl ↥Pl ((ρ ϖ) ^ e))
            (hxy' : (MulSemiringAction.toRingHom _ (↥Pl) τ) x' * (MulSemiringAction.toRingHom _ (↥Pl) τ) y' =
              algebraMap ↥Pl ↥Pl ((ρ ϖ) ^ e))
            (sU sU' : Spec (CommRingCat.of ↥Pl) ⟶ (U : Scheme.{0})),
            sU ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ → sU' ≫ U.ι ≫ pullback.snd _ _ = 𝟙 _ →
            sU' ≫ U.ι ≫ pullback.fst _ _ =
              Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom _ (↥Pl) τ)) ≫ sU ≫ U.ι ≫ pullback.fst _ _ →
            sU ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := (ρ ϖ) ^ e) x' y' hxy).toRingHom) →
            sU' ≫ f = Spec.map (CommRingCat.ofHom (CrossingQuotient.lift (t := (ρ ϖ) ^ e)
              ((MulSemiringAction.toRingHom _ (↥Pl) τ) x') ((MulSemiringAction.toRingHom _ (↥Pl) τ) y') hxy').toRingHom)) ∧

        (∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal →
            U.ι.base y ∈ Set.range (i₁.1 ≫ bc).base) ∧
        (∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal →
            U.ι.base y ∈ Set.range (i₂.1 ≫ bc).base) ∧

        (∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (i₁.1 ≫ bc).base →
            CrossingQuotient.V ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal) ∧
        (∀ y : ↥(U : Scheme.{0}), U.ι.base y ∈ Set.range (i₂.1 ≫ bc).base →
            CrossingQuotient.U ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal) := by
  classical
  have hAlgkO : (πk.comp ι).comp ρO = algebraMap A k := by
    rw [RingHom.comp_assoc, hι, ← hAlgk]
  have hkerπ : RingHom.ker πk = IsLocalRing.maximalIdeal ↥Pl :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective πk hπk)
  have hbotk : ∀ q : PrimeSpectrum k, q.asIdeal = ⊥ := by
    intro q; ext x; simp only [Ideal.mem_bot]; constructor
    · intro hx; by_contra h0; exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (IsUnit.mk0 x h0))
    · rintro rfl; exact Ideal.zero_mem _
  have hπkpt : (Spec.map (CommRingCat.ofHom πk)).base (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint ↥Pl := by
    apply PrimeSpectrum.ext
    rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal]
    show Ideal.comap πk (IsLocalRing.closedPoint k).asIdeal = IsLocalRing.maximalIdeal ↥Pl
    rw [hbotk, ← RingHom.ker_eq_comap_bot, hkerπ]

  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : Spec (CommRingCat.of k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k),
      t ≫ pullback.snd _ _ = 𝟙 _ ∧
      t.base (IsLocalRing.closedPoint k) = i₁.1.base ((pullback.fst i₁.1 i₂.1).base ν) := by
    let gν : pullback i₁.1 i₂.1 ⟶ Spec (CommRingCat.of k) := pullback.fst i₁.1 i₂.1 ≫ c₁
    haveI : LocallyOfFiniteType gν := inferInstance
    haveI : JacobsonSpace ↥(pullback i₁.1 i₂.1) := LocallyOfFiniteType.jacobsonSpace gν
    haveI : Finite ↥(pullback i₁.1 i₂.1) := Nat.finite_of_card_ne_zero (by rw [hn]; exact hn0.ne')
    have hνc : IsClosed ({ν} : Set ↥(pullback i₁.1 i₂.1)) := isClosed_discrete _
    let t₀ : Spec (CommRingCat.of k) ⟶ pullback i₁.1 i₂.1 := pointOfClosedPoint gν ν hνc
    have ht₀g : t₀ ≫ gν = 𝟙 _ := pointOfClosedPoint_comp gν ν hνc
    have ht₀ν : t₀.base (IsLocalRing.closedPoint k) = ν := pointOfClosedPoint_apply gν ν hνc _
    refine ⟨t₀ ≫ pullback.fst i₁.1 i₂.1 ≫ i₁.1, ?_, ?_⟩
    · have hi₁ : i₁.1 ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = c₁ := i₁.2
      rw [Category.assoc, Category.assoc, hi₁]
      exact ht₀g
    · rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ht₀ν]

  letI : Algebra O ↥Pl := ι.toAlgebra
  have hρι : Spec.map (CommRingCat.ofHom ι) ≫ Spec.map (CommRingCat.ofHom ρO) = Spec.map (CommRingCat.ofHom ρ) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hι]
  set pr : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ)) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)) :=
    pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom ι)) (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hρι]) with hpr
  have hpr₁ : pr ≫ pullback.fst _ _ = pullback.fst _ _ := by
    rw [hpr]; erw [pullback.lift_fst]; rw [Category.comp_id]
  have hpr₂ : pr ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ι) := by
    rw [hpr]; erw [pullback.lift_snd]
  have hprPB : IsPullback pr (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ)))
      (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))) (Spec.map (CommRingCat.ofHom ι)) := by
    have key : IsPullback (pr ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) _)
        (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ))) (ModularCurve.TwoChart.modelTo A (↥K) j)
        (Spec.map (CommRingCat.ofHom ι) ≫ Spec.map (CommRingCat.ofHom ρO)) := by
      rw [hpr₁, hρι]; exact IsPullback.of_hasPullback _ _
    exact IsPullback.of_right key hpr₂ (IsPullback.of_hasPullback _ _)

  have hbc : bc ≫ pr = bcO := by
    apply pullback.hom_ext
    · rw [Category.assoc, hpr₁, hbc₁, hbcO₁]
    · rw [Category.assoc, hpr₂, ← Category.assoc, hbc₂, hbcO₂, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  set xA := (pullback.fst (i₁.1) (i₂.1) ≫ i₁.1 ≫ bc).base ν with hxA
  set xO := (pullback.fst (i₁.1) (i₂.1) ≫ i₁.1 ≫ bcO).base ν with hxO
  have hprx : pr.base xA = xO := by
    rw [hxA, hxO, ← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, hbc]

  let U : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ))).Opens := pr ⁻¹ᵁ U₀
  have hxU : xA ∈ U := by show pr.base xA ∈ U₀; rw [hprx]; exact hxU₀

  obtain ⟨φ, ψ, hφψ, hψφ, hφU, hφV, hψR, hφalg, hψO⟩ := R4Alg.crossing_bc O ↥Pl ((ρO ϖ) ^ e) ((ρ ϖ) ^ e)
    (by rw [map_pow, RingHom.algebraMap_toAlgebra, ← RingHom.comp_apply, hι])
  let sφ : Spec (CommRingCat.of (CrossingQuotient O ((ρO ϖ) ^ e) ⊗[O] ↥Pl)) ⟶ CrossingQuotient.crossingScheme ((ρ ϖ) ^ e) := Spec.map (CommRingCat.ofHom φ)
  let sψ : CrossingQuotient.crossingScheme ((ρ ϖ) ^ e) ⟶ Spec (CommRingCat.of (CrossingQuotient O ((ρO ϖ) ^ e) ⊗[O] ↥Pl)) := Spec.map (CommRingCat.ofHom ψ)
  haveI hφiso : IsIso sφ := by
    refine ⟨⟨sψ, ?_, ?_⟩⟩
    · simp only [sφ, sψ, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφψ, CommRingCat.ofHom_id, Spec.map_id]
    · simp only [sφ, sψ, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψφ, CommRingCat.ofHom_id, Spec.map_id]

  let g₁ : (U : Scheme.{0}) ⟶ (U₀ : Scheme.{0}) := pr ∣_ U₀
  have hg₁ : g₁ ≫ U₀.ι = U.ι ≫ pr := morphismRestrict_ι _ _
  let h : (U : Scheme.{0}) ⟶ pullback (Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O ((ρO ϖ) ^ e)))))
      (Spec.map (CommRingCat.ofHom ι)) :=
    pullback.lift (g₁ ≫ f₀) (U.ι ≫ pullback.snd _ _) (by
      rw [Category.assoc, hover₀, ← Category.assoc, hg₁, Category.assoc, Category.assoc]
      show U.ι ≫ pr ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)) = _
      rw [hpr₂])
  let f : (U : Scheme.{0}) ⟶ CrossingQuotient.crossingScheme ((ρ ϖ) ^ e) :=
    h ≫ (pullbackSpecIso O (CrossingQuotient O ((ρO ϖ) ^ e)) ↥Pl).hom ≫ sφ
  have hf : f = h ≫ (pullbackSpecIso O (CrossingQuotient O ((ρO ϖ) ^ e)) ↥Pl).hom ≫ Spec.map (CommRingCat.ofHom φ) := rfl
  have hf' : f = (h ≫ (pullbackSpecIso O (CrossingQuotient O ((ρO ϖ) ^ e)) ↥Pl).hom) ≫ sφ := (Category.assoc _ _ _).symm
  have hh₁ : h ≫ pullback.fst _ _ = g₁ ≫ f₀ := pullback.lift_fst _ _ _
  have hh₂ : h ≫ pullback.snd _ _ = U.ι ≫ pullback.snd _ _ := pullback.lift_snd _ _ _

  have hmem : ∀ (y : ↥(U : Scheme.{0})) (c : CrossingQuotient O ((ρO ϖ) ^ e)) (cA : CrossingQuotient ↥Pl ((ρ ϖ) ^ e)), φ cA = Algebra.TensorProduct.includeLeftRingHom c →
      (cA ∈ (f.base y).asIdeal ↔ c ∈ (f₀.base (g₁.base y)).asIdeal) := by
    intro y c cA hc
    have e1 : f₀.base (g₁.base y) = (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := O) (A := CrossingQuotient O ((ρO ϖ) ^ e)) (B := ↥Pl)))).base (((pullbackSpecIso O (CrossingQuotient O ((ρO ϖ) ^ e)) ↥Pl).hom).base (h.base y)) := by
      rw [← Scheme.Hom.comp_apply, ← hh₁, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply _ (Spec.map _),
        pullbackSpecIso_hom_fst]
    rw [hf, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, e1, Spec.map_apply, Spec.map_apply,
      PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, Ideal.mem_comap]
    show φ cA ∈ _ ↔ Algebra.TensorProduct.includeLeftRingHom c ∈ _
    rw [hc]
  have hmemU : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.U ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal ↔ CrossingQuotient.U ((ρO ϖ) ^ e) ∈ (f₀.base (g₁.base y)).asIdeal :=
    fun y => hmem y _ _ hφU
  have hmemV : ∀ y : ↥(U : Scheme.{0}), CrossingQuotient.V ((ρ ϖ) ^ e) ∈ (f.base y).asIdeal ↔ CrossingQuotient.V ((ρO ϖ) ^ e) ∈ (f₀.base (g₁.base y)).asIdeal :=
    fun y => hmem y _ _ hφV
  have hιg₁ : ∀ y : ↥(U : Scheme.{0}), U₀.ι.base (g₁.base y) = pr.base (U.ι.base y) := by
    intro y; rw [← Scheme.Hom.comp_apply, hg₁, Scheme.Hom.comp_apply]

  have htoκsurj : Function.Surjective (πk.comp ι) := hιsurj
  haveI : IsClosedImmersion (bcO) := by
    have hpb : IsPullback (bcO) (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) _) (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)))
        (Spec.map (CommRingCat.ofHom (πk.comp ι))) := by
      have key : IsPullback (bcO ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) _)
          (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) (ModularCurve.TwoChart.modelTo A (↥K) j)
          (Spec.map (CommRingCat.ofHom (πk.comp ι)) ≫ Spec.map (CommRingCat.ofHom ρO)) := by
        rw [hbcO₁, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hAlgkO]; exact IsPullback.of_hasPullback _ _
      exact IsPullback.of_right key hbcO₂ (IsPullback.of_hasPullback _ _)
    haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (πk.comp ι))) :=
      IsClosedImmersion.spec_of_surjective _ htoκsurj
    exact MorphismProperty.of_isPullback hpb.flip inferInstance
  have hbcpb : IsPullback bc (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) _) (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ)))
      (Spec.map (CommRingCat.ofHom (πk))) := by
    have key : IsPullback (bc ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) _)
        (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) (ModularCurve.TwoChart.modelTo A (↥K) j)
        (Spec.map (CommRingCat.ofHom (πk)) ≫ Spec.map (CommRingCat.ofHom ρ)) := by
      rw [hbc₁, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hAlgk]; exact IsPullback.of_hasPullback _ _
    exact IsPullback.of_right key hbc₂ (IsPullback.of_hasPullback _ _)
  have hfibre : ∀ (z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ)))) (w : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))), pr.base z = (bcO).base w → z = bc.base w := by
    intro z w hzw

    have h1 : (Spec.map (CommRingCat.ofHom ι)).base ((pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ))).base z) =
        IsLocalRing.closedPoint O := by
      rw [← Scheme.Hom.comp_apply, ← hpr₂, Scheme.Hom.comp_apply, hzw, ← Scheme.Hom.comp_apply, hbcO₂, Scheme.Hom.comp_apply]
      apply PrimeSpectrum.ext
      show Ideal.comap (πk.comp ι) _ = IsLocalRing.maximalIdeal O
      have : ((pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base w).asIdeal = ⊥ := by
        ext x; simp only [Ideal.mem_bot]; constructor
        · intro hx; by_contra h0; exact (PrimeSpectrum.isPrime _).ne_top (Ideal.eq_top_of_isUnit_mem _ hx (IsUnit.mk0 x h0))
        · rintro rfl; exact Ideal.zero_mem _
      rw [this, ← RingHom.ker_eq_comap_bot]
      exact IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ htoκsurj)
    have h2 : (pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ))).base z = IsLocalRing.closedPoint ↥Pl := by
      apply PrimeSpectrum.ext
      by_contra hne
      have hbot := ValuationSubring.eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime (Fact.out : p.Prime) Pl hPl _ hne
      have h3 : Ideal.comap ι ((pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ))).base z).asIdeal = IsLocalRing.maximalIdeal O :=
        congrArg PrimeSpectrum.asIdeal h1
      rw [hbot, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot ι).mp hιinj] at h3
      exact IsDiscreteValuationRing.not_isField O (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h3.symm)

    obtain ⟨w₁, hw₁, -⟩ := Scheme.exists_preimage_of_isPullback hbcpb z (IsLocalRing.closedPoint _) (by
      rw [h2]; exact hπkpt.symm)

    have h4 : (bc ≫ pr).base w₁ = (bcO).base w := by
      rw [Scheme.Hom.comp_apply, hw₁, hzw]
    rw [hbc] at h4
    rw [← hw₁, (bcO).isClosedEmbedding.injective h4]

  have hfibx : ∀ y : ↥(U : Scheme.{0}), pr.base (U.ι.base y) = xO ↔ U.ι.base y = xA := by
    intro y; constructor
    · intro hy
      have := hfibre (U.ι.base y) ((i₁.1).base ((pullback.fst (i₁.1) (i₂.1)).base ν)) (by
        rw [hy, hxO, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply])
      rw [this, hxA, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    · intro hy; rw [hy, hprx]

  have hbig : IsPullback g₁ (U.ι ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρ)))
      (U₀.ι ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))) (Spec.map (CommRingCat.ofHom ι)) :=
    (isPullback_morphismRestrict pr U₀).paste_vert hprPB
  have hPBU : IsPullback g₁ h f₀ (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O ((ρO ϖ) ^ e))))) (Spec.map (CommRingCat.ofHom ι))) := by
    refine IsPullback.of_bot (?_ : IsPullback g₁ (h ≫ pullback.snd _ _) (f₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap O (CrossingQuotient O ((ρO ϖ) ^ e))))) (Spec.map (CommRingCat.ofHom ι)))
      hh₁.symm (IsPullback.of_hasPullback _ _)
    rw [hh₂, hover₀]; exact hbig

  obtain ⟨V₀, hyV₀, hV₀⟩ := het₀ (g₁.base ⟨xA, hxU⟩) (by rw [hιg₁]; exact hprx)
  let W : (U : Scheme.{0}).Opens := g₁ ⁻¹ᵁ V₀
  have hxW : (⟨xA, hxU⟩ : ↥(U : Scheme.{0})) ∈ W := hyV₀
  have hWet : Etale (W.ι ≫ f) := by
    have sq : IsPullback (g₁ ∣_ V₀) (W.ι ≫ h) (V₀.ι ≫ f₀) (pullback.fst _ _) :=
      (isPullback_morphismRestrict g₁ V₀).paste_vert hPBU
    have hWh : Etale (W.ι ≫ h) := MorphismProperty.of_isPullback sq hV₀
    have e3 : W.ι ≫ f = ((W.ι ≫ h) ≫ (pullbackSpecIso O (CrossingQuotient O ((ρO ϖ) ^ e)) ↥Pl).hom) ≫ sφ := by
      rw [hf']; simp only [Category.assoc]
    rw [e3, MorphismProperty.cancel_right_of_respectsIso @Etale, MorphismProperty.cancel_right_of_respectsIso @Etale]
    exact hWh
  have hoverA : f ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥Pl (CrossingQuotient ↥Pl ((ρ ϖ) ^ e)))) = U.ι ≫ pullback.snd _ _ := by
    rw [hf, Category.assoc, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [hφalg]
    erw [pullbackSpecIso_hom_snd]
    exact hh₂
  refine ⟨U, hxU, f, ?_, ?_, ?_, ⟨W, ⟨⟨xA, hxU⟩, rfl, hxW⟩, hWet⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact hoverA
  ·
    intro y
    rw [hmemU, hmemV, hfib₀, hιg₁, hfibx]
  ·

    intro y hy
    have hyx : y = ⟨xA, hxU⟩ := Subtype.ext hy
    have hyW : y ∈ W := hyx ▸ hxW
    haveI := hWet
    haveI : LocallyOfFinitePresentation (W.ι ≫ f) := (Etale.iff_flat_and_formallyUnramified.mp hWet).2.2
    haveI : LocallyOfFiniteType (W.ι ≫ f) := inferInstance
    let w : ↥(W : Scheme.{0}) := ⟨y, hyW⟩
    have hw : W.ι.base w = y := rfl
    have e1 : (W.ι ≫ f).stalkMap w = f.stalkMap (W.ι.base w) ≫ W.ι.stalkMap w := Scheme.Hom.stalkMap_comp _ _ _
    have hfl : (f.stalkMap (W.ι.base w)).hom.Flat := by
      have h0 := Flat.stalkMap (W.ι ≫ f) w
      rw [e1] at h0
      exact (RingHom.Flat.respectsIso.cancel_right_isIso _ _).mp h0
    have hfu : (f.stalkMap (W.ι.base w)).hom.FormallyUnramified := by
      have h0 := FormallyUnramified.stalkMap (W.ι ≫ f) w
      rw [e1] at h0
      exact (RingHom.FormallyUnramified.respectsIso.cancel_right_isIso _ _).mp h0
    have hft : (f.stalkMap (W.ι.base w)).hom.EssFiniteType := by
      have h0 := LocallyOfFiniteType.stalkMap (W.ι ≫ f) w
      rw [e1] at h0
      exact (RingHom.EssFiniteType.respectsIso.cancel_right_isIso _ _).mp h0
    refine ⟨hfl, ?_, ?_⟩
    ·
      exact map_stalkMap_maximalIdeal_eq_of_formallyUnramified f (W.ι.base w) hft hfu
    ·
      have hjrange : Set.range (t ≫ bc).base ⊆ Set.range (U.ι).base := by
        rintro _ ⟨q, rfl⟩
        have hq : q = IsLocalRing.closedPoint _ := Subsingleton.elim _ _
        refine ⟨⟨xA, hxU⟩, ?_⟩
        rw [hq, Scheme.Hom.comp_apply, ht₂]
        show xA = _
        rw [hxA, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      let jk : Spec (CommRingCat.of k) ⟶ (U : Scheme.{0}) := IsOpenImmersion.lift U.ι (t ≫ bc) hjrange
      have hjfac : jk ≫ U.ι = t ≫ bc := IsOpenImmersion.lift_fac _ _ _
      have hjpt : jk.base (IsLocalRing.closedPoint _) = y := by
        apply U.ι.isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, hjfac, Scheme.Hom.comp_apply, ht₂, hy, hxA, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom πk)) := IsClosedImmersion.spec_of_surjective _ hπk
      have e5 : jk ≫ (U.ι ≫ pullback.snd _ _) = Spec.map (CommRingCat.ofHom πk) := by
        rw [← Category.assoc, hjfac, Category.assoc, hbc₂, ← Category.assoc, ht₁, Category.id_comp]
      have e4 : (jk ≫ f) ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥Pl (CrossingQuotient ↥Pl ((ρ ϖ) ^ e)))) = Spec.map (CommRingCat.ofHom πk) := by
        rw [Category.assoc, hoverA, e5]
      have h1s : Function.Surjective (jk.residueFieldMap (IsLocalRing.closedPoint _)).hom := by
        apply residueFieldMap_surjective_of_comp jk (U.ι ≫ pullback.snd _ _)
        rw [e5]; exact residueFieldMap_surjective_of_isClosedImmersion _ _
      have h2 : Function.Surjective ((jk ≫ f).residueFieldMap (IsLocalRing.closedPoint _)).hom := by
        apply residueFieldMap_surjective_of_comp (jk ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap ↥Pl (CrossingQuotient ↥Pl ((ρ ϖ) ^ e)))))
        rw [e4]; exact residueFieldMap_surjective_of_isClosedImmersion _ _

      rw [← hjpt]
      have hcomp := Scheme.residueFieldMap_comp jk f (IsLocalRing.closedPoint _)
      have h1 : Function.Bijective (jk.residueFieldMap (IsLocalRing.closedPoint _)).hom :=
        ⟨(jk.residueFieldMap _).hom.injective, h1s⟩
      rw [hcomp] at h2
      refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨(f.residueFieldMap _).hom.injective, fun b => ?_⟩
      obtain ⟨a, ha⟩ := h2 (jk.residueFieldMap _ b)
      exact ⟨a, h1.1 ha⟩
  ·

    intro τ hτ hτL x' y' hxy hxy' sU sU' hsU hsU' hsU'₁ hfs
    exact R4Alg.equivariance_geom (ModularCurve.TwoChart.modelTo A (↥K) j) O ↥Pl (Spec.map (CommRingCat.ofHom ρ)) (Spec.map (CommRingCat.ofHom ρO))
      ((ρO ϖ) ^ e) ((ρ ϖ) ^ e) φ ψ hφψ hψφ hφU hφV hψR hψO pr hpr₁ hpr₂ U₀ U g₁ hg₁ f₀ h hh₁ hh₂ f hf'
      (MulSemiringAction.toRingHom _ (↥Pl) τ) (fun o => hιfix τ hτ hτL o) x' y' hxy hxy' sU sU' hsU hsU' hsU'₁ hfs
  · intro y hy
    rw [hmemV] at hy
    obtain ⟨c, hc⟩ := hor₁ _ hy
    refine ⟨c, ?_⟩
    rw [Scheme.Hom.comp_apply]
    exact (hfibre _ _ (by rw [← hιg₁, ← hc, Scheme.Hom.comp_apply])).symm
  · intro y hy
    rw [hmemU] at hy
    obtain ⟨c, hc⟩ := hor₂ _ hy
    refine ⟨c, ?_⟩
    rw [Scheme.Hom.comp_apply]
    exact (hfibre _ _ (by rw [← hιg₁, ← hc, Scheme.Hom.comp_apply])).symm
  · intro y hy
    rw [hmemV]
    apply hor₃
    obtain ⟨c, hc⟩ := hy
    refine ⟨c, ?_⟩
    rw [hιg₁, ← hc, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply bc, hbc]
  · intro y hy
    rw [hmemU]
    apply hor₄
    obtain ⟨c, hc⟩ := hy
    refine ⟨c, ?_⟩
    rw [hιg₁, ← hc, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply bc, hbc]

end S_ModularCurve_XOneP_exists_orientedCrossingChart_valuationSubring_of_chart_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_orientedCrossingChart_valuationSubring_of_chart_twoChartModel_x1_mul (solution)
