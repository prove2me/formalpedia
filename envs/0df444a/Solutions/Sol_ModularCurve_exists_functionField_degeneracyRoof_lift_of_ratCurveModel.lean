-- Prove2me | solution 1 for ModularCurve.exists_functionField_degeneracyRoof_lift_of_ratCurveModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/9856bba6-4d67-5600-a900-addebcf0ee9b

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_ModularCurve_HeckeProj
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverKaehler
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_RigKerDualNumber
import Definitions.Def_AlgebraicGeometry_RelPicardStageHom
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_CechH1PushPull
import Definitions.Def_AlgebraicCurve_KaehlerToFunctionField
import Definitions.Def_AlgebraicCurve_SerrePairing
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_AlgebraicCurve_FibreResidueIdentityAlong
import Definitions.Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2
import Theorems.Thm_AlgebraicGeometry_Scheme_finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton
import Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import Theorems.Thm_AlgebraicCurve_germToFunctionField_app_eq_of_fromSpecStalk_comp_eq
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_ModularCurve_CanonicalDivisor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_functionField_degeneracyRoof_lift_of_ratCurveModel
set_option autoImplicit false
universe u
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicCurve IsLocalRing CuspForm AlgebraicGeometry.Scheme.TwoAffineOpenCover KaehlerDifferential"

theorem RiAux.apply_genericPoint_eq_of_surjective {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : Y ⟶ X)
    (hf : Function.Surjective f) : f (genericPoint Y) = genericPoint X := by
  have h := (genericPoint_spec Y).image f.continuous
  rw [Set.image_univ, Set.range_eq_univ.mpr hf, closure_univ] at h
  exact h.eq (genericPoint_spec X)

theorem RiAux.exists_ringHom_functionField_of_surjective {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) (hf : Function.Surjective f) :
    ∃ φ : X.functionField →+* Y.functionField,
      Y.fromSpecStalk (genericPoint Y) ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X) := by
  have hgen := RiAux.apply_genericPoint_eq_of_surjective f hf
  have hsp : f (genericPoint Y) ⤳ genericPoint X := hgen ▸ specializes_rfl
  refine ⟨(X.presheaf.stalkSpecializes hsp ≫ f.stalkMap (genericPoint Y)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

theorem RiAux.finite_functionField_of_isFinite {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsFinite f] (hf : Function.Surjective f)
    (φ : X.functionField →+* Y.functionField)
    (hφ : Y.fromSpecStalk (genericPoint Y) ≫ f = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X)) :
    letI := φ.toAlgebra; Module.Finite X.functionField Y.functionField := by
  classical
  letI algF := φ.toAlgebra

  let U : X.Opens := (X.affineCover.f (X.affineCover.idx (genericPoint X))).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have hηU : genericPoint X ∈ U := X.affineCover.covers (genericPoint X)
  haveI : Nonempty U := ⟨⟨_, hηU⟩⟩
  let V : Y.Opens := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  have hηV : genericPoint Y ∈ V := by
    show f (genericPoint Y) ∈ U
    rw [RiAux.apply_genericPoint_eq_of_surjective f hf]; exact hηU
  haveI : Nonempty V := ⟨⟨_, hηV⟩⟩

  letI algAB : Algebra Γ(X, U) Γ(Y, V) := (f.app U).hom.toAlgebra
  haveI : Module.Finite Γ(X, U) Γ(Y, V) := f.finite_app U hU
  haveI : IsFractionRing Γ(Y, V) Y.functionField := functionField_isFractionRing_of_isAffineOpen Y V hV
  let ιA : Γ(X, U) →+* X.functionField := (X.germToFunctionField U).hom
  let ιB : Γ(Y, V) →+* Y.functionField := (Y.germToFunctionField V).hom

  have hcompat : ∀ s : Γ(X, U), ιB (f.app U s) = φ (ιA s) := fun s =>
    AlgebraicCurve.germToFunctionField_app_eq_of_fromSpecStalk_comp_eq f φ hφ U s

  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Γ(X, U)) (M := Γ(Y, V))
  let S : Set Y.functionField := ιB '' (s : Set Γ(Y, V))
  haveI : Finite S := ((Finset.finite_toSet s).image ιB).to_subtype

  have hint : ∀ b : Γ(Y, V), IsIntegral X.functionField (ιB b) := by
    intro b
    haveI : Algebra.IsIntegral Γ(X, U) Γ(Y, V) := Algebra.IsIntegral.of_finite _ _
    obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := Γ(X, U)) b
    refine ⟨p.map ιA, hpm.map _, ?_⟩
    have hcomp : (algebraMap X.functionField Y.functionField).comp ιA = ιB.comp (f.app U).hom :=
      RingHom.ext fun a => (hcompat a).symm
    rw [Polynomial.eval₂_map, hcomp, ← Polynomial.hom_eval₂, show Polynomial.eval₂ (f.app U).hom b p = 0 from hp,
      map_zero]
  have hSint : ∀ x ∈ S, IsIntegral X.functionField x := by
    rintro x ⟨b, -, rfl⟩
    exact hint b
  haveI : FiniteDimensional X.functionField (IntermediateField.adjoin X.functionField S) :=
    IntermediateField.finiteDimensional_adjoin hSint

  have hB : ∀ b : Γ(Y, V), ιB b ∈ IntermediateField.adjoin X.functionField S := by
    intro b
    have hb : b ∈ Submodule.span Γ(X, U) (s : Set Γ(Y, V)) := by rw [hs]; exact Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem x hx =>
      exact IntermediateField.subset_adjoin _ _ (Set.mem_image_of_mem _ hx)
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [Algebra.smul_def, map_mul, show algebraMap Γ(X, U) Γ(Y, V) a = f.app U a from rfl, hcompat]
      exact mul_mem (IntermediateField.algebraMap_mem _ (ιA a)) hx

  have htop : IntermediateField.adjoin X.functionField S = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, V)) z
    exact div_mem (hB a) (hB b)
  haveI : FiniteDimensional X.functionField (⊤ : IntermediateField X.functionField Y.functionField) := by
    rw [← htop]; infer_instance
  exact LinearEquiv.finiteDimensional
    (IntermediateField.topEquiv (F := X.functionField) (E := Y.functionField)).toLinearEquiv

theorem solution
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]

    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull p))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)

    (q : Nat.Primes) [NeZero (q : ℕ)] [NeZero (p * (q : ℕ))]

    (M' : CurveModel ℚ ↥(modularFunctionFieldFull (p * (q : ℕ))))
    (φα φβ : ↥(modularFunctionFieldFull p) →+* ↥(modularFunctionFieldFull (p * (q : ℕ))))
    (πα πβ : M'.C ⟶ X)
    (Hα : πα ≫ c = M'.toBase ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ) (Hβ : πβ ≫ c = M'.toBase ≫ specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)
    (πα₀ πβ₀ : M'.C ⟶ M₀.C) (d : ℕ)
    (hdeg :
      πα = πα₀ ≫ e₀ ≫ pullback.fst c _ ∧ πβ = πβ₀ ≫ e₀ ≫ pullback.fst c _ ∧
      πα₀ ≫ M₀.toBase = M'.toBase ∧ πβ₀ ≫ M₀.toBase = M'.toBase ∧
      IsFinite πα₀ ∧ Flat πα₀ ∧ LocallyOfFinitePresentation πα₀ ∧
      IsFinite πβ₀ ∧ Flat πβ₀ ∧ LocallyOfFinitePresentation πβ₀ ∧
      (∀ x, πα₀.finrank x = d) ∧

      M'.C.fromSpecStalk (genericPoint M'.C) ≫ πα₀ =
        Spec.map (CommRingCat.ofHom (M'.ffEquiv.toRingHom.comp (φα.comp M₀.ffEquiv.symm.toRingHom))) ≫
          M₀.C.fromSpecStalk (genericPoint M₀.C) ∧
      M'.C.fromSpecStalk (genericPoint M'.C) ≫ πβ₀ =
        Spec.map (CommRingCat.ofHom (M'.ffEquiv.toRingHom.comp (φβ.comp M₀.ffEquiv.symm.toRingHom))) ≫
          M₀.C.fromSpecStalk (genericPoint M₀.C) ∧
      (∀ f : ↥(modularFunctionFieldFull p),
        heckeAlphaBar (AlgebraicClosure ℚ) p q (baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p) (1 ⊗ₜ f)) =
          baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull (p * (q : ℕ))) (1 ⊗ₜ φα f)) ∧
      (∀ f : ↥(modularFunctionFieldFull p),
        heckeBetaBar (AlgebraicClosure ℚ) p q (baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p) (1 ⊗ₜ f)) =
          baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull (p * (q : ℕ))) (1 ⊗ₜ φβ f)))

    (𝒱 : X.TwoAffineOpenCover)
    (hgen0 : genericPoint M₀.C ∈ (e₀ ≫ pullback.fst c _) ⁻¹ᵁ 𝒱.U0) :
    letI Rℓ := ↥(GaloisRep.ratLocalizedAt ℓ)
    letI Xq := Limits.pullback c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)
    letI cq : Xq ⟶ Spec (.of ℚ) := pullback.snd c (specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)
    letI := (AlgebraicCurve.baseToFunctionField cq).toAlgebra
    letI := (AlgebraicCurve.baseToFunctionField M'.toBase).toAlgebra
    letI Vq := 𝒱.pullback c ℚ
    ∃ (_ : IsIntegral Xq) (_ : IsSeparated cq) (_ : SmoothOfRelativeDimension 1 cq)
      (_ : ∀ Z : Set Xq, IsClosed Z → Z ≠ Set.univ → Z.Finite)
      (_ : IsIntegral M'.C)
      (_ : IsFinite (pullback.lift πα M'.toBase Hα : M'.C ⟶ Xq))
      (_ : Flat (pullback.lift πα M'.toBase Hα : M'.C ⟶ Xq))
      (_ : LocallyOfFinitePresentation (pullback.lift πα M'.toBase Hα : M'.C ⟶ Xq))
      (_ : IsAffineHom (pullback.lift πβ M'.toBase Hβ : M'.C ⟶ Xq))
      (_ : ∀ z, (pullback.lift πα M'.toBase Hα : M'.C ⟶ Xq).finrank z = d)
      (φα' φβ' : Xq.functionField →ₐ[ℚ] M'.C.functionField)
      (_ : M'.C.fromSpecStalk (genericPoint M'.C) ≫ pullback.lift πα M'.toBase Hα =
        Spec.map (CommRingCat.ofHom φα'.toRingHom) ≫ Xq.fromSpecStalk (genericPoint Xq))
      (_ : M'.C.fromSpecStalk (genericPoint M'.C) ≫ pullback.lift πβ M'.toBase Hβ =
        Spec.map (CommRingCat.ofHom φβ'.toRingHom) ≫ Xq.fromSpecStalk (genericPoint Xq))
      (_ : AlgebraicCurve.FiniteAlong ℚ φα') (_ : AlgebraicCurve.FiniteAlong ℚ φβ'),
      Nonempty (Vq.U0 : Xq.Opens) := by

  set Rℓ := ↥(GaloisRep.ratLocalizedAt ℓ) with hRℓ
  let ιq := specMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ
  let Xq := Limits.pullback c ιq
  let cq : Xq ⟶ Spec (.of ℚ) := pullback.snd c ιq
  obtain ⟨hdeg1, hdeg2, hdeg3, hdeg4, hfinα, hflatα, hlfpα, hfinβ, hflatβ, hlfpβ, hrank, hgenα, hgenβ, -, -⟩ := hdeg

  have hliftα : (pullback.lift πα M'.toBase Hα : M'.C ⟶ Xq) = πα₀ ≫ e₀ := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, hdeg1]
    · rw [pullback.lift_snd, Category.assoc, he₀, hdeg3]
  have hliftβ : (pullback.lift πβ M'.toBase Hβ : M'.C ⟶ Xq) = πβ₀ ≫ e₀ := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, hdeg2]
    · rw [pullback.lift_snd, Category.assoc, he₀, hdeg4]

  haveI hIq : IsIntegral Xq := inferInstance
  haveI hSq : IsSeparated cq := inferInstance
  haveI hSmq : SmoothOfRelativeDimension 1 cq := inferInstance

  have hC : ∀ Z : Set Xq, IsClosed Z → Z ≠ Set.univ → Z.Finite := by
    haveI : IsLocallyNoetherian Xq := LocallyOfFiniteType.isLocallyNoetherian cq
    haveI : CompactSpace ↥(Spec (CommRingCat.of ℚ)) := inferInstanceAs (CompactSpace (PrimeSpectrum _))
    haveI : CompactSpace Xq := QuasiCompact.compactSpace_of_compactSpace cq
    haveI : IsNoetherian Xq := {}
    exact AlgebraicGeometry.Scheme.finite_of_isClosed_of_ne_univ_of_forall_isClosed_singleton
      (fun x hx => AlgebraicCurve.isClosed_singleton_of_ne_genericPoint cq x hx)

  haveI : IsFinite (pullback.lift πα M'.toBase Hα : M'.C ⟶ Xq) := by rw [hliftα]; infer_instance
  haveI : Flat (pullback.lift πα M'.toBase Hα : M'.C ⟶ Xq) := by rw [hliftα]; infer_instance
  haveI : LocallyOfFinitePresentation (pullback.lift πα M'.toBase Hα : M'.C ⟶ Xq) := by rw [hliftα]; infer_instance
  haveI : IsAffineHom (pullback.lift πβ M'.toBase Hβ : M'.C ⟶ Xq) := by
    rw [hliftβ]; haveI := hfinβ; infer_instance
  have hd' : ∀ z, (pullback.lift πα M'.toBase Hα : M'.C ⟶ Xq).finrank z = d := by
    haveI := hfinα; haveI := hflatα
    have hsq : IsPullback (𝟙 M'.C) πα₀ (pullback.lift πα M'.toBase Hα : M'.C ⟶ Xq) e₀ :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, hliftα]⟩
    intro z
    have h := Scheme.Hom.finrank_of_isPullback (𝟙 M'.C) πα₀ (pullback.lift πα M'.toBase Hα : M'.C ⟶ Xq) e₀ hsq
      (inv e₀ z)
    rw [hrank] at h
    rw [h]
    congr 1
    change z = (inv e₀ ≫ e₀) z
    rw [IsIso.inv_hom_id]; rfl

  letI := (AlgebraicCurve.baseToFunctionField cq).toAlgebra
  letI := (AlgebraicCurve.baseToFunctionField M'.toBase).toAlgebra
  have hφ' : ∃ (φα' φβ' : Xq.functionField →ₐ[ℚ] M'.C.functionField),
      M'.C.fromSpecStalk (genericPoint M'.C) ≫ pullback.lift πα M'.toBase Hα =
        Spec.map (CommRingCat.ofHom φα'.toRingHom) ≫ Xq.fromSpecStalk (genericPoint Xq) ∧
      M'.C.fromSpecStalk (genericPoint M'.C) ≫ pullback.lift πβ M'.toBase Hβ =
        Spec.map (CommRingCat.ofHom φβ'.toRingHom) ≫ Xq.fromSpecStalk (genericPoint Xq) ∧
      AlgebraicCurve.FiniteAlong ℚ φα' ∧ AlgebraicCurve.FiniteAlong ℚ φβ' := by
    haveI := hfinα; haveI := hflatα; haveI := hlfpα; haveI := hfinβ; haveI := hflatβ; haveI := hlfpβ

    have y₀ : M'.C := genericPoint M'.C
    have hsurjα : Function.Surjective πα₀ := by
      have hS : Surjective πα₀ := by
        rw [← Scheme.Hom.one_le_finrank_iff_surjective]
        intro x
        have h1 := Scheme.Hom.one_le_finrank_map πα₀ y₀
        rw [hrank] at h1
        show 1 ≤ πα₀.finrank x
        rw [hrank]; exact h1
      exact hS.1
    have hsurjβ : Function.Surjective πβ₀ := by
      have hS : Surjective πβ₀ := by
        rw [← Scheme.Hom.one_le_finrank_iff_surjective]
        intro x
        have hconst := (Scheme.Hom.isLocallyConstant_finrank πβ₀).apply_eq_of_preconnectedSpace x (πβ₀ y₀)
        show 1 ≤ πβ₀.finrank x
        rw [hconst]; exact Scheme.Hom.one_le_finrank_map πβ₀ y₀
      exact hS.1
    have hsurj : ∀ {g : M'.C ⟶ M₀.C}, Function.Surjective g →
        Function.Surjective (g ≫ e₀ : M'.C ⟶ Xq) := fun {g} hg => by
      rw [Scheme.Hom.comp_base]
      exact (e₀.homeomorph.surjective).comp hg

    obtain ⟨ψα, hψα⟩ := RiAux.exists_ringHom_functionField_of_surjective (pullback.lift πα M'.toBase Hα : M'.C ⟶ Xq)
      (by rw [hliftα]; exact hsurj hsurjα)
    obtain ⟨ψβ, hψβ⟩ := RiAux.exists_ringHom_functionField_of_surjective (pullback.lift πβ M'.toBase Hβ : M'.C ⟶ Xq)
      (by rw [hliftβ]; exact hsurj hsurjβ)

    have hcomm : ∀ (ψ : Xq.functionField →+* M'.C.functionField) (r : ℚ),
        ψ (algebraMap ℚ Xq.functionField r) = algebraMap ℚ M'.C.functionField r := fun ψ r =>
      RingHom.congr_fun (RingHom.ext_rat (ψ.comp (algebraMap ℚ Xq.functionField)) (algebraMap ℚ M'.C.functionField)) r
    let φα' : Xq.functionField →ₐ[ℚ] M'.C.functionField := { ψα with commutes' := hcomm ψα }
    let φβ' : Xq.functionField →ₐ[ℚ] M'.C.functionField := { ψβ with commutes' := hcomm ψβ }
    refine ⟨φα', φβ', hψα, hψβ, ?_, ?_⟩
    · exact RiAux.finite_functionField_of_isFinite (pullback.lift πα M'.toBase Hα : M'.C ⟶ Xq)
        (by rw [hliftα]; exact hsurj hsurjα) ψα hψα
    · haveI : IsFinite (pullback.lift πβ M'.toBase Hβ : M'.C ⟶ Xq) := by rw [hliftβ]; infer_instance
      exact RiAux.finite_functionField_of_isFinite (pullback.lift πβ M'.toBase Hβ : M'.C ⟶ Xq)
        (by rw [hliftβ]; exact hsurj hsurjβ) ψβ hψβ
  obtain ⟨φα', φβ', hφπα, hφπβ, hfinα', hfinβ'⟩ := hφ'

  have hne : Nonempty ((𝒱.pullback c ℚ).U0 : Xq.Opens) := ⟨⟨e₀ (genericPoint M₀.C), hgen0⟩⟩
  exact ⟨hIq, hSq, hSmq, hC, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hd', φα', φβ',
    hφπα, hφπβ, hfinα', hfinβ', hne⟩

end S_ModularCurve_exists_functionField_degeneracyRoof_lift_of_ratCurveModel
end P2MW
export P2MW.S_ModularCurve_exists_functionField_degeneracyRoof_lift_of_ratCurveModel (solution)
