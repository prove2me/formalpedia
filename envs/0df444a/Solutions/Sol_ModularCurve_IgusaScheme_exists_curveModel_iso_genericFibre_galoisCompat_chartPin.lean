-- Prove2me | solution 1 for ModularCurve.IgusaScheme.exists_curveModel_iso_genericFibre_galoisCompat_chartPin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/9f6f1dd4-a9b6-51d9-aa46-bbdb6d8b1ce1

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Theorems.Thm_ModularCurve_IgusaScheme_exists_algEquiv_tensor_chartAlg_chartRing
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_ModularCurve_CharPModel_finiteDimensional_adjoin_jBar
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_IgusaScheme_exists_genericFibreIso_chartPin_and_galoisCompat_of_algEquiv_chartAlg_chartRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_exists_curveModel_iso_genericFibre_galoisCompat_chartPin
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.IgusaScheme ModularCurve.CharPModel

universe u

namespace B1PrimeExport

section ExportTools
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

theorem appIso_hom_res_app_appIso_inv_apply
    {X Y : Scheme} (f : Y ⟶ X) {A B : CommRingCat} (ι : Spec A ⟶ X) [IsOpenImmersion ι]
    (g : Spec B ⟶ Y) [IsOpenImmersion g] (θ : A ⟶ B) (hfac : g ≫ f = Spec.map θ ≫ ι) (a : A)
    (V' : (Spec B).Opens) (hV' : g ''ᵁ V' ≤ f ⁻¹ᵁ (ι ''ᵁ ⊤)) :
    (g.appIso V').hom (Y.presheaf.map (homOfLE hV').op
      ((f.app (ι ''ᵁ ⊤)) ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A).inv a)))) =
    (Spec B).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso B).inv (θ a)) := by
  let V : X.Opens := ι ''ᵁ ⊤
  let r := (Scheme.ΓSpecIso A).inv a
  show (g.appIso V').hom (Y.presheaf.map (homOfLE hV').op ((f.app V) ((ι.appIso ⊤).inv r))) = _

  have e1 := CategoryTheory.ConcreteCategory.congr_hom (g.appIso_hom V')
    (Y.presheaf.map (homOfLE hV').op ((f.app V) ((ι.appIso ⊤).inv r)))
  rw [CategoryTheory.comp_apply] at e1
  rw [e1]

  have e2 := CategoryTheory.ConcreteCategory.congr_hom (g.naturality (homOfLE hV').op) ((f.app V) ((ι.appIso ⊤).inv r))
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e2
  rw [e2]

  have e3 := CategoryTheory.ConcreteCategory.congr_hom
    ((Scheme.Hom.comp_app g f V).symm.trans ((Scheme.Hom.congr_app hfac V).trans
      (congrArg (· ≫ (Spec B).presheaf.map _) (Scheme.Hom.comp_app (Spec.map θ) ι V))))
    ((ι.appIso ⊤).inv r)
  erw [e3]
  erw [CategoryTheory.comp_apply, CategoryTheory.comp_apply]

  have e4 := CategoryTheory.ConcreteCategory.congr_hom (ι.appIso_inv_app ⊤) r
  rw [CategoryTheory.comp_apply] at e4
  erw [e4]

  have e5 := CategoryTheory.ConcreteCategory.congr_hom
    ((Spec.map θ).naturality (eqToHom (ι.preimage_image_eq ⊤)).op) r
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e5
  erw [e5]

  have e6 := CategoryTheory.ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality θ) a
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at e6
  erw [← e6]

  simp only [← CategoryTheory.comp_apply]
  rfl

end ExportTools

section ExportGenerator
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicCurve AlgebraicCurve.CurveModel
open scoped IntermediateField

theorem glued_ffEquiv_symm_germToFunctionField
    (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)
    [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L]
    {X : Scheme.{u}} (f : glued K t ⟶ X) {A₀ : CommRingCat.{u}}
    (ι : Spec A₀ ⟶ X) [IsOpenImmersion ι]
    (θ : A₀ ⟶ CommRingCat.of ↥(chartRing K ({t} : Set L)))
    (hfac : ι₀ K t ≫ f = Spec.map θ ≫ ι) (a : A₀)
    [hne : Nonempty (f ⁻¹ᵁ (ι ''ᵁ ⊤))] :
    (((gluedFunctionFieldEquiv K t).symm
      ((glued K t).germToFunctionField (f ⁻¹ᵁ (ι ''ᵁ ⊤))
        ((f.app (ι ''ᵁ ⊤)) ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A₀).inv a))))) : L) =
      ((θ a : ↥(chartRing K ({t} : Set L))) : L) := by
  set U : (glued K t).Opens := f ⁻¹ᵁ (ι ''ᵁ ⊤) with hU
  set σ : Γ(glued K t, U) := (f.app (ι ''ᵁ ⊤)) ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A₀).inv a)) with hσ
  let V' : (X₀ K t).Opens := (ι₀ K t) ⁻¹ᵁ U
  have hV'U : (ι₀ K t) ''ᵁ V' ≤ U := by
    rintro _ ⟨x, hx, rfl⟩; exact hx

  have hηU : genericPoint (glued K t) ∈ U := by
    obtain ⟨⟨x, hx⟩⟩ := hne
    exact ((genericPoint_spec (glued K t)).mem_open_set_iff U.isOpen).mpr ⟨x, trivial, hx⟩
  have hξV' : genericPoint (X₀ K t) ∈ V' := by
    show (ι₀ K t).base (genericPoint (X₀ K t)) ∈ U
    rw [genericPoint_eq_of_isOpenImmersion]
    exact hηU
  have hη : genericPoint (glued K t) ∈ (ι₀ K t) ''ᵁ V' :=
    ⟨genericPoint (X₀ K t), hξV', genericPoint_eq_of_isOpenImmersion _⟩

  have step1 : (glued K t).germToFunctionField U σ =
      (glued K t).presheaf.germ ((ι₀ K t) ''ᵁ V') (genericPoint (glued K t)) hη
        (((ι₀ K t).appIso V').inv (((ι₀ K t).appIso V').hom
          ((glued K t).presheaf.map (homOfLE hV'U).op σ))) := by
    rw [Iso.hom_inv_id_apply, TopCat.Presheaf.germ_res_apply]

  have step2 : ((ι₀ K t).appIso V').hom ((glued K t).presheaf.map (homOfLE hV'U).op σ) =
      (X₀ K t).presheaf.map (homOfLE le_top).op (secTop K (chartRing K ({t} : Set L)) (θ a)) :=
    appIso_hom_res_app_appIso_inv_apply f ι (ι₀ K t) θ hfac a V' hV'U
  rw [step1, step2]

  rw [ffEquiv_symm_germ_appIso_inv K t (chartRing K ({t} : Set L)) (ι₀ K t) (incl₀ K t)
    (fun b => coe_chartIncl K _ b) rfl V' _ (genericPoint (X₀ K t)) hξV' hη]

  rw [germ_res_secTop]
  exact thetaHom_toStalk K t (chartRing K ({t} : Set L)) (incl₀ K t) (fun b => coe_chartIncl K _ b) _ _

theorem ofGenerator_ffEquiv_symm_germToFunctionField
    (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L] (t : L)
    [CharZero K] [Fact (t ≠ 0)] [FiniteDimensional K⟮t⟯ L] [FiniteDimensional K⟮t⁻¹⟯ L]
    (ht : Transcendental K t)
    {X : Scheme.{u}} (f : (CurveModel.ofGenerator K t ht).C ⟶ X) {A₀ : CommRingCat.{u}}
    (ι : Spec A₀ ⟶ X) [IsOpenImmersion ι]
    (θ : A₀ ⟶ CommRingCat.of ↥(chartRing K ({t} : Set L)))
    (hfac : ι₀ K t ≫ f = Spec.map θ ≫ ι) (a : A₀)
    [hne : Nonempty (f ⁻¹ᵁ (ι ''ᵁ ⊤))] :
    (((CurveModel.ofGenerator K t ht).ffEquiv.symm
      ((CurveModel.ofGenerator K t ht).C.germToFunctionField (f ⁻¹ᵁ (ι ''ᵁ ⊤))
        ((f.app (ι ''ᵁ ⊤)) ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso A₀).inv a))))) : L) =
      ((θ a : ↥(chartRing K ({t} : Set L))) : L) :=
  @glued_ffEquiv_symm_germToFunctionField K _ L _ _ t _ _ X f A₀ ι _ θ hfac a hne

end ExportGenerator

end B1PrimeExport

open B1PrimeExport in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ (M : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
      (e : M.C ⟶ pullback (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom (algebraMap (↥(GaloisRep.ratLocalizedAt ℓ)) (AlgebraicClosure ℚ)))))
      (_ : IsIso e),
      e ≫ pullback.snd _ _ = M.toBase ∧
      (∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
        (x x' : {s : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.C // s ≫ M.toBase = 𝟙 _}),
        x'.1 ≫ e ≫ pullback.fst _ _ =
          Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ x.1 ≫ e ≫ pullback.fst _ _ →
        M.pointEquivPlace x' = arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull N) g • M.pointEquivPlace x) ∧
      ∃ (_ : Nonempty (Scheme.Opens.toScheme ((e ≫ pullback.fst (igusaTo N ℓ)
          (Spec.map (CommRingCat.ofHom (algebraMap (↥(GaloisRep.ratLocalizedAt ℓ)) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((IgusaScheme.ιFin N ℓ) ''ᵁ ⊤)))),
        ∀ a : ↥(IgusaScheme.chartAlgFin N ℓ),
          ((M.ffEquiv.symm
              (M.C.germToFunctionField
                ((e ≫ pullback.fst (igusaTo N ℓ)
                    (Spec.map (CommRingCat.ofHom (algebraMap (↥(GaloisRep.ratLocalizedAt ℓ)) (AlgebraicClosure ℚ))))) ⁻¹ᵁ ((IgusaScheme.ιFin N ℓ) ''ᵁ ⊤))
                (((e ≫ pullback.fst (igusaTo N ℓ)
                    (Spec.map (CommRingCat.ofHom (algebraMap (↥(GaloisRep.ratLocalizedAt ℓ)) (AlgebraicClosure ℚ))))).app ((IgusaScheme.ιFin N ℓ) ''ᵁ ⊤)).hom
                  (((IgusaScheme.ιFin N ℓ).appIso ⊤).inv
                    ((Scheme.ΓSpecIso (CommRingCat.of ↥(IgusaScheme.chartAlgFin N ℓ))).inv a))))
              : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) =
            coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ)  := by
  classical

  have dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d :=
    fun d _ _ => Classical.choice (ModularCurve.nonempty_modularPolynomialData d)
  have htrans : Transcendental (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar N) := by
    simpa [ModularCurve.CharPModel.jBar] using ModularCurve.transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N
  haveI hne0 : Fact (ModularCurve.CharPModel.jBar N ≠ 0) :=
    ⟨fun h => htrans (by rw [h]; exact isAlgebraic_zero)⟩
  haveI hfd : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({ModularCurve.CharPModel.jBar N} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N) :=
    ModularCurve.CharPModel.finiteDimensional_adjoin_jBar N dataAll
  haveI hfd_inv : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({(ModularCurve.CharPModel.jBar N)⁻¹} : Set (modularFunctionFieldBar N)))
      (modularFunctionFieldBar N) := by
    have h : IntermediateField.adjoin (AlgebraicClosure ℚ) ({(ModularCurve.CharPModel.jBar N)⁻¹} : Set (modularFunctionFieldBar N)) =
        IntermediateField.adjoin (AlgebraicClosure ℚ) ({ModularCurve.CharPModel.jBar N} : Set (modularFunctionFieldBar N)) := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_simple_le_iff]
        exact inv_mem (IntermediateField.mem_adjoin_simple_self _ _)
      · rw [IntermediateField.adjoin_simple_le_iff]
        simpa using inv_mem (IntermediateField.mem_adjoin_simple_self (AlgebraicClosure ℚ) ((ModularCurve.CharPModel.jBar N)⁻¹))
    rw [h]; infer_instance

  obtain ⟨⟨eFin, hFin⟩, ⟨eInf, hInf⟩⟩ := ModularCurve.IgusaScheme.exists_algEquiv_tensor_chartAlg_chartRing N ℓ

  obtain ⟨e, hiso, heeta, hcF, -, hgal⟩ :=
    ModularCurve.IgusaScheme.exists_genericFibreIso_chartPin_and_galoisCompat_of_algEquiv_chartAlg_chartRing N ℓ htrans eFin hFin eInf hInf

  let θr : ↥(ModularCurve.IgusaScheme.chartAlgFin N ℓ) →+*
      ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ) ({ModularCurve.CharPModel.jBar N} : Set (modularFunctionFieldBar N))) :=
    eFin.toAlgHom.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := AlgebraicClosure ℚ)
        (B := ↥(ModularCurve.IgusaScheme.chartAlgFin N ℓ))).toRingHom
  have hθr : ∀ a, ((θr a : ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
      ({ModularCurve.CharPModel.jBar N} : Set (modularFunctionFieldBar N)))) : modularFunctionFieldBar N) =
      ⟨coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (a : ↥(modularFunctionFieldFull N)).2⟩ :=
    fun a => hFin a
  let θ : CommRingCat.of ↥(ModularCurve.IgusaScheme.chartAlgFin N ℓ) ⟶
      CommRingCat.of ↥(AlgebraicCurve.CurveModel.chartRing (AlgebraicClosure ℚ)
        ({ModularCurve.CharPModel.jBar N} : Set (modularFunctionFieldBar N))) :=
    CommRingCat.ofHom θr
  have hfac : AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar N) ≫
      (e ≫ pullback.fst (igusaTo N ℓ) _) = Spec.map θ ≫ ιFin N ℓ := hcF
  have hUne : ∀ ξ : ↥(AlgebraicCurve.CurveModel.X₀ (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar N)),
      (AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar N)).base ξ ∈
        (e ≫ pullback.fst (igusaTo N ℓ) _) ⁻¹ᵁ ((ιFin N ℓ) ''ᵁ ⊤) := by
    intro ξ
    have e := congrArg (fun g => g.base ξ) hfac
    exact ⟨(Spec.map θ).base ξ, trivial, e.symm⟩
  have hne : Nonempty (Scheme.Opens.toScheme ((e ≫ pullback.fst (igusaTo N ℓ)
      (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) ⁻¹ᵁ
        ((ιFin N ℓ) ''ᵁ ⊤))) :=
    ⟨⟨(AlgebraicCurve.CurveModel.ι₀ (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar N)).base
      (Classical.arbitrary _), hUne _⟩⟩
  have hMη : ∀ a : ↥(ModularCurve.IgusaScheme.chartAlgFin N ℓ),
      (((CurveModel.ofGenerator (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar N) htrans).ffEquiv.symm
          ((CurveModel.ofGenerator (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar N) htrans).C.germToFunctionField
            ((e ≫ pullback.fst (igusaTo N ℓ)
              (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) ⁻¹ᵁ
              ((ιFin N ℓ) ''ᵁ ⊤))
            (((e ≫ pullback.fst (igusaTo N ℓ)
              (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))).app
                ((ιFin N ℓ) ''ᵁ ⊤)).hom
              (((ιFin N ℓ).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.IgusaScheme.chartAlgFin N ℓ))).inv a))))
          : ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) ((a : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ) := by
    intro a
    have key := ofGenerator_ffEquiv_symm_germToFunctionField (AlgebraicClosure ℚ)
      (ModularCurve.CharPModel.jBar N) htrans (e ≫ pullback.fst (igusaTo N ℓ) _) (ιFin N ℓ) θ hfac a
    refine (congrArg (fun y : modularFunctionFieldBar N => (y : LaurentSeries (AlgebraicClosure ℚ))) key).trans ?_
    simp only [θ, CommRingCat.hom_ofHom, hθr]
  exact ⟨CurveModel.ofGenerator (AlgebraicClosure ℚ) (ModularCurve.CharPModel.jBar N) htrans, e, hiso, heeta, hgal, hne, hMη⟩

end S_ModularCurve_IgusaScheme_exists_curveModel_iso_genericFibre_galoisCompat_chartPin
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_exists_curveModel_iso_genericFibre_galoisCompat_chartPin (solution)
