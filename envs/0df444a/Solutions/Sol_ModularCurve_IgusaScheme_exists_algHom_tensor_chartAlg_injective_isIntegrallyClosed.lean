-- Prove2me | solution 1 for ModularCurve.IgusaScheme.exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/d207648e-bd36-5553-b430-fb22000b326b

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_JacJ1_ChartAlgebra
import Theorems.Thm_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isAlgebraic_mem_range
import Theorems.Thm_ModularCurve_exists_eq_algebraMap_of_isAlgebraic_modularFunctionFieldFull
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_of_liesOverPrime
import Theorems.Thm_IsIntegrallyClosed_of_directed_iUnion_subring
import Theorems.Thm_ModularCurve_IgusaScheme_isIntegrallyClosed_tensor_chartAlgFin_of_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_IgusaScheme_isIntegrallyClosed_tensor_chartAlgInf_of_isDiscreteValuationRing
import Theorems.Thm_ModularCurve_IgusaScheme_isIntegrallyClosed_tensor_chartAlgFin_of_charZero
import Theorems.Thm_ModularCurve_IgusaScheme_isIntegrallyClosed_tensor_chartAlgInf_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd"
p2m_attr_erase "simp" "ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open scoped TensorProduct
p2m_open "IsLocalRing ModularCurve P2MW.S_ModularCurve_IgusaScheme_exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed.ModularCurve.IgusaScheme ModularCurve.CharPModel AlgebraicCurve"

noncomputable section

namespace FibreIsoAux

theorem exists_injective_to_fieldTensor
    (R Q L F A' B : Type*) [CommRing R] [IsDedekindDomain R]
    [Field Q] [Algebra R Q] [IsFractionRing R Q]
    [Field L] [Algebra R L] [Algebra Q L] [IsScalarTower R Q L]
    [Field F] [Algebra R F] [Algebra Q F] [IsScalarTower R Q F]
    [CommRing A'] [Algebra R A'] [Module.Flat R A']
    [AddCommGroup B] [Module R B]
    (ιA : A' →ₗ[R] L) (hιA : Function.Injective ιA)
    (ιB : B →ₗ[R] F) (hιB : Function.Injective ιB) :
    ∃ Θ : A' ⊗[R] B →ₗ[R] L ⊗[Q] F, Function.Injective Θ ∧
      ∀ (a : A') (b : B), Θ (a ⊗ₜ b) = ιA a ⊗ₜ ιB b := by
  haveI : FaithfulSMul R F := by
    rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq R Q F]
    exact (algebraMap Q F).injective.comp (IsFractionRing.injective R Q)
  haveI : Module.Flat R F := inferInstance
  haveI : IsLocalizedModule (nonZeroDivisors R) (LinearMap.id : F →ₗ[R] F) :=
    isLocalizedModule_id (nonZeroDivisors R) F Q
  have hbc : IsBaseChange Q (LinearMap.id : F →ₗ[R] F) :=
    IsLocalizedModule.isBaseChange (nonZeroDivisors R) Q LinearMap.id
  let e2 : Q ⊗[R] F ≃ₗ[Q] F := hbc.equiv
  let e1 : L ⊗[R] F ≃ₗ[Q] L ⊗[Q] (Q ⊗[R] F) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R Q Q L F).symm
  let e3 : L ⊗[Q] (Q ⊗[R] F) ≃ₗ[Q] L ⊗[Q] F := TensorProduct.congr (LinearEquiv.refl Q L) e2
  let e : L ⊗[R] F ≃ₗ[Q] L ⊗[Q] F := e1.trans e3
  refine ⟨(e.toLinearMap.restrictScalars R) ∘ₗ TensorProduct.map ιA ιB, ?_, ?_⟩
  · refine e.injective.comp ?_
    rw [← LinearMap.rTensor_comp_lTensor]
    exact (Module.Flat.rTensor_preserves_injective_linearMap (M := F) ιA hιA).comp
      (Module.Flat.lTensor_preserves_injective_linearMap (M := A') ιB hιB)
  · intro a b
    change e (TensorProduct.map ιA ιB (a ⊗ₜ b)) = _
    rw [TensorProduct.map_tmul]
    change e3 (e1 (ιA a ⊗ₜ ιB b)) = _
    rw [show e1 (ιA a ⊗ₜ ιB b) = ιA a ⊗ₜ ((1 : Q) ⊗ₜ ιB b) from rfl]
    change (LinearEquiv.refl Q L) (ιA a) ⊗ₜ e2 ((1 : Q) ⊗ₜ ιB b) = _
    rw [LinearEquiv.refl_apply, show e2 ((1 : Q) ⊗ₜ ιB b) = (1 : Q) • (LinearMap.id (ιB b)) from
      hbc.equiv_tmul 1 (ιB b), one_smul, LinearMap.id_apply]

theorem injective_of_isField {K S : Type*} [CommRing K] [Semiring S] [Nontrivial S]
    (hK : IsField K) (f : K →+* S) : Function.Injective f := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  by_contra h
  obtain ⟨y, hy⟩ := hK.mul_inv_cancel h
  have := congrArg f hy
  rw [map_mul, hx, zero_mul, map_one] at this
  exact zero_ne_one this

end FibreIsoAux

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme modularFunctionFieldFull coeffMap coeffMap_single algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange exists_eq_algebraMap_of_isAlgebraic_modularFunctionFieldFull IgusaScheme.isIntegrallyClosed_tensor_chartAlgFin_of_isDiscreteValuationRing IgusaScheme.isIntegrallyClosed_tensor_chartAlgInf_of_isDiscreteValuationRing IgusaScheme.isIntegrallyClosed_tensor_chartAlgFin_of_charZero IgusaScheme.isIntegrallyClosed_tensor_chartAlgInf_of_charZero"
namespace IgusaScheme
p2m_export "ModularCurve.IgusaScheme" "chartAlgFin chartAlgInf isIntegrallyClosed_tensor_chartAlgFin_of_isDiscreteValuationRing isIntegrallyClosed_tensor_chartAlgInf_of_isDiscreteValuationRing isIntegrallyClosed_tensor_chartAlgFin_of_charZero isIntegrallyClosed_tensor_chartAlgInf_of_charZero"
namespace FibreIsoA
p2m_open "ModularCurve.IgusaScheme ModularCurve"

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)
set_option quotPrecheck false in
local notation "Qb" => AlgebraicClosure ℚ
set_option quotPrecheck false in
local notation "FN" => ↥(modularFunctionFieldFull N)
set_option quotPrecheck false in
local notation "TT" => ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))

theorem algebraMap_laurent (q : ℚ) :
    algebraMap ℚ (LaurentSeries Qb) q = HahnSeries.C (algebraMap ℚ Qb q) := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C]

def cQ : Qb →ₐ[ℚ] LaurentSeries Qb :=
  { (HahnSeries.C : Qb →+* LaurentSeries Qb) with
    commutes' := fun q => (algebraMap_laurent q).symm }

@[scoped simp] theorem cQ_apply (x : Qb) : cQ x = HahnSeries.C x := rfl

def valF : FN →+* LaurentSeries ℚ :=
  { toFun := Subtype.val, map_one' := rfl, map_mul' := fun _ _ => rfl,
    map_zero' := rfl, map_add' := fun _ _ => rfl }

theorem valF_algebraMap (q : ℚ) : valF N (algebraMap ℚ FN q) = HahnSeries.C q :=
  congrArg (fun f : ℚ →+* LaurentSeries ℚ => f q)
    (Subsingleton.elim ((valF N).comp (algebraMap ℚ FN)) (HahnSeries.C : ℚ →+* LaurentSeries ℚ))

def eF : FN →ₐ[ℚ] LaurentSeries Qb :=
  { (coeffEmb Qb).comp (valF N) with
    commutes' := fun q => by
      change coeffEmb Qb (valF N (algebraMap ℚ FN q)) = _
      rw [valF_algebraMap, algebraMap_laurent]
      change coeffMap (algebraMap ℚ Qb) (HahnSeries.single 0 q) = HahnSeries.single 0 (algebraMap ℚ Qb q)
      rw [coeffMap_single] }

@[scoped simp] theorem eF_apply (f : FN) : eF N f = coeffEmb Qb (f : LaurentSeries ℚ) := rfl

def Phi : FN ⊗[ℚ] Qb →ₐ[ℚ] LaurentSeries Qb :=
  Algebra.TensorProduct.productMap (eF N) cQ

theorem Phi_tmul (f : FN) (x : Qb) :
    Phi N (f ⊗ₜ x) = coeffEmb Qb (f : LaurentSeries ℚ) * HahnSeries.C x :=
  Algebra.TensorProduct.productMap_apply_tmul _ _ f x

scoped instance isAlgebraic_Qb : Algebra.IsAlgebraic ℚ Qb := by
  convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | exact Subsingleton.elim _ _

scoped instance isIntegral_Qb : Algebra.IsIntegral ℚ Qb :=
  ⟨fun x => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral⟩

scoped instance isSeparable_Qb : Algebra.IsSeparable ℚ Qb :=
  ⟨fun x => (minpoly.irreducible (Algebra.IsIntegral.isIntegral x)).separable⟩

theorem isField_tensor : IsField (FN ⊗[ℚ] Qb) :=
  Algebra.TensorProduct.isField_of_isSeparable_of_forall_isAlgebraic_mem_range ℚ FN Qb
    (fun y hy => by
      obtain ⟨c, hc⟩ := ModularCurve.exists_eq_algebraMap_of_isAlgebraic_modularFunctionFieldFull N y hy
      exact ⟨c, hc.symm⟩)

theorem Phi_injective : Function.Injective (Phi N) :=
  FibreIsoAux.injective_of_isField (isField_tensor N) (Phi N).toRingHom

scoped instance : IsPrincipalIdealRing ℤℓ := GaloisRep.isPrincipalIdealRing_ratLocalizedAt ℓ

variable (A : ValuationSubring (AlgebraicClosure ℚ)) [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥A]
  [Algebra ↥A ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N))]
  (hρ : ∀ r : ↥(GaloisRep.ratLocalizedAt ℓ),
    ((algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥A r : ↥A) : AlgebraicClosure ℚ) =
      algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ) r)
  (hcT : ∀ a : ↥A, algebraMap ↥A ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) a =
    constantsHom N A a)
  (S : Subalgebra ↥(GaloisRep.ratLocalizedAt ℓ) ↥(modularFunctionFieldFull N))

include hρ hcT

omit hρ hcT in

theorem coe_algebraMap_T (y : Qb) : ((algebraMap Qb TT y : TT) : LaurentSeries Qb) = HahnSeries.C y := by
  rw [show ((algebraMap Qb TT y : TT) : LaurentSeries Qb) = algebraMap Qb (LaurentSeries Qb) y from rfl,
    algebraMap_laurentSeries_eq_single]
  rfl

def gS : letI : Algebra ℤℓ TT := ((algebraMap ↥A TT).comp (algebraMap ℤℓ ↥A)).toAlgebra
    S →ₐ[ℤℓ] TT := by
  letI : Algebra ℤℓ TT := ((algebraMap ↥A TT).comp (algebraMap ℤℓ ↥A)).toAlgebra
  refine
    { toFun := fun b => ⟨coeffEmb Qb ((b : FN) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange Qb (b : FN).2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp)
      commutes' := fun r => Subtype.ext ?_ }

  change coeffEmb Qb (((algebraMap ℤℓ S r : S) : FN) : LaurentSeries ℚ) =
    ((algebraMap ↥A TT (algebraMap ℤℓ ↥A r) : TT) : LaurentSeries Qb)
  rw [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply ℤℓ ℚ FN,
    show ((algebraMap ℚ FN (algebraMap ℤℓ ℚ r) : FN) : LaurentSeries ℚ) =
      valF N (algebraMap ℚ FN (algebraMap ℤℓ ℚ r)) from rfl,
    valF_algebraMap, hcT]
  change coeffMap (algebraMap ℚ Qb) (HahnSeries.single 0 (algebraMap ℤℓ ℚ r)) =
    ((algebraMap Qb TT ((algebraMap ℤℓ ↥A r : ↥A) : Qb) : TT) : LaurentSeries Qb)
  rw [coeffMap_single, coe_algebraMap_T, hρ]
  rfl

theorem gS_apply (b : S) :
    letI : Algebra ℤℓ TT := ((algebraMap ↥A TT).comp (algebraMap ℤℓ ↥A)).toAlgebra
    ((gS N ℓ A hρ hcT S b : TT) : LaurentSeries Qb) = coeffEmb Qb ((b : FN) : LaurentSeries ℚ) := rfl

theorem core :
    ∃ ψ : ↥A ⊗[ℤℓ] S →ₐ[↥A] TT,
      (∀ (a : ↥A) (b : S), (ψ (a ⊗ₜ b) : LaurentSeries Qb) =
          (constantsHom N A a : LaurentSeries Qb) *
            coeffEmb Qb ((b : FN) : LaurentSeries ℚ)) ∧
      Function.Injective ψ ∧ IsDomain ↥ψ.range := by
  classical
  letI : Algebra ℤℓ TT := ((algebraMap ↥A TT).comp (algebraMap ℤℓ ↥A)).toAlgebra
  haveI : IsScalarTower ℤℓ ↥A TT := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let ψ : ↥A ⊗[ℤℓ] S →ₐ[↥A] TT :=
    Algebra.TensorProduct.lift (Algebra.ofId ↥A TT) (gS N ℓ A hρ hcT S) (fun _ _ => Commute.all _ _)
  have hψ : ∀ (a : ↥A) (b : S), (ψ (a ⊗ₜ b) : LaurentSeries Qb) =
      (constantsHom N A a : LaurentSeries Qb) * coeffEmb Qb ((b : FN) : LaurentSeries ℚ) := by
    intro a b
    change ((Algebra.TensorProduct.lift (Algebra.ofId ↥A TT) (gS N ℓ A hρ hcT S) _ (a ⊗ₜ b) : TT) :
      LaurentSeries Qb) = _
    rw [Algebra.TensorProduct.lift_tmul, MulMemClass.coe_mul, Algebra.ofId_apply, hcT]
    rfl
  refine ⟨ψ, hψ, ?_, inferInstance⟩

  haveI : FaithfulSMul ℤℓ ↥A := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro r s h
    have h' := hρ r
    rw [h, hρ s] at h'

    change algebraMap ℚ Qb (s : ℚ) = algebraMap ℚ Qb (r : ℚ) at h'
    exact (Subtype.val_injective ((algebraMap ℚ Qb).injective h')).symm
  haveI : Module.Flat ℤℓ ↥A := inferInstance
  haveI : IsFractionRing ℤℓ ℚ := GaloisRep.isFractionRing_ratLocalizedAt ℓ

  let ιA : ↥A →ₗ[ℤℓ] Qb :=
    { toFun := fun a => (a : Qb)
      map_add' := fun _ _ => rfl
      map_smul' := fun r a => by
        change (((r • a : ↥A)) : Qb) = r • (a : Qb)
        rw [Algebra.smul_def, MulMemClass.coe_mul, hρ, show r • (a : Qb) = ((r : ℚ) • (a : Qb) : Qb) from rfl,
          Algebra.smul_def]
        rfl }
  have hιA : Function.Injective ιA := Subtype.val_injective
  let ιB : S →ₗ[ℤℓ] FN := S.val.toLinearMap
  have hιB : Function.Injective ιB := Subtype.val_injective
  obtain ⟨Θ, hΘinj, hΘ⟩ :=
    FibreIsoAux.exists_injective_to_fieldTensor ℤℓ ℚ Qb FN ↥A S ιA hιA ιB hιB

  have key : ∀ t : ↥A ⊗[ℤℓ] S,
      ((ψ t : TT) : LaurentSeries Qb) = Phi N (TensorProduct.comm ℚ Qb FN (Θ t)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [hψ, hΘ, TensorProduct.comm_tmul, Phi_tmul, mul_comm]
      congr 1
      exact coe_algebraMap_T N (a : Qb)
    | add x y hx hy =>
      rw [map_add, AddMemClass.coe_add, hx, hy, map_add, map_add, map_add]
  intro t₁ t₂ h
  have h' : Phi N (TensorProduct.comm ℚ Qb FN (Θ t₁)) = Phi N (TensorProduct.comm ℚ Qb FN (Θ t₂)) := by
    rw [← key, ← key, h]
  exact hΘinj ((TensorProduct.comm ℚ Qb FN).injective (Phi_injective N h'))

omit hρ hcT in
theorem flat_S : Module.Flat ℤℓ S := by
  haveI : FaithfulSMul ℤℓ S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro r s h
    have h' := congrArg (fun x : S => ((x : FN) : LaurentSeries ℚ)) h
    simp only [Subalgebra.coe_algebraMap] at h'
    have e : ∀ t : ℤℓ, ((algebraMap ℤℓ FN t : FN) : LaurentSeries ℚ) = HahnSeries.C (t : ℚ) := fun t => by
      rw [IsScalarTower.algebraMap_apply ℤℓ ℚ FN]
      exact valF_algebraMap N (t : ℚ)
    rw [e, e] at h'
    exact Subtype.val_injective (HahnSeries.C_injective h')
  infer_instance

section Slice

variable (K : IntermediateField ℚ (AlgebraicClosure ℚ))

omit hcT in
theorem algebraMap_K_mem (r : ℤℓ) : algebraMap K Qb (algebraMap ℤℓ K r) ∈ A := by
  have h : algebraMap K Qb (algebraMap ℤℓ K r) = algebraMap ℤℓ Qb r := rfl
  rw [h, ← hρ r]
  exact (algebraMap ℤℓ ↥A r).2

def ρK : ℤℓ →+* ↥(A.comap (algebraMap K Qb)) where
  toFun r := ⟨algebraMap ℤℓ K r, (ValuationSubring.mem_comap).mpr (algebraMap_K_mem ℓ A hρ K r)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp)

omit hcT in
theorem coe_ρK (r : ℤℓ) : ((ρK ℓ A hρ K r : ↥(A.comap (algebraMap K Qb))) : K) = algebraMap ℤℓ K r := rfl

def inclK : letI : Algebra ℤℓ ↥(A.comap (algebraMap K Qb)) := (ρK ℓ A hρ K).toAlgebra
    ↥(A.comap (algebraMap K Qb)) →ₐ[ℤℓ] ↥A := by
  letI : Algebra ℤℓ ↥(A.comap (algebraMap K Qb)) := (ρK ℓ A hρ K).toAlgebra
  exact
    { toFun := fun x => ⟨algebraMap K Qb (x : K), (ValuationSubring.mem_comap).mp x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun _ _ => Subtype.ext (by simp)
      commutes' := fun r => Subtype.ext (by
        change algebraMap K Qb ((ρK ℓ A hρ K r : ↥(A.comap (algebraMap K Qb))) : K) =
          ((algebraMap ℤℓ ↥A r : ↥A) : Qb)
        rw [coe_ρK, hρ]
        rfl) }

omit hcT in
theorem coe_inclK (x : ↥(A.comap (algebraMap K Qb))) :
    letI : Algebra ℤℓ ↥(A.comap (algebraMap K Qb)) := (ρK ℓ A hρ K).toAlgebra
    ((inclK ℓ A hρ K x : ↥A) : Qb) = algebraMap K Qb (x : K) := rfl

omit hcT in
theorem inclK_injective :
    letI : Algebra ℤℓ ↥(A.comap (algebraMap K Qb)) := (ρK ℓ A hρ K).toAlgebra
    Function.Injective (inclK ℓ A hρ K) := by
  intro x y h
  have h' := congrArg (fun z : ↥A => (z : Qb)) h
  exact Subtype.ext ((algebraMap K Qb).injective h')

theorem slice [FiniteDimensional ℚ K] (hA : A.LiesOverPrime ℓ)
    (hNBI : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
      [Algebra ℤℓ R'] [CharP (IsLocalRing.ResidueField R') ℓ]
      (K' : Type) [Field K'] [Algebra R' K'] [IsFractionRing R' K']
      [Algebra ℤℓ K'] [IsScalarTower ℤℓ R' K']
      [IsDomain (K' ⊗[ℤℓ] S)] [IsIntegrallyClosed (K' ⊗[ℤℓ] S)],
      IsDomain (R' ⊗[ℤℓ] S) ∧ IsIntegrallyClosed (R' ⊗[ℤℓ] S))
    (hGFN : ∀ (K' : Type) [Field K'] [CharZero K'] [Algebra ℤℓ K'] [FiniteDimensional ℚ K'],
      IsDomain (K' ⊗[ℤℓ] S) ∧ IsIntegrallyClosed (K' ⊗[ℤℓ] S)) :
    ∃ Im : Subalgebra ℤℓ (↥A ⊗[ℤℓ] S), IsIntegrallyClosed ↥Im ∧
      ∀ (x : K) (hx : algebraMap K Qb x ∈ A) (b : S),
        (⟨algebraMap K Qb x, hx⟩ : ↥A) ⊗ₜ b ∈ Im := by
  classical
  letI : Algebra ℤℓ ↥(A.comap (algebraMap K Qb)) := (ρK ℓ A hρ K).toAlgebra
  haveI : Module.Flat ℤℓ S := flat_S N ℓ S

  haveI hDVR : IsDiscreteValuationRing ↥(A.comap (algebraMap K Qb)) :=
    ValuationSubring.isDiscreteValuationRing_comap_of_liesOverPrime K A (Fact.out : ℓ.Prime) hA
  haveI : IsScalarTower ℤℓ ↥(A.comap (algebraMap K Qb)) K :=
    IsScalarTower.of_algebraMap_eq (fun r => rfl)
  haveI : CharP (IsLocalRing.ResidueField ↥(A.comap (algebraMap K Qb))) ℓ := by
    rw [CharP.charP_iff_prime_eq_zero (Fact.out : ℓ.Prime)]
    have h1 : ((ℓ : ℕ) : IsLocalRing.ResidueField ↥(A.comap (algebraMap K Qb))) =
        IsLocalRing.residue ↥(A.comap (algebraMap K Qb)) (ℓ : ↥(A.comap (algebraMap K Qb))) := by
      rw [map_natCast]
    rw [h1, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu' : IsUnit ((ℓ : ℕ) : ↥A) := by
      have := hu.map (inclK ℓ A hρ K)
      rwa [map_natCast] at this
    have hmem : ((ℓ : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
      rw [ValuationSubring.valuation_lt_one_iff]
      have e : (((ℓ : ℕ) : ↥A) : Qb) = ((ℓ : ℕ) : Qb) := rfl
      rw [e]
      exact (ValuationSubring.mem_nonunits_iff A).mp hA
    exact ((IsLocalRing.mem_maximalIdeal _).mp hmem) hu'
  haveI : CharZero ↥K := charZero_of_injective_algebraMap (algebraMap ℚ ↥K).injective
  obtain ⟨hKdom, hKic⟩ := hGFN ↥K
  haveI := hKdom
  haveI := hKic
  obtain ⟨hRdom, hRic⟩ := hNBI ↥(A.comap (algebraMap K Qb)) ↥K
  haveI := hRdom
  haveI := hRic

  let φ : ↥(A.comap (algebraMap K Qb)) ⊗[ℤℓ] S →ₐ[ℤℓ] ↥A ⊗[ℤℓ] S :=
    Algebra.TensorProduct.map (inclK ℓ A hρ K) (AlgHom.id ℤℓ S)
  have hφ' : ∀ t, φ t = ((inclK ℓ A hρ K).toLinearMap.rTensor S) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hφ : Function.Injective φ := by
    intro x y h
    rw [hφ', hφ'] at h
    exact Module.Flat.rTensor_preserves_injective_linearMap _ (inclK_injective ℓ A hρ K) h
  refine ⟨φ.range, ?_, ?_⟩
  · exact IsIntegrallyClosed.of_equiv (AlgEquiv.ofInjective φ hφ).toRingEquiv
  · intro x hx b
    refine ⟨(⟨x, (ValuationSubring.mem_comap).mpr hx⟩ : ↥(A.comap (algebraMap K Qb))) ⊗ₜ b, ?_⟩
    change φ ((⟨x, (ValuationSubring.mem_comap).mpr hx⟩ : ↥(A.comap (algebraMap K Qb))) ⊗ₜ b) = _
    rw [Algebra.TensorProduct.map_tmul]
    rfl

end Slice

section SliceDefs

variable (K : IntermediateField ℚ (AlgebraicClosure ℚ))

def φK : letI : Algebra ℤℓ ↥(A.comap (algebraMap K Qb)) := (ρK ℓ A hρ K).toAlgebra
    ↥(A.comap (algebraMap K Qb)) ⊗[ℤℓ] S →ₐ[ℤℓ] ↥A ⊗[ℤℓ] S :=
  letI : Algebra ℤℓ ↥(A.comap (algebraMap K Qb)) := (ρK ℓ A hρ K).toAlgebra
  Algebra.TensorProduct.map (inclK ℓ A hρ K) (AlgHom.id ℤℓ S)

def ImK : Subalgebra ℤℓ (↥A ⊗[ℤℓ] S) :=
  letI : Algebra ℤℓ ↥(A.comap (algebraMap K Qb)) := (ρK ℓ A hρ K).toAlgebra
  (φK N ℓ A hρ S K).range

omit hcT in
theorem tmul_mem_ImK (x : K) (hx : algebraMap K Qb x ∈ A) (b : S) :
    (⟨algebraMap K Qb x, hx⟩ : ↥A) ⊗ₜ b ∈ ImK N ℓ A hρ S K := by
  letI : Algebra ℤℓ ↥(A.comap (algebraMap K Qb)) := (ρK ℓ A hρ K).toAlgebra
  refine ⟨(⟨x, (ValuationSubring.mem_comap).mpr hx⟩ : ↥(A.comap (algebraMap K Qb))) ⊗ₜ b, ?_⟩
  change φK N ℓ A hρ S K ((⟨x, (ValuationSubring.mem_comap).mpr hx⟩ : ↥(A.comap (algebraMap K Qb))) ⊗ₜ b) = _
  rw [φK, Algebra.TensorProduct.map_tmul]
  rfl

omit hcT in

theorem ImK_mono {K K' : IntermediateField ℚ (AlgebraicClosure ℚ)} (hKK : K ≤ K') :
    ImK N ℓ A hρ S K ≤ ImK N ℓ A hρ S K' := by
  letI : Algebra ℤℓ ↥(A.comap (algebraMap K Qb)) := (ρK ℓ A hρ K).toAlgebra
  rintro y ⟨t, rfl⟩
  change φK N ℓ A hρ S K t ∈ ImK N ℓ A hρ S K'
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul a b =>
    rw [φK, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    have ha : algebraMap K' Qb (⟨(a : K), hKK (a : K).2⟩ : K') ∈ A := (ValuationSubring.mem_comap).mp a.2
    have := tmul_mem_ImK N ℓ A hρ S K' (⟨(a : K), hKK (a : K).2⟩ : K') ha b
    exact this
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

omit hcT in

theorem exists_mem_ImK (t : ↥A ⊗[ℤℓ] S) :
    ∃ K : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ K ∧ t ∈ ImK N ℓ A hρ S K := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨⊥, inferInstance, zero_mem _⟩
  | tmul a b =>
    refine ⟨IntermediateField.adjoin ℚ {(a : Qb)}, ?_, ?_⟩
    · exact IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (a : Qb))
    · have hmem : (a : Qb) ∈ IntermediateField.adjoin ℚ {(a : Qb)} :=
        IntermediateField.mem_adjoin_simple_self ℚ (a : Qb)
      have := tmul_mem_ImK N ℓ A hρ S (IntermediateField.adjoin ℚ {(a : Qb)}) ⟨(a : Qb), hmem⟩ a.2 b
      exact this
  | add x y hx hy =>
    obtain ⟨K₁, h₁, hx⟩ := hx
    obtain ⟨K₂, h₂, hy⟩ := hy
    haveI := h₁
    haveI := h₂
    exact ⟨K₁ ⊔ K₂, inferInstance,
      add_mem (ImK_mono N ℓ A hρ S le_sup_left hx) (ImK_mono N ℓ A hρ S le_sup_right hy)⟩

omit hcT in

theorem isIntegrallyClosed_ImK [FiniteDimensional ℚ K] (hA : A.LiesOverPrime ℓ)
    (hNBI : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
      [Algebra ℤℓ R'] [CharP (IsLocalRing.ResidueField R') ℓ]
      (K' : Type) [Field K'] [Algebra R' K'] [IsFractionRing R' K']
      [Algebra ℤℓ K'] [IsScalarTower ℤℓ R' K']
      [IsDomain (K' ⊗[ℤℓ] S)] [IsIntegrallyClosed (K' ⊗[ℤℓ] S)],
      IsDomain (R' ⊗[ℤℓ] S) ∧ IsIntegrallyClosed (R' ⊗[ℤℓ] S))
    (hGFN : ∀ (K' : Type) [Field K'] [CharZero K'] [Algebra ℤℓ K'] [FiniteDimensional ℚ K'],
      IsDomain (K' ⊗[ℤℓ] S) ∧ IsIntegrallyClosed (K' ⊗[ℤℓ] S)) :
    IsIntegrallyClosed ↥(ImK N ℓ A hρ S K) := by
  classical
  letI : Algebra ℤℓ ↥(A.comap (algebraMap K Qb)) := (ρK ℓ A hρ K).toAlgebra
  haveI : Module.Flat ℤℓ S := flat_S N ℓ S
  haveI hDVR : IsDiscreteValuationRing ↥(A.comap (algebraMap K Qb)) :=
    ValuationSubring.isDiscreteValuationRing_comap_of_liesOverPrime K A (Fact.out : ℓ.Prime) hA
  haveI : IsScalarTower ℤℓ ↥(A.comap (algebraMap K Qb)) K :=
    IsScalarTower.of_algebraMap_eq (fun r => rfl)
  haveI : CharP (IsLocalRing.ResidueField ↥(A.comap (algebraMap K Qb))) ℓ := by
    rw [CharP.charP_iff_prime_eq_zero (Fact.out : ℓ.Prime)]
    have h1 : ((ℓ : ℕ) : IsLocalRing.ResidueField ↥(A.comap (algebraMap K Qb))) =
        IsLocalRing.residue ↥(A.comap (algebraMap K Qb)) (ℓ : ↥(A.comap (algebraMap K Qb))) := by
      rw [map_natCast]
    rw [h1, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have hu' : IsUnit ((ℓ : ℕ) : ↥A) := by
      have := hu.map (inclK ℓ A hρ K)
      rwa [map_natCast] at this
    have hmem : ((ℓ : ℕ) : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
      rw [ValuationSubring.valuation_lt_one_iff]
      have e : (((ℓ : ℕ) : ↥A) : Qb) = ((ℓ : ℕ) : Qb) := rfl
      rw [e]
      exact (ValuationSubring.mem_nonunits_iff A).mp hA
    exact ((IsLocalRing.mem_maximalIdeal _).mp hmem) hu'
  haveI : CharZero ↥K := charZero_of_injective_algebraMap (algebraMap ℚ ↥K).injective
  obtain ⟨hKdom, hKic⟩ := hGFN ↥K
  haveI := hKdom
  haveI := hKic
  obtain ⟨hRdom, hRic⟩ := hNBI ↥(A.comap (algebraMap K Qb)) ↥K
  haveI := hRdom
  haveI := hRic
  have hφ' : ∀ t, φK N ℓ A hρ S K t = ((inclK ℓ A hρ K).toLinearMap.rTensor S) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [φK, Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hφ : Function.Injective (φK N ℓ A hρ S K) := by
    intro x y h
    rw [hφ', hφ'] at h
    exact Module.Flat.rTensor_preserves_injective_linearMap _ (inclK_injective ℓ A hρ K) h
  exact IsIntegrallyClosed.of_equiv (AlgEquiv.ofInjective (φK N ℓ A hρ S K) hφ).toRingEquiv

end SliceDefs

omit hcT in

theorem isIntegrallyClosed_tensor (hA : A.LiesOverPrime ℓ)
    (hNBI : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
      [Algebra ℤℓ R'] [CharP (IsLocalRing.ResidueField R') ℓ]
      (K' : Type) [Field K'] [Algebra R' K'] [IsFractionRing R' K']
      [Algebra ℤℓ K'] [IsScalarTower ℤℓ R' K']
      [IsDomain (K' ⊗[ℤℓ] S)] [IsIntegrallyClosed (K' ⊗[ℤℓ] S)],
      IsDomain (R' ⊗[ℤℓ] S) ∧ IsIntegrallyClosed (R' ⊗[ℤℓ] S))
    (hGFN : ∀ (K' : Type) [Field K'] [CharZero K'] [Algebra ℤℓ K'] [FiniteDimensional ℚ K'],
      IsDomain (K' ⊗[ℤℓ] S) ∧ IsIntegrallyClosed (K' ⊗[ℤℓ] S))
    [IsDomain (↥A ⊗[ℤℓ] S)] :
    IsIntegrallyClosed (↥A ⊗[ℤℓ] S) := by
  haveI : Nonempty {K : IntermediateField ℚ (AlgebraicClosure ℚ) // FiniteDimensional ℚ K} :=
    ⟨⟨⊥, inferInstance⟩⟩
  refine IsIntegrallyClosed.of_directed_iUnion_subring
    (fun K : {K : IntermediateField ℚ (AlgebraicClosure ℚ) // FiniteDimensional ℚ K} =>
      (ImK N ℓ A hρ S K.1).toSubring) ?_ ?_ ?_
  · rintro ⟨K₁, h₁⟩ ⟨K₂, h₂⟩
    haveI := h₁
    haveI := h₂
    exact ⟨⟨K₁ ⊔ K₂, inferInstance⟩, ImK_mono N ℓ A hρ S le_sup_left, ImK_mono N ℓ A hρ S le_sup_right⟩
  · intro b
    obtain ⟨K, hK, hb⟩ := exists_mem_ImK N ℓ A hρ S b
    exact ⟨⟨K, hK⟩, hb⟩
  · rintro ⟨K, hK⟩
    haveI := hK
    exact isIntegrallyClosed_ImK N ℓ A hρ S K hA hNBI hGFN

theorem chart (hA : A.LiesOverPrime ℓ)
    (hNBI : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
      [Algebra ℤℓ R'] [CharP (IsLocalRing.ResidueField R') ℓ]
      (K' : Type) [Field K'] [Algebra R' K'] [IsFractionRing R' K']
      [Algebra ℤℓ K'] [IsScalarTower ℤℓ R' K']
      [IsDomain (K' ⊗[ℤℓ] S)] [IsIntegrallyClosed (K' ⊗[ℤℓ] S)],
      IsDomain (R' ⊗[ℤℓ] S) ∧ IsIntegrallyClosed (R' ⊗[ℤℓ] S))
    (hGFN : ∀ (K' : Type) [Field K'] [CharZero K'] [Algebra ℤℓ K'] [FiniteDimensional ℚ K'],
      IsDomain (K' ⊗[ℤℓ] S) ∧ IsIntegrallyClosed (K' ⊗[ℤℓ] S)) :
    ∃ ψ : ↥A ⊗[ℤℓ] S →ₐ[↥A] TT,
      (∀ (a : ↥A) (b : S), (ψ (a ⊗ₜ b) : LaurentSeries Qb) =
          (constantsHom N A a : LaurentSeries Qb) *
            coeffEmb Qb ((b : FN) : LaurentSeries ℚ)) ∧
      Function.Injective ψ ∧ IsDomain ↥ψ.range ∧ IsIntegrallyClosed ↥ψ.range := by
  obtain ⟨ψ, hψ, hinj, hdom⟩ := core N ℓ A hρ hcT S
  haveI : IsDomain (↥A ⊗[ℤℓ] S) := Function.Injective.isDomain ψ.toRingHom hinj
  haveI : IsIntegrallyClosed (↥A ⊗[ℤℓ] S) := isIntegrallyClosed_tensor N ℓ A hρ S hA hNBI hGFN
  exact ⟨ψ, hψ, hinj, hdom, IsIntegrallyClosed.of_equiv (AlgEquiv.ofInjective ψ hinj).toRingEquiv⟩

end ModularCurve.IgusaScheme.FibreIsoA
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed.ModularCurve P2MW.S_ModularCurve_IgusaScheme_exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed.ModularCurve.IgusaScheme.FibreIsoA"
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed.ModularCurve P2MW.S_ModularCurve_IgusaScheme_exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed.ModularCurve.IgusaScheme"
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed.ModularCurve"

open scoped TensorProduct
p2m_open "IsLocalRing ModularCurve P2MW.S_ModularCurve_IgusaScheme_exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed.ModularCurve ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed.ModularCurve.IgusaScheme ModularCurve.CharPModel AlgebraicCurve"

theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (ρ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* ↥A)
    (hρ : A.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)) :
    letI := ρ.toAlgebra
    letI := (constantsHom N A).toAlgebra
    (∃ ψ : ↥A ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ) →ₐ[↥A]
        laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N),
      (∀ (a : ↥A) (b : ↥(chartAlgFin N ℓ)),
        (ψ (a ⊗ₜ b) : LaurentSeries (AlgebraicClosure ℚ)) =
          (constantsHom N A a : LaurentSeries (AlgebraicClosure ℚ)) *
            coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ)) ∧
      Function.Injective ψ ∧ IsDomain ↥ψ.range ∧ IsIntegrallyClosed ↥ψ.range) ∧
    (∃ ψ : ↥A ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ) →ₐ[↥A]
        laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N),
      (∀ (a : ↥A) (b : ↥(chartAlgInf N ℓ)),
        (ψ (a ⊗ₜ b) : LaurentSeries (AlgebraicClosure ℚ)) =
          (constantsHom N A a : LaurentSeries (AlgebraicClosure ℚ)) *
            coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ)) ∧
      Function.Injective ψ ∧ IsDomain ↥ψ.range ∧ IsIntegrallyClosed ↥ψ.range) := by
  letI := ρ.toAlgebra
  letI := (constantsHom N A).toAlgebra
  have hρ' : ∀ r : ↥(GaloisRep.ratLocalizedAt ℓ),
      ((algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥A r : ↥A) : AlgebraicClosure ℚ) =
        algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ) r :=
    fun r => (congrArg (fun f : ↥(GaloisRep.ratLocalizedAt ℓ) →+* AlgebraicClosure ℚ => f r) hρ :)
  have hcT : ∀ a : ↥A, algebraMap ↥A ↥(laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) a =
      constantsHom N A a := fun a => rfl
  refine ⟨?_, ?_⟩
  · refine ModularCurve.IgusaScheme.FibreIsoA.chart N ℓ A hρ' hcT (chartAlgFin N ℓ) hA ?_ ?_
    · intro R' _ _ _ _ _ K' _ _ _ _ _ _ _
      exact ModularCurve.IgusaScheme.isIntegrallyClosed_tensor_chartAlgFin_of_isDiscreteValuationRing
        N ℓ hℓN R' K'
    · intro K' _ _ _ _
      exact ModularCurve.IgusaScheme.isIntegrallyClosed_tensor_chartAlgFin_of_charZero N ℓ K'
  · refine ModularCurve.IgusaScheme.FibreIsoA.chart N ℓ A hρ' hcT (chartAlgInf N ℓ) hA ?_ ?_
    · intro R' _ _ _ _ _ K' _ _ _ _ _ _ _
      exact ModularCurve.IgusaScheme.isIntegrallyClosed_tensor_chartAlgInf_of_isDiscreteValuationRing
        N ℓ hℓN R' K'
    · intro K' _ _ _ _
      exact ModularCurve.IgusaScheme.isIntegrallyClosed_tensor_chartAlgInf_of_charZero N ℓ K'

end
p2m_reactivate "P2MW.S_ModularCurve_IgusaScheme_exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed.ModularCurve P2MW.S_ModularCurve_IgusaScheme_exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed.ModularCurve.IgusaScheme P2MW.S_ModularCurve_IgusaScheme_exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed.ModularCurve.IgusaScheme.FibreIsoA"

end S_ModularCurve_IgusaScheme_exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed (solution)
