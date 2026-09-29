-- Prove2me | solution 1 for ModularCurve.exists_linearMap_injective_tensorProduct_kaehler_qExpFunctionFieldC_apply_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/ea9adaf2-7308-5baf-8515-376af83712ec

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_HeckeDifferential
import Definitions.Def_ModularCurve_QExpCoeffSemilinearAut
import Theorems.Thm_ModularCurve_diffQExp_qExpFunctionFieldC_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_linearMap_injective_tensorProduct_kaehler_qExpFunctionFieldC_apply_tmul
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.qExpandAlgHomC_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X"
p2m_attr_erase "simp" "ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct MatrixGroups
p2m_open "ModularCurve P2MW.S_ModularCurve_exists_linearMap_injective_tensorProduct_kaehler_qExpFunctionFieldC_apply_tmul.ModularCurve HahnSeries KaehlerDifferential"

namespace ModularCurve
p2m_export "ModularCurve" "qExpFunctionFieldC coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single qEuler diffQExp diffQExp_D coeffMap_mem_qExpFunctionFieldC_of_mem diffQExp_qExpFunctionFieldC_injective"
namespace BaseChangeDiff
p2m_open "ModularCurve"

variable (k : Type*) [Field k] (K : Type*) [Field K] [Algebra k K] (Γ : Subgroup SL(2, ℤ))

local notation "σ" => algebraMap k K
local notation "Fk" => qExpFunctionFieldC k Γ
local notation "FK" => qExpFunctionFieldC K Γ

def iota : ↥(qExpFunctionFieldC k Γ) →+* ↥(qExpFunctionFieldC K Γ) where
  toFun x := ⟨coeffMap (algebraMap k K) (x : LaurentSeries k),
    coeffMap_mem_qExpFunctionFieldC_of_mem (algebraMap k K) Γ x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[scoped simp] theorem coe_iota (x : ↥(qExpFunctionFieldC k Γ)) :
    ((iota k K Γ x : ↥(qExpFunctionFieldC K Γ)) : LaurentSeries K) = coeffMap (algebraMap k K) (x : LaurentSeries k) :=
  rfl

theorem coeffMap_algebraMap_eq (a : k) :
    coeffMap (algebraMap k K) (algebraMap k (LaurentSeries k) a) = algebraMap K (LaurentSeries K) (algebraMap k K a) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

scoped instance algebraFkFK : Algebra ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ) := (iota k K Γ).toAlgebra

scoped instance algebrakFK : Algebra k ↥(qExpFunctionFieldC K Γ) :=
  ((algebraMap K ↥(qExpFunctionFieldC K Γ)).comp (algebraMap k K)).toAlgebra

theorem algebraMap_Fk_FK_apply (x : ↥(qExpFunctionFieldC k Γ)) :
    algebraMap ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ) x = iota k K Γ x := rfl

theorem algebraMap_k_FK_apply (a : k) :
    algebraMap k ↥(qExpFunctionFieldC K Γ) a = algebraMap K ↥(qExpFunctionFieldC K Γ) (algebraMap k K a) := rfl

scoped instance isScalarTower_k_K_FK : IsScalarTower k K ↥(qExpFunctionFieldC K Γ) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

scoped instance isScalarTower_k_Fk_FK : IsScalarTower k ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ) := by
  refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
  apply Subtype.ext
  rw [algebraMap_k_FK_apply, algebraMap_Fk_FK_apply, coe_iota]
  change algebraMap K (LaurentSeries K) (algebraMap k K a) =
    coeffMap (algebraMap k K) (algebraMap k (LaurentSeries k) a)
  rw [coeffMap_algebraMap_eq]

scoped instance smulCommClass_K_Fk_FK : SMulCommClass K ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ) :=
  ⟨fun c f x => by
    simp only [Algebra.smul_def]
    ring⟩

scoped instance smulCommClass_Fk_K_FK : SMulCommClass ↥(qExpFunctionFieldC k Γ) K ↥(qExpFunctionFieldC K Γ) :=
  SMulCommClass.symm _ _ _

set_option synthInstance.maxHeartbeats 400000 in
scoped instance smulCommClass_k_K_FK : SMulCommClass k K ↥(qExpFunctionFieldC K Γ) where
  smul_comm a c x := by
    show a • (c • x) = c • (a • x)
    rw [Algebra.smul_def a, Algebra.smul_def a, Algebra.smul_def c, Algebra.smul_def c]
    ring

scoped instance smulCommClass_K_k_FK : SMulCommClass K k ↥(qExpFunctionFieldC K Γ) :=
  SMulCommClass.symm _ _ _

scoped instance isScalarTower_Fk_FK_Omega :
    IsScalarTower ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ) Ω[↥(qExpFunctionFieldC K Γ)⁄K] :=
  KaehlerDifferential.isScalarTower_of_tower K ↥(qExpFunctionFieldC K Γ)

scoped instance isScalarTower_k_K_Omega : IsScalarTower k K Ω[↥(qExpFunctionFieldC K Γ)⁄K] :=
  KaehlerDifferential.isScalarTower_of_tower K ↥(qExpFunctionFieldC K Γ)

scoped instance isScalarTower_K_FK_Omega : IsScalarTower K ↥(qExpFunctionFieldC K Γ) Ω[↥(qExpFunctionFieldC K Γ)⁄K] :=
  KaehlerDifferential.isScalarTower_of_tower K ↥(qExpFunctionFieldC K Γ)

def mapDiff : Ω[↥(qExpFunctionFieldC k Γ)⁄k] →ₗ[↥(qExpFunctionFieldC k Γ)] Ω[↥(qExpFunctionFieldC K Γ)⁄K] :=
  KaehlerDifferential.map k K ↥(qExpFunctionFieldC k Γ) ↥(qExpFunctionFieldC K Γ)

theorem mapDiff_D (g : ↥(qExpFunctionFieldC k Γ)) :
    mapDiff k K Γ (D k ↥(qExpFunctionFieldC k Γ) g) = D K ↥(qExpFunctionFieldC K Γ) (iota k K Γ g) :=
  KaehlerDifferential.map_D k K _ _ g

theorem mapDiff_smul (f : ↥(qExpFunctionFieldC k Γ)) (ω : Ω[↥(qExpFunctionFieldC k Γ)⁄k]) :
    mapDiff k K Γ (f • ω) = iota k K Γ f • mapDiff k K Γ ω := by
  rw [LinearMap.map_smul, ← algebraMap_smul ↥(qExpFunctionFieldC K Γ) f (mapDiff k K Γ ω), algebraMap_Fk_FK_apply]

def Phi : K ⊗[k] Ω[↥(qExpFunctionFieldC k Γ)⁄k] →ₗ[K] Ω[↥(qExpFunctionFieldC K Γ)⁄K] :=
  ((mapDiff k K Γ).restrictScalars k).liftBaseChange K

theorem Phi_tmul (c : K) (ω : Ω[↥(qExpFunctionFieldC k Γ)⁄k]) :
    Phi k K Γ (c ⊗ₜ[k] ω) = c • mapDiff k K Γ ω :=
  rfl

theorem Phi_tmul_smul_D (c : K) (f g : ↥(qExpFunctionFieldC k Γ)) (f' g' : ↥(qExpFunctionFieldC K Γ))
    (hf : (f' : LaurentSeries K) = coeffMap (algebraMap k K) (f : LaurentSeries k))
    (hg : (g' : LaurentSeries K) = coeffMap (algebraMap k K) (g : LaurentSeries k)) :
    Phi k K Γ (c ⊗ₜ[k] (f • D k ↥(qExpFunctionFieldC k Γ) g)) = c • (f' • D K ↥(qExpFunctionFieldC K Γ) g') := by
  have hf' : f' = iota k K Γ f := Subtype.ext (by rw [hf, coe_iota])
  have hg' : g' = iota k K Γ g := Subtype.ext (by rw [hg, coe_iota])
  rw [Phi_tmul, mapDiff_smul, mapDiff_D, hf', hg']

theorem coeffMap_qEuler (x : LaurentSeries k) :
    coeffMap (algebraMap k K) (qEuler k x) = qEuler K (coeffMap (algebraMap k K) x) := by
  ext m
  simp

theorem diffQExp_mapDiff (ω : Ω[↥(qExpFunctionFieldC k Γ)⁄k]) :
    diffQExp (qExpFunctionFieldC K Γ) (mapDiff k K Γ ω) =
      coeffMap (algebraMap k K) (diffQExp (qExpFunctionFieldC k Γ) ω) := by
  have hmem : ω ∈ Submodule.span ↥(qExpFunctionFieldC k Γ) (Set.range (D k ↥(qExpFunctionFieldC k Γ))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hmem using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      rw [mapDiff_D, diffQExp_D, diffQExp_D, coe_iota, coeffMap_qEuler]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  | smul f x _ hx =>
      rw [mapDiff_smul, LinearMap.map_smul, LinearMap.map_smul]
      change ((iota k K Γ f : ↥(qExpFunctionFieldC K Γ)) : LaurentSeries K) * _ =
        coeffMap (algebraMap k K) ((f : LaurentSeries k) * _)
      rw [map_mul, hx, coe_iota]

theorem diffQExp_smul_K (c : K) (η : Ω[↥(qExpFunctionFieldC K Γ)⁄K]) :
    diffQExp (qExpFunctionFieldC K Γ) (c • η) = single 0 c * diffQExp (qExpFunctionFieldC K Γ) η := by
  have h : c • η = (algebraMap K ↥(qExpFunctionFieldC K Γ) c) • η := (algebraMap_smul _ c η).symm
  rw [h, LinearMap.map_smul]
  change algebraMap K (LaurentSeries K) c * _ = _
  rw [algebraMap_laurentSeries_eq_single]

theorem sum_single_mul_coeffMap_eq_zero {ι : Type*} [Fintype ι] {e : ι → K} (he : LinearIndependent k e)
    (s : ι → LaurentSeries k) (h : ∑ i, single 0 (e i) * coeffMap (algebraMap k K) (s i) = 0) :
    ∀ i, s i = 0 := by
  classical
  have hcoeff : ∀ (n : ℤ) (i : ι), (s i).coeff n = 0 := by
    intro n
    have hn := congrArg (fun z : LaurentSeries K => z.coeff n) h
    simp only [HahnSeries.coeff_sum, coeff_single_zero_mul, coeffMap_coeff, HahnSeries.coeff_zero] at hn

    have hn' : ∑ i, ((s i).coeff n) • e i = 0 := by
      rw [← hn]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, mul_comm]
    exact fun i => Fintype.linearIndependent_iff.mp he _ hn' i
  intro i
  ext n
  rw [hcoeff n i, HahnSeries.coeff_zero]

variable [IsAlgClosed k] [Γ.FiniteIndex]

set_option maxHeartbeats 6400000 in

theorem Phi_injective (hT : ModularGroup.T ∈ Γ) : Function.Injective (Phi k K Γ) := by
  classical
  have hinjk := ModularCurve.diffQExp_qExpFunctionFieldC_injective k Γ hT
  rw [injective_iff_map_eq_zero]
  intro x hx

  let b := Module.Basis.ofVectorSpace k K
  let e : K ⊗[k] Ω[↥(qExpFunctionFieldC k Γ)⁄k] ≃ₗ[k]
      (Module.Basis.ofVectorSpaceIndex k K →₀ Ω[↥(qExpFunctionFieldC k Γ)⁄k]) :=
    (TensorProduct.congr b.repr (LinearEquiv.refl k _)).trans
      (TensorProduct.finsuppScalarLeft k Ω[↥(qExpFunctionFieldC k Γ)⁄k] _)
  set v := e x with hv
  have hxv : x = e.symm v := by rw [hv, LinearEquiv.symm_apply_apply]
  have hdecomp : x = ∑ α ∈ v.support, b α ⊗ₜ[k] v α := by
    conv_lhs => rw [hxv, ← Finsupp.sum_single v]
    rw [map_finsuppSum, Finsupp.sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    change (TensorProduct.congr b.repr (LinearEquiv.refl k _)).symm
        ((TensorProduct.finsuppScalarLeft k Ω[↥(qExpFunctionFieldC k Γ)⁄k] _).symm (Finsupp.single α (v α))) = _
    rw [TensorProduct.finsuppScalarLeft_symm_apply_single, TensorProduct.congr_symm_tmul]
    simp only [LinearEquiv.refl_symm, LinearEquiv.refl_apply, Module.Basis.repr_symm_apply,
      Finsupp.linearCombination_single, one_smul]

  have hΦ : ∑ α ∈ v.support, b α • mapDiff k K Γ (v α) = 0 := by
    rw [← hx, hdecomp, map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Phi_tmul]
  have hΘ : ∑ α ∈ v.support, single 0 (b α) * coeffMap (algebraMap k K)
      (diffQExp (qExpFunctionFieldC k Γ) (v α)) = 0 := by
    have := congrArg (diffQExp (qExpFunctionFieldC K Γ)) hΦ
    rw [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [diffQExp_smul_K, diffQExp_mapDiff]

  have hli : LinearIndependent k (fun α : v.support => b (α : Module.Basis.ofVectorSpaceIndex k K)) :=
    b.linearIndependent.comp _ Subtype.val_injective
  have hsum' : ∑ i : ↥v.support, single 0 (b (i : Module.Basis.ofVectorSpaceIndex k K)) *
      coeffMap (algebraMap k K) (diffQExp (qExpFunctionFieldC k Γ) (v i)) = 0 := by
    rw [Finset.sum_coe_sort v.support (fun α => single 0 (b α) *
      coeffMap (algebraMap k K) (diffQExp (qExpFunctionFieldC k Γ) (v α)))]
    exact hΘ
  have hzero := sum_single_mul_coeffMap_eq_zero k K hli
    (fun α : v.support => diffQExp (qExpFunctionFieldC k Γ) (v α)) hsum'
  have hvα : ∀ α ∈ v.support, v α = 0 := by
    intro α hα
    apply hinjk
    rw [map_zero]
    exact hzero ⟨α, hα⟩
  have hv0 : v = 0 := by
    ext α
    by_cases hα : α ∈ v.support
    · rw [hvα α hα]; rfl
    · rwa [Finsupp.notMem_support_iff] at hα
  rw [hxv, hv0, map_zero]

end ModularCurve.BaseChangeDiff
p2m_reactivate "P2MW.S_ModularCurve_exists_linearMap_injective_tensorProduct_kaehler_qExpFunctionFieldC_apply_tmul.ModularCurve P2MW.S_ModularCurve_exists_linearMap_injective_tensorProduct_kaehler_qExpFunctionFieldC_apply_tmul.ModularCurve.BaseChangeDiff"
p2m_reactivate "P2MW.S_ModularCurve_exists_linearMap_injective_tensorProduct_kaehler_qExpFunctionFieldC_apply_tmul.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_linearMap_injective_tensorProduct_kaehler_qExpFunctionFieldC_apply_tmul.ModularCurve P2MW.S_ModularCurve_exists_linearMap_injective_tensorProduct_kaehler_qExpFunctionFieldC_apply_tmul.ModularCurve.BaseChangeDiff"

open scoped TensorProduct MatrixGroups in
open _root_.ModularCurve _root_.P2MW.S_ModularCurve_exists_linearMap_injective_tensorProduct_kaehler_qExpFunctionFieldC_apply_tmul.ModularCurve KaehlerDifferential in

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] (K : Type*) [Field K] [Algebra k K]
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) :
    ∃ Φ : K ⊗[k] Ω[↥(qExpFunctionFieldC k Γ)⁄k] →ₗ[K] Ω[↥(qExpFunctionFieldC K Γ)⁄K],
      Function.Injective Φ ∧
      ∀ (c : K) (f g : ↥(qExpFunctionFieldC k Γ)) (f' g' : ↥(qExpFunctionFieldC K Γ)),
        (f' : LaurentSeries K) = coeffMap (algebraMap k K) (f : LaurentSeries k) →
        (g' : LaurentSeries K) = coeffMap (algebraMap k K) (g : LaurentSeries k) →
        Φ (c ⊗ₜ[k] (f • D k ↥(qExpFunctionFieldC k Γ) g)) = c • (f' • D K ↥(qExpFunctionFieldC K Γ) g') :=
  ⟨BaseChangeDiff.Phi k K Γ, BaseChangeDiff.Phi_injective k K Γ hT,
    fun c f g f' g' hf hg => BaseChangeDiff.Phi_tmul_smul_D k K Γ c f g f' g' hf hg⟩

#print axioms solution

end S_ModularCurve_exists_linearMap_injective_tensorProduct_kaehler_qExpFunctionFieldC_apply_tmul
end P2MW
export P2MW.S_ModularCurve_exists_linearMap_injective_tensorProduct_kaehler_qExpFunctionFieldC_apply_tmul (solution)
