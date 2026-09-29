-- Prove2me | solution 1 for ModularCurve.genusFF_qExpFunctionFieldC_eq_of_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/d186ba5f-52de-52f9-9fa6-8fc3cce11c20

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_LaurentSeries_eq_C_coeff_zero_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_genusFF_qExpFunctionFieldC_eq_of_ringHom
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"

set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped MatrixGroups
p2m_open "IntermediateField AlgebraicCurve ModularCurve P2MW.S_ModularCurve_genusFF_qExpFunctionFieldC_eq_of_ringHom.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "intSeriesC intFormRatiosC qExpFunctionFieldC div_mem_qExpFunctionFieldC coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single"
namespace QExpConstExt
p2m_open "ModularCurve"

section CoeffChange

variable {K₀ K : Type*} [Field K₀] [Field K] (φ : K₀ →+* K) (Γ : Subgroup SL(2, ℤ))

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : PowerSeries R) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R x) = HahnSeries.ofPowerSeries ℤ S (x.map f) := by
  ext i
  rw [coeffMap_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hi
  · exact map_zero f
  · rw [PowerSeries.coeff_map]

theorem coeffMap_intSeriesC (p : PowerSeries ℤ) : coeffMap φ (intSeriesC K₀ p) = intSeriesC K p := by
  rw [intSeriesC, coeffMap_ofPowerSeries, intSeriesC]
  congr 1
  ext n
  simp [PowerSeries.coeff_map]

theorem coeffMap_injective : Function.Injective (coeffMap φ) := by
  intro x y h
  ext n
  have h1 := congrArg (fun s : LaurentSeries K => s.coeff n) h
  simp only [coeffMap_coeff] at h1
  exact φ.injective h1

theorem coeffMap_algebraMap_const (c : K₀) :
    coeffMap φ (algebraMap K₀ (LaurentSeries K₀) c) = algebraMap K (LaurentSeries K) (φ c) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem coeffMap_C (c : K₀) : coeffMap φ (HahnSeries.C c) = HahnSeries.C (φ c) := by
  rw [HahnSeries.C_apply, HahnSeries.C_apply, coeffMap_single]

theorem coeffMap_mem {x : LaurentSeries K₀} (hx : x ∈ qExpFunctionFieldC K₀ Γ) :
    coeffMap φ x ∈ qExpFunctionFieldC K Γ := by
  change x ∈ adjoin K₀ (intFormRatiosC K₀ Γ) at hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨κ, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
    have hgK : intSeriesC K pg ≠ 0 := by
      rw [← coeffMap_intSeriesC φ]
      exact (map_ne_zero_iff _ (coeffMap_injective φ)).mpr hg0
    rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]
    exact div_mem_qExpFunctionFieldC f g hf hg hgK
  | algebraMap c =>
    rw [coeffMap_algebraMap_const]
    exact IntermediateField.algebraMap_mem _ _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

def qMap : qExpFunctionFieldC K₀ Γ →+* qExpFunctionFieldC K Γ :=
  ((coeffMap φ).comp (qExpFunctionFieldC K₀ Γ).subtype).codRestrict
    (qExpFunctionFieldC K Γ).toSubring fun x => coeffMap_mem φ Γ x.2

@[scoped simp] theorem coe_qMap (x : qExpFunctionFieldC K₀ Γ) :
    (qMap φ Γ x : LaurentSeries K) = coeffMap φ x := rfl

theorem le_map_adjoin_range :
    qExpFunctionFieldC K Γ ≤
      (IntermediateField.adjoin K (Set.range (qMap φ Γ))).map (qExpFunctionFieldC K Γ).val := by
  change IntermediateField.adjoin K (intFormRatiosC K Γ) ≤ _
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨κ, f, g, pf, pg, hf, hg, hg0, rfl⟩
  have hg0' : intSeriesC K₀ pg ≠ 0 := by
    intro h
    apply hg0
    rw [← coeffMap_intSeriesC φ, h, map_zero]
  refine (IntermediateField.mem_map _).mpr
    ⟨⟨intSeriesC K pf / intSeriesC K pg, div_mem_qExpFunctionFieldC f g hf hg hg0⟩, ?_, rfl⟩
  apply IntermediateField.subset_adjoin
  refine ⟨⟨intSeriesC K₀ pf / intSeriesC K₀ pg, div_mem_qExpFunctionFieldC f g hf hg hg0'⟩, ?_⟩
  apply Subtype.ext
  change coeffMap φ (intSeriesC K₀ pf / intSeriesC K₀ pg) = intSeriesC K pf / intSeriesC K pg
  rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]

end CoeffChange

section Transfer

variable {K K' F F' : Type*} [Field K] [Field K'] [Field F] [Field F']
  [Algebra K F] [Algebra K' F'] [Algebra K K'] [Algebra F F'] [Algebra K F']
  [IsScalarTower K K' F'] [IsScalarTower K F F']

theorem finiteDimensional_adjoin_algebraMap
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (x : F) (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    FiniteDimensional (IntermediateField.adjoin K' ({algebraMap F F' x} : Set F')) F' := by
  classical
  let ψ : F →+* F' := algebraMap F F'
  let ψa : F →ₐ[K] F' := IsScalarTower.toAlgHom K F F'
  have hψa : ∀ y, ψa y = ψ y := fun _ => rfl
  let Kx : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F)
  let M : IntermediateField K' F' := IntermediateField.adjoin K' ({ψ x} : Set F')

  have hθmem : ∀ c : Kx, ψ (c : F) ∈ M := by
    intro c
    have h1 : ψa (c : F) ∈ Kx.map ψa := (IntermediateField.mem_map _).mpr ⟨c, c.2, rfl⟩
    have h2 : Kx.map ψa = IntermediateField.adjoin K ({ψa x} : Set F') := by
      change (IntermediateField.adjoin K ({x} : Set F)).map ψa = _
      rw [IntermediateField.adjoin_map, Set.image_singleton]
    rw [h2] at h1
    have hle : IntermediateField.adjoin K ({ψa x} : Set F') ≤ M.restrictScalars K := by
      rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      exact IntermediateField.subset_adjoin K' _ (Set.mem_singleton _)
    exact hle h1
  let θ : Kx →+* M := (ψ.comp Kx.subtype).codRestrict M.toSubring fun c => hθmem c
  have hθ : ∀ c : Kx, ((θ c : M) : F') = ψ c := fun _ => rfl

  letI : Algebra Kx M := θ.toAlgebra
  haveI : IsScalarTower Kx M F' := IsScalarTower.of_algebraMap_eq fun c => (hθ c).symm

  haveI : Algebra.IsIntegral Kx F := Algebra.IsIntegral.of_finite Kx F
  have hint : ∀ y : F, IsIntegral M (ψ y) := by
    intro y
    have h1 : IsIntegral Kx y := Algebra.IsIntegral.isIntegral y
    have h2 : IsIntegral Kx (ψ y) := h1.map (IsScalarTower.toAlgHom Kx F F')
    exact h2.tower_top

  let b := Module.finBasis Kx F
  let S : Set F' := Set.range fun i => ψ (b i)
  haveI : Finite S := (Set.finite_range _).to_subtype
  haveI hfd : FiniteDimensional M (IntermediateField.adjoin M S) :=
    IntermediateField.finiteDimensional_adjoin fun y hy => by
      obtain ⟨i, rfl⟩ := hy
      exact hint (b i)
  have hrange : Set.range ψ ⊆ (IntermediateField.adjoin M S : Set F') := by
    rintro _ ⟨y, rfl⟩
    have hy : y = ∑ i, (b.repr y i) • b i := (b.sum_repr y).symm
    rw [hy, map_sum]
    refine sum_mem fun i _ => ?_
    rw [Algebra.smul_def, map_mul]
    have h1 : ψ (algebraMap Kx F (b.repr y i)) = algebraMap M F' (θ (b.repr y i)) := rfl
    rw [h1]
    refine mul_mem (IntermediateField.algebraMap_mem _ _) ?_
    exact IntermediateField.subset_adjoin M S ⟨i, rfl⟩
  have htop : IntermediateField.adjoin M S = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z ∈ (⊤ : IntermediateField K' F') := IntermediateField.mem_top
    rw [← hgen] at hz
    have hle : IntermediateField.adjoin K' (Set.range ψ) ≤
        (IntermediateField.adjoin M S).restrictScalars K' :=
      IntermediateField.adjoin_le_iff.mpr hrange
    exact hle hz
  have e : (IntermediateField.adjoin M S) ≃ₗ[M] F' :=
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv).toLinearEquiv
  exact LinearEquiv.finiteDimensional e

end Transfer

section Transc

variable {K₀ K : Type*} [Field K₀] [Field K] (φ : K₀ →+* K) (Γ : Subgroup SL(2, ℤ))

theorem transcendental_qMap {x : qExpFunctionFieldC K₀ Γ} (hx : Transcendental K₀ x) :
    Transcendental K (qMap φ Γ x) := by
  intro halg
  apply hx

  have halg' : IsAlgebraic K ((qMap φ Γ x : qExpFunctionFieldC K Γ) : LaurentSeries K) :=
    halg.algebraMap
  have hconst := LaurentSeries.eq_C_coeff_zero_of_isAlgebraic halg'
  rw [coe_qMap, coeffMap_coeff] at hconst

  have hx0 : (x : LaurentSeries K₀) = HahnSeries.C ((x : LaurentSeries K₀).coeff 0) := by
    apply coeffMap_injective φ
    rw [coeffMap_C]
    exact hconst
  have halgx : IsAlgebraic K₀ (x : LaurentSeries K₀) := by
    rw [hx0, HahnSeries.C_apply, ← algebraMap_laurentSeries_eq_single]
    exact isAlgebraic_algebraMap _
  exact (isAlgebraic_algebraMap_iff (R := K₀) (A := LaurentSeries K₀)
    (FaithfulSMul.algebraMap_injective (qExpFunctionFieldC K₀ Γ) (LaurentSeries K₀))).mp halgx

end Transc

section Main

variable {K₀ K : Type*} [Field K₀] [Field K]

set_option maxHeartbeats 3200000 in

theorem genusFF_eq [IsAlgClosed K₀] [IsAlgClosed K] (φ : K₀ →+* K) (Γ : Subgroup SL(2, ℤ))
    (hfg : ∃ x : qExpFunctionFieldC K₀ Γ, Transcendental K₀ x ∧
      FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set (qExpFunctionFieldC K₀ Γ)))
        (qExpFunctionFieldC K₀ Γ)) :
    genusFF K (qExpFunctionFieldC K Γ) = genusFF K₀ (qExpFunctionFieldC K₀ Γ) := by
  letI : Algebra K₀ K := φ.toAlgebra
  letI : Algebra (qExpFunctionFieldC K₀ Γ) (qExpFunctionFieldC K Γ) := (qMap φ Γ).toAlgebra
  letI : Algebra K₀ (qExpFunctionFieldC K Γ) :=
    ((algebraMap K (qExpFunctionFieldC K Γ)).comp φ).toAlgebra
  haveI : IsScalarTower K₀ K (qExpFunctionFieldC K Γ) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower K₀ (qExpFunctionFieldC K₀ Γ) (qExpFunctionFieldC K Γ) := by
    refine IsScalarTower.of_algebraMap_eq (fun c => ?_)
    apply Subtype.ext
    change algebraMap K (LaurentSeries K) (φ c) = coeffMap φ (algebraMap K₀ (LaurentSeries K₀) c)
    rw [coeffMap_algebraMap_const]
  have hψ : ∀ y, algebraMap (qExpFunctionFieldC K₀ Γ) (qExpFunctionFieldC K Γ) y = qMap φ Γ y :=
    fun _ => rfl

  have hgen : IntermediateField.adjoin K
      (Set.range (algebraMap (qExpFunctionFieldC K₀ Γ) (qExpFunctionFieldC K Γ))) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨y, hy, hyz⟩ := (IntermediateField.mem_map _).mp (le_map_adjoin_range φ Γ z.2)
    rwa [← Subtype.ext hyz]
  obtain ⟨x, hx, hfin⟩ := hfg
  have hx' : Transcendental K (algebraMap (qExpFunctionFieldC K₀ Γ) (qExpFunctionFieldC K Γ) x) := by
    rw [hψ]; exact transcendental_qMap φ Γ hx
  have hfin' := finiteDimensional_adjoin_algebraMap (K := K₀) (K' := K) hgen x hfin
  haveI : IsCurveOver K₀ (qExpFunctionFieldC K₀ Γ) :=
    isCurveOver_of_transcendental_of_perfectField hx hfin
  haveI : IsCurveOver K (qExpFunctionFieldC K Γ) :=
    isCurveOver_of_transcendental_of_perfectField hx' hfin'
  exact genusFF_eq_of_constantFieldExtension_of_isAlgClosed K₀ (qExpFunctionFieldC K₀ Γ) K
    (qExpFunctionFieldC K Γ) ⟨x, hx, hfin⟩ ⟨_, hx', hfin'⟩ hgen

end Main

end ModularCurve.QExpConstExt
p2m_reactivate "P2MW.S_ModularCurve_genusFF_qExpFunctionFieldC_eq_of_ringHom.ModularCurve P2MW.S_ModularCurve_genusFF_qExpFunctionFieldC_eq_of_ringHom.ModularCurve.QExpConstExt"
p2m_reactivate "P2MW.S_ModularCurve_genusFF_qExpFunctionFieldC_eq_of_ringHom.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_genusFF_qExpFunctionFieldC_eq_of_ringHom.ModularCurve P2MW.S_ModularCurve_genusFF_qExpFunctionFieldC_eq_of_ringHom.ModularCurve.QExpConstExt"

theorem solution
    {K₀ K : Type*} [Field K₀] [Field K] [IsAlgClosed K₀] [IsAlgClosed K] (φ : K₀ →+* K)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hfg : ∃ x : ModularCurve.qExpFunctionFieldC K₀ Γ, Transcendental K₀ x ∧
      FiniteDimensional
        (IntermediateField.adjoin K₀ ({x} : Set (ModularCurve.qExpFunctionFieldC K₀ Γ)))
        (ModularCurve.qExpFunctionFieldC K₀ Γ)) :
    AlgebraicCurve.genusFF K (ModularCurve.qExpFunctionFieldC K Γ) =
      AlgebraicCurve.genusFF K₀ (ModularCurve.qExpFunctionFieldC K₀ Γ) :=
  ModularCurve.QExpConstExt.genusFF_eq φ Γ hfg

end S_ModularCurve_genusFF_qExpFunctionFieldC_eq_of_ringHom
end P2MW
export P2MW.S_ModularCurve_genusFF_qExpFunctionFieldC_eq_of_ringHom (solution)
