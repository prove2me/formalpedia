-- Prove2me | solution 1 for ModularCurve.HpoolLevelRing.exists_forall_etale_rat_tensorProduct_quotient_span_aeval_jChartFin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/dac75d7c-9793-50e4-8de9-24b8b67e697f

import Mathlib
import Definitions.Def_ModularCurve_HpoolLevelRing
import Definitions.Def_JacJ1_ChartAlgebra
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_algEquiv_tensor_chartAlg
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_transcendental_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_jFull_modularFunctionFieldFull
import Theorems.Thm_IsDedekindDomain_exists_ne_zero_forall_isUnramifiedAt_of_notMem
import Theorems.Thm_IsDedekindDomain_etale_quotient_map_span_of_forall_isUnramifiedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_etale_rat_tensorProduct_quotient_span_aeval_jChartFin
p2m_attr_erase "instance" "AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

open Polynomial ModularCurve ModularCurve.HpoolLevelRing AlgebraicCurve
open scoped TensorProduct

namespace LevelL
namespace GenEt

variable (p : ℕ) [Fact p.Prime] [NeZero p]

set_option linter.unusedSectionVars false

noncomputable abbrev jF : ↥(modularFunctionFieldFull p) := IgusaScheme.jFull p

abbrev B : Type := ↥(TwoChartIntegralModel.chartAlgFin ℚ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))

noncomputable abbrev jB : B p := TwoChartIntegralModel.jChartFin ℚ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)

noncomputable scoped instance algebraPolyB : Algebra ℚ[X] (B p) :=
  (TwoChartIntegralModel.polynomialToChartFin ℚ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)).toRingHom.toAlgebra

theorem algebraMap_polyB (q : ℚ[X]) : algebraMap ℚ[X] (B p) q = Polynomial.aeval (jB p) q := rfl

scoped instance isScalarTower_polyB : IsScalarTower ℚ ℚ[X] (B p) :=
  IsScalarTower.of_algebraMap_eq' (R := ℚ) (S := ℚ[X]) (A := B p)
    ((TwoChartIntegralModel.polynomialToChartFin ℚ ↥(modularFunctionFieldFull p)
      (IgusaScheme.jFull p)).comp_algebraMap.symm)

theorem transcendental_rat_jF : Transcendental ℚ (jF p) := by
  rintro ⟨q, hq0, hq⟩
  apply ModularCurve.transcendental_jq
  refine ⟨q, hq0, ?_⟩
  set ψ : ↥(modularFunctionFieldFull p) →+* LaurentSeries ℚ :=
    algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ) with hψ
  have hval : ψ (aeval (jF p) q) = aeval jq q := by
    rw [aeval_def, hom_eval₂, aeval_def]
    have hj : ψ (jF p) = jq := rfl
    rw [hj]
    congr 1
    exact RingHom.ext_rat _ _
  rw [← hval, hq, map_zero]

theorem algebraMap_polyB_injective : Function.Injective (algebraMap ℚ[X] (B p)) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  by_contra h0
  apply transcendental_rat_jF p
  refine ⟨q, h0, ?_⟩
  have : ((aeval (jB p) q : B p) : ↥(modularFunctionFieldFull p)) = aeval (jF p) q :=
    (aeval_algHom_apply ((TwoChartIntegralModel.chartAlgFin ℚ ↥(modularFunctionFieldFull p)
      (IgusaScheme.jFull p)).val) (jB p) q).symm
  rw [← this, ← algebraMap_polyB, hq]
  rfl

scoped instance finite_polyB : Module.Finite ℚ[X] (B p) := by
  haveI := ModularCurve.finiteDimensional_adjoin_jFull_modularFunctionFieldFull p
  exact (TwoChartIntegralModel.finite_polynomial_chartAlgFin_and_chartAlgInf ℚ ℚ
    ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p) (transcendental_rat_jF p)
    (ModularCurve.finiteDimensional_adjoin_jFull_modularFunctionFieldFull p) inferInstance).1

scoped instance isDedekindDomain_B : IsDedekindDomain (B p) := by
  haveI := ModularCurve.finiteDimensional_adjoin_jFull_modularFunctionFieldFull p
  exact CurveModel.isDedekindDomain_chartRing ℚ (IgusaScheme.jFull p)

scoped instance noZeroSMulDivisors_polyB : NoZeroSMulDivisors ℚ[X] (B p) :=
  ⟨fun {c x} h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    rcases h with h | h
    · exact Or.inl ((injective_iff_map_eq_zero _).mp (algebraMap_polyB_injective p) c h)
    · exact Or.inr h⟩

scoped instance isTorsionFree_polyB : Module.IsTorsionFree ℚ[X] (B p) :=
  ⟨fun r hr x y h => by
    have hr0 : algebraMap ℚ[X] (B p) r ≠ 0 := fun h0 =>
      hr.ne_zero ((injective_iff_map_eq_zero _).mp (algebraMap_polyB_injective p) r h0)
    simp only [Algebra.smul_def] at h
    exact mul_left_cancel₀ hr0 h⟩

scoped instance faithfulSMul_polyB : FaithfulSMul ℚ[X] (B p) :=
  (faithfulSMul_iff_algebraMap_injective ℚ[X] (B p)).mpr (algebraMap_polyB_injective p)

scoped instance isSeparable_fractionRing_B : Algebra.IsSeparable (FractionRing ℚ[X]) (FractionRing (B p)) := by
  haveI : Algebra.IsIntegral ℚ[X] (B p) := inferInstance
  haveI : Algebra.IsAlgebraic (FractionRing ℚ[X]) (FractionRing (B p)) :=
    isAlgebraic_of_isFractionRing (R := ℚ[X]) (S := B p) _ _
  exact Algebra.IsAlgebraic.isSeparable_of_perfectField

theorem dvd_of_map_dvd_map (g c₀ : ℤ[X]) (hg : g.Monic)
    (h : g.map (Int.castRingHom ℚ) ∣ c₀.map (Int.castRingHom ℚ)) : g ∣ c₀ := by
  rw [← modByMonic_eq_zero_iff_dvd hg]
  have h1 : (c₀ %ₘ g).map (Int.castRingHom ℚ) = 0 := by
    rw [map_modByMonic _ hg, modByMonic_eq_zero_iff_dvd (hg.map _)]
    exact h
  exact (Polynomial.map_injective _ (Int.castRingHom ℚ).injective_int) (by rw [h1, Polynomial.map_zero])

set_option maxHeartbeats 3200000 in

theorem exists_c0_etale_quotient_B :
    ∃ c₀ : ℤ[X], c₀ ≠ 0 ∧ ∀ g : ℤ[X], g.Monic → Irreducible (g.map (Int.castRingHom ℚ)) → ¬ g ∣ c₀ →
      Algebra.Etale ℚ (B p ⧸ Ideal.map (algebraMap ℚ[X] (B p)) (Ideal.span {g.map (Int.castRingHom ℚ)})) := by
  classical
  obtain ⟨c, hc0, hc⟩ := IsDedekindDomain.exists_ne_zero_forall_isUnramifiedAt_of_notMem ℚ[X] (B p)
  obtain ⟨b, hb, hbc⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) c
  set c₀ : ℤ[X] := IsLocalization.integerNormalization (nonZeroDivisors ℤ) c with hc₀def
  have hb0 : (b : ℤ) ≠ 0 := nonZeroDivisors.ne_zero hb
  have hc₀map : c₀.map (Int.castRingHom ℚ) = (b : ℤ) • c := by
    rw [← algebraMap_int_eq]; exact hbc
  have hc₀ : c₀ ≠ 0 := by
    intro h
    rw [h, Polynomial.map_zero] at hc₀map
    exact hc0 (by
      have := hc₀map.symm
      rwa [smul_eq_zero, or_iff_right hb0] at this)
  refine ⟨c₀, hc₀, fun g hg hirr hndvd => ?_⟩
  set h : ℚ[X] := g.map (Int.castRingHom ℚ) with hhdef
  have hsep : h.Separable := hirr.separable

  have hunr : ∀ (P : Ideal (B p)) [P.IsPrime], P ≠ ⊥ →
      Ideal.span {h} ≤ P.comap (algebraMap ℚ[X] (B p)) → Algebra.IsUnramifiedAt ℚ[X] P := by
    intro P _ hP hle
    apply hc P
    intro hcP

    have hmax : (Ideal.span {h}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hirr
    have hne : P.comap (algebraMap ℚ[X] (B p)) ≠ ⊤ := Ideal.comap_ne_top _ (Ideal.IsPrime.ne_top inferInstance)
    have heq : P.comap (algebraMap ℚ[X] (B p)) = Ideal.span {h} := (hmax.eq_of_le hne hle).symm
    have hmem : c ∈ Ideal.span {h} := by rw [← heq]; exact hcP
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
    apply hndvd
    refine dvd_of_map_dvd_map g c₀ hg ?_
    rw [hc₀map, ← hhdef, ← hr]
    exact Dvd.intro ((b : ℤ) • r) (by rw [mul_comm, smul_mul_assoc])
  exact IsDedekindDomain.etale_quotient_map_span_of_forall_isUnramifiedAt (B p) h hirr hsep hunr

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution' :
    ∃ c₀ : ℤ[X], c₀ ≠ 0 ∧ ∀ g : ℤ[X], g.Monic → Irreducible (g.map (Int.castRingHom ℚ)) → ¬ g ∣ c₀ →
      Algebra.Etale ℚ ((ℚ ⊗[ℤ] Afin p) ⧸
        Ideal.span {(1 : ℚ) ⊗ₜ[ℤ] Polynomial.aeval
          (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) g}) := by
  obtain ⟨c₀, hc₀, H⟩ := exists_c0_etale_quotient_B p
  refine ⟨c₀, hc₀, fun g hg hirr hndvd => ?_⟩
  haveI := H g hg hirr hndvd

  obtain ⟨e, he⟩ := AlgebraicCurve.TwoChartIntegralModel.exists_algEquiv_tensor_chartAlg ℤ ℚ
    ↥(modularFunctionFieldFull p) (nonZeroDivisors ℤ) {IgusaScheme.jFull p}

  have hej : e ((1 : ℚ) ⊗ₜ[ℤ] TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) =
      jB p := by
    apply Subtype.ext
    rw [he, one_smul]
    rfl

  have heg : e ((1 : ℚ) ⊗ₜ[ℤ] Polynomial.aeval
      (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) g) =
      algebraMap ℚ[X] (B p) (g.map (Int.castRingHom ℚ)) := by
    have h1 : ((1 : ℚ) ⊗ₜ[ℤ] Polynomial.aeval
        (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) g) =
        Polynomial.aeval ((1 : ℚ) ⊗ₜ[ℤ] TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p)
          (IgusaScheme.jFull p)) g := by
      rw [← Algebra.TensorProduct.includeRight_apply, ← Algebra.TensorProduct.includeRight_apply,
        ← aeval_algHom_apply]
    rw [h1, show e (Polynomial.aeval ((1 : ℚ) ⊗ₜ[ℤ] TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p)
          (IgusaScheme.jFull p)) g) = Polynomial.aeval (e ((1 : ℚ) ⊗ₜ[ℤ] TwoChartIntegralModel.jChartFin ℤ
          ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p))) g from
        (aeval_algHom_apply e.toAlgHom.toRingHom.toIntAlgHom _ g).symm,
      hej, algebraMap_polyB, aeval_def, aeval_def, eval₂_map]
    congr 1
  have hI : Ideal.map (algebraMap ℚ[X] (B p)) (Ideal.span {g.map (Int.castRingHom ℚ)}) =
      Ideal.map (e : (ℚ ⊗[ℤ] Afin p) →+* B p) (Ideal.span {(1 : ℚ) ⊗ₜ[ℤ] Polynomial.aeval
        (TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) g}) := by
    rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton]
    congr 2
    exact heg.symm
  exact Algebra.Etale.of_equiv (Ideal.quotientEquivAlg _ _ e hI).symm

end LevelL.GenEt
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_etale_rat_tensorProduct_quotient_span_aeval_jChartFin.LevelL P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_etale_rat_tensorProduct_quotient_span_aeval_jChartFin.LevelL.GenEt"
p2m_reactivate "P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_etale_rat_tensorProduct_quotient_span_aeval_jChartFin.LevelL"

open LevelL.GenEt in
theorem solution (p : ℕ) [Fact p.Prime] [NeZero p] :
    ∃ c₀ : ℤ[X], c₀ ≠ 0 ∧ ∀ g : ℤ[X], g.Monic → Irreducible (g.map (Int.castRingHom ℚ)) → ¬ g ∣ c₀ →
      Algebra.Etale ℚ ((ℚ ⊗[ℤ] Afin p) ⧸
        Ideal.span {(1 : ℚ) ⊗ₜ[ℤ] Polynomial.aeval (AlgebraicCurve.TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) g}) :=
  solution' p

end S_ModularCurve_HpoolLevelRing_exists_forall_etale_rat_tensorProduct_quotient_span_aeval_jChartFin
end P2MW
export P2MW.S_ModularCurve_HpoolLevelRing_exists_forall_etale_rat_tensorProduct_quotient_span_aeval_jChartFin (solution)
