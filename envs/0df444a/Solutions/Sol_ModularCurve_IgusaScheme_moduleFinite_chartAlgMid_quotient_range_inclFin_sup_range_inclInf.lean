-- Prove2me | solution 1 for ModularCurve.IgusaScheme.moduleFinite_chartAlgMid_quotient_range_inclFin_sup_range_inclInf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/3c20d780-9a54-5da3-930a-7a7fe6c767c9

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Theorems.Thm_ModularCurve_IgusaScheme_finiteType_chartAlgFin_and_chartAlgInf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_moduleFinite_chartAlgMid_quotient_range_inclFin_sup_range_inclInf
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord"

open ModularCurve ModularCurve.IgusaScheme Polynomial

noncomputable section

namespace IgusaCechH1Finite

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)
set_option quotPrecheck false in
local notation "F" => ↥(modularFunctionFieldFull N)

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem exists_finset_span_polynomial :
    ∃ T : Finset F, (↑T ⊆ (chartAlgFin N ℓ : Set F)) ∧ ∀ a : F, a ∈ chartAlgFin N ℓ →
      ∃ f : F → ℤℓ[X], a = ∑ t ∈ T, aeval (jFull N) (f t) * t := by
  classical
  let P0 : Subalgebra ℤℓ F := Algebra.adjoin ℤℓ {jFull N}
  have hle : P0 ≤ chartAlgFin N ℓ := adjoin_le_chartAlg N ℓ _
  haveI : Algebra.FiniteType ℤℓ ↥(chartAlgFin N ℓ) := (finiteType_chartAlgFin_and_chartAlgInf N ℓ).1
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra ℤℓ ↥(chartAlgFin N ℓ)).FG)

  let s' : Finset F := s.image Subtype.val
  have hs'sub : (↑s' : Set F) ⊆ chartAlgFin N ℓ := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
    exact y.2
  have hs'int : ∀ x ∈ (↑s' : Set F), IsIntegral P0 x := fun x hx =>
    (mem_chartAlg_iff N ℓ).mp (hs'sub hx)
  have hFG : (Algebra.adjoin P0 (↑s' : Set F)).toSubmodule.FG :=
    fg_adjoin_of_finite s'.finite_toSet hs'int
  obtain ⟨T, hT⟩ := hFG

  have hadj : (chartAlgFin N ℓ : Subalgebra ℤℓ F) = Algebra.adjoin ℤℓ (↑s' : Set F) := by
    have h1 : (Algebra.adjoin ℤℓ (↑s : Set ↥(chartAlgFin N ℓ))).map (chartAlgFin N ℓ).val =
        Algebra.adjoin ℤℓ (↑s' : Set F) := by
      rw [AlgHom.map_adjoin]
      congr 1
      simp [s']
    rw [← h1, hs, Algebra.map_top, Subalgebra.range_val]

  let A0' : Subalgebra P0 F :=
    { (chartAlgFin N ℓ).toSubring with
      algebraMap_mem' := fun r => hle r.2 }
  have hsub1 : Algebra.adjoin P0 (↑s' : Set F) ≤ A0' := Algebra.adjoin_le hs'sub
  have hsub2 : Algebra.adjoin ℤℓ (↑s' : Set F) ≤ (Algebra.adjoin P0 (↑s' : Set F)).restrictScalars ℤℓ :=
    Algebra.adjoin_le Algebra.subset_adjoin
  refine ⟨T, ?_, fun a ha => ?_⟩
  · intro t ht
    have : (t : F) ∈ (Algebra.adjoin P0 (↑s' : Set F)).toSubmodule := by
      rw [← hT]; exact Submodule.subset_span ht
    exact hsub1 this
  · have ha' : a ∈ Submodule.span P0 (↑T : Set F) := by
      rw [hT]
      have ha2 : a ∈ Algebra.adjoin ℤℓ (↑s' : Set F) := hadj ▸ ha
      exact hsub2 ha2
    obtain ⟨g, -, hg⟩ := Submodule.mem_span_finset.mp ha'
    have hpoly : ∀ t, ∃ f : ℤℓ[X], ((g t : P0) : F) = aeval (jFull N) f := fun t => by
      have hmem : ((g t : P0) : F) ∈ Algebra.adjoin ℤℓ {jFull N} := (g t).2
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hmem
      obtain ⟨f, hf⟩ := hmem
      exact ⟨f, hf.symm⟩
    choose f hf using hpoly
    refine ⟨f, ?_⟩
    rw [← hg]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← hf, Subalgebra.smul_def]
    rfl

end IgusaCechH1Finite

namespace IgusaCechH1Finite

set_option synthInstance.maxHeartbeats 1600000

variable (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]

set_option quotPrecheck false in
local notation "ℤℓ" => ↥(GaloisRep.ratLocalizedAt ℓ)
set_option quotPrecheck false in
local notation "F" => ↥(modularFunctionFieldFull N)

abbrev J : ↥(chartAlgMid N ℓ) := inclFin N ℓ (jChartFin N ℓ)
abbrev U : ↥(chartAlgMid N ℓ) := inclInf N ℓ (jInvChartInf N ℓ)

theorem J_mul_U : J N ℓ * U N ℓ = 1 := by
  apply Subtype.ext
  rw [Subalgebra.coe_mul, Subalgebra.coe_one, coe_chartIncl, coe_chartIncl, coe_jChartFin, coe_jInvChartInf]
  exact mul_inv_cancel₀ (jFull_ne_zero N)

theorem U_pow_mul_J_pow_of_le {i k : ℕ} (h : i ≤ k) : J N ℓ ^ i * U N ℓ ^ k = U N ℓ ^ (k - i) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, ← mul_assoc, ← mul_pow, J_mul_U, one_pow, one_mul, Nat.add_sub_cancel_left]

theorem U_pow_mul_J_pow_of_lt {i k : ℕ} (h : k < i) : J N ℓ ^ i * U N ℓ ^ k = J N ℓ ^ (i - k) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt h
  rw [show k + d + 1 = (d + 1) + k by ring, pow_add, mul_assoc, ← mul_pow, J_mul_U, one_pow,
    mul_one, Nat.add_sub_cancel]

abbrev W : Submodule ℤℓ ↥(chartAlgMid N ℓ) :=
  LinearMap.range (inclFin N ℓ).toLinearMap ⊔ LinearMap.range (inclInf N ℓ).toLinearMap

theorem inclFin_mem_W (a : ↥(chartAlgFin N ℓ)) : inclFin N ℓ a ∈ W N ℓ :=
  Submodule.mem_sup_left ⟨a, rfl⟩

theorem inclInf_mem_W (b : ↥(chartAlgInf N ℓ)) : inclInf N ℓ b ∈ W N ℓ :=
  Submodule.mem_sup_right ⟨b, rfl⟩

theorem exists_mul_J_pow_eq (x : ↥(chartAlgMid N ℓ)) :
    ∃ (a : ↥(chartAlgFin N ℓ)) (k : ℕ), x * J N ℓ ^ k = inclFin N ℓ a := by
  letI := (inclFin N ℓ).toRingHom.toAlgebra
  haveI := isLocalization_away_inclFin N ℓ
  obtain ⟨⟨a, ⟨_, k, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers (jChartFin N ℓ)) x
  refine ⟨a, k, ?_⟩
  simpa [RingHom.algebraMap_toAlgebra] using h

theorem exists_mul_U_pow_eq (x : ↥(chartAlgMid N ℓ)) :
    ∃ (b : ↥(chartAlgInf N ℓ)) (k : ℕ), x * U N ℓ ^ k = inclInf N ℓ b := by
  letI := (inclInf N ℓ).toRingHom.toAlgebra
  haveI := isLocalization_away_inclInf N ℓ
  obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers (jInvChartInf N ℓ)) x
  refine ⟨b, k, ?_⟩
  simpa [RingHom.algebraMap_toAlgebra] using h

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem moduleFinite_quotient :
    Module.Finite ℤℓ (↥(chartAlgMid N ℓ) ⧸ W N ℓ) := by
  classical
  obtain ⟨T, hTsub, hTspan⟩ := exists_finset_span_polynomial N ℓ

  let M : F → ↥(chartAlgMid N ℓ) := fun t =>
    if h : t ∈ (chartAlgFin N ℓ : Set F) then inclFin N ℓ ⟨t, h⟩ else 0
  have hMcoe : ∀ t ∈ T, (M t : F) = t := fun t ht => by
    simp only [M, dif_pos (hTsub ht), coe_chartIncl]

  have hd : ∀ t, ∃ (b : ↥(chartAlgInf N ℓ)) (d : ℕ), M t * U N ℓ ^ d = inclInf N ℓ b :=
    fun t => exists_mul_U_pow_eq N ℓ (M t)
  choose b d hbd using hd

  let G : Finset ↥(chartAlgMid N ℓ) :=
    T.biUnion fun t => (Finset.range (d t)).image fun s => U N ℓ ^ s * M t
  have hG : ∀ t ∈ T, ∀ s < d t, U N ℓ ^ s * M t ∈ Submodule.span ℤℓ (↑G : Set ↥(chartAlgMid N ℓ)) :=
    fun t ht s hs => Submodule.subset_span (Finset.mem_biUnion.mpr
      ⟨t, ht, Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr hs, rfl⟩⟩)

  have hkey : ∀ x : ↥(chartAlgMid N ℓ), x ∈ W N ℓ ⊔ Submodule.span ℤℓ (↑G : Set ↥(chartAlgMid N ℓ)) := by
    intro x
    obtain ⟨a, k, hak⟩ := exists_mul_J_pow_eq N ℓ x
    have hx : x = inclFin N ℓ a * U N ℓ ^ k := by
      rw [← hak, mul_assoc, ← mul_pow, J_mul_U, one_pow, mul_one]
    obtain ⟨f, hf⟩ := hTspan a a.2
    have ha : inclFin N ℓ a = ∑ t ∈ T, aeval (J N ℓ) (f t) * M t := by
      apply Subtype.ext
      rw [coe_chartIncl, hf]
      rw [← Subalgebra.coe_val, map_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [map_mul]
      change _ = ((aeval (J N ℓ) (f t) : ↥(chartAlgMid N ℓ)) : F) * (M t : F)
      rw [hMcoe t ht, Polynomial.aeval_subalgebra_coe, coe_chartIncl, coe_jChartFin]
    rw [hx, ha, Finset.sum_mul]
    refine Submodule.sum_mem _ fun t ht => ?_
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_mul, Finset.sum_mul]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc]
    refine Submodule.smul_mem _ _ ?_
    rw [mul_right_comm]
    rcases le_or_gt i k with hik | hik
    · rw [U_pow_mul_J_pow_of_le N ℓ hik]
      rcases lt_or_ge (k - i) (d t) with hlt | hge
      · exact Submodule.mem_sup_right (hG t ht _ hlt)
      · refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
        obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hge
        refine ⟨jInvChartInf N ℓ ^ e * b t, ?_⟩
        change inclInf N ℓ (jInvChartInf N ℓ ^ e * b t) = _
        rw [he, add_comm, pow_add, mul_assoc, mul_comm (U N ℓ ^ d t), hbd t, map_mul, map_pow]
    · rw [U_pow_mul_J_pow_of_lt N ℓ hik]
      refine Submodule.mem_sup_left (Submodule.mem_sup_left ?_)
      by_cases hmem : (t : F) ∈ (chartAlgFin N ℓ : Set F)
      · refine ⟨jChartFin N ℓ ^ (i - k) * ⟨t, hmem⟩, ?_⟩
        change inclFin N ℓ (jChartFin N ℓ ^ (i - k) * ⟨t, hmem⟩) = _
        rw [map_mul, map_pow]
        simp only [M, dif_pos hmem]
      · refine ⟨0, ?_⟩
        change inclFin N ℓ 0 = _
        simp only [M, dif_neg hmem, mul_zero, map_zero]

  rw [Module.finite_def]
  have htop : (⊤ : Submodule ℤℓ (↥(chartAlgMid N ℓ) ⧸ W N ℓ)) =
      (Submodule.span ℤℓ (↑G : Set ↥(chartAlgMid N ℓ))).map (W N ℓ).mkQ := by
    refine le_antisymm ?_ le_top
    rintro y -
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (W N ℓ) y
    obtain ⟨w, hw, g, hg, rfl⟩ := Submodule.mem_sup.mp (hkey x)
    refine ⟨g, hg, ?_⟩
    simp only [map_add, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero (W N ℓ)).mpr hw, zero_add]
  rw [htop]
  exact (Submodule.fg_span G.finite_toSet).map _

end IgusaCechH1Finite

theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    Module.Finite ↥(GaloisRep.ratLocalizedAt ℓ)
      (↥(chartAlgMid N ℓ) ⧸ (LinearMap.range (inclFin N ℓ).toLinearMap ⊔
        LinearMap.range (inclInf N ℓ).toLinearMap)) :=
  IgusaCechH1Finite.moduleFinite_quotient N ℓ

end
end S_ModularCurve_IgusaScheme_moduleFinite_chartAlgMid_quotient_range_inclFin_sup_range_inclInf
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_moduleFinite_chartAlgMid_quotient_range_inclFin_sup_range_inclInf (solution)
