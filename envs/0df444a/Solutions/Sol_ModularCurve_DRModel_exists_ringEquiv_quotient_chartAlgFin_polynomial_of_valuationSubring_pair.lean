-- Prove2me | solution 1 for ModularCurve.DRModel.exists_ringEquiv_quotient_chartAlgFin_polynomial_of_valuationSubring_pair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/a672a96a-8982-5937-a42a-02966099a540

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_ValuationSubring_exists_ringEquiv_quotient_polynomial_zmod_of_residue_generated
import Theorems.Thm_ModularCurve_DRModel_jFull_sub_pow_mem_nonunits_of_valuationSubring_pair
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModel_exists_ringEquiv_quotient_chartAlgFin_polynomial_of_valuationSubring_pair
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

p2m_open "ModularCurve P2MW.S_ModularCurve_DRModel_exists_ringEquiv_quotient_chartAlgFin_polynomial_of_valuationSubring_pair.ModularCurve AlgebraicCurve Polynomial"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme.jFull IgusaScheme qExpand jq modularFunctionFieldFull DRModel.jFull_sub_pow_mem_nonunits_of_valuationSubring_pair"
namespace DRModel
p2m_export "ModularCurve.DRModel" "jFull_sub_pow_mem_nonunits_of_valuationSubring_pair"
namespace ResidueRingAux
p2m_open "ModularCurve.DRModel ModularCurve"

theorem mem_of_isIntegral_adjoin {K : Type*} [Field K] (W : ValuationSubring K) (s : Set K)
    (hs : s ⊆ W) (x : K) (hx : IsIntegral ↥(Algebra.adjoin ℤ s) x) : x ∈ W := by
  have hle : ∀ y ∈ Algebra.adjoin ℤ s, y ∈ W := by
    intro y hy
    have : Algebra.adjoin ℤ s ≤ subalgebraOfSubring W.toSubring := Algebra.adjoin_le hs
    exact this hy
  let φ : ↥(Algebra.adjoin ℤ s) →+* ↥W :=
    (Algebra.adjoin ℤ s).val.toRingHom.codRestrict W.toSubring fun y => hle y y.2
  have hx' : IsIntegral ↥W x :=
    hx.map_of_comp_eq φ (RingHom.id K) (by ext; rfl)
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥W) (K := K)).mp hx'
  rw [← hy]
  exact y.2

end ModularCurve.DRModel.ResidueRingAux

end

theorem solution
    (p : ℕ) [Fact p.Prime] [NeZero p]
    (jp : ↥(TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)))
    (hjp : ((jp : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ) = qExpand ℚ p jq)
    (W₀ W₁ : ValuationSubring ↥(modularFunctionFieldFull p))
    (hp₀ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits)
    (hp₁ : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits)
    (hne : W₀ ≠ W₁)
    (hgen : ∀ i : Fin 2, ∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
        Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P
            ∈ (![W₀, W₁] i) ∧
        (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P)⁻¹
            ∈ (![W₀, W₁] i))
    (hcomplete : ∀ V : ValuationSubring ↥(modularFunctionFieldFull p),
        ((p : ℕ) : ↥(modularFunctionFieldFull p)) ∈ V.nonunits →
        (∀ P : Polynomial ℤ, P.map (Int.castRingHom (ZMod p)) ≠ 0 →
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P ∈ V ∧
          (Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁)
    (ht : ((jp : ↥(modularFunctionFieldFull p)) - (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ^ p) ∈ W₀.nonunits)
    (hres₀ : ∀ x : ↥(modularFunctionFieldFull p), x ∈ W₀ → ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) Q -
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P
            ∈ W₀.nonunits)
    (hres₁ : ∀ x : ↥(modularFunctionFieldFull p), x ∈ W₁ → ∃ P Q : Polynomial ℤ, Q.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
        x * Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (jp : ↥(modularFunctionFieldFull p)) Q -
          Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (jp : ↥(modularFunctionFieldFull p)) P
            ∈ W₁.nonunits) :
    let A := TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)
    let j : ↥A := TwoChartIntegralModel.jChartFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)
    (∀ 𝔭 : Ideal ↥A, (∀ a : ↥A, a ∈ 𝔭 ↔ ((a : ↥(modularFunctionFieldFull p)) ∈ W₀.nonunits)) →
        ∃ e : (↥A ⧸ 𝔭) ≃+* Polynomial (ZMod p),
          e (Ideal.Quotient.mk 𝔭 j) = X ∧ e (Ideal.Quotient.mk 𝔭 jp) = X ^ p) ∧
    (∀ 𝔭 : Ideal ↥A, (∀ a : ↥A, a ∈ 𝔭 ↔ ((a : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits)) →
        ∃ e : (↥A ⧸ 𝔭) ≃+* Polynomial (ZMod p),
          e (Ideal.Quotient.mk 𝔭 jp) = X ∧ e (Ideal.Quotient.mk 𝔭 j) = X ^ p) := by
  intro A j
  classical
  have hpprime : (p : ℕ).Prime := Fact.out

  have hp0 : ((p : ℕ) : ↥(modularFunctionFieldFull p)) ≠ 0 := Nat.cast_ne_zero.mpr hpprime.ne_zero
  have haeval : ∀ (x : ↥(modularFunctionFieldFull p)) (P : Polynomial ℤ),
      Polynomial.eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) x P = aeval x P := fun x P => rfl
  have hjW : ∀ i : Fin 2, (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ∈ (![W₀, W₁] i) := by
    intro i
    have := (hgen i Polynomial.X (by rw [Polynomial.map_X]; exact X_ne_zero)).1
    simpa only [eval₂_X] using this
  have hint : ∀ a : ↥(modularFunctionFieldFull p), a ∈ A →
      IsIntegral ↥(Algebra.adjoin ℤ ({(IgusaScheme.jFull p : ↥(modularFunctionFieldFull p))} :
        Set ↥(modularFunctionFieldFull p))) a :=
    fun a ha => (TwoChartIntegralModel.mem_chartAlg_iff ℤ ↥(modularFunctionFieldFull p)).mp ha
  have hAW : ∀ i : Fin 2, ∀ a : ↥(modularFunctionFieldFull p), a ∈ A → a ∈ (![W₀, W₁] i) := by
    intro i a ha
    exact ModularCurve.DRModel.ResidueRingAux.mem_of_isIntegral_adjoin _ _
      (Set.singleton_subset_iff.mpr (hjW i)) _ (hint a ha)
  have hjA : (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ∈ A := j.2
  have hjpA : (jp : ↥(modularFunctionFieldFull p)) ∈ A := jp.2
  have hzero : ∀ W : ValuationSubring ↥(modularFunctionFieldFull p),
      (0 : ↥(modularFunctionFieldFull p)) ∈ W.nonunits := fun W => by
    rw [ValuationSubring.mem_nonunits_iff, map_zero]; exact zero_lt_one
  constructor
  ·
    intro 𝔭 h𝔭
    obtain ⟨e, he⟩ :=
      ValuationSubring.exists_ringEquiv_quotient_polynomial_zmod_of_residue_generated W₀ p hp0 hp₀ A
        (hAW 0) (IgusaScheme.jFull p) hjA hint
        (fun P hP => by have h__af := hgen 0 P hP; simp only [haeval] at h__af; exact h__af)
        (IgusaScheme.jFull p) hjA
        (fun x hx => by simpa only [haeval] using hres₀ x hx)
        Polynomial.X (by simpa using hzero W₀) 𝔭 h𝔭
    refine ⟨e, ?_, ?_⟩
    · have := he j Polynomial.X (by simp [j, hzero])
      simpa using this
    · have := he jp (Polynomial.X ^ p) (by simpa using ht)
      simpa using this
  ·
    intro 𝔭 h𝔭
    have ht₁ := ModularCurve.DRModel.jFull_sub_pow_mem_nonunits_of_valuationSubring_pair p jp hjp W₀ W₁
      hp₀ hp₁ hne hgen hcomplete ht hres₀ hres₁
    obtain ⟨e, he⟩ :=
      ValuationSubring.exists_ringEquiv_quotient_polynomial_zmod_of_residue_generated W₁ p hp0 hp₁ A
        (hAW 1) (IgusaScheme.jFull p) hjA hint
        (fun P hP => by have h__af := hgen 1 P hP; simp only [haeval] at h__af; exact h__af)
        (jp : ↥(modularFunctionFieldFull p)) hjpA
        (fun x hx => by simpa only [haeval] using hres₁ x hx)
        (Polynomial.X ^ p) (by simpa using ht₁) 𝔭 h𝔭
    refine ⟨e, ?_, ?_⟩
    · have := he jp Polynomial.X (by simp [hzero])
      simpa using this
    · have := he j (Polynomial.X ^ p) (by simpa [j] using ht₁)
      simpa using this

end S_ModularCurve_DRModel_exists_ringEquiv_quotient_chartAlgFin_polynomial_of_valuationSubring_pair
end P2MW
export P2MW.S_ModularCurve_DRModel_exists_ringEquiv_quotient_chartAlgFin_polynomial_of_valuationSubring_pair (solution)
