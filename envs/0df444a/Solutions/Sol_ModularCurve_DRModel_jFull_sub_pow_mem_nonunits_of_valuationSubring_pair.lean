-- Prove2me | solution 1 for ModularCurve.DRModel.jFull_sub_pow_mem_nonunits_of_valuationSubring_pair
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/37b5ecc9-d7e0-5e2c-8e48-d14eb8ca55e9

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_ModularCurve_transcendental_jq
import Theorems.Thm_ModularCurve_exists_sub_mul_sub_eq_natCast_mul_of_coe_eq_qExpand
import Theorems.Thm_IntermediateField_not_mem_adjoin_pow_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModel_jFull_sub_pow_mem_nonunits_of_valuationSubring_pair
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

p2m_open "ModularCurve P2MW.S_ModularCurve_DRModel_jFull_sub_pow_mem_nonunits_of_valuationSubring_pair.ModularCurve AlgebraicCurve Polynomial"

namespace ModularCurve
p2m_export "ModularCurve" "IgusaScheme.jFull IgusaScheme.coe_jFull IgusaScheme qExpand jq modularFunctionFieldFull transcendental_jq exists_sub_mul_sub_eq_natCast_mul_of_coe_eq_qExpand"
namespace DRModel
namespace KroneckerAux
p2m_open "ModularCurve"

theorem not_mem_nonunits_of_inv_mem {K : Type*} [Field K] (W : ValuationSubring K) {x : K}
    (hx0 : x ≠ 0) (hx : x ∈ W) (hinv : x⁻¹ ∈ W) : x ∉ W.nonunits := by
  intro h
  rw [ValuationSubring.mem_nonunits_iff] at h
  have h1 : W.valuation x⁻¹ ≤ 1 := (W.valuation_le_one_iff _).mpr hinv
  have hpos : 0 < W.valuation x := zero_lt_iff.mpr ((_root_.map_ne_zero _).mpr hx0)
  rw [map_inv₀, inv_le_one₀ hpos] at h1
  exact (lt_irrefl _) (lt_of_lt_of_le h h1)

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

theorem coe_eval₂ {K : Type*} [Field K] (W : ValuationSubring K) (x : ↥W) (P : ℤ[X]) :
    ((eval₂ (algebraMap ℤ ↥W) x P : ↥W) : K) = eval₂ (algebraMap ℤ K) (x : K) P := by
  have h := Polynomial.hom_eval₂ P (algebraMap ℤ ↥W) W.subtype x
  rw [RingHom.ext_int (W.subtype.comp (algebraMap ℤ ↥W)) (algebraMap ℤ K)] at h
  exact h

theorem residue_eval₂ {K : Type*} [Field K] (W : ValuationSubring K) (x : ↥W) (P : ℤ[X]) :
    IsLocalRing.residue ↥W (eval₂ (algebraMap ℤ ↥W) x P) =
      eval₂ (algebraMap ℤ (IsLocalRing.ResidueField ↥W)) (IsLocalRing.residue ↥W x) P := by
  rw [Polynomial.hom_eval₂, RingHom.ext_int ((IsLocalRing.residue ↥W).comp (algebraMap ℤ ↥W)) (algebraMap ℤ _)]

theorem residue_eval₂_eq_aeval {K : Type*} [Field K] (W : ValuationSubring K) (p : ℕ)
    [Algebra (ZMod p) (IsLocalRing.ResidueField ↥W)] (x : ↥W) (P : ℤ[X]) :
    IsLocalRing.residue ↥W (eval₂ (algebraMap ℤ ↥W) x P) =
      aeval (IsLocalRing.residue ↥W x) (P.map (Int.castRingHom (ZMod p))) := by
  rw [Polynomial.hom_eval₂, aeval_def, eval₂_map]
  exact congrArg (fun f : ℤ →+* IsLocalRing.ResidueField ↥W => eval₂ f (IsLocalRing.residue ↥W x) P)
    (RingHom.ext_int _ _)

theorem eval₂_eq_aeval_map {κ : Type*} [CommRing κ] (p : ℕ) [Algebra (ZMod p) κ] (y : κ) (P : ℤ[X]) :
    eval₂ (algebraMap ℤ κ) y P = aeval y (P.map (Int.castRingHom (ZMod p))) := by
  rw [aeval_def, eval₂_map, RingHom.ext_int ((algebraMap (ZMod p) κ).comp (Int.castRingHom (ZMod p))) (algebraMap ℤ κ)]

end ModularCurve.DRModel.KroneckerAux

open ModularCurve.DRModel.KroneckerAux in

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
    ((IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) -
        (jp : ↥(modularFunctionFieldFull p)) ^ p) ∈ W₁.nonunits := by
  classical
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp0 : 0 < p := (Fact.out : p.Prime).pos

  have htjℚ : Transcendental ℚ (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) := by
    intro halg
    obtain ⟨q, hq, hev⟩ := halg
    refine ModularCurve.transcendental_jq ⟨q, hq, ?_⟩
    have h0 : (algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ))
        ((Polynomial.aeval (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p))) q) = 0 := by
      rw [hev, map_zero]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂,
        show (algebraMap ↥(modularFunctionFieldFull p) (LaurentSeries ℚ)) (IgusaScheme.jFull p) = jq from
          IgusaScheme.coe_jFull p] at h0
    rw [Polynomial.aeval_def]
    convert h0 using 2 <;> first | rfl | exact Subsingleton.elim _ _ | exact (RingHom.ext_rat _ _)
  have htj : Transcendental ℤ (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) := fun h =>
    htjℚ ((IsFractionRing.isAlgebraic_iff ℤ ℚ ↥(modularFunctionFieldFull p)).mp h)
  have heval0 : ∀ P : Polynomial ℤ, P ≠ 0 → eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) P ≠ 0 := fun P hP h =>
    hP (transcendental_iff_injective.mp htj (by rw [aeval_def, h, map_zero]))

  have hX : (X : ℤ[X]).map (Int.castRingHom (ZMod p)) ≠ 0 := by rw [Polynomial.map_X]; exact X_ne_zero
  have hjW : (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ∈ W₁ := by
    have h := (hgen 1 X hX).1
    simp only [eval₂_X, Matrix.cons_val_one] at h
    exact h
  have htW : (jp : ↥(modularFunctionFieldFull p)) ∈ W₁ :=
    mem_of_isIntegral_adjoin W₁ {IgusaScheme.jFull p} (Set.singleton_subset_iff.mpr hjW) _
      ((TwoChartIntegralModel.mem_chartAlg_iff ℤ ↥(modularFunctionFieldFull p)).mp jp.2)

  obtain ⟨w, hw, hK⟩ := ModularCurve.exists_sub_mul_sub_eq_natCast_mul_of_coe_eq_qExpand p (jp : ↥(modularFunctionFieldFull p)) hjp
  have hwW : w ∈ W₁ := by
    have hle : Algebra.adjoin ℤ ({(IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)), (jp : ↥(modularFunctionFieldFull p))} : Set ↥(modularFunctionFieldFull p)) ≤ subalgebraOfSubring W₁.toSubring :=
      Algebra.adjoin_le (Set.insert_subset_iff.mpr ⟨hjW, Set.singleton_subset_iff.mpr htW⟩)
    exact hle hw
  have hprod : W₁.valuation (((IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ^ p - (jp : ↥(modularFunctionFieldFull p))) * ((IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) - (jp : ↥(modularFunctionFieldFull p)) ^ p)) < 1 := by
    rw [hK, map_mul]
    calc W₁.valuation ((p : ℕ) : ↥(modularFunctionFieldFull p)) * W₁.valuation w
        ≤ W₁.valuation ((p : ℕ) : ↥(modularFunctionFieldFull p)) * 1 := mul_le_mul_right ((W₁.valuation_le_one_iff _).mpr hwW) _
      _ = W₁.valuation ((p : ℕ) : ↥(modularFunctionFieldFull p)) := mul_one _
      _ < 1 := by have h := hp₁; rwa [ValuationSubring.mem_nonunits_iff] at h

  have haW : (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) ^ p - (jp : ↥(modularFunctionFieldFull p)) ∈ W₁ := W₁.sub_mem (W₁.pow_mem hjW p) htW
  rw [map_mul] at hprod
  rcases ((W₁.valuation_le_one_iff _).mpr haW).lt_or_eq with ha | ha
  swap
  · rw [ha, one_mul] at hprod
    rw [ValuationSubring.mem_nonunits_iff]
    exact hprod

  exfalso
  have hres0 : ∀ x : ↥W₁, (x : ↥(modularFunctionFieldFull p)) ∈ W₁.nonunits ↔ IsLocalRing.residue ↥W₁ x = 0 := fun x => by
    rw [ValuationSubring.coe_mem_nonunits_iff, IsLocalRing.residue_eq_zero_iff]
  have hpκ : (p : IsLocalRing.ResidueField ↥W₁) = 0 := by
    rw [← map_natCast (IsLocalRing.residue ↥W₁)]
    exact (hres0 _).mp (by simpa using hp₁)
  haveI : CharP (IsLocalRing.ResidueField ↥W₁) p := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hpκ
  letI : Algebra (ZMod p) (IsLocalRing.ResidueField ↥W₁) := ZMod.algebra _ p
  set j₁ : ↥W₁ := ⟨(IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)), hjW⟩ with hj₁
  set t₁ : ↥W₁ := ⟨(jp : ↥(modularFunctionFieldFull p)), htW⟩ with ht₁

  have htbar : IsLocalRing.residue ↥W₁ t₁ = IsLocalRing.residue ↥W₁ j₁ ^ p := by
    have h : IsLocalRing.residue ↥W₁ (j₁ ^ p - t₁) = 0 :=
      (hres0 _).mp (by rw [ValuationSubring.mem_nonunits_iff]; exact ha)
    rw [map_sub, map_pow, sub_eq_zero] at h
    exact h.symm

  have hjbar : Transcendental (ZMod p) (IsLocalRing.residue ↥W₁ j₁) := by
    rintro ⟨Pb, hPb0, hPb⟩
    obtain ⟨P, hP⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod p)) (ZMod.ringHom_surjective _) Pb
    have hPmap : P.map (Int.castRingHom (ZMod p)) ≠ 0 := hP ▸ hPb0
    have hP0 : P ≠ 0 := fun h => hPmap (by rw [h, Polynomial.map_zero])
    obtain ⟨hPW, hPinvW⟩ := hgen 1 P hPmap
    simp only [Matrix.cons_val_one] at hPW hPinvW
    have hnot := not_mem_nonunits_of_inv_mem W₁ (heval0 P hP0) hPW hPinvW
    apply hnot
    rw [← coe_eval₂ W₁ j₁ P, hres0, residue_eval₂_eq_aeval W₁ p, hP]
    exact hPb

  obtain ⟨P, Q, hQmap, hPQ⟩ := hres₁ (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) hjW
  have hκ : IsLocalRing.residue ↥W₁ j₁ * aeval (IsLocalRing.residue ↥W₁ t₁) (Q.map (Int.castRingHom (ZMod p))) -
      aeval (IsLocalRing.residue ↥W₁ t₁) (P.map (Int.castRingHom (ZMod p))) = 0 := by
    have helt : ((j₁ * eval₂ (algebraMap ℤ ↥W₁) t₁ Q - eval₂ (algebraMap ℤ ↥W₁) t₁ P : ↥W₁) : ↥(modularFunctionFieldFull p)) =
        (IgusaScheme.jFull p : ↥(modularFunctionFieldFull p)) * eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (jp : ↥(modularFunctionFieldFull p)) Q - eval₂ (algebraMap ℤ ↥(modularFunctionFieldFull p)) (jp : ↥(modularFunctionFieldFull p)) P := by
      rw [← coe_eval₂ W₁ t₁ Q, ← coe_eval₂ W₁ t₁ P]
      rfl
    have h0 : IsLocalRing.residue ↥W₁ (j₁ * eval₂ (algebraMap ℤ ↥W₁) t₁ Q - eval₂ (algebraMap ℤ ↥W₁) t₁ P) = 0 :=
      (hres0 _).mp (by rw [helt]; exact hPQ)
    rw [map_sub, map_mul, residue_eval₂_eq_aeval W₁ p, residue_eval₂_eq_aeval W₁ p] at h0
    exact h0
  rw [htbar] at hκ
  have hQ0 : aeval (IsLocalRing.residue ↥W₁ j₁ ^ p) (Q.map (Int.castRingHom (ZMod p))) ≠ 0 := by
    rw [← expand_aeval]
    intro h
    have hinj := transcendental_iff_injective.mp hjbar
    have : expand (ZMod p) p (Q.map (Int.castRingHom (ZMod p))) = 0 := hinj (by rw [h, map_zero])
    exact hQmap ((expand_eq_zero hp0).mp this)
  have hmem : IsLocalRing.residue ↥W₁ j₁ ∈
      IntermediateField.adjoin (ZMod p) ({IsLocalRing.residue ↥W₁ j₁ ^ p} : Set (IsLocalRing.ResidueField ↥W₁)) := by
    rw [IntermediateField.mem_adjoin_simple_iff]
    exact ⟨P.map (Int.castRingHom (ZMod p)), Q.map (Int.castRingHom (ZMod p)),
      (eq_div_iff hQ0).mpr (sub_eq_zero.mp hκ)⟩
  exact IntermediateField.not_mem_adjoin_pow_of_transcendental (ZMod p) (IsLocalRing.ResidueField ↥W₁)
    (IsLocalRing.residue ↥W₁ j₁) hjbar p hp2 hmem

end S_ModularCurve_DRModel_jFull_sub_pow_mem_nonunits_of_valuationSubring_pair
end P2MW
export P2MW.S_ModularCurve_DRModel_jFull_sub_pow_mem_nonunits_of_valuationSubring_pair (solution)
