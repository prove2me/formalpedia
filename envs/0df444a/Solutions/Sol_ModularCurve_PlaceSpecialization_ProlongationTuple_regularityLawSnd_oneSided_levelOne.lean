-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.regularityLawSnd_oneSided_levelOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c5d9e30c-473a-5daa-a368-767e1974167e

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Theorems.Thm_ModularCurve_ord_coeffEmb_modularUnitSeries_of_not_isCusp
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceEquiv_placeInfty_eq_order
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_placeInfty_of_forall_ord_le_zero
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces_levelOne
import Theorems.Thm_ModularCurve_coe_frickeInvolutionFull_modularUnitSeries
import Theorems.Thm_ModularCurve_geomAut_atkinLehnerInvolutionFull_one_eq_frickeInvolutionBar
import Theorems.Thm_ModularCurve_isAffineGeomPlace_frobOnPlacesGeomLevel
import Theorems.Thm_ModularCurve_mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceOfPoint
import Theorems.Thm_ModularCurve_pow_mem_ssJSet_iff_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided_levelOne
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd"
p2m_attr_erase "simp" "ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄"
p2m_attr_erase "simp" "TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"
set_option Elab.async false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar jq ModularPolynomialData modularFunctionFieldFull algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel frobOnPlacesGeomLevel_injective KroneckerCongruence ssPlaces jGeomGen coe_jGeomGen IsAffineGeomPlace order_jqModC_def jq_mem_full IsCusp charLGeomPlaceEquiv atkinLehnerInvolutionFull frickeInvolutionBar_def frickeInvolutionFull geomAut coe_geomAut_coeffEmb modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_charLGeomPlaceEquiv_placeInfty_eq_order modularUnitSeries_mem_modularFunctionFieldFull coe_frickeInvolutionFull_modularUnitSeries geomAut_atkinLehnerInvolutionFull_one_eq_frickeInvolutionBar isAffineGeomPlace_frobOnPlacesGeomLevel mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq frobOnPlacesGeomLevel_charLGeomPlaceOfPoint pow_mem_ssJSet_iff_of_perfectField coeffEmb_smul'"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple ProlongationTuple.residue₁_apply ProlongationTuple.residue₂_apply reduceFst redFst redFst_eq_placeInfty_of_forall_ord_le_zero ProlongationTuple.exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level ProlongationTuple.ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces_levelOne"
namespace ProlongationTuple
p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "atkinLehnerBar mem_integers₂_iff residue₁ residue₂ residue₁_apply residue₂_apply RegularityLaw R₁ ι redBar_residue R₂ residue₂_eq exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces_levelOne"
p2m_open "ModularCurve.PlaceSpecialization.ProlongationTuple ModularCurve.PlaceSpecialization ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided_levelOne.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided_levelOne.ModularCurve"

set_option autoImplicit false

section SepUnit

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
  {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private theorem _root_.AlgebraicCurve.Place.ord_pow' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {g : F} (hg : g ≠ 0) (n : ℕ) : v.ord (g ^ n) = n * v.ord g := by
  induction n with
  | zero => simp [Place.ord_one]
  | succ n ih =>
    rw [pow_succ, v.ord_mul (pow_ne_zero n hg) hg, ih]
    push_cast
    ring

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided_levelOne.AlgebraicCurve.Place.ord_pow'" "AlgebraicCurve.Place.ord_pow'"

theorem regularityLawFst_oneSided_of_sepFunction
    [IsAlgClosed k] [DecidableEq k]
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (R : ProlongationTuple P) (hreg : R.RegularityLaw W)
    (U : ↥(modularFunctionFieldBar (N * q)))
    (hU₁ : U ∈ R.R₁.integers) (hUres : R.R₁.residue ⟨U, hU₁⟩ ≠ 0)
    (hArch : ∀ f : ↥(modularFunctionFieldBar (N * q)), ∃ b : ℕ, f * U ^ b ∈ R.R₂.integers)
    (hpoleU : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      IsAffineGeomPlace k N (P.reduceFst V) → 0 ≤ V.ord U)
    (hresU : ∀ v : Place k ↥(modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      IsAffineGeomPlace k N v → v ∉ W →
      v.ord (R.residue₁ ⟨U, hU₁⟩ : ↥(modularFunctionFieldC k N)) = 0) :
    ∀ (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers),
      R.R₁.residue ⟨f, h₁⟩ ≠ 0 →
      ∀ v : Place k (modularFunctionFieldC k N),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
        IsAffineGeomPlace k N v →
        v ∉ W →
        (∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
          P.reduceFst V = v → 0 ≤ V.ord f) →
        0 ≤ v.ord (R.residue₁ ⟨f, h₁⟩) := by
  intro f h₁ hf v hfix haff hvW hpole
  classical

  have hU0 : U ≠ 0 := by
    intro h0; apply hUres
    have : (⟨U, hU₁⟩ : ↥R.R₁.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hf0 : f ≠ 0 := by
    intro h0; apply hf
    have : (⟨f, h₁⟩ : ↥R.R₁.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]

  obtain ⟨b, hb⟩ := hArch f
  have hF₁ : f * U ^ b ∈ R.R₁.integers := mul_mem h₁ (pow_mem hU₁ b)
  have hFeq : (⟨f * U ^ b, hF₁⟩ : ↥R.R₁.integers) = ⟨f, h₁⟩ * ⟨U, hU₁⟩ ^ b := by
    apply Subtype.ext
    simp
  have hFres : R.R₁.residue ⟨f * U ^ b, hF₁⟩ ≠ 0 := by
    rw [hFeq, map_mul, map_pow]
    exact mul_ne_zero hf (pow_ne_zero b hUres)
  have hFres' : R.residue₁ ⟨f * U ^ b, hF₁⟩ ≠ 0 := by
    rw [residue₁_apply]
    exact (map_ne_zero R.ι).mpr hFres

  have hpoleF : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.reduceFst V = v → 0 ≤ V.ord (f * U ^ b) := by
    intro V hV
    rw [V.ord_mul hf0 (pow_ne_zero b hU0), Place.ord_pow' V hU0]
    have h1 := hpole V hV
    have h2 : 0 ≤ V.ord U := hpoleU V (by rw [hV]; exact haff)
    positivity

  have hmain := (hreg.1 (f * U ^ b) hF₁ hb v hfix haff hpoleF).1 hFres'

  have hres₁f : R.residue₁ ⟨f, h₁⟩ ≠ 0 := by
    rw [residue₁_apply]; exact (map_ne_zero R.ι).mpr hf
  have hres₁U : R.residue₁ ⟨U, hU₁⟩ ≠ 0 := by
    rw [residue₁_apply]; exact (map_ne_zero R.ι).mpr hUres
  rw [hFeq, map_mul, map_pow, v.ord_mul hres₁f (pow_ne_zero b hres₁U),
    Place.ord_pow' v hres₁U, hresU v hfix haff hvW, mul_zero, add_zero] at hmain
  exact hmain

end SepUnit

end ModularCurve.PlaceSpecialization.ProlongationTuple

private theorem _root_.ValuationSubring.exists_natCast_pow_mul_mem_of_forall_isUnit
    (A : ValuationSubring (AlgebraicClosure ℚ)) {k : Type*} [Field k] (red : A →+* k)
    (q : ℕ) [Fact q.Prime] [CharP k q]
    (hunit : ∀ a : A, red a ≠ 0 → IsUnit a) (c : AlgebraicClosure ℚ) :
    ∃ b : ℕ, ((q : AlgebraicClosure ℚ) ^ b * c) ∈ A := by
  classical
  have halgQ : IsAlgebraic ℚ c := (AlgebraicClosure.isAlgebraic ℚ).isAlgebraic c
  have halgZ : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr halgQ
  obtain ⟨y, hy0, hint⟩ := halgZ.exists_integral_multiple

  set n : ℕ := y.natAbs with hn_def
  have hn0 : n ≠ 0 := Int.natAbs_ne_zero.mpr hy0
  have hintn : IsIntegral ℤ ((n : ℤ) • c) := by
    rcases Int.natAbs_eq y with h | h
    · rw [hn_def, ← h]; exact hint
    · have : ((n : ℤ)) • c = -(y • c) := by
        rw [hn_def, show (y.natAbs : ℤ) = -y by omega, neg_smul]
      rw [this]; exact hint.neg
  have hintA : IsIntegral A ((n : ℤ) • c) := by
    obtain ⟨p, hpm, hpx⟩ := hintn
    refine ⟨p.map (algebraMap ℤ A), hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap (↥A) (AlgebraicClosure ℚ)).comp (algebraMap ℤ ↥A) = algebraMap ℤ (AlgebraicClosure ℚ) := by
      ext m
      simp
    rw [hcomp]
    exact hpx
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := AlgebraicClosure ℚ)).mp hintA
  have hnc : ((n : ℕ) : AlgebraicClosure ℚ) * c = (z : AlgebraicClosure ℚ) := by
    have h := hz.symm
    rw [zsmul_eq_mul] at h
    push_cast at h
    exact h

  obtain ⟨e, n', hndvd, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 q (Fact.out : q.Prime).one_lt.ne'
  have hn'0 : n' ≠ 0 := by rintro rfl; rw [mul_zero] at hn; exact hn0 hn

  have hn'unit : IsUnit ((n' : ℕ) : A) := by
    apply hunit
    rw [map_natCast]
    intro h0
    exact hndvd ((CharP.cast_eq_zero_iff k q n').mp h0)
  obtain ⟨w, hw⟩ := hn'unit
  have hwinv : (((n' : ℕ) : AlgebraicClosure ℚ))⁻¹ = ((w⁻¹ : Aˣ) : A) := by
    apply inv_eq_of_mul_eq_one_right
    have h2 : ((w : A) : AlgebraicClosure ℚ) * (((w⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv]; rfl
    rw [hw] at h2
    exact_mod_cast h2
  refine ⟨e, ?_⟩
  have hq' : ((n' : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn'0
  have key : (q : AlgebraicClosure ℚ) ^ e * c = (z : AlgebraicClosure ℚ) * (((n' : ℕ) : AlgebraicClosure ℚ))⁻¹ := by
    rw [← hnc, hn]
    push_cast
    field_simp
  rw [key, hwinv]
  exact mul_mem z.2 ((w⁻¹ : Aˣ) : A).2

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided_levelOne.ValuationSubring.exists_natCast_pow_mul_mem_of_forall_isUnit" "ValuationSubring.exists_natCast_pow_mul_mem_of_forall_isUnit"
namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar jq ModularPolynomialData modularFunctionFieldFull algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel frobOnPlacesGeomLevel_injective KroneckerCongruence ssPlaces jGeomGen coe_jGeomGen IsAffineGeomPlace order_jqModC_def jq_mem_full IsCusp charLGeomPlaceEquiv atkinLehnerInvolutionFull frickeInvolutionBar_def frickeInvolutionFull geomAut coe_geomAut_coeffEmb modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_charLGeomPlaceEquiv_placeInfty_eq_order modularUnitSeries_mem_modularFunctionFieldFull coe_frickeInvolutionFull_modularUnitSeries geomAut_atkinLehnerInvolutionFull_one_eq_frickeInvolutionBar isAffineGeomPlace_frobOnPlacesGeomLevel mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq frobOnPlacesGeomLevel_charLGeomPlaceOfPoint pow_mem_ssJSet_iff_of_perfectField coeffEmb_smul'"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple ProlongationTuple.residue₁_apply ProlongationTuple.residue₂_apply reduceFst redFst redFst_eq_placeInfty_of_forall_ord_le_zero ProlongationTuple.exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level ProlongationTuple.ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces_levelOne"
namespace ProlongationTuple
p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "atkinLehnerBar mem_integers₂_iff residue₁ residue₂ residue₁_apply residue₂_apply RegularityLaw R₁ ι redBar_residue R₂ residue₂_eq exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces_levelOne"
p2m_open "ModularCurve.PlaceSpecialization.ProlongationTuple ModularCurve.PlaceSpecialization ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided_levelOne.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided_levelOne.ModularCurve"

set_option autoImplicit false

private theorem _root_.ModularCurve.PlaceSpecialization.ProlongationTuple.isUnit_of_red_ne_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (a : A) (ha : red a ≠ 0) : IsUnit a := by
  by_contra h
  apply ha
  have hmem : a ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal a).mpr h
  rw [← R.redBar_residue a, (IsLocalRing.residue_eq_zero_iff a).mpr hmem, map_zero]

p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "isUnit_of_red_ne_zero"

theorem exists_mul_pow_mem_integersSnd_of_atkinLehnerBar_eq
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ} (R : ProlongationTuple P)
    (U : ↥(modularFunctionFieldBar (N * q)))
    (hU₁ : U ∈ R.R₁.integers) (hUres : R.R₁.residue ⟨U, hU₁⟩ ≠ 0)
    (hALU : atkinLehnerBar N q U
      = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((q : AlgebraicClosure ℚ) ^ 12) * U⁻¹) :
    ∀ f : ↥(modularFunctionFieldBar (N * q)), ∃ b : ℕ, f * U ^ b ∈ R.R₂.integers := by
  intro f
  classical

  have hUunit : IsUnit (⟨U, hU₁⟩ : ↥R.R₁.integers) := R.R₁.isUnit_of_residue_ne_zero hUres
  obtain ⟨w, hw⟩ := hUunit.exists_right_inv
  have hwF : (U : ↥(modularFunctionFieldBar (N * q))) * (w : ↥(modularFunctionFieldBar (N * q))) = 1 := by
    have h := congrArg Subtype.val hw
    simpa using h
  have hU0 : U ≠ 0 := left_ne_zero_of_mul_eq_one hwF
  have hUinv : U⁻¹ ∈ R.R₁.integers := by
    rw [← eq_inv_of_mul_eq_one_right hwF]; exact w.2

  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, by rw [zero_mul]; exact zero_mem _⟩
  set g := atkinLehnerBar N q f with hg
  have hg0 : g ≠ 0 := by
    rw [hg]; exact (map_ne_zero_iff _ (atkinLehnerBar N q).injective).mpr hf0
  obtain ⟨c, hcg, hcres⟩ := R.R₁.exists_smul_mem g hg0
  have hc0 : c ≠ 0 := R.R₁.smul_const_ne_zero hcg hcres

  obtain ⟨b, hb⟩ := A.exists_natCast_pow_mul_mem_of_forall_isUnit red q (R.isUnit_of_red_ne_zero) c⁻¹
  refine ⟨b, ?_⟩
  rw [R.mem_integers₂_iff, map_mul, map_pow, hALU, ← hg, mul_pow, ← map_pow, ← pow_mul]

  have hq12 : ((q : AlgebraicClosure ℚ) ^ (12 * b) * c⁻¹) ∈ A := by
    have : (q : AlgebraicClosure ℚ) ^ (12 * b) * c⁻¹ = (q : AlgebraicClosure ℚ) ^ (11 * b) * ((q : AlgebraicClosure ℚ) ^ b * c⁻¹) := by ring
    rw [this]
    refine mul_mem (pow_mem ?_ _) hb
    exact_mod_cast (natCast_mem A q)
  have hrw : g * (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((q : AlgebraicClosure ℚ) ^ (12 * b)) * U⁻¹ ^ b)
      = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) ((q : AlgebraicClosure ℚ) ^ (12 * b) * c⁻¹)
        * ((c • g) * U⁻¹ ^ b) := by
    rw [Algebra.smul_def, map_mul]
    have hcc : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c⁻¹ *
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) c = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hc0, map_one]
    calc g * (algebraMap _ _ ((q : AlgebraicClosure ℚ) ^ (12 * b)) * U⁻¹ ^ b)
        = algebraMap _ _ ((q : AlgebraicClosure ℚ) ^ (12 * b)) * (algebraMap _ _ c⁻¹ * algebraMap _ _ c) * g * U⁻¹ ^ b := by
          rw [hcc]; ring
      _ = _ := by ring
  rw [hrw]
  exact mul_mem ((R.R₁.algebraMap_mem_iff _).mpr hq12) (mul_mem hcg (pow_mem hUinv b))

end ModularCurve.PlaceSpecialization.ProlongationTuple

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar jq ModularPolynomialData modularFunctionFieldFull algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel frobOnPlacesGeomLevel_injective KroneckerCongruence ssPlaces jGeomGen coe_jGeomGen IsAffineGeomPlace order_jqModC_def jq_mem_full IsCusp charLGeomPlaceEquiv atkinLehnerInvolutionFull frickeInvolutionBar_def frickeInvolutionFull geomAut coe_geomAut_coeffEmb modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_charLGeomPlaceEquiv_placeInfty_eq_order modularUnitSeries_mem_modularFunctionFieldFull coe_frickeInvolutionFull_modularUnitSeries geomAut_atkinLehnerInvolutionFull_one_eq_frickeInvolutionBar isAffineGeomPlace_frobOnPlacesGeomLevel mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq frobOnPlacesGeomLevel_charLGeomPlaceOfPoint pow_mem_ssJSet_iff_of_perfectField coeffEmb_smul'"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple ProlongationTuple.residue₁_apply ProlongationTuple.residue₂_apply reduceFst redFst redFst_eq_placeInfty_of_forall_ord_le_zero ProlongationTuple.exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level ProlongationTuple.ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces_levelOne"
p2m_open "ModularCurve.PlaceSpecialization ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided_levelOne.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided_levelOne.ModularCurve"

set_option autoImplicit false

theorem forall_ord_sub_algebraMap_le_zero_of_isCusp {K F : Type*} [Field K] [Field F] [Algebra K F]
    {j : F} {V : Place K F} (hc : IsCusp j V) (a : K) : V.ord (j - algebraMap K F a) ≤ 0 := by
  by_contra h
  push Not at h
  have hne : j - algebraMap K F a ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h; exact lt_irrefl _ h
  have hmem : j - algebraMap K F a ∈ V.toValuationSubring := V.mem_of_ord_nonneg hne h.le
  apply hc
  have : j = (j - algebraMap K F a) + algebraMap K F a := by ring
  rw [this]
  exact add_mem hmem (V.algebraMap_mem' a)

theorem ord_modularUnit_eq_zero_of_isAffineGeomPlace_reduceFst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (U : ↥(modularFunctionFieldBar (1 * q)))
    (hU : (U : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (haff : IsAffineGeomPlace k 1 (P.reduceFst V)) : V.ord U = 0 := by
  classical
  haveI : Fact (1 * q).Prime := ⟨by rw [one_mul]; exact Fact.out⟩
  have hmem : modularUnitSeries (1 * q) ∈ modularFunctionFieldFull (1 * q) :=
    ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull (1 * q)
  have hUeq : U = ⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmem⟩ := by
    apply Subtype.ext
    rw [hU]
    simp only [one_mul]

  have hnc : ¬ IsCusp (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (jq_mem_full (1 * q))⟩ : ↥(modularFunctionFieldBar (1 * q))) V := by
    intro hc
    have hred := redFst_eq_placeInfty_of_forall_ord_le_zero P V
      (fun a => forall_ord_sub_algebraMap_le_zero_of_isCusp hc (a : AlgebraicClosure ℚ))
    have hj : jGeomGen k 1 ∈ (P.reduceFst V).toValuationSubring := haff.1
    rw [show P.reduceFst V = P.redFst V from rfl, hred] at hj
    have h1 := (charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k)).ord_nonneg_of_mem hj
    rw [ord_charLGeomPlaceEquiv_placeInfty_eq_order k, coe_jGeomGen, order_jqModC_def] at h1
    omega
  rw [hUeq, ord_coeffEmb_modularUnitSeries_of_not_isCusp (1 * q) hmem V hnc]

theorem ord_modularUnit_nonneg_of_isAffineGeomPlace_reduceFst
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (U : ↥(modularFunctionFieldBar (1 * q)))
    (hU : (U : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (haff : IsAffineGeomPlace k 1 (P.reduceFst V)) : 0 ≤ V.ord U :=
  (ord_modularUnit_eq_zero_of_isAffineGeomPlace_reduceFst P U hU V haff).ge

end ModularCurve.PlaceSpecialization

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar jq ModularPolynomialData modularFunctionFieldFull algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel frobOnPlacesGeomLevel_injective KroneckerCongruence ssPlaces jGeomGen coe_jGeomGen IsAffineGeomPlace order_jqModC_def jq_mem_full IsCusp charLGeomPlaceEquiv atkinLehnerInvolutionFull frickeInvolutionBar_def frickeInvolutionFull geomAut coe_geomAut_coeffEmb modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_charLGeomPlaceEquiv_placeInfty_eq_order modularUnitSeries_mem_modularFunctionFieldFull coe_frickeInvolutionFull_modularUnitSeries geomAut_atkinLehnerInvolutionFull_one_eq_frickeInvolutionBar isAffineGeomPlace_frobOnPlacesGeomLevel mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq frobOnPlacesGeomLevel_charLGeomPlaceOfPoint pow_mem_ssJSet_iff_of_perfectField coeffEmb_smul'"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple ProlongationTuple.residue₁_apply ProlongationTuple.residue₂_apply reduceFst redFst redFst_eq_placeInfty_of_forall_ord_le_zero ProlongationTuple.exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level ProlongationTuple.ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces_levelOne"
namespace ProlongationTuple
p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "atkinLehnerBar mem_integers₂_iff residue₁ residue₂ residue₁_apply residue₂_apply RegularityLaw R₁ ι redBar_residue R₂ residue₂_eq exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces_levelOne"
p2m_open "ModularCurve.PlaceSpecialization.ProlongationTuple ModularCurve.PlaceSpecialization ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided_levelOne.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided_levelOne.ModularCurve"

set_option autoImplicit false

private theorem _root_.ModularCurve.coeffEmb_smul' (L : Type*) [Field L] [Algebra ℚ L] (r : ℚ) (w : LaurentSeries ℚ) :
    coeffEmb L (r • w) = algebraMap L (LaurentSeries L) (algebraMap ℚ L r) * coeffEmb L w := by
  rw [algebraMap_laurentSeries_eq_single, HahnSeries.single_zero_mul_eq_smul]
  ext n
  simp only [HahnSeries.coeff_smul, coeffEmb_coeff, smul_eq_mul, map_mul]

p2m_alias "P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided_levelOne.ModularCurve.coeffEmb_smul'" "ModularCurve.coeffEmb_smul'"

theorem atkinLehnerBar_one_modularUnit
    {q : ℕ} [Fact q.Prime]
    (U : ↥(modularFunctionFieldBar (1 * q)))
    (hU : (U : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q)) :
    atkinLehnerBar 1 q U
      = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ((q : AlgebraicClosure ℚ) ^ 12) * U⁻¹ := by
  haveI : Fact (1 * q).Prime := ⟨by rw [one_mul]; exact Fact.out⟩
  have hmem : modularUnitSeries (1 * q) ∈ modularFunctionFieldFull (1 * q) :=
    ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull (1 * q)
  have hy : modularUnitSeries (1 * q) = modularUnitSeries q := by simp only [one_mul]
  set u₀ : ↥(modularFunctionFieldFull (1 * q)) := ⟨modularUnitSeries (1 * q), hmem⟩ with hu₀
  have hUeq : U = ⟨coeffEmb (AlgebraicClosure ℚ) (u₀ : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) u₀.2⟩ := by
    apply Subtype.ext
    rw [hU]
    simp only [hu₀, one_mul]
  apply Subtype.ext
  have hL : ((atkinLehnerBar 1 q U : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) ((frickeInvolutionFull (1 * q) u₀ : ↥(modularFunctionFieldFull (1 * q))) : LaurentSeries ℚ) := by
    rw [hUeq]
    show ((geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull (1 * q)) (atkinLehnerInvolutionFull 1 q)) _ : LaurentSeries (AlgebraicClosure ℚ)) = _
    rw [geomAut_atkinLehnerInvolutionFull_one_eq_frickeInvolutionBar q, frickeInvolutionBar_def,
      coe_geomAut_coeffEmb]
  rw [hL, hu₀, coe_frickeInvolutionFull_modularUnitSeries (1 * q) hmem, coeffEmb_smul', map_inv₀, hy, ← hU]
  have hval : ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ((q : AlgebraicClosure ℚ) ^ 12) * U⁻¹ :
      ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))
      = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) ((q : AlgebraicClosure ℚ) ^ 12)
        * ((U : LaurentSeries (AlgebraicClosure ℚ)))⁻¹ := by
    push_cast
    rfl
  rw [hval]
  congr 2
  rw [map_pow, map_natCast]
  push_cast
  rw [one_mul]

end ModularCurve.PlaceSpecialization.ProlongationTuple

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.ProlongationTuple modularFunctionFieldBar jq ModularPolynomialData modularFunctionFieldFull algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff coeffEmb_mem_laurentBaseChange modularFunctionFieldC PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobOnPlacesGeomLevel frobOnPlacesGeomLevel_injective KroneckerCongruence ssPlaces jGeomGen coe_jGeomGen IsAffineGeomPlace order_jqModC_def jq_mem_full IsCusp charLGeomPlaceEquiv atkinLehnerInvolutionFull frickeInvolutionBar_def frickeInvolutionFull geomAut coe_geomAut_coeffEmb modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_charLGeomPlaceEquiv_placeInfty_eq_order modularUnitSeries_mem_modularFunctionFieldFull coe_frickeInvolutionFull_modularUnitSeries geomAut_atkinLehnerInvolutionFull_one_eq_frickeInvolutionBar isAffineGeomPlace_frobOnPlacesGeomLevel mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq frobOnPlacesGeomLevel_charLGeomPlaceOfPoint pow_mem_ssJSet_iff_of_perfectField coeffEmb_smul'"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "ProlongationTuple ProlongationTuple.residue₁_apply ProlongationTuple.residue₂_apply reduceFst redFst redFst_eq_placeInfty_of_forall_ord_le_zero ProlongationTuple.exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level ProlongationTuple.ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces_levelOne"
namespace ProlongationTuple
p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "atkinLehnerBar mem_integers₂_iff residue₁ residue₂ residue₁_apply residue₂_apply RegularityLaw R₁ ι redBar_residue R₂ residue₂_eq exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces_levelOne"
p2m_open "ModularCurve.PlaceSpecialization.ProlongationTuple ModularCurve.PlaceSpecialization ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided_levelOne.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided_levelOne.ModularCurve"

set_option autoImplicit false

theorem regularityLawSnd_oneSided_of_sepFunction
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [IsAlgClosed k] [DecidableEq k]
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (R : ProlongationTuple P) (hreg : R.RegularityLaw W)
    (U : ↥(modularFunctionFieldBar (N * q)))
    (hU₂ : U ∈ R.R₂.integers) (hUres : R.R₂.residue ⟨U, hU₂⟩ ≠ 0)
    (hArch : ∀ f : ↥(modularFunctionFieldBar (N * q)), ∃ b : ℕ, f * U ^ b ∈ R.R₁.integers)
    (hpoleU : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      IsAffineGeomPlace k N (P.reduceFst V) → 0 ≤ V.ord U)
    (hresU : ∀ v : Place k ↥(modularFunctionFieldC k N),
      frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
      IsAffineGeomPlace k N v → v ∉ W →
      (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨U, hU₂⟩ : ↥(modularFunctionFieldC k N)) = 0) :
    ∀ (f : modularFunctionFieldBar (N * q)) (h₂ : f ∈ R.R₂.integers),
      R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ v : Place k (modularFunctionFieldC k N),
        frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v →
        IsAffineGeomPlace k N v →
        v ∉ W →
        (∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
          P.reduceFst V = v → 0 ≤ V.ord f) →
        0 ≤ (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨f, h₂⟩) := by
  intro f h₂ hf v hfix haff hvW hpole
  classical
  have hU0 : U ≠ 0 := by
    intro h0; apply hUres
    have : (⟨U, hU₂⟩ : ↥R.R₂.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hf0 : f ≠ 0 := by
    intro h0; apply hf
    have : (⟨f, h₂⟩ : ↥R.R₂.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  obtain ⟨b, hb⟩ := hArch f
  have hF₂ : f * U ^ b ∈ R.R₂.integers := mul_mem h₂ (pow_mem hU₂ b)
  have hFeq : (⟨f * U ^ b, hF₂⟩ : ↥R.R₂.integers) = ⟨f, h₂⟩ * ⟨U, hU₂⟩ ^ b := by
    apply Subtype.ext
    simp
  have hFres : R.R₂.residue ⟨f * U ^ b, hF₂⟩ ≠ 0 := by
    rw [hFeq, map_mul, map_pow]
    exact mul_ne_zero hf (pow_ne_zero b hUres)
  have hFres' : R.residue₂ ⟨f * U ^ b, hF₂⟩ ≠ 0 := by
    rw [residue₂_apply]
    exact (map_ne_zero R.ι).mpr hFres
  have hpoleF : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)),
      P.reduceFst V = v → 0 ≤ V.ord (f * U ^ b) := by
    intro V hV
    rw [V.ord_mul hf0 (pow_ne_zero b hU0), Place.ord_pow' V hU0]
    have h1 := hpole V hV
    have h2 : 0 ≤ V.ord U := hpoleU V (by rw [hV]; exact haff)
    positivity
  have hmain := (hreg.1 (f * U ^ b) hb hF₂ v hfix haff hpoleF).2 hFres'
  have hres₂f : R.residue₂ ⟨f, h₂⟩ ≠ 0 := by
    rw [residue₂_apply]; exact (map_ne_zero R.ι).mpr hf
  have hres₂U : R.residue₂ ⟨U, hU₂⟩ ≠ 0 := by
    rw [residue₂_apply]; exact (map_ne_zero R.ι).mpr hUres
  rw [hFeq, map_mul, map_pow, (frobOnPlacesGeomLevel k N data hKr v).ord_mul hres₂f (pow_ne_zero b hres₂U),
    Place.ord_pow' _ hres₂U, hresU v hfix haff hvW, mul_zero, add_zero] at hmain
  exact hmain

private theorem _root_.ModularCurve.PlaceSpecialization.ProlongationTuple.modularUnitTransport_facts_levelOne
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : ProlongationTuple P)
    (U : ↥(modularFunctionFieldBar (1 * q)))
    (hU : (U : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (hU₁ : U ∈ R.R₁.integers) (hUres : R.R₁.residue ⟨U, hU₁⟩ ≠ 0) :
    ∃ (h₂ : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ((q : AlgebraicClosure ℚ) ^ 12) * U⁻¹
        ∈ R.R₂.integers),
      R.R₂.residue ⟨_, h₂⟩ = R.R₁.residue ⟨U, hU₁⟩ ∧
      (∀ f : ↥(modularFunctionFieldBar (1 * q)), ∃ b : ℕ,
        f * (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ((q : AlgebraicClosure ℚ) ^ 12) * U⁻¹) ^ b
          ∈ R.R₁.integers) := by
  classical
  set c : AlgebraicClosure ℚ := (q : AlgebraicClosure ℚ) ^ 12 with hc
  have hc0 : c ≠ 0 := pow_ne_zero 12 (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
  have hcA : c ∈ A := by rw [hc]; exact pow_mem (by exact_mod_cast natCast_mem A q) 12
  set U' : ↥(modularFunctionFieldBar (1 * q)) := algebraMap (AlgebraicClosure ℚ) _ c * U⁻¹ with hU'

  have hUunit : IsUnit (⟨U, hU₁⟩ : ↥R.R₁.integers) := R.R₁.isUnit_of_residue_ne_zero hUres
  obtain ⟨w, hw⟩ := hUunit.exists_right_inv
  have hwF : (U : ↥(modularFunctionFieldBar (1 * q))) * (w : ↥(modularFunctionFieldBar (1 * q))) = 1 := by
    have h := congrArg Subtype.val hw
    simpa using h
  have hU0 : U ≠ 0 := left_ne_zero_of_mul_eq_one hwF
  have hUinv : U⁻¹ ∈ R.R₁.integers := by
    rw [← eq_inv_of_mul_eq_one_right hwF]; exact w.2

  have hAL : atkinLehnerBar 1 q U' = U := by
    rw [hU', map_mul, AlgEquiv.commutes, map_inv₀, atkinLehnerBar_one_modularUnit U hU, mul_inv, ← mul_assoc,
      ← map_inv₀, ← map_mul, ← hc, mul_inv_cancel₀ hc0, map_one, inv_inv]
    exact _root_.one_mul U
  have h₂ : U' ∈ R.R₂.integers := by
    rw [R.mem_integers₂_iff, hAL]; exact hU₁
  refine ⟨h₂, ?_, ?_⟩
  · rw [R.residue₂_eq U' h₂]
    congr 1
    exact Subtype.ext hAL
  · intro f
    rcases eq_or_ne f 0 with rfl | hf0
    · exact ⟨0, by rw [zero_mul]; exact zero_mem _⟩
    obtain ⟨d, hdf, hdres⟩ := R.R₁.exists_smul_mem f hf0
    have hd0 : d ≠ 0 := R.R₁.smul_const_ne_zero hdf hdres
    obtain ⟨b, hb⟩ := A.exists_natCast_pow_mul_mem_of_forall_isUnit red q (R.isUnit_of_red_ne_zero) d⁻¹
    refine ⟨b, ?_⟩
    have hq12 : (c ^ b * d⁻¹) ∈ A := by
      have : c ^ b * d⁻¹ = (q : AlgebraicClosure ℚ) ^ (11 * b) * ((q : AlgebraicClosure ℚ) ^ b * d⁻¹) := by
        rw [hc]; ring
      rw [this]
      exact mul_mem (pow_mem (by exact_mod_cast natCast_mem A q) _) hb
    have hrw : f * U' ^ b = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (c ^ b * d⁻¹)
        * ((d • f) * U⁻¹ ^ b) := by
      rw [hU', mul_pow, ← map_pow, Algebra.smul_def, map_mul]
      have hdd : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) d⁻¹ *
          algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) d = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hd0, map_one]
      calc f * (algebraMap _ _ (c ^ b) * U⁻¹ ^ b)
          = algebraMap _ _ (c ^ b) * (algebraMap _ _ d⁻¹ * algebraMap _ _ d) * f * U⁻¹ ^ b := by rw [hdd]; ring
        _ = _ := by ring
    rw [hrw]
    exact mul_mem ((R.R₁.algebraMap_mem_iff _).mpr hq12) (mul_mem hdf (pow_mem hUinv b))

p2m_export "ModularCurve.PlaceSpecialization.ProlongationTuple" "modularUnitTransport_facts_levelOne"

theorem mem_ssPlaces_of_frob_mem_ssPlaces
    {q : ℕ} [Fact q.Prime] {k : Type*} [Field k] [CharP k q] [IsAlgClosed k] [DecidableEq k]
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
    (v : Place k ↥(modularFunctionFieldC k 1)) (h : frobOnPlacesGeomLevel k 1 data hKr v ∈ ssPlaces q 1 k) :
    v ∈ ssPlaces q 1 k := by
  haveI : PerfectField k := inferInstance
  obtain ⟨a, ha, hav⟩ := (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k _).mp h
  obtain ⟨b, rfl⟩ := IsAlgClosed.exists_pow_nat_eq a (Fact.out : q.Prime).pos
  rw [← ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceOfPoint k data hKr b] at hav
  have hv := frobOnPlacesGeomLevel_injective k 1 data hKr hav
  rw [← hv]
  exact (ModularCurve.mem_ssPlaces_one_iff_exists_charLGeomPlaceOfPoint_eq q k _).mpr
    ⟨b, (ModularCurve.pow_mem_ssJSet_iff_of_perfectField q b).mp ha, rfl⟩

end ModularCurve.PlaceSpecialization.ProlongationTuple

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "Place Place.ord_zero Place.ord_one Place.ord_inv RationalFunctionField.placeInfty Place.ord_pow'" namespace Place p2m_export "AlgebraicCurve.Place" "hasValue_algebraMap ext ord ord_zero ord_one ord_mul ord_inv ord_coe_unit algebraMap_mem' toValuationSubring ord_nonneg_of_mem mem_of_ord_nonneg ord_pow'" end AlgebraicCurve.Place
namespace AlgebraicCurve.Place
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.ord_algebraMap_mul' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {c : K} (hc : c ≠ 0) (g : F) :
    v.ord (algebraMap K F c * g) = v.ord g := by
  rcases eq_or_ne g 0 with rfl | hg
  · rw [mul_zero]
  · rw [v.ord_mul ((map_ne_zero _).mpr hc) hg]
    have hu : IsUnit (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) :=
      (v.hasValue_algebraMap c).isUnit hc
    have h0 := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at h0
    change v.ord (algebraMap K F c) = 0 at h0
    rw [h0, zero_add]

end AlgebraicCurve.Place
p2m_export "" "AlgebraicCurve.Place.ord_algebraMap_mul'"
open HahnSeries _root_.ModularCurve _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided_levelOne.ModularCurve _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided_levelOne.AlgebraicCurve IsLocalRing _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided_levelOne.ModularCurve.PlaceSpecialization in
theorem solution {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q} [IsAlgClosed k]
    [DecidableEq k]
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Finset (Place k (modularFunctionFieldC k 1)))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 k)
    (R : ProlongationTuple P) (hreg : R.RegularityLaw W) :
    ∀ (f : modularFunctionFieldBar (1 * q)) (h₂ : f ∈ R.R₂.integers),
      R.R₂.residue ⟨f, h₂⟩ ≠ 0 →
      ∀ v : Place k (modularFunctionFieldC k 1),
        frobOnPlacesGeomLevel k 1 data hKr (frobOnPlacesGeomLevel k 1 data hKr v) = v →
        IsAffineGeomPlace k 1 v →
        v ∉ W →
        (∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)),
          P.reduceFst V = v → 0 ≤ V.ord f) →
        0 ≤ (frobOnPlacesGeomLevel k 1 data hKr v).ord (R.residue₂ ⟨f, h₂⟩) := by

  let U : ↥(modularFunctionFieldBar (1 * q)) := ⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩
  have hU : (U : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q) := by
    show coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)) = _
    simp only [one_mul]
  obtain ⟨hU₁, hUres, -⟩ :=
    ProlongationTuple.exists_mem_integersFst_residue_ne_zero_of_coe_eq_modularUnitSeries_level P R U hU
  obtain ⟨h₂', hres₂', hArch'⟩ := R.modularUnitTransport_facts_levelOne U hU hU₁ hUres
  have hq0 : ((q : AlgebraicClosure ℚ) ^ 12) ≠ 0 := pow_ne_zero 12 (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero)
  have hU0 : U ≠ 0 := by
    intro h0; apply hUres
    have : (⟨U, hU₁⟩ : ↥R.R₁.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  refine ProlongationTuple.regularityLawSnd_oneSided_of_sepFunction P W R hreg _ h₂' (by rw [hres₂']; exact hUres)
    hArch' ?_ ?_
  · intro V hV
    rw [V.ord_algebraMap_mul' hq0, Place.ord_inv, ord_modularUnit_eq_zero_of_isAffineGeomPlace_reduceFst P U hU V hV, neg_zero]
  · intro v hfix haff hvW
    have hres : (R.residue₂ ⟨_, h₂'⟩ : ↥(modularFunctionFieldC k 1)) = R.residue₁ ⟨U, hU₁⟩ := by
      rw [ProlongationTuple.residue₂_apply, hres₂', ProlongationTuple.residue₁_apply]
    rw [hres]
    refine ProlongationTuple.ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces_levelOne
      P R U hU hU₁ _ (ModularCurve.isAffineGeomPlace_frobOnPlacesGeomLevel k 1 data hKr v haff) ?_
    intro h
    exact hvW ((hW v).mpr (ProlongationTuple.mem_ssPlaces_of_frob_mem_ssPlaces data hKr v h))

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided_levelOne
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_regularityLawSnd_oneSided_levelOne (solution)
