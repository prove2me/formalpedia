-- Prove2me | solution 1 for ModularCurve.MultCovering.exists_famData_of_bifiltered_digits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e2b308d7-b043-5517-a5d5-70279a500725

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Theorems.Thm_ModularCurve_MultCovering_hasseContent_nonneg
import Theorems.Thm_ModularCurve_exists_mul_coeff_frickeInvolutionBar_mem_of_mem_riemannRochSpace_cuspInftyBar
import Theorems.Thm_ModularCurve_exists_isLeast_padicValRat_coeff_of_mul_coeffEmb_coeff_mem
import Theorems.Thm_ModularCurve_coeffEmb_smul_coeff_mem_and_not_mem_nonunits_of_le_padicValRat
import Theorems.Thm_ModularCurve_MultCovering_mem_infChart_integers_iff_coe_mem_modularLocalized
import Theorems.Thm_ModularCurve_CharPReduction_modularRedLocHom_eq_coeffRed
import Theorems.Thm_ValuationSubring_ratCast_mem_iff_padicValRat_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_exists_famData_of_bifiltered_digits
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst"
p2m_attr_erase "simp" "ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk"
p2m_attr_erase "simp" "ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

namespace UMK

variable {p : ℕ} [Fact p.Prime] {r : ℕ}

theorem algebraMap_LS_eq_C (c : AlgebraicClosure ℚ) :
    algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c = HahnSeries.C c := by
  rw [algebraMap_laurentSeries_eq_single]; rfl

def IsContent (Φ : FamData p r) (l : Fin r) (n : ℤ) : Prop :=
  (∀ k : ℤ, (zeroSeries Φ l).coeff k ≠ 0 → n ≤ padicValRat p ((zeroSeries Φ l).coeff k)) ∧
    (∃ k : ℤ, (zeroSeries Φ l).coeff k ≠ 0 ∧ padicValRat p ((zeroSeries Φ l).coeff k) = n)

theorem isContent_hasseContent (Φ : FamData p r) (l : Fin r) (hex : ∃ n : ℤ, IsContent Φ l n) :
    IsContent Φ l (hasseContent Φ l) := by
  have hex' : ∃ n : ℤ, (∀ k : ℤ, (zeroSeries Φ l).coeff k ≠ 0 → n ≤ padicValRat p ((zeroSeries Φ l).coeff k)) ∧
      (∃ k : ℤ, (zeroSeries Φ l).coeff k ≠ 0 ∧ padicValRat p ((zeroSeries Φ l).coeff k) = n) := hex
  rw [hasseContent, dif_pos hex']
  exact hex'.choose_spec

theorem IsContent.eq {Φ : FamData p r} {l : Fin r} {m n : ℤ} (hm : IsContent Φ l m) (hn : IsContent Φ l n) :
    m = n := by
  obtain ⟨k, hk, hkm⟩ := hm.2
  obtain ⟨k', hk', hkn⟩ := hn.2
  have h1 := hn.1 k hk
  have h2 := hm.1 k' hk'
  rw [hkm] at h1; rw [hkn] at h2
  exact le_antisymm h2 h1

theorem hasseContent_eq_of_isContent {Φ : FamData p r} {l : Fin r} {n : ℤ} (hn : IsContent Φ l n) :
    hasseContent Φ l = n :=
  (isContent_hasseContent Φ l ⟨n, hn⟩).eq hn

theorem zeroSeries_ne_zero (Φ : FamData p r) (l : Fin r) (ht0 : Φ.t l ≠ 0) : zeroSeries Φ l ≠ 0 := by
  intro h
  apply ht0
  have h1 : ((frickeInvolutionBar (1 * p) (Φ.t l) : modularFunctionFieldBar (1 * p)) :
      LaurentSeries (AlgebraicClosure ℚ)) = 0 := by
    rw [coe_frickeInvolutionBar_t, h, map_zero]
  have h2 : frickeInvolutionBar (1 * p) (Φ.t l) = 0 := Subtype.ext h1
  exact (EmbeddingLike.map_eq_zero_iff (f := frickeInvolutionBar (1 * p))).mp h2

theorem exists_isContent (Φ : FamData p r) (l : Fin r) (ht0 : Φ.t l ≠ 0)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) (c : AlgebraicClosure ℚ) (hc : c ≠ 0)
    (hcA : ∀ k : ℤ, c * ((frickeInvolutionBar (1 * p) (Φ.t l) : modularFunctionFieldBar (1 * p)) :
        LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A) :
    ∃ n : ℤ, IsContent Φ l n := by
  have hcA' : ∀ k : ℤ, c * (coeffEmb (AlgebraicClosure ℚ) (zeroSeries Φ l)).coeff k ∈ A := by
    intro k; rw [← coe_frickeInvolutionBar_t]; exact hcA k
  obtain ⟨n, h1, k₀, hk₀, hk₀n⟩ := exists_isLeast_padicValRat_coeff_of_mul_coeffEmb_coeff_mem
    (Fact.out : p.Prime) A hA (zeroSeries Φ l) (zeroSeries_ne_zero Φ l ht0) c hc hcA'
  exact ⟨n, h1, k₀, hk₀, hk₀n⟩

theorem coeff_smul_zeroSeries_mem (Φ : FamData p r) (l : Fin r) {n : ℤ} (hn : IsContent Φ l n)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) (k : ℤ) :
    (coeffEmb (AlgebraicClosure ℚ) (((p : ℚ) ^ n)⁻¹ • zeroSeries Φ l)).coeff k ∈ A := by
  obtain ⟨k₀, hk₀, hk₀n⟩ := hn.2
  exact (coeffEmb_smul_coeff_mem_and_not_mem_nonunits_of_le_padicValRat A (Fact.out : p.Prime)
    hA (zeroSeries Φ l) n hn.1 k₀ hk₀ hk₀n).1 k

theorem hasseExp_cast (Φ : FamData p r) (l : Fin r) (h0 : 0 ≤ hasseContent Φ l) :
    (hasseExp Φ l : ℤ) = hasseContent Φ l := by
  rw [hasseExp, Int.toNat_of_nonneg h0]

theorem coe_frickeInvolutionBar_goodFamilyZero (Φ : FamData p r) (l : Fin r) :
    ((frickeInvolutionBar (1 * p) (goodFamilyZero Φ l) : modularFunctionFieldBar (1 * p)) :
        LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (((p : ℚ) ^ (hasseExp Φ l : ℤ))⁻¹ • zeroSeries Φ l) := by
  rw [goodFamilyZero, map_mul, map_inv₀, AlgEquiv.commutes]
  have hcoe : (((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
        ((p : AlgebraicClosure ℚ) ^ hasseExp Φ l))⁻¹ * frickeInvolutionBar (1 * p) (Φ.t l) :
          modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ))
      = (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))
          ((p : AlgebraicClosure ℚ) ^ hasseExp Φ l))⁻¹ *
        ((frickeInvolutionBar (1 * p) (Φ.t l) : modularFunctionFieldBar (1 * p)) :
          LaurentSeries (AlgebraicClosure ℚ)) := by
    push_cast
    rfl
  rw [hcoe, coe_frickeInvolutionBar_t]
  ext k
  rw [coeffEmb_coeff, ← map_inv₀, algebraMap_laurentSeries_eq_single, HahnSeries.single_zero_mul_eq_smul,
    HahnSeries.coeff_smul, coeffEmb_coeff, smul_eq_mul]
  show ((p : AlgebraicClosure ℚ) ^ hasseExp Φ l)⁻¹ * algebraMap ℚ (AlgebraicClosure ℚ) ((zeroSeries Φ l).coeff k)
    = algebraMap ℚ (AlgebraicClosure ℚ) ((((p : ℚ) ^ (hasseExp Φ l : ℤ))⁻¹ • zeroSeries Φ l).coeff k)
  rw [show ((((p : ℚ) ^ (hasseExp Φ l : ℤ))⁻¹ • zeroSeries Φ l).coeff k)
      = ((p : ℚ) ^ (hasseExp Φ l : ℤ))⁻¹ * (zeroSeries Φ l).coeff k from rfl,
    map_mul, map_inv₀, zpow_natCast, map_pow, map_natCast]

theorem frobenius_residue_ratCast (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] (q : ℚ) (hq : (algebraMap ℚ (AlgebraicClosure ℚ) q) ∈ A) :
    frobenius (ResidueField ↥A) p (IsLocalRing.residue ↥A ⟨_, hq⟩) = IsLocalRing.residue ↥A ⟨_, hq⟩ := by
  have hp : p.Prime := Fact.out
  by_cases hq0 : q = 0
  · subst hq0
    have : (⟨algebraMap ℚ (AlgebraicClosure ℚ) 0, hq⟩ : ↥A) = 0 := Subtype.ext (by simp)
    rw [this, map_zero, map_zero]

  have hq' : ((q : ℚ) : AlgebraicClosure ℚ) ∈ A := by rwa [eq_ratCast] at hq
  have hAp : A.valuation ((p : ℕ) : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff A).mp hA
  have hv : 0 ≤ padicValRat p q := (ValuationSubring.ratCast_mem_iff_padicValRat_nonneg A hp hAp hq0).mp hq'

  have hden : ¬ p ∣ q.den := by
    intro hdvd
    have h1 : 1 ≤ padicValNat p q.den := one_le_padicValNat_of_dvd q.den_nz hdvd
    have hcop : Nat.Coprime q.num.natAbs q.den := q.reduced
    have hnum : ¬ (p : ℤ) ∣ q.num := by
      intro h
      have h' : p ∣ q.num.natAbs := Int.natCast_dvd.mp (by simpa using h)
      have := (Nat.coprime_self p).mp (Nat.Coprime.coprime_dvd_left h' (Nat.Coprime.coprime_dvd_right hdvd hcop))
      exact hp.one_lt.ne' this
    have h2 : padicValInt p q.num = 0 := padicValInt.eq_zero_of_not_dvd hnum
    have h3 : padicValRat p q = padicValInt p q.num - padicValNat p q.den := rfl
    rw [h3, h2] at hv
    omega
  have hdenk : ((q.den : ℕ) : ResidueField ↥A) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (ResidueField ↥A) p]
    exact hden

  have hmul : (⟨algebraMap ℚ (AlgebraicClosure ℚ) q, hq⟩ : ↥A) * (q.den : ↥A) = (q.num : ↥A) := by
    apply Subtype.ext
    push_cast
    rw [eq_ratCast, ← Rat.cast_natCast, ← Rat.cast_mul, Rat.mul_den_eq_num, Rat.cast_intCast]
  have hres : IsLocalRing.residue ↥A ⟨_, hq⟩ * ((q.den : ℕ) : ResidueField ↥A)
      = ((q.num : ℤ) : ResidueField ↥A) := by
    rw [← map_natCast (IsLocalRing.residue ↥A), ← map_intCast (IsLocalRing.residue ↥A), ← map_mul, hmul]
  have hres' : IsLocalRing.residue ↥A ⟨_, hq⟩
      = ((q.num : ℤ) : ResidueField ↥A) / ((q.den : ℕ) : ResidueField ↥A) :=
    eq_div_of_mul_eq hdenk hres
  rw [hres', map_div₀, map_intCast, map_natCast]

section PortedW8
variable (p) in

theorem coe_sum_single_smul_coeff (X : Fin r → ↥(modularFunctionFieldFull (1 * p))) (l : Fin r) (a : ℚ) (m : ℤ) :
    (((∑ i, (Pi.single l a : Fin r → ℚ) i • X i : ↥(modularFunctionFieldFull (1 * p)))) : LaurentSeries ℚ).coeff m
      = a * ((X l : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m := by
  rw [Finset.sum_eq_single l (fun i _ hi => by rw [Pi.single_eq_of_ne hi, zero_smul])
    (fun h => (h (Finset.mem_univ l)).elim), Pi.single_eq_same]
  first
  | rfl
  | (rw [IntermediateField.coe_smul]; rfl)
  | simp [Algebra.smul_def, algebraMap_laurentSeries_eq_single, HahnSeries.single_zero_mul_eq_smul, HahnSeries.coeff_smul]

theorem coe_frickeInvolutionBar_algebraMap_mul (Φ : FamData p r) (l : Fin r) (y : ℚ) :
    ((frickeInvolutionBar (1 * p)
        (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) (algebraMap ℚ (AlgebraicClosure ℚ) y) * Φ.t l) :
          modularFunctionFieldBar (1 * p)) : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (y • zeroSeries Φ l) := by
  rw [map_mul, AlgEquiv.commutes]
  push_cast
  rw [coe_frickeInvolutionBar_t]
  ext k
  rw [coeffEmb_coeff]
  first
  | rw [IntermediateField.algebraMap_apply]
  | skip
  rw [algebraMap_laurentSeries_eq_single,
    HahnSeries.single_zero_mul_eq_smul, HahnSeries.coeff_smul, coeffEmb_coeff, smul_eq_mul,
    show ((y • zeroSeries Φ l).coeff k) = y * (zeroSeries Φ l).coeff k from rfl, map_mul]

noncomputable def recombine (D : FamData p r) (U : Matrix (Fin r) (Fin r) ℚ) : FamData p r where
  tRat i := ∑ j, U i j • D.tRat j
  t i := ⟨coeffEmb (AlgebraicClosure ℚ) ((∑ j, U i j • D.tRat j : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (∑ j, U i j • D.tRat j : ↥(modularFunctionFieldFull (1 * p))).2⟩
  t_eq i := rfl

theorem recombine_tRat (D : FamData p r) (U : Matrix (Fin r) (Fin r) ℚ) (i : Fin r) :
    (recombine D U).tRat i = ∑ j, U i j • D.tRat j := rfl

theorem coe_sum_smul_coeff (X : Fin r → ↥(modularFunctionFieldFull (1 * p))) (c : Fin r → ℚ) (m : ℤ) :
    ((∑ j, c j • X j : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m
      = ∑ j, c j * ((X j : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ).coeff m := by
  rw [IntermediateField.coe_sum, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have key := coe_sum_single_smul_coeff (p := p) X j (c j) m
  rw [Finset.sum_eq_single j (fun i _ hi => by rw [Pi.single_eq_of_ne hi, zero_smul])
    (fun h => (h (Finset.mem_univ j)).elim), Pi.single_eq_same] at key
  exact key

theorem recombine_t (D : FamData p r) (U : Matrix (Fin r) (Fin r) ℚ) (i : Fin r) :
    (recombine D U).t i = ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
        (algebraMap ℚ (AlgebraicClosure ℚ) (U i j)) * D.t j := by
  apply Subtype.ext
  change coeffEmb (AlgebraicClosure ℚ) ((∑ j, U i j • D.tRat j : ↥(modularFunctionFieldFull (1 * p))) : LaurentSeries ℚ) = _
  ext m
  rw [coeffEmb_coeff, coe_sum_smul_coeff, map_sum, IntermediateField.coe_sum, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, IntermediateField.coe_mul]
  have e1 : ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
      (algebraMap ℚ (AlgebraicClosure ℚ) (U i j)) : ↥(modularFunctionFieldBar (1 * p))) : LaurentSeries (AlgebraicClosure ℚ))
      = HahnSeries.C (algebraMap ℚ (AlgebraicClosure ℚ) (U i j)) := by
    first
    | (change algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) _ = _
       exact algebraMap_LS_eq_C _)
    | (rw [IntermediateField.algebraMap_apply]; exact algebraMap_LS_eq_C _)
    | (rw [SubalgebraClass.coe_algebraMap]; exact algebraMap_LS_eq_C _)
  rw [e1, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
  congr 1
  have := congrArg (fun x : ↥(modularFunctionFieldBar (1 * p)) => (x : LaurentSeries (AlgebraicClosure ℚ)).coeff m) (D.t_eq j)
  simpa only [coeffEmb_coeff] using this.symm

theorem zeroSeries_recombine_coeff (D : FamData p r) (U : Matrix (Fin r) (Fin r) ℚ) (i : Fin r) (m : ℤ) :
    (zeroSeries (recombine D U) i).coeff m = ∑ j, U i j * (zeroSeries D j).coeff m := by
  unfold zeroSeries
  rw [recombine_tRat, map_sum]
  simp_rw [map_rat_smul]
  exact coe_sum_smul_coeff _ _ _

theorem le_padicValRat_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (n : ℤ)
    (h : ∀ j ∈ s, f j ≠ 0 → n ≤ padicValRat p (f j)) (hs : ∑ j ∈ s, f j ≠ 0) :
    n ≤ padicValRat p (∑ j ∈ s, f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | insert a s ha ih =>
    rw [Finset.sum_insert ha] at hs ⊢
    by_cases hfa : f a = 0
    · rw [hfa, zero_add] at hs ⊢
      exact ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) hs
    by_cases hss : ∑ j ∈ s, f j = 0
    · rw [hss, add_zero]
      exact h a (Finset.mem_insert_self a s) hfa
    have h1 := h a (Finset.mem_insert_self a s) hfa
    have h2 := ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) hss
    exact (le_min h1 h2).trans (padicValRat.min_le_padicValRat_add hs)

theorem le_padicValRat_mul_coeff (U : Matrix (Fin r) (Fin r) ℚ) (D : FamData p r) (n : Fin r → ℕ) (i j : Fin r) (m : ℤ)
    (hrow : U i j = 0 ∨ ((n i : ℤ) - (n j : ℤ)) ≤ padicValRat p (U i j))
    (hD : (zeroSeries D j).coeff m ≠ 0 → ((n j : ℕ) : ℤ) ≤ padicValRat p ((zeroSeries D j).coeff m))
    (hne : U i j * (zeroSeries D j).coeff m ≠ 0) :
    ((n i : ℕ) : ℤ) ≤ padicValRat p (U i j * (zeroSeries D j).coeff m) := by
  have hU0 : U i j ≠ 0 := left_ne_zero_of_mul hne
  have hc0 : (zeroSeries D j).coeff m ≠ 0 := right_ne_zero_of_mul hne
  rcases hrow with h | h
  · exact absurd h hU0
  rw [padicValRat.mul hU0 hc0]
  have := hD hc0
  omega

theorem hasseExp_recombine_eq (D : FamData p r) (U : Matrix (Fin r) (Fin r) ℚ) (n : Fin r → ℕ) (i : Fin r)
    (hrow : ∀ j, U i j = 0 ∨ ((n i : ℤ) - (n j : ℤ)) ≤ padicValRat p (U i j))
    (hD : ∀ j (m : ℤ), (zeroSeries D j).coeff m ≠ 0 → ((n j : ℕ) : ℤ) ≤ padicValRat p ((zeroSeries D j).coeff m))
    (hunit : ∃ m : ℤ, (zeroSeries (recombine D U) i).coeff m ≠ 0 ∧
      padicValRat p ((zeroSeries (recombine D U) i).coeff m) = n i) :
    hasseExp (recombine D U) i = n i := by
  have hc : IsContent (recombine D U) i (n i) := by
    refine ⟨fun k hk => ?_, hunit⟩
    rw [zeroSeries_recombine_coeff] at hk ⊢
    exact le_padicValRat_sum _ _ _ (fun j _ hj => le_padicValRat_mul_coeff U D n i j k (hrow j) (hD j k) hj) hk
  rw [hasseExp, hasseContent_eq_of_isContent hc]
  simp

theorem le_padicValRat_zeroSeries_recombine (D : FamData p r) (U : Matrix (Fin r) (Fin r) ℚ) (n : Fin r → ℕ) (i : Fin r)
    (hrow : ∀ j, U i j = 0 ∨ ((n i : ℤ) - (n j : ℤ)) ≤ padicValRat p (U i j))
    (hD : ∀ j (m : ℤ), (zeroSeries D j).coeff m ≠ 0 → ((n j : ℕ) : ℤ) ≤ padicValRat p ((zeroSeries D j).coeff m))
    (m : ℤ) (hm : (zeroSeries (recombine D U) i).coeff m ≠ 0) :
    ((n i : ℕ) : ℤ) ≤ padicValRat p ((zeroSeries (recombine D U) i).coeff m) := by
  rw [zeroSeries_recombine_coeff] at hm ⊢
  exact le_padicValRat_sum _ _ _ (fun j _ hj => le_padicValRat_mul_coeff U D n i j m (hrow j) (hD j m) hj) hm

section Charts

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A)

theorem goodFamilyZero_recombine (D : FamData p r) (U : Matrix (Fin r) (Fin r) ℚ) (i : Fin r)
    (hexp : hasseExp (recombine D U) i = hasseExp D i) :
    goodFamilyZero (recombine D U) i
      = ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
          (algebraMap ℚ (AlgebraicClosure ℚ) (U i j) * (p : AlgebraicClosure ℚ) ^ hasseExp D j
            * ((p : AlgebraicClosure ℚ) ^ hasseExp D i)⁻¹) * goodFamilyZero D j := by
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold goodFamilyZero
  rw [hexp, recombine_t, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, map_inv₀, map_pow, map_natCast]
  have hpj : (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((p : AlgebraicClosure ℚ) ^ hasseExp D j)) ≠ 0 :=
    (map_ne_zero _).mpr (pow_ne_zero _ hp0)
  rw [map_pow, map_natCast] at hpj ⊢
  field_simp

theorem zeroChart_residue_goodFamilyZero_recombine (D : FamData p r) (U : Matrix (Fin r) (Fin r) ℚ) (i : Fin r)
    (hexp : hasseExp (recombine D U) i = hasseExp D i)
    (hrow : ∀ j, U i j = 0 ∨ ((hasseExp D i : ℤ) - (hasseExp D j : ℤ)) ≤ padicValRat p (U i j))
    (hint : ∀ j, goodFamilyZero D j ∈ (zeroChart Γ).integers)
    (c : Fin r → ↥A)
    (hc : ∀ j, (c j : AlgebraicClosure ℚ) = algebraMap ℚ (AlgebraicClosure ℚ) (U i j) * (p : AlgebraicClosure ℚ) ^ hasseExp D j
            * ((p : AlgebraicClosure ℚ) ^ hasseExp D i)⁻¹) :
    ∃ h : goodFamilyZero (recombine D U) i ∈ (zeroChart Γ).integers,
      (zeroChart Γ).residue ⟨goodFamilyZero (recombine D U) i, h⟩
        = ∑ j, algebraMap (ResidueField ↥A) _ (IsLocalRing.residue ↥A (c j))
            * (zeroChart Γ).residue ⟨goodFamilyZero D j, hint j⟩ := by
  set C := zeroChart Γ
  have hform := goodFamilyZero_recombine D U i hexp
  have hmem : goodFamilyZero (recombine D U) i ∈ C.integers := by
    rw [hform]
    refine sum_mem fun j _ => mul_mem ?_ (hint j)
    rw [← hc j]
    exact (C.algebraMap_mem_iff _).2 (c j).2
  refine ⟨hmem, ?_⟩
  have e1 : (⟨goodFamilyZero (recombine D U) i, hmem⟩ : C.integers)
      = ∑ j, ⟨algebraMap (AlgebraicClosure ℚ) _ (c j : AlgebraicClosure ℚ), (C.algebraMap_mem_iff _).2 (c j).2⟩ * ⟨goodFamilyZero D j, hint j⟩ := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul]
    rw [hform]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc j]
  rw [e1, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, C.residue_algebraMap]

theorem infChart_residue_recombine (D : FamData p r) (U : Matrix (Fin r) (Fin r) ℚ) (i : Fin r)
    (hintI : ∀ j, D.t j ∈ (infChart Γ).integers)
    (c : Fin r → ↥A) (hc : ∀ j, (c j : AlgebraicClosure ℚ) = algebraMap ℚ (AlgebraicClosure ℚ) (U i j)) :
    ∃ h : (recombine D U).t i ∈ (infChart Γ).integers,
      (infChart Γ).residue ⟨(recombine D U).t i, h⟩
        = ∑ j, algebraMap (ResidueField ↥A) _ (IsLocalRing.residue ↥A (c j))
            * (infChart Γ).residue ⟨D.t j, hintI j⟩ := by
  set C := infChart Γ
  have hform := recombine_t D U i
  have hmem : (recombine D U).t i ∈ C.integers := by
    rw [hform]
    refine sum_mem fun j _ => mul_mem ?_ (hintI j)
    rw [← hc j]
    exact (C.algebraMap_mem_iff _).2 (c j).2
  refine ⟨hmem, ?_⟩
  have e1 : (⟨(recombine D U).t i, hmem⟩ : C.integers)
      = ∑ j, ⟨algebraMap (AlgebraicClosure ℚ) _ (c j : AlgebraicClosure ℚ), (C.algebraMap_mem_iff _).2 (c j).2⟩ * ⟨D.t j, hintI j⟩ := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul]
    rw [hform]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hc j]
  rw [e1, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, C.residue_algebraMap]
end Charts
end PortedW8

theorem residue_algebraMap_rat_eq_zero_of_padicValRat_pos
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) (q : ℚ) (hq : q ≠ 0)
    (hv : 1 ≤ padicValRat p q) (hmem : algebraMap ℚ (AlgebraicClosure ℚ) q ∈ A) :
    IsLocalRing.residue ↥A ⟨algebraMap ℚ (AlgebraicClosure ℚ) q, hmem⟩ = 0 := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  set q' : ℚ := q / p with hq'
  have hq'0 : q' ≠ 0 := div_ne_zero hq hp0
  have hqq' : q = p * q' := by rw [hq', mul_div_cancel₀ q hp0]
  have hvq' : 0 ≤ padicValRat p q' := by
    have h1 : padicValRat p q = padicValRat p (p : ℚ) + padicValRat p q' := by
      rw [hqq', padicValRat.mul hp0 hq'0]
    rw [padicValRat.self hp.one_lt] at h1
    linarith
  have hAp : A.valuation ((p : ℕ) : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff A).1 hA
  have hq'A : ((q' : ℚ) : AlgebraicClosure ℚ) ∈ A :=
    (ValuationSubring.ratCast_mem_iff_padicValRat_nonneg A hp hAp hq'0).2 hvq'
  have hpA : ((p : ℕ) : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  have hp𝔪 : (⟨(p : AlgebraicClosure ℚ), hpA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A :=
    (ValuationSubring.coe_mem_nonunits_iff (a := ⟨(p : AlgebraicClosure ℚ), hpA⟩)).1 hA
  have e1 : (⟨algebraMap ℚ (AlgebraicClosure ℚ) q, hmem⟩ : ↥A)
      = ⟨(p : AlgebraicClosure ℚ), hpA⟩ * ⟨((q' : ℚ) : AlgebraicClosure ℚ), hq'A⟩ := by
    apply Subtype.ext
    show algebraMap ℚ (AlgebraicClosure ℚ) q = (p : AlgebraicClosure ℚ) * ((q' : ℚ) : AlgebraicClosure ℚ)
    rw [eq_ratCast, hqq']; push_cast; ring
  rw [e1]
  exact (IsLocalRing.residue_eq_zero_iff _).2 (Ideal.mul_mem_right _ _ hp𝔪)

theorem algebraMap_rat_mem_of_padicValRat_nonneg
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) (q : ℚ)
    (hv : q = 0 ∨ 0 ≤ padicValRat p q) : algebraMap ℚ (AlgebraicClosure ℚ) q ∈ A := by
  have hp : p.Prime := Fact.out
  rcases eq_or_ne q 0 with h0 | h0
  · subst h0; rw [map_zero]; exact zero_mem A
  have hv' : 0 ≤ padicValRat p q := by rcases hv with h | h; exact absurd h h0; exact h
  have hAp : A.valuation ((p : ℕ) : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff A).1 hA
  rw [eq_ratCast]
  exact (ValuationSubring.ratCast_mem_iff_padicValRat_nonneg A hp hAp h0).2 hv'

variable (n : Fin r → ℕ) (d : Fin r → Fin r → ZMod p)

theorem coeff_rescaled_eq_natCast (U : Matrix (Fin r) (Fin r) ℚ)
    (hUd : ∀ i j, U i j = (p : ℚ) ^ (max 0 ((n i : ℤ) - (n j : ℤ))).toNat * ((d i j).val : ℚ)) (i j : Fin r) :
    U i j * (p : ℚ) ^ (n j) * ((p : ℚ) ^ (n i))⁻¹ = ((p ^ (n j - n i) * (d i j).val : ℕ) : ℚ) := by
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  rw [hUd i j]
  have hmax : (max 0 ((n i : ℤ) - (n j : ℤ))).toNat = n i - n j := by omega
  rw [hmax]
  rcases le_total (n i) (n j) with h | h
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
    rw [hk, Nat.add_sub_cancel_left, Nat.sub_eq_zero_of_le (Nat.le_add_right _ _), pow_zero, one_mul, pow_add]
    push_cast
    field_simp
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
    rw [hk, Nat.add_sub_cancel_left, Nat.sub_eq_zero_of_le (Nat.le_add_right _ _), pow_zero, one_mul, pow_add]
    push_cast
    field_simp

theorem coeff_eq_natCast (U : Matrix (Fin r) (Fin r) ℚ)
    (hUd : ∀ i j, U i j = (p : ℚ) ^ (max 0 ((n i : ℤ) - (n j : ℤ))).toNat * ((d i j).val : ℚ)) (i j : Fin r) :
    U i j = ((p ^ (n i - n j) * (d i j).val : ℕ) : ℚ) := by
  rw [hUd i j]
  have hmax : (max 0 ((n i : ℤ) - (n j : ℤ))).toNat = n i - n j := by omega
  rw [hmax]; push_cast; ring

theorem natCast_pow_mul_val (k : Type*) [CommRing k] [CharP k p] (a b : ℕ) (x : ZMod p) :
    ((p ^ (a - b) * x.val : ℕ) : k) = if a ≤ b then (x.val : k) else 0 := by
  split_ifs with h
  · rw [Nat.sub_eq_zero_of_le h, pow_zero, one_mul]
  · push_cast
    rw [CharP.cast_eq_zero k p, zero_pow (by omega), zero_mul]

section Main

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Φ : FamCtx p r)

include hA Γ in

theorem isContent_hasseExp (j : Fin r) : IsContent Φ.toFamData j (hasseExp Φ.toFamData j : ℤ) := by
  have ht0 : Φ.t j ≠ 0 := Φ.t_basis.1.ne_zero j
  have htRR : Φ.t j ∈ riemannRochSpace (embDivisor (1 * p)) := by
    rw [← Φ.t_basis.2]; exact Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨c, hc0, hcA⟩ := exists_mul_coeff_frickeInvolutionBar_mem_of_mem_riemannRochSpace_cuspInftyBar p
    (embDegree (1 * p)) (Φ.t j) htRR ht0 A hA
  have hex : ∃ n : ℤ, IsContent Φ.toFamData j n := exists_isContent Φ.toFamData j ht0 A hA c hc0 hcA
  rw [hasseExp_cast Φ.toFamData j (hasseContent_nonneg p A hA Γ Φ j)]
  exact isContent_hasseContent Φ.toFamData j hex

theorem infChart_residue_eq_zero_of_coeff (g : ↥(modularFunctionFieldBar (1 * p))) (hg : g ∈ (infChart Γ).integers)
    (q : ℤ → ℚ) (hq : ∀ k, (g : LaurentSeries (AlgebraicClosure ℚ)).coeff k = algebraMap ℚ (AlgebraicClosure ℚ) (q k))
    (hqA : ∀ k, algebraMap ℚ (AlgebraicClosure ℚ) (q k) ∈ A)
    (hres : ∀ k, IsLocalRing.residue ↥A ⟨_, hqA k⟩ = 0) :
    (infChart Γ).residue ⟨g, hg⟩ = 0 := by
  have hf : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.integralCoeffs A.toSubring := by
    intro k; show (g : LaurentSeries (AlgebraicClosure ℚ)).coeff k ∈ A; rw [hq]; exact hqA k
  have hgL : (g : LaurentSeries (AlgebraicClosure ℚ)) ∈
      CharPReduction.modularLocalized (1 * p) A.toSubring (IsLocalRing.residue ↥A) :=
    (mem_infChart_integers_iff_coe_mem_modularLocalized Γ g).mp hg
  obtain ⟨h', hres'⟩ :=
    ModularCurve.PlaceSpecialization.LevelOneProlongationPair.chartFst_residue_eq_modularRedLocHom
      Γ.R Γ.S₁ Γ.Wn Γ.hWn Γ.supply g hgL
  have hLS : (((infChart Γ).residue ⟨g, hg⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) 1)) :
      LaurentSeries (ResidueField ↥A)) = 0 := by
    have e : (((infChart Γ).residue ⟨g, hg⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) 1)) :
        LaurentSeries (ResidueField ↥A))
        = CharPReduction.coeffRed A.toSubring (IsLocalRing.residue ↥A) ⟨_, hf⟩ := by
      rw [← CharPReduction.modularRedLocHom_eq_coeffRed A.toSubring (IsLocalRing.residue ↥A) (1 * p) ⟨_, hgL⟩ hf]
      exact hres'
    rw [e]
    ext k
    rw [CharPReduction.coeffRed_coeff, HahnSeries.coeff_zero]
    have hsub : (⟨(g : LaurentSeries (AlgebraicClosure ℚ)).coeff k, hf k⟩ : ↥A.toSubring) = ⟨_, hqA k⟩ :=
      Subtype.ext (hq k)
    rw [hsub]; exact hres k
  exact_mod_cast hLS

variable (U : Matrix (Fin r) (Fin r) ℚ) (d : Fin r → Fin r → ZMod p)
  (hU : ∀ i j, max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ)) ≤ padicValRat p (U i j)
    ∨ U i j = 0)
  (hUd : ∀ i j, U i j = (p : ℚ) ^ (max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ))).toNat
    * ((d i j).val : ℚ))

noncomputable def cN (i j : Fin r) : ℕ := p ^ (hasseExp Φ.toFamData j - hasseExp Φ.toFamData i) * (d i j).val

noncomputable def uN (i j : Fin r) : ℕ := p ^ (hasseExp Φ.toFamData i - hasseExp Φ.toFamData j) * (d i j).val

include hU in
theorem hrow (i j : Fin r) :
    U i j = 0 ∨ ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ)) ≤ padicValRat p (U i j) := by
  rcases hU i j with h | h
  · exact Or.inr ((le_max_right _ _).trans h)
  · exact Or.inl h

noncomputable def g (i : Fin r) : ↥(modularFunctionFieldBar (1 * p)) :=
  algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
      (algebraMap ℚ (AlgebraicClosure ℚ) (((p : ℚ) ^ hasseExp Φ.toFamData i)⁻¹))
    * (recombine Φ.toFamData U).t i

include hUd in

theorem g_eq_sum (i : Fin r) :
    g Φ U i = ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((cN Φ d i j : ℕ) : AlgebraicClosure ℚ)
      * goodFamilyZero Φ.toFamData j := by
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold g goodFamilyZero
  rw [recombine_t, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have key : (algebraMap ℚ (AlgebraicClosure ℚ) (((p : ℚ) ^ hasseExp Φ.toFamData i)⁻¹)) *
      algebraMap ℚ (AlgebraicClosure ℚ) (U i j)
      = ((cN Φ d i j : ℕ) : AlgebraicClosure ℚ) * ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData j)⁻¹ := by
    have := congrArg (algebraMap ℚ (AlgebraicClosure ℚ)) (coeff_rescaled_eq_natCast (fun l => hasseExp Φ.toFamData l) d U hUd i j)
    rw [map_mul, map_mul, map_inv₀, map_pow, map_pow, map_natCast, map_natCast] at this
    unfold cN
    rw [← this, map_inv₀, map_pow, map_natCast]
    field_simp
  rw [← mul_assoc, ← map_mul, key, map_mul, map_inv₀, map_pow, map_natCast, mul_assoc]

include hUd in

theorem g_mem_and_residue (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers) (i : Fin r) :
    ∃ h : g Φ U i ∈ (zeroChart Γ).integers,
      (zeroChart Γ).residue ⟨g Φ U i, h⟩
        = ∑ j, algebraMap (ResidueField ↥A) _ ((cN Φ d i j : ℕ) : ResidueField ↥A)
            * (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩ := by
  set C := zeroChart Γ
  have hform := g_eq_sum Φ U d hUd i
  have hcmem : ∀ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((cN Φ d i j : ℕ) : AlgebraicClosure ℚ)
      ∈ C.integers := fun j => by rw [map_natCast]; exact natCast_mem _ _
  have hmem : g Φ U i ∈ C.integers := by
    rw [hform]
    exact sum_mem fun j _ => mul_mem (hcmem j) (hint j)
  refine ⟨hmem, ?_⟩
  have e1 : (⟨g Φ U i, hmem⟩ : C.integers) = ∑ j, ⟨_, hcmem j⟩ * ⟨goodFamilyZero Φ.toFamData j, hint j⟩ := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul]
    exact hform
  rw [e1, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  congr 1
  have : (⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((cN Φ d i j : ℕ) : AlgebraicClosure ℚ), hcmem j⟩ : C.integers)
      = ((cN Φ d i j : ℕ) : C.integers) := Subtype.ext (by
        show algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((cN Φ d i j : ℕ) : AlgebraicClosure ℚ)
          = ((cN Φ d i j : C.integers) : ↥(modularFunctionFieldBar (1 * p)))
        rw [map_natCast]; exact (SubringClass.coe_natCast _ _).symm)
  rw [this]
  simp only [map_natCast]

end Main

section Transfer
variable {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A)

theorem mem_zeroChart_integers_iff (f : ↥(modularFunctionFieldBar (1 * p))) :
    f ∈ (zeroChart Γ).integers ↔ frickeInvolutionBar (1 * p) f ∈ (infChart Γ).integers := Iff.rfl

theorem zeroChart_residue_eq (f : ↥(modularFunctionFieldBar (1 * p))) (h : f ∈ (zeroChart Γ).integers) :
    (zeroChart Γ).residue ⟨f, h⟩ = (infChart Γ).residue ⟨frickeInvolutionBar (1 * p) f, (mem_zeroChart_integers_iff Γ f).mp h⟩ :=
  rfl

end Transfer

section Witness

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
  [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Φ : FamCtx p r)
  (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
  (hLI : LinearIndependent (ResidueField ↥A)
    (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
  (U : Matrix (Fin r) (Fin r) ℚ) (d : Fin r → Fin r → ZMod p)
  (hU : ∀ i j, max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ)) ≤ padicValRat p (U i j)
    ∨ U i j = 0)
  (hUd : ∀ i j, U i j = (p : ℚ) ^ (max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ))).toNat
    * ((d i j).val : ℚ))
  (hblock : ∀ c : ℕ, IsUnit (Matrix.det (Matrix.of fun (i j : {a : Fin r // hasseExp Φ.toFamData a = c}) => d i.1 j.1)))

theorem cN_cast (i j : Fin r) :
    ((cN Φ d i j : ℕ) : ResidueField ↥A)
      = if hasseExp Φ.toFamData j ≤ hasseExp Φ.toFamData i then ((d i j).val : ResidueField ↥A) else 0 :=
  natCast_pow_mul_val (ResidueField ↥A) _ _ (d i j)

theorem uN_cast (i j : Fin r) :
    ((uN Φ d i j : ℕ) : ResidueField ↥A)
      = if hasseExp Φ.toFamData i ≤ hasseExp Φ.toFamData j then ((d i j).val : ResidueField ↥A) else 0 :=
  natCast_pow_mul_val (ResidueField ↥A) _ _ (d i j)

include hblock in

theorem exists_digit_ne_zero (i : Fin r) : ∃ j : Fin r, hasseExp Φ.toFamData j = hasseExp Φ.toFamData i ∧ d i j ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hB := hblock (hasseExp Φ.toFamData i)
  set B := Matrix.of fun (a b : {a : Fin r // hasseExp Φ.toFamData a = hasseExp Φ.toFamData i}) => d a.1 b.1 with hBdef
  have hrow : ∀ b, B ⟨i, rfl⟩ b = 0 := fun b => by
    rw [hBdef, Matrix.of_apply]; exact hcon b.1 b.2
  have hdet : B.det = 0 := Matrix.det_eq_zero_of_row_eq_zero ⟨i, rfl⟩ hrow
  rw [hdet] at hB
  exact not_isUnit_zero hB

theorem val_cast_ne_zero {x : ZMod p} (hx : x ≠ 0) : ((x.val : ℕ) : ResidueField ↥A) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff (ResidueField ↥A) p] at h
  have hlt : x.val < p := x.val_lt
  have hpos : 0 < x.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero x).mpr hx)
  exact Nat.not_dvd_of_pos_of_lt hpos hlt h

include hLI hUd hblock in

theorem residue_g_ne_zero (i : Fin r) : (zeroChart Γ).residue ⟨g Φ U i, (g_mem_and_residue A Γ Φ U d hUd hint i).1⟩ ≠ 0 := by
  obtain ⟨hmem, hres⟩ := g_mem_and_residue A Γ Φ U d hUd hint i
  rw [hres]
  intro hzero
  obtain ⟨j₀, hj₀, hd⟩ := exists_digit_ne_zero Φ d hblock i
  have hsmul : ∑ j, ((cN Φ d i j : ℕ) : ResidueField ↥A) • (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩ = 0 := by
    simpa only [Algebra.smul_def] using hzero
  have hall := (Fintype.linearIndependent_iff.mp hLI) _ hsmul j₀
  rw [cN_cast, if_pos hj₀.le] at hall
  exact val_cast_ne_zero A hd hall

include hA hLI hU hUd hblock in

theorem exists_coeff_padicValRat_eq (i : Fin r) :
    ∃ m : ℤ, (zeroSeries (recombine Φ.toFamData U) i).coeff m ≠ 0 ∧
      padicValRat p ((zeroSeries (recombine Φ.toFamData U) i).coeff m) = hasseExp Φ.toFamData i := by
  have hp : p.Prime := Fact.out
  have hD : ∀ j (m : ℤ), (zeroSeries Φ.toFamData j).coeff m ≠ 0 →
      ((hasseExp Φ.toFamData j : ℕ) : ℤ) ≤ padicValRat p ((zeroSeries Φ.toFamData j).coeff m) :=
    fun j m hm => (isContent_hasseExp A hA Γ Φ j).1 m hm
  have hge : ∀ m, (zeroSeries (recombine Φ.toFamData U) i).coeff m ≠ 0 →
      ((hasseExp Φ.toFamData i : ℕ) : ℤ) ≤ padicValRat p ((zeroSeries (recombine Φ.toFamData U) i).coeff m) :=
    fun m hm => le_padicValRat_zeroSeries_recombine Φ.toFamData U (fun l => hasseExp Φ.toFamData l) i
      (hrow Φ U hU i) hD m hm
  by_contra hcon
  push_neg at hcon

  have hgt : ∀ m, (zeroSeries (recombine Φ.toFamData U) i).coeff m ≠ 0 →
      ((hasseExp Φ.toFamData i : ℕ) : ℤ) + 1 ≤ padicValRat p ((zeroSeries (recombine Φ.toFamData U) i).coeff m) := by
    intro m hm
    have h1 := hge m hm
    have h2 := hcon m hm
    omega

  let q : ℤ → ℚ := fun k => ((p : ℚ) ^ hasseExp Φ.toFamData i)⁻¹ * (zeroSeries (recombine Φ.toFamData U) i).coeff k
  have hqk : ∀ k, q k = ((p : ℚ) ^ hasseExp Φ.toFamData i)⁻¹ * (zeroSeries (recombine Φ.toFamData U) i).coeff k :=
    fun k => rfl
  have hcoeff : ∀ k, ((frickeInvolutionBar (1 * p) (g Φ U i) : ↥(modularFunctionFieldBar (1 * p))) :
      LaurentSeries (AlgebraicClosure ℚ)).coeff k = algebraMap ℚ (AlgebraicClosure ℚ) (q k) := by
    intro k
    unfold g
    rw [coe_frickeInvolutionBar_algebraMap_mul, coeffEmb_coeff]
    rfl
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hvq : ∀ k, q k ≠ 0 → 1 ≤ padicValRat p (q k) := by
    intro k hk
    have hc : (zeroSeries (recombine Φ.toFamData U) i).coeff k ≠ 0 := by
      intro h; apply hk; rw [hqk, h, mul_zero]
    rw [hqk, padicValRat.mul (inv_ne_zero (pow_ne_zero _ hp0)) hc, padicValRat.inv, padicValRat.pow _,
      padicValRat.self hp.one_lt]
    have := hgt k hc
    push_cast at this ⊢
    linarith
  have hqA : ∀ k, algebraMap ℚ (AlgebraicClosure ℚ) (q k) ∈ A := fun k =>
    algebraMap_rat_mem_of_padicValRat_nonneg A hA (q k)
      (by by_cases h : q k = 0; exact Or.inl h; exact Or.inr (zero_le_one.trans (hvq k h)))
  have hres0 : ∀ k, IsLocalRing.residue ↥A ⟨_, hqA k⟩ = 0 := by
    intro k
    by_cases h : q k = 0
    · have h0 : (⟨algebraMap ℚ (AlgebraicClosure ℚ) (q k), hqA k⟩ : ↥A) = 0 :=
        Subtype.ext (by show algebraMap ℚ (AlgebraicClosure ℚ) (q k) = ((0 : ↥A) : AlgebraicClosure ℚ); rw [h, map_zero]; rfl)
      rw [h0, map_zero]
    · exact residue_algebraMap_rat_eq_zero_of_padicValRat_pos A hA (q k) h (hvq k h) (hqA k)

  have hmem := (g_mem_and_residue A Γ Φ U d hUd hint i).1
  have hmemI : frickeInvolutionBar (1 * p) (g Φ U i) ∈ (infChart Γ).integers :=
    (mem_zeroChart_integers_iff Γ _).mp hmem
  have hz : (infChart Γ).residue ⟨_, hmemI⟩ = 0 :=
    infChart_residue_eq_zero_of_coeff A Γ _ hmemI q hcoeff hqA hres0
  have hz' : (zeroChart Γ).residue ⟨g Φ U i, hmem⟩ = 0 := by
    rw [zeroChart_residue_eq Γ]; exact hz
  exact residue_g_ne_zero A Γ Φ hint hLI U d hUd hblock i hz'

include hA hLI hU hUd hblock in

theorem hasseExp_recombine (i : Fin r) : hasseExp (recombine Φ.toFamData U) i = hasseExp Φ.toFamData i :=
  hasseExp_recombine_eq Φ.toFamData U (fun l => hasseExp Φ.toFamData l) i (hrow Φ U hU i)
    (fun j m hm => (isContent_hasseExp A hA Γ Φ j).1 m hm)
    (exists_coeff_padicValRat_eq A hA Γ Φ hint hLI U d hU hUd hblock i)

include hA hLI hU hUd hblock in

theorem goodFamilyZero_recombine_eq_g (i : Fin r) : goodFamilyZero (recombine Φ.toFamData U) i = g Φ U i := by
  unfold goodFamilyZero g
  rw [hasseExp_recombine A hA Γ Φ hint hLI U d hU hUd hblock i]
  simp only [map_pow, map_natCast, map_inv₀]

end Witness

section LI

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem linearIndependent_matrix_combination {ρ : ι → V} (hρ : LinearIndependent k ρ)
    (M : Matrix ι ι k) (hM : IsUnit M.det) :
    LinearIndependent k (fun i => ∑ j, M i j • ρ j) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have hsum : ∑ j, (∑ i, a i * M i j) • ρ j = 0 := by
    rw [← ha]
    simp_rw [Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
  have hzero : ∀ j, ∑ i, a i * M i j = 0 := (Fintype.linearIndependent_iff.mp hρ) _ hsum
  have hvec : Matrix.vecMul a M = 0 := funext fun j => by rw [Matrix.vecMul, dotProduct]; exact hzero j
  have := Matrix.eq_zero_of_vecMul_eq_zero hM.ne_zero hvec
  exact fun i => congrFun this i

end LI

section LIMain

variable (A : ValuationSubring (AlgebraicClosure ℚ)) [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Φ : FamCtx p r)
  (d : Fin r → Fin r → ZMod p)
  (hblock : ∀ c : ℕ, IsUnit (Matrix.det (Matrix.of fun (i j : {a : Fin r // hasseExp Φ.toFamData a = c}) => d i.1 j.1)))

noncomputable def Mred : Matrix (Fin r) (Fin r) (ResidueField ↥A) :=
  Matrix.of fun i j => ((cN Φ d i j : ℕ) : ResidueField ↥A)

theorem Mred_transpose_blockTriangular :
    (Mred A Φ d).transpose.BlockTriangular (fun l => hasseExp Φ.toFamData l) := by
  intro i j hij
  rw [Matrix.transpose_apply, Mred, Matrix.of_apply, cN_cast A Φ d j i, if_neg (not_le.mpr hij)]

include hblock in
theorem isUnit_det_Mred : IsUnit (Mred A Φ d).det := by
  classical
  rw [isUnit_iff_ne_zero, ← Matrix.det_transpose, (Mred_transpose_blockTriangular A Φ d).det,
    Finset.prod_ne_zero_iff]
  intro c _

  set φ : ZMod p →+* ResidueField ↥A := ZMod.castHom (dvd_refl p) (ResidueField ↥A) with hφ
  have hB : ((Mred A Φ d).transpose.toSquareBlock (fun l => hasseExp Φ.toFamData l) c)
      = (φ.mapMatrix (Matrix.of fun (i j : {a : Fin r // hasseExp Φ.toFamData a = c}) => d i.1 j.1)).transpose := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Matrix.toSquareBlock_def, Matrix.transpose_apply, Mred, Matrix.of_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply]
    rw [cN_cast A Φ d j i, hi, hj, if_pos le_rfl, hφ, ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [hB, Matrix.det_transpose, ← RingHom.map_det]
  exact (map_ne_zero φ).mpr (hblock c).ne_zero

end LIMain

end UMK

open UMK in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (ResidueField ↥A)] [CharP (ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r)
    (hintI : ∀ l, Φ.t l ∈ (infChart Γ).integers)
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (U : Matrix (Fin r) (Fin r) ℚ) (d : Fin r → Fin r → ZMod p)
    (hUunit : IsUnit U)
    (hU : ∀ i j, max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ)) ≤ padicValRat p (U i j)
      ∨ U i j = 0)
    (hUinv : ∀ i j, max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ)) ≤ padicValRat p (U⁻¹ i j)
      ∨ U⁻¹ i j = 0)
    (hU0 : ∀ i j : Fin r, (i : ℕ) = 0 → U i j = if (j : ℕ) = 0 then 1 else 0)
    (hUd : ∀ i j, U i j = (p : ℚ) ^ (max 0 ((hasseExp Φ.toFamData i : ℤ) - (hasseExp Φ.toFamData j : ℤ))).toNat
      * ((d i j).val : ℚ))
    (hblock : ∀ c : ℕ, IsUnit (Matrix.det (Matrix.of fun (i j : {a : Fin r // hasseExp Φ.toFamData a = c}) => d i.1 j.1))) :
    ∃ (D' : FamData p r) (hint' : ∀ l, goodFamilyZero D' l ∈ (zeroChart Γ).integers)
      (hintI' : ∀ l, D'.t l ∈ (infChart Γ).integers),
      (∀ i, D'.tRat i = ∑ j, U i j • Φ.tRat j) ∧
      (∀ i, D'.t i = ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
          (algebraMap ℚ (AlgebraicClosure ℚ) (U i j)) * Φ.t j) ∧
      (∀ l, hasseExp D' l = hasseExp Φ.toFamData l) ∧
      (∀ l, goodFamilyZero D' l = (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
          ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹
        * ∑ j, algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))
          (algebraMap ℚ (AlgebraicClosure ℚ) (U l j)) * Φ.t j) ∧
      LinearIndependent (ResidueField ↥A) (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero D' l, hint' l⟩) ∧
      (∀ i, (infChart Γ).residue ⟨D'.t i, hintI' i⟩
          = ∑ j, algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)
              (if hasseExp Φ.toFamData i ≤ hasseExp Φ.toFamData j then ((d i j).val : ResidueField ↥A) else 0)
              * (infChart Γ).residue ⟨Φ.t j, hintI j⟩) ∧
      (∀ i, (zeroChart Γ).residue ⟨goodFamilyZero D' i, hint' i⟩
          = ∑ j, algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1)
              (if hasseExp Φ.toFamData j ≤ hasseExp Φ.toFamData i then ((d i j).val : ResidueField ↥A) else 0)
              * (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩) := by
  classical

  let D' : FamData p r := recombine Φ.toFamData U
  have hexp : ∀ l, hasseExp D' l = hasseExp Φ.toFamData l :=
    fun l => hasseExp_recombine A hA Γ Φ hint hLI U d hU hUd hblock l
  have hgf : ∀ i, goodFamilyZero D' i = g Φ U i :=
    fun i => goodFamilyZero_recombine_eq_g A hA Γ Φ hint hLI U d hU hUd hblock i
  have hg := fun i => g_mem_and_residue A Γ Φ U d hUd hint i
  have hint' : ∀ l, goodFamilyZero D' l ∈ (zeroChart Γ).integers := fun l => by
    rw [hgf]; exact (hg l).1

  have hcI : ∀ i j, ((uN Φ d i j : ↥A) : AlgebraicClosure ℚ) = algebraMap ℚ (AlgebraicClosure ℚ) (U i j) := by
    intro i j
    rw [coeff_eq_natCast (fun l => hasseExp Φ.toFamData l) d U hUd i j, map_natCast]
    exact SubringClass.coe_natCast _ _
  have hI := fun i => infChart_residue_recombine A Γ Φ.toFamData U i hintI (fun j => (uN Φ d i j : ↥A)) (hcI i)
  have hintI' : ∀ l, D'.t l ∈ (infChart Γ).integers := fun l => (hI l).1

  have hres0 : ∀ i, (zeroChart Γ).residue ⟨goodFamilyZero D' i, hint' i⟩
      = ∑ j, algebraMap (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) 1) ((cN Φ d i j : ℕ) : ResidueField ↥A)
          * (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩ := by
    intro i
    have e : (⟨goodFamilyZero D' i, hint' i⟩ : (zeroChart Γ).integers) = ⟨g Φ U i, (hg i).1⟩ := Subtype.ext (hgf i)
    rw [e]
    exact (hg i).2
  refine ⟨D', hint', hintI', fun i => rfl, fun i => recombine_t Φ.toFamData U i, hexp, ?_, ?_, ?_, ?_⟩
  ·
    intro l
    show goodFamilyZero D' l = _
    unfold goodFamilyZero
    rw [hexp l, recombine_t]
  ·
    have hfun : (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero D' l, hint' l⟩)
        = fun l => ∑ j, (Mred A Φ d) l j • (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData j, hint j⟩ := by
      funext l
      rw [hres0 l]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def]; rfl
    rw [hfun]
    exact linearIndependent_matrix_combination hLI (Mred A Φ d) (isUnit_det_Mred A Φ d hblock)
  ·
    intro i
    rw [(hI i).2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_natCast, uN_cast A Φ d i j]
  ·
    intro i
    rw [hres0 i]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cN_cast A Φ d i j]

end S_ModularCurve_MultCovering_exists_famData_of_bifiltered_digits
end P2MW
export P2MW.S_ModularCurve_MultCovering_exists_famData_of_bifiltered_digits (solution)
