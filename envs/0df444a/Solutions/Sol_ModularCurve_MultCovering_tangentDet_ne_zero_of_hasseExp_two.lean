-- Prove2me | solution 1 for ModularCurve.MultCovering.tangentDet_ne_zero_of_hasseExp_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/c1445994-b068-501a-9177-81516453c5b1

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_ModularCurve_MultCoveringFamily
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_ValuationSubring_exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime
import Theorems.Thm_AlgebraicCurve_Annulus_abv_modulus_zpow_ord_residue_le_abv_of_isAttached_both_ends
import Theorems.Thm_AlgebraicCurve_Annulus_residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt
import Theorems.Thm_ModularCurve_MultCovering_abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom
import Theorems.Thm_ModularCurve_MultCovering_AnnCtx_exists_mem_dom_abv_evalAt_param_ne
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_MultCovering_infChart_goodFamily_residue_ne_zero
import Theorems.Thm_ModularCurve_MultCovering_zeroChart_residue_goodFamilyZero_ne_zero
import Theorems.Thm_ModularCurve_MultCovering_hasseExp_zero
import Theorems.Thm_ModularCurve_ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_tangentDet_ne_zero_of_hasseExp_two
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.GaussReduction.isLocalHom_constToGauss WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.GaussReduction.constToGauss_coe AlgebraicCurve.ComponentChart.ofConstantReductionNodes_dom"
p2m_attr_erase "simp" "AlgebraicCurve.ComponentChart.ofConstantReductionNodes_placeMap AlgebraicCurve.ComponentChart.ofConstantReductionNodes_nodes AlgebraicCurve.ComponentChart.ofConstantReductionNodes_residue AlgebraicCurve.ComponentChart.ofConstantReductionNodes_integers compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.ProjectiveLine.map_mk ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_MultCovering_tangentDet_ne_zero_of_hasseExp_two.AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_MultCovering_tangentDet_ne_zero_of_hasseExp_two.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_tangentDet_ne_zero_of_hasseExp_two.ModularCurve.MultCovering"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.ord Place.ord_zero Place.ord_inv HasPrincipalDivisors Place.mem_of_ord_nonneg Annulus.abv_modulus_zpow_ord_residue_le_abv_of_isAttached_both_ends Annulus.residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt Place.isRational_of_isAlgClosed Place.ord_finset_prod'"
p2m_open "AlgebraicCurve"

private theorem abv_sub_le_max {L : Type*} [Field L] {A : ValuationSubring L}
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1) (a b : L) :
    μ (a - b) ≤ max (μ a) (μ b) := by
  rcases le_total (μ b) (μ a) with hab | hab
  ·
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [map_zero] at hab
      have hb : b = 0 := μ.eq_zero.1 (le_antisymm hab (μ.nonneg b))
      simp [hb]
    have hq : b * a⁻¹ ∈ A := (hμA _).2 (by
      rw [map_mul, map_inv₀]
      exact (mul_inv_le_iff₀ (μ.pos ha0)).2 (by simpa using hab))
    have h1 : 1 - b * a⁻¹ ∈ A := sub_mem (one_mem _) hq
    have h2 : μ (1 - b * a⁻¹) ≤ 1 := (hμA _).1 h1
    have : a - b = a * (1 - b * a⁻¹) := by field_simp
    rw [this, map_mul]
    calc μ a * μ (1 - b * a⁻¹) ≤ μ a * 1 := mul_le_mul_of_nonneg_left h2 (μ.nonneg a)
      _ = μ a := mul_one _
      _ ≤ max (μ a) (μ b) := le_max_left _ _
  · rcases eq_or_ne b 0 with rfl | hb0
    · rw [map_zero] at hab
      have ha : a = 0 := μ.eq_zero.1 (le_antisymm hab (μ.nonneg a))
      simp [ha]
    have hq : a * b⁻¹ ∈ A := (hμA _).2 (by
      rw [map_mul, map_inv₀]
      exact (mul_inv_le_iff₀ (μ.pos hb0)).2 (by simpa using hab))
    have h1 : a * b⁻¹ - 1 ∈ A := sub_mem hq (one_mem _)
    have h2 : μ (a * b⁻¹ - 1) ≤ 1 := (hμA _).1 h1
    have : a - b = b * (a * b⁻¹ - 1) := by field_simp
    rw [this, map_mul]
    calc μ b * μ (a * b⁻¹ - 1) ≤ μ b * 1 := mul_le_mul_of_nonneg_left h2 (μ.nonneg b)
      _ = μ b := mul_one _
      _ ≤ max (μ a) (μ b) := le_max_right _ _

private theorem abv_eq_one_of_isUnit_vs {L : Type*} [Field L] {A : ValuationSubring L}
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1) {a : L} (ha : a ∈ A)
    (hu : IsUnit (⟨a, ha⟩ : A)) : μ a = 1 := by
  obtain ⟨b, hb⟩ := hu.exists_right_inv
  have hb' : a * (b : L) = 1 := by
    have := congrArg (fun t : A => (t : L)) hb
    simpa using this
  have h1 : μ a * μ (b : L) = 1 := by rw [← map_mul, hb', map_one]
  have ha1 : μ a ≤ 1 := (hμA a).1 ha
  have hb1 : μ (b : L) ≤ 1 := (hμA (b : L)).1 b.2
  have ha0 : 0 ≤ μ a := μ.nonneg a
  exact le_antisymm ha1 (by nlinarith)

private theorem abv_lt_one_of_mem_maximalIdeal_vs {L : Type*} [Field L]
    {A : ValuationSubring L} (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1) {a : L}
    (ha : a ∈ A) (hm : (⟨a, ha⟩ : A) ∈ IsLocalRing.maximalIdeal A) : μ a < 1 := by
  have ha1 : μ a ≤ 1 := (hμA a).1 ha
  refine lt_of_le_of_ne ha1 fun h1 => ?_
  apply (IsLocalRing.mem_maximalIdeal _).1 hm
  have ha0 : a ≠ 0 := fun h0 => by simp [h0] at h1
  have hinv : a⁻¹ ∈ A := (hμA _).2 (by rw [map_inv₀, h1, inv_one])
  exact isUnit_iff_exists_inv.2 ⟨⟨a⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

private theorem residue_eq_zero_of_mem_maximalIdeal' {L : Type*} [Field L] {A : ValuationSubring L}
    {a : L} (ha : a ∈ A) (hm : (⟨a, ha⟩ : A) ∈ IsLocalRing.maximalIdeal A) :
    IsLocalRing.residue A ⟨a, ha⟩ = 0 :=
  (IsLocalRing.residue_eq_zero_iff _).2 hm

private theorem abv_evalAt_eq_zpow_of_isAttached
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An : Annulus A F) (C : ComponentChart A F Fbar) (x : Place (IsLocalRing.ResidueField A) Fbar)
    (hatt : An.IsAttached C x) (f : F) (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (hzf : ∀ Q ∈ An.dom, Q.ord f = 0) :
    ∀ Q ∈ An.dom, 0 < μ (Q.evalAt An.param) ∧ μ (Q.evalAt An.param) < 1 ∧
      μ (Q.evalAt f) = μ (Q.evalAt An.param) ^ (x.ord (C.residue ⟨f, hf⟩)) := by
  intro Q hQ
  obtain ⟨-, hzC, -, hlaw⟩ := hatt
  obtain ⟨hw, hunit⟩ := hlaw f hf hres hzf Q hQ
  obtain ⟨-, -, ⟨hzA, hzmax⟩, hz0, -⟩ := An.mem_dom Q hQ
  have hμz1 : μ (Q.evalAt An.param) < 1 := abv_lt_one_of_mem_maximalIdeal_vs μ hμA hzA hzmax
  have hμz0 : 0 < μ (Q.evalAt An.param) := μ.pos hz0
  have hunit1 := abv_eq_one_of_isUnit_vs μ hμA hw hunit
  rw [map_mul, map_zpow₀, zpow_neg] at hunit1
  exact ⟨hμz0, hμz1, (mul_inv_eq_one₀ (zpow_ne_zero _ hμz0.ne')).1 hunit1⟩

namespace Place p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField deg ord ord_zero ord_mul ord_inv ord_coe_unit ord_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring adicValuation_le_one_of_mem adicValuation_le_one_iff IsRational algebraMap_residueField_injective residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt mem_of_ord_nonneg isRational_of_isAlgClosed ord_finset_prod'" end Place
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.evalAt_mul' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (mul_mem hf hg), map_mul, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_mul'"
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.evalAt_sub' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (sub_mem hf hg), map_sub, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_sub]
  rfl

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.evalAt_algebraMap' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have h : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring a := Subtype.ext (v.coe_algebraMap a).symm
  rw [h, ← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
    v.residueInv_algebraMap]

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.evalAt_prod' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {ι : Type*} (S : Finset ι) (f : ι → F)
    (hf : ∀ i ∈ S, f i ∈ v.toValuationSubring) :
    (∏ i ∈ S, f i) ∈ v.toValuationSubring ∧ v.evalAt (∏ i ∈ S, f i) = ∏ i ∈ S, v.evalAt (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨by simp, by simp⟩
  | @insert i S hi ih =>
    obtain ⟨hmem, heq⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hfi : f i ∈ v.toValuationSubring := hf i (Finset.mem_insert_self _ _)
    refine ⟨?_, ?_⟩
    · rw [Finset.prod_insert hi]; exact mul_mem hfi hmem
    · rw [Finset.prod_insert hi, Finset.prod_insert hi, v.evalAt_mul' hv hfi hmem, heq]

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.evalAt_pow' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (n : ℕ) :
    v.evalAt (f ^ n) = v.evalAt f ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, v.evalAt_mul' hv (pow_mem hf n) hf, ih]

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.ord_neg' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (f : F) : v.ord (-f) = v.ord f := by
  unfold Place.ord
  rw [Valuation.map_neg]

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.ord_pow' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  rw [← zpow_natCast, v.ord_zpow]

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.ord_prod' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {ι : Type*} (S : Finset ι) (f : ι → F) (hf : ∀ i ∈ S, f i ≠ 0) :
    v.ord (∏ i ∈ S, f i) = ∑ i ∈ S, v.ord (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      v.ord_mul (hf i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.2 fun j hj => hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.ord_algebraMap' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have hmem := v.algebraMap_mem' c
  have hmem' : (algebraMap K F c)⁻¹ ∈ v.toValuationSubring := by
    rw [← map_inv₀]; exact v.algebraMap_mem' _
  have h1 : 0 ≤ v.ord (algebraMap K F c) := by
    rcases (v.adicValuation_le_one_iff).1 (v.adicValuation_le_one_of_mem hmem) with h | h
    · simp [h]
    · exact h
  have h2 : 0 ≤ v.ord (algebraMap K F c)⁻¹ := by
    rcases (v.adicValuation_le_one_iff).1 (v.adicValuation_le_one_of_mem hmem') with h | h
    · simp [h]
    · exact h
  rw [v.ord_inv] at h2
  omega

namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases (v.adicValuation_le_one_iff).1 (v.adicValuation_le_one_of_mem hf) with h | h
  · simp [h]
  · exact h

end Place
p2m_export "AlgebraicCurve" "Place.ord_nonneg_of_mem'"
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.isUnit_of_ord_eq_zero' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) (h : v.ord f = 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hϖ
  rw [h, zpow_zero, mul_one] at hu
  have : (⟨f, hf⟩ : v.toValuationSubring) = u := Subtype.ext hu
  rw [this]
  exact Units.isUnit u

p2m_open_scoped "AlgebraicCurve.Place" in

private theorem Place.ord_eq_zero_of_evalAt_ne_zero' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) :
    v.ord f = 0 := by
  by_contra hne
  have hpos : 0 < v.ord f := lt_of_le_of_ne (v.ord_nonneg_of_mem' hf) (Ne.symm hne)
  apply h
  have hnu : ¬ IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
    intro hu
    obtain ⟨u, hu⟩ := hu
    have : v.ord f = 0 := by
      have := v.ord_coe_unit u
      rwa [hu] at this
    omega
  have hmax : (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    (IsLocalRing.mem_maximalIdeal _).2 hnu
  rw [v.evalAt_of_mem hf, (IsLocalRing.residue_eq_zero_iff _).2 hmax, ← map_zero (algebraMap K _),
    v.residueInv_algebraMap]

private theorem inv_mem_of_isUnit' {F : Type*} [Field F] {O : ValuationSubring F} {x : F}
    (hx : x ∈ O) (hu : IsUnit (⟨x, hx⟩ : O)) : x⁻¹ ∈ O := by
  obtain ⟨u, hu⟩ := hu
  have hx0 : x ≠ 0 := by
    rintro rfl
    have : (u : O) = 0 := by rw [hu]; rfl
    exact u.ne_zero this
  have hval : ((u⁻¹ : Oˣ) : O).1 = x⁻¹ := by
    have h1 := congrArg (fun t : O => (t : F)) u.mul_inv
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
    rw [hu] at h1
    exact (eq_inv_of_mul_eq_one_right h1)
  exact hval ▸ ((u⁻¹ : Oˣ) : O).2

namespace ComponentChart p2m_export "AlgebraicCurve.ComponentChart" "integers residue nodes ker_residue dom" end ComponentChart
p2m_open_scoped "AlgebraicCurve.ComponentChart" in

private theorem ComponentChart.isUnit_of_residue_ne_zero'
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0) :
    IsUnit (⟨f, hf⟩ : C.integers) := by
  by_contra hnu
  apply hres
  have : (⟨f, hf⟩ : C.integers) ∈ RingHom.ker C.residue := by
    rw [C.ker_residue]
    exact (IsLocalRing.mem_maximalIdeal _).2 hnu
  exact this

p2m_open_scoped "AlgebraicCurve.ComponentChart" in

private theorem ComponentChart.residue_inv'
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (hfi : f⁻¹ ∈ C.integers) : C.residue ⟨f⁻¹, hfi⟩ = (C.residue ⟨f, hf⟩)⁻¹ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    apply hres
    have : (⟨(0 : F), hf⟩ : C.integers) = 0 := rfl
    rw [this, map_zero]
  have h1 : C.residue ⟨f⁻¹, hfi⟩ * C.residue ⟨f, hf⟩ = 1 := by
    rw [← map_mul]
    have : (⟨f⁻¹, hfi⟩ : C.integers) * ⟨f, hf⟩ = 1 := Subtype.ext (inv_mul_cancel₀ hf0)
    rw [this, map_one]
  exact eq_inv_of_mul_eq_one_left h1

end AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar modularFunctionFieldC ratFuncEquivCharLOneC charLGeomPlaceOfPoint jWidth jWidth_of_ne hasPrincipalDivisors_modularFunctionFieldBar_unconditional ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "jBar mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart src tgt ssValue ssValue_injective nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero ssPolyBar FamCtx goodFamily abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom infChart_goodFamily_residue_ne_zero zeroChart_residue_goodFamilyZero_ne_zero hasseExp_zero"
p2m_open "ModularCurve.MultCovering ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_MultCovering_tangentDet_ne_zero_of_hasseExp_two.AlgebraicCurve IsLocalRing"

section GenericHelpers

theorem evalAt_mul_D {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (mul_mem hf hg), map_mul, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

theorem evalAt_algebraMap_D {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have h : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring a := Subtype.ext (v.coe_algebraMap a).symm
  rw [h, ← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
    v.residueInv_algebraMap]

theorem minor_mulVec_D {K : Type*} [Field K] {r : ℕ} (M : Matrix (Fin r) (Fin r) K)
    (x y : Fin r → K) (i j : Fin r) :
    M.mulVec x i * M.mulVec y j - M.mulVec x j * M.mulVec y i
      = ∑ p : Fin r × Fin r, M i p.1 * M j p.2 * (x p.1 * y p.2 - x p.2 * y p.1) := by
  have hswap : ∑ p : Fin r × Fin r, M j p.1 * x p.1 * (M i p.2 * y p.2)
      = ∑ p : Fin r × Fin r, M j p.2 * x p.2 * (M i p.1 * y p.1) := by
    rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_product, Finset.sum_comm]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
  rw [hswap, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

end GenericHelpers

section FamilyFacts
variable {p : ℕ} [Fact p.Prime] {r : ℕ} (Φ : FamCtx p r)

theorem goodFamily_ne_zero' (i : Fin r) : goodFamily Φ i ≠ 0 := Φ.t_basis.1.ne_zero i

theorem goodFamilyZero_eq_inv_mul' (l : Fin r) :
    goodFamilyZero Φ.toFamData l
      = (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))
          ((p : AlgebraicClosure ℚ) ^ hasseExp Φ.toFamData l))⁻¹ * goodFamily Φ l := rfl

end FamilyFacts

section CtxFacts
variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
  (Γ : ChartCtx p A) (Δ : AnnCtx Γ)

theorem modulus_dvd' (e : Fin (mAnnuli p)) : ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
    (p : AlgebraicClosure ℚ) ^ modulusExp = ((Δ.annIn e).modulus : AlgebraicClosure ℚ) * a := by
  have hw : jWidth (ssValue Γ e) ≤ 3 := by
    unfold jWidth; split_ifs <;> norm_num
  refine ⟨(p : AlgebraicClosure ℚ) ^ (3 - jWidth (ssValue Γ e)), pow_mem (natCast_mem A p) _, ?_⟩
  have hm : ((Δ.annIn e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) ^ jWidth (ssValue Γ e) := by
    show (((Δ.An e).modulus : ↥A) : AlgebraicClosure ℚ) = _
    rw [Δ.modulus_eq e]; push_cast; rfl
  rw [hm, ← pow_add, show modulusExp = 3 from rfl, Nat.add_sub_cancel' hw]

end CtxFacts

theorem annOut_wide' (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ) (e : Fin (mAnnuli p)) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∃ Q₁ ∈ (Δ.annOut e).dom, ∃ Q₂ ∈ (Δ.annOut e).dom,
        μ (Q₁.evalAt (Δ.annOut e).param) ≠ μ (Q₂.evalAt (Δ.annOut e).param) := by
  intro μ hμA
  obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded e
  obtain ⟨Q₁, hQ₁, Q₂, hQ₂, hne⟩ := Δ.exists_mem_dom_abv_evalAt_param_ne e μ hμA
  refine ⟨Q₁, hdom ▸ hQ₁, Q₂, hdom ▸ hQ₂, ?_⟩
  have key : ∀ Q ∈ (Δ.annIn e).dom,
      μ (Q.evalAt (Δ.annOut e).param) * μ (Q.evalAt (Δ.annIn e).param)
        = μ ((Δ.annIn e).modulus : AlgebraicClosure ℚ) := by
    intro Q hQ
    obtain ⟨hrat, hzin, -, hz0, -⟩ := (Δ.annIn e).mem_dom Q hQ
    obtain ⟨-, hzout, -⟩ := (Δ.annOut e).mem_dom Q (hdom ▸ hQ)
    rw [← map_mul, ← evalAt_mul_D Q hrat hzout hzin, htwo, evalAt_algebraMap_D]
  intro heq
  apply hne
  have h1 := key Q₁ hQ₁
  have h2 := key Q₂ hQ₂
  rw [heq] at h1
  have h12 := h1.trans h2.symm
  have hne0 : μ (Q₂.evalAt (Δ.annOut e).param) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    exact (μ.pos hmod0).ne' h2.symm
  exact mul_left_cancel₀ hne0 h12

end ModularCurve.MultCovering

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar modularFunctionFieldC ratFuncEquivCharLOneC charLGeomPlaceOfPoint jWidth jWidth_of_ne hasPrincipalDivisors_modularFunctionFieldBar_unconditional ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "jBar mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart src tgt ssValue ssValue_injective nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero ssPolyBar FamCtx goodFamily abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom infChart_goodFamily_residue_ne_zero zeroChart_residue_goodFamilyZero_ne_zero hasseExp_zero"
p2m_open "ModularCurve.MultCovering ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_MultCovering_tangentDet_ne_zero_of_hasseExp_two.AlgebraicCurve IsLocalRing"

section ResidueLinePort

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A)

theorem ord_charLGeomPlaceOfPoint_jBar_sub' (k : Type) [Field k] [DecidableEq k] (a c : k) :
    (charLGeomPlaceOfPoint k a).ord (jBar k - algebraMap k ↥(modularFunctionFieldC k 1) c) = if c = a then 1 else 0 :=
  ModularCurve.ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap k a c

theorem jBar_sub_algebraMap_ne_zero' (k : Type) [Field k] [DecidableEq k] (c : k) :
    jBar k - algebraMap k ↥(modularFunctionFieldC k 1) c ≠ 0 := by
  intro h
  have := ord_charLGeomPlaceOfPoint_jBar_sub' k c c
  rw [h, Place.ord_zero, if_pos rfl] at this
  exact zero_ne_one this

theorem jBar_ne_zero' (k : Type) [Field k] [DecidableEq k] : jBar k ≠ 0 := by
  simpa using jBar_sub_algebraMap_ne_zero' k 0

private theorem _root_.AlgebraicCurve.Place.ord_finset_prod' {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {ι : Type*} (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, f i ≠ 0) :
    v.ord (∏ i ∈ s, f i) = ∑ i ∈ s, v.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      v.ord_mul (hf a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

p2m_alias "P2MW.S_ModularCurve_MultCovering_tangentDet_ne_zero_of_hasseExp_two.AlgebraicCurve.Place.ord_finset_prod'" "AlgebraicCurve.Place.ord_finset_prod'"
theorem ssPolyBar_ne_zero' : ssPolyBar Γ ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun e _ => jBar_sub_algebraMap_ne_zero' _ _

theorem ord_nodeTgt_ssPolyBar' (e : Fin (mAnnuli p)) : (nodeTgt Γ e).ord (ssPolyBar Γ) = 1 := by
  show (charLGeomPlaceOfPoint (IsLocalRing.ResidueField ↥A) (ssValue Γ e)).ord _ = 1
  rw [ssPolyBar, Place.ord_finset_prod' _ _ _ (fun e' _ => jBar_sub_algebraMap_ne_zero' _ _)]
  simp_rw [ord_charLGeomPlaceOfPoint_jBar_sub', (ssValue_injective Γ).eq_iff]
  simp [Finset.sum_ite_eq']

theorem ord_nodeTgt_jBar' (e : Fin (mAnnuli p)) :
    (nodeTgt Γ e).ord (jBar (IsLocalRing.ResidueField ↥A)) = if (0 : IsLocalRing.ResidueField ↥A) = ssValue Γ e then 1 else 0 := by
  have h := ord_charLGeomPlaceOfPoint_jBar_sub' (IsLocalRing.ResidueField ↥A) (ssValue Γ e) 0
  rw [map_zero, sub_zero] at h
  exact h

theorem nodeTgt_isRational' (e : Fin (mAnnuli p)) : (nodeTgt Γ e).IsRational := by
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  let eqv := ratFuncEquivCharLOneC (IsLocalRing.ResidueField ↥A)
  letI : Algebra (RatFunc (IsLocalRing.ResidueField ↥A)) (Fbar A (tgt p e)) := eqv.toAlgHom.toRingHom.toAlgebra
  haveI : IsScalarTower (IsLocalRing.ResidueField ↥A) (RatFunc (IsLocalRing.ResidueField ↥A)) (Fbar A (tgt p e)) :=
    IsScalarTower.of_algebraMap_eq fun c => (eqv.commutes c).symm
  haveI : FiniteDimensional (RatFunc (IsLocalRing.ResidueField ↥A)) (Fbar A (tgt p e)) := by
    let L : RatFunc (IsLocalRing.ResidueField ↥A) ≃ₗ[RatFunc (IsLocalRing.ResidueField ↥A)] Fbar A (tgt p e) :=
      { eqv.toRingEquiv.toAddEquiv with
        map_smul' := fun r y => by
          show eqv (r * y) = eqv r * eqv y
          exact map_mul eqv r y }
    exact L.finiteDimensional
  exact Place.isRational_of_isAlgClosed _

end ResidueLinePort

end ModularCurve.MultCovering

set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar modularFunctionFieldC ratFuncEquivCharLOneC charLGeomPlaceOfPoint jWidth jWidth_of_ne hasPrincipalDivisors_modularFunctionFieldBar_unconditional ord_charLGeomPlaceOfPoint_jqModC_sub_algebraMap"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "jBar mAnnuli modulusExp Fbar ChartCtx infChart zeroChart chart src tgt ssValue ssValue_injective nodeSrc nodeTgt AnnCtx hasseExp goodFamilyZero ssPolyBar FamCtx goodFamily abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom infChart_goodFamily_residue_ne_zero zeroChart_residue_goodFamilyZero_ne_zero hasseExp_zero"
p2m_open "ModularCurve.MultCovering ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_MultCovering_tangentDet_ne_zero_of_hasseExp_two.AlgebraicCurve IsLocalRing"

section TubeSepTangent

private theorem abv_sub_eq_of_abv_lt {L : Type*} [Field L] (μ : AbsoluteValue L ℝ) (hμ : IsNonarchimedean μ)
    {a b : L} (h : μ b < μ a) : μ (a - b) = μ a := by
  apply le_antisymm
  · have := hμ a (-b)
    rw [← sub_eq_add_neg, μ.map_neg] at this
    exact this.trans (max_le le_rfl h.le)
  · have := hμ (a - b) b
    rw [sub_add_cancel] at this
    rcases le_max_iff.1 this with h1 | h1
    · exact h1
    · exact absurd h1 (not_le.2 h)

private theorem Place.evalAt_add' {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (add_mem hf hg), map_add, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem aeval_jBar_mem_and_evalAt {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (e : Fin (mAnnuli p))
    (q : Polynomial (IsLocalRing.ResidueField ↥A)) :
    Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) q ∈ (nodeTgt Γ e).toValuationSubring ∧
    (nodeTgt Γ e).evalAt (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) q) = q.eval (ssValue Γ e) := by
  have hxrat := nodeTgt_isRational' Γ e
  have hjreg : jBar (IsLocalRing.ResidueField ↥A) ∈ (nodeTgt Γ e).toValuationSubring :=
    Place.mem_of_ord_nonneg _ (jBar_ne_zero' _) (by rw [ord_nodeTgt_jBar']; split_ifs <;> norm_num)
  have hjval : (nodeTgt Γ e).evalAt (jBar (IsLocalRing.ResidueField ↥A)) = ssValue Γ e := by
    have hpos : (nodeTgt Γ e).ord (jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) _ (ssValue Γ e)) = 1 := by
      have h := ord_charLGeomPlaceOfPoint_jBar_sub' (IsLocalRing.ResidueField ↥A) (ssValue Γ e) (ssValue Γ e)
      rw [if_pos rfl] at h
      exact h
    have hreg : jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) _ (ssValue Γ e) ∈ (nodeTgt Γ e).toValuationSubring :=
      sub_mem hjreg ((nodeTgt Γ e).algebraMap_mem' _)
    have h0 : (nodeTgt Γ e).evalAt (jBar (IsLocalRing.ResidueField ↥A) - algebraMap (IsLocalRing.ResidueField ↥A) _ (ssValue Γ e)) = 0 := by
      by_contra hne
      have := Place.ord_eq_zero_of_evalAt_ne_zero' _ hreg hne
      exact zero_ne_one (this.symm.trans hpos)
    rw [Place.evalAt_sub' _ hxrat hjreg ((nodeTgt Γ e).algebraMap_mem' _), Place.evalAt_algebraMap', sub_eq_zero] at h0
    exact h0
  induction q using Polynomial.induction_on with
  | C a =>
    rw [Polynomial.aeval_C, Polynomial.eval_C]
    exact ⟨(nodeTgt Γ e).algebraMap_mem' _, Place.evalAt_algebraMap' _ _⟩
  | add f g hf hg =>
    rw [map_add, Polynomial.eval_add]
    exact ⟨add_mem hf.1 hg.1, by rw [Place.evalAt_add' _ hxrat hf.1 hg.1, hf.2, hg.2]⟩
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Polynomial.eval_mul, Polynomial.eval_X]
    exact ⟨mul_mem h.1 hjreg, by rw [Place.evalAt_mul' _ hxrat h.1 hjreg, h.2, hjval]⟩

theorem tubeMember_value_D (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p] (Γ : ChartCtx p A) (Δ : AnnCtx Γ)
    {r : ℕ} (Φ : FamCtx p r) (e : Fin (mAnnuli p))
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμ : IsNonarchimedean μ) (hμA : ∀ a : (AlgebraicClosure ℚ), a ∈ A ↔ μ a ≤ 1)
    (R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p))) (hR : R ∈ (Δ.annIn e).dom) (l : Fin r) (hl : 1 ≤ (l : ℕ))
    (hout : ∀ Q ∈ (Δ.annIn e).dom, Q.ord (goodFamily Φ l) ≠ 0 →
      μ (Q.evalAt (Δ.annOut e).param) < μ (R.evalAt (Δ.annOut e).param))
    (hint : goodFamily Φ l ∈ (chart Γ (tgt p e)).integers) (hzoC : (Δ.annOut e).param ∈ (chart Γ (tgt p e)).integers) :
    ∃ hmem : R.evalAt (goodFamily Φ l) * (R.evalAt (Δ.annOut e).param)
        ^ (-((nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨goodFamily Φ l, hint⟩))) ∈ A,
      IsUnit (⟨_, hmem⟩ : A) ∧
      IsLocalRing.residue A ⟨_, hmem⟩ = (nodeTgt Γ e).evalAt ((chart Γ (tgt p e)).residue ⟨goodFamily Φ l, hint⟩
        * ((chart Γ (tgt p e)).residue ⟨(Δ.annOut e).param, hzoC⟩) ^ (-((nodeTgt Γ e).ord ((chart Γ (tgt p e)).residue ⟨goodFamily Φ l, hint⟩)))) := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : (AlgebraicClosure ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded e
  have hattOut := Δ.attached_tgt e
  have hattIn := Δ.attached_src e
  obtain ⟨hintI, hresI⟩ := infChart_goodFamily_residue_ne_zero p A hA Γ Φ
  obtain ⟨hintZ, hresZ⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  have hres : (chart Γ (tgt p e)).residue ⟨goodFamily Φ l, hint⟩ ≠ 0 := hresI l
  set c' : (AlgebraicClosure ℚ) := (p : (AlgebraicClosure ℚ)) ^ hasseExp Φ.toFamData l with hc'
  have hc'0 : c' ≠ 0 := pow_ne_zero _ hp0
  have hc'A : c' ∈ A := pow_mem (natCast_mem A p) _
  have heqZ : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c')⁻¹ * goodFamily Φ l = goodFamilyZero Φ.toFamData l := by
    rw [goodFamilyZero_eq_inv_mul']
  have hC' : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c')⁻¹ * goodFamily Φ l ∈ (chart Γ (src p e)).integers := by
    rw [heqZ]; exact hintZ l
  have hres' : (chart Γ (src p e)).residue ⟨_, hC'⟩ ≠ 0 := by
    have e1 : (⟨_, hC'⟩ : (chart Γ (src p e)).integers) = ⟨goodFamilyZero Φ.toFamData l, hintZ l⟩ := Subtype.ext heqZ
    rw [e1]; exact hresZ l
  have hpole : ∀ Q ∈ (Δ.annOut e).dom, 0 ≤ Q.ord (goodFamily Φ l) := by
    intro Q hQ
    rw [hdom] at hQ
    exact Place.ord_nonneg_of_mem' Q (abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom p A hA Γ Δ Φ μ hμA e Q hQ l hl).1
  have hwide := annOut_wide' p A hA Γ Δ e μ hμA
  have hx : (nodeTgt Γ e).IsRational := nodeTgt_isRational' Γ e
  have hmod0' : ((Δ.annOut e).modulus : (AlgebraicClosure ℚ)) ≠ 0 := by rw [hmod]; exact hmod0
  have htwo' : (Δ.annIn e).param * (Δ.annOut e).param = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((Δ.annOut e).modulus : (AlgebraicClosure ℚ)) := by
    rw [mul_comm (Δ.annIn e).param, hmod]; exact htwo
  have hR' : R ∈ (Δ.annOut e).dom := by rw [hdom]; exact hR
  have hout' : ∀ Q ∈ (Δ.annOut e).dom, Q.ord (goodFamily Φ l) ≠ 0 →
      μ (Q.evalAt (Δ.annOut e).param) < μ (R.evalAt (Δ.annOut e).param) := by
    intro Q hQ; rw [hdom] at hQ; exact hout Q hQ
  exact AlgebraicCurve.Annulus.residue_evalAt_mul_zpow_param_eq_of_isAttached_both_ends_of_forall_abv_lt μ hμA
    (Δ.annOut e) (Δ.annIn e) hdom.symm hmod.symm hmod0' htwo' (chart Γ (tgt p e)) (nodeTgt Γ e) hattOut hx
    (chart Γ (src p e)) (nodeSrc Γ e) hattIn hwide (goodFamily Φ l) hint hres c' hc'0 hc'A hC' hres' hpole hzoC R hR' hout'

end TubeSepTangent

end ModularCurve.MultCovering

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_MultCovering_tangentDet_ne_zero_of_hasseExp_two.AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_MultCovering_tangentDet_ne_zero_of_hasseExp_two.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_tangentDet_ne_zero_of_hasseExp_two.ModularCurve.MultCovering"

theorem solution (p : ℕ) [Fact p.Prime] (hp13 : 13 ≤ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    (Γ : ChartCtx p A) (Δ : AnnCtx Γ) {r : ℕ} (Φ : FamCtx p r)
    (hint : ∀ l, goodFamilyZero Φ.toFamData l ∈ (zeroChart Γ).integers)
    (hLI : LinearIndependent (IsLocalRing.ResidueField ↥A)
      (fun l : Fin r => (zeroChart Γ).residue ⟨goodFamilyZero Φ.toFamData l, hint l⟩))
    (e e' : Fin (mAnnuli p)) (hne : e ≠ e') (hw : jWidth (ssValue Γ e) ≠ 1) (hw' : jWidth (ssValue Γ e') ≠ 1)
    (l₂ l₃ : Fin r) (h23 : l₂ ≠ l₃) (hn₂ : hasseExp Φ.toFamData l₂ = 2) (hn₃ : hasseExp Φ.toFamData l₃ = 2) :
    ∃ (hintI : ∀ l, goodFamily Φ l ∈ (infChart Γ).integers) (hz : (Δ.annOut e).param ∈ (infChart Γ).integers)
      (hz' : (Δ.annOut e').param ∈ (infChart Γ).integers),
      (nodeTgt Γ e).evalAt ((infChart Γ).residue ⟨goodFamily Φ l₂, hintI l₂⟩ * ((infChart Γ).residue ⟨(Δ.annOut e).param, hz⟩)⁻¹)
          * (nodeTgt Γ e').evalAt ((infChart Γ).residue ⟨goodFamily Φ l₃, hintI l₃⟩ * ((infChart Γ).residue ⟨(Δ.annOut e').param, hz'⟩)⁻¹)
        ≠ (nodeTgt Γ e).evalAt ((infChart Γ).residue ⟨goodFamily Φ l₃, hintI l₃⟩ * ((infChart Γ).residue ⟨(Δ.annOut e).param, hz⟩)⁻¹)
          * (nodeTgt Γ e').evalAt ((infChart Γ).residue ⟨goodFamily Φ l₂, hintI l₂⟩ * ((infChart Γ).residue ⟨(Δ.annOut e').param, hz'⟩)⁻¹) := by
  classical
  have hp : p.Prime := Fact.out
  have hp0 : (p : (AlgebraicClosure ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * p)
  obtain ⟨μ, hμ, -, hμA⟩ := ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime hp A hA

  obtain ⟨hintI, h0res, P, hP, hPind, hPspan⟩ := Φ.t_inf A hA Γ
  obtain ⟨hintZ, hresZ⟩ := zeroChart_residue_goodFamilyZero_ne_zero p A hA Γ Φ
  obtain ⟨hintI2, hresI⟩ := infChart_goodFamily_residue_ne_zero p A hA Γ Φ
  have hz : (Δ.annOut e).param ∈ (infChart Γ).integers := by obtain ⟨-, h, -⟩ := Δ.attached_tgt e; exact h
  have hz' : (Δ.annOut e').param ∈ (infChart Γ).integers := by obtain ⟨-, h, -⟩ := Δ.attached_tgt e'; exact h
  refine ⟨hintI, hz, hz', ?_⟩
  set C := infChart Γ with hC_def
  have hss0 : ssPolyBar Γ ≠ 0 := ssPolyBar_ne_zero' Γ

  have tangent : ∀ (ε : Fin (mAnnuli p)) (hzε : (Δ.annOut ε).param ∈ C.integers),
      ∃ κ : IsLocalRing.ResidueField ↥A, κ ≠ 0 ∧ ∀ l : Fin r, 1 ≤ (l : ℕ) →
        (nodeTgt Γ ε).evalAt (C.residue ⟨goodFamily Φ l, hintI l⟩ * (C.residue ⟨(Δ.annOut ε).param, hzε⟩)⁻¹)
          = κ * (P l).eval (ssValue Γ ε) := by
    intro ε hzε
    obtain ⟨-, hzoC, hzoord, -⟩ := Δ.attached_tgt ε
    set xe := nodeTgt Γ ε with hxe_def
    have hxrat : xe.IsRational := nodeTgt_isRational' Γ ε
    have hordss : xe.ord (ssPolyBar Γ) = 1 := ord_nodeTgt_ssPolyBar' Γ ε
    have hzoord' : xe.ord (C.residue ⟨(Δ.annOut ε).param, hzε⟩) = 1 := hzoord
    have hzbar0 : C.residue ⟨(Δ.annOut ε).param, hzε⟩ ≠ 0 := by
      intro h0; rw [h0, Place.ord_zero] at hzoord'; exact zero_ne_one hzoord'
    have hzoord' : xe.ord (C.residue ⟨(Δ.annOut ε).param, hzε⟩) = 1 := hzoord
    have hreg1 : ssPolyBar Γ * (C.residue ⟨(Δ.annOut ε).param, hzε⟩)⁻¹ ∈ xe.toValuationSubring := by
      refine Place.mem_of_ord_nonneg xe (mul_ne_zero hss0 (inv_ne_zero hzbar0)) ?_
      rw [xe.ord_mul hss0 (inv_ne_zero hzbar0), Place.ord_inv, hordss, hzoord']; norm_num
    set κ := xe.evalAt (ssPolyBar Γ * (C.residue ⟨(Δ.annOut ε).param, hzε⟩)⁻¹) with hκ_def
    have hκ0 : κ ≠ 0 := by
      intro h0
      have h00 : xe.ord (ssPolyBar Γ * (C.residue ⟨(Δ.annOut ε).param, hzε⟩)⁻¹) = 0 := by
        rw [xe.ord_mul hss0 (inv_ne_zero hzbar0), Place.ord_inv, hordss, hzoord']; norm_num
      have hu := Place.isUnit_of_ord_eq_zero' xe hreg1 (mul_ne_zero hss0 (inv_ne_zero hzbar0)) h00
      have hr0 : IsLocalRing.residue xe.toValuationSubring ⟨_, hreg1⟩ ≠ 0 :=
        (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu
      apply hr0
      rw [← xe.algebraMap_evalAt hxrat hreg1, ← hκ_def, h0, map_zero]
    refine ⟨κ, hκ0, fun l hl => ?_⟩
    obtain ⟨hPreg, hPval⟩ := aeval_jBar_mem_and_evalAt Γ ε (P l)
    rw [(hP l hl).2]
    have : ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l) * (C.residue ⟨(Δ.annOut ε).param, hzε⟩)⁻¹
        = (ssPolyBar Γ * (C.residue ⟨(Δ.annOut ε).param, hzε⟩)⁻¹) * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l) := by ring
    rw [this, Place.evalAt_mul' xe hxrat hreg1 hPreg, hPval]

  have hμp0 : 0 < μ (p : (AlgebraicClosure ℚ)) := μ.pos hp0
  have hμp1 : μ (p : (AlgebraicClosure ℚ)) < 1 := by
    obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded e
    have hπ : (((Δ.annIn e).modulus : ↥A) : (AlgebraicClosure ℚ)) = (p : (AlgebraicClosure ℚ)) ^ jWidth (ssValue Γ e) := by
      show (((Δ.An e).modulus : ↥A) : (AlgebraicClosure ℚ)) = _
      rw [Δ.modulus_eq e]; norm_cast
    have hlt : μ ((p : (AlgebraicClosure ℚ)) ^ jWidth (ssValue Γ e)) < 1 := by
      rw [← hπ]; exact abv_lt_one_of_mem_maximalIdeal_vs μ hμA ((Δ.annIn e).modulus).2 (by simpa using (Δ.annIn e).modulus_mem)
    rw [map_pow] at hlt
    by_contra hge; push_neg at hge
    exact absurd hlt (not_lt.2 (one_le_pow₀ hge))

  have vanish : ∀ (ε : Fin (mAnnuli p)), jWidth (ssValue Γ ε) = 1 → ∀ (l : Fin r), 1 ≤ (l : ℕ) →
      hasseExp Φ.toFamData l = 2 → (P l).eval (ssValue Γ ε) = 0 := by
    intro ε hw1 l hl hn
    obtain ⟨hdom, hmod, hmod0, htwo⟩ := Δ.twoEnded ε
    have hattOut := Δ.attached_tgt ε
    have hattIn := Δ.attached_src ε
    set xe := nodeTgt Γ ε with hxe_def
    have hxrat : xe.IsRational := nodeTgt_isRational' Γ ε
    have hordss : xe.ord (ssPolyBar Γ) = 1 := ord_nodeTgt_ssPolyBar' Γ ε
    have hintC : goodFamily Φ l ∈ (chart Γ (tgt p ε)).integers := hintI l
    have hres : (chart Γ (tgt p ε)).residue ⟨goodFamily Φ l, hintC⟩ ≠ 0 := hresI l
    set c' : (AlgebraicClosure ℚ) := (p : (AlgebraicClosure ℚ)) ^ hasseExp Φ.toFamData l with hc'
    have hc'0 : c' ≠ 0 := pow_ne_zero _ hp0
    have hc'A : c' ∈ A := pow_mem (natCast_mem A p) _
    have heqZ : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c')⁻¹ * goodFamily Φ l = goodFamilyZero Φ.toFamData l := rfl
    have hC' : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) c')⁻¹ * goodFamily Φ l ∈ (chart Γ (src p ε)).integers := by
      rw [heqZ]; exact hintZ l
    have eZ : (⟨_, hC'⟩ : (chart Γ (src p ε)).integers) = ⟨goodFamilyZero Φ.toFamData l, hintZ l⟩ := Subtype.ext heqZ
    have hres' : (chart Γ (src p ε)).residue ⟨_, hC'⟩ ≠ 0 := by rw [eZ]; exact hresZ l
    have hpole : ∀ Q ∈ (Δ.annOut ε).dom, 0 ≤ Q.ord (goodFamily Φ l) := by
      intro Q hQ; rw [hdom] at hQ
      exact Place.ord_nonneg_of_mem' Q (abv_evalAt_goodFamily_lt_one_of_mem_annIn_dom p A hA Γ Δ Φ μ hμA ε Q hQ l hl).1
    have hwide := annOut_wide' p A hA Γ Δ ε μ hμA
    have hmod0' : ((Δ.annOut ε).modulus : (AlgebraicClosure ℚ)) ≠ 0 := by rw [hmod]; exact hmod0
    have htwo' : (Δ.annIn ε).param * (Δ.annOut ε).param = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * p)) ((Δ.annOut ε).modulus : (AlgebraicClosure ℚ)) := by
      rw [mul_comm (Δ.annIn ε).param, hmod]; exact htwo
    have hb := AlgebraicCurve.Annulus.abv_modulus_zpow_ord_residue_le_abv_of_isAttached_both_ends μ hμA (Δ.annOut ε) (Δ.annIn ε) hdom.symm hmod.symm hmod0' htwo' (chart Γ (tgt p ε)) xe hattOut
      (chart Γ (src p ε)) (nodeSrc Γ ε) hattIn hwide (goodFamily Φ l) hintC hres c' hc'0 hc'A hC' hres' hpole

    have hμmod : μ (((Δ.annOut ε).modulus : (AlgebraicClosure ℚ))) = μ (p : (AlgebraicClosure ℚ)) := by
      rw [hmod]
      show μ ((((Δ.An ε).modulus : ↥A)) : (AlgebraicClosure ℚ)) = _
      rw [Δ.modulus_eq ε, hw1, pow_one]; norm_cast
    rw [hμmod, hc', map_pow] at hb
    obtain ⟨hPreg, hPval⟩ := aeval_jBar_mem_and_evalAt Γ ε (P l)
    have hresl' : (chart Γ (tgt p ε)).residue ⟨goodFamily Φ l, hintC⟩
        = ssPolyBar Γ * Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l) := (hP l hl).2
    have hPne : Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l) ≠ 0 := by
      intro h0; apply hres
      rw [hresl', h0, mul_zero]
    have ha : xe.ord ((chart Γ (tgt p ε)).residue ⟨goodFamily Φ l, hintC⟩) = 1 + xe.ord (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l)) := by
      rw [hresl', xe.ord_mul hss0 hPne, hordss]
    rw [ha, hn] at hb
    have hordP : 0 ≤ xe.ord (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l)) := Place.ord_nonneg_of_mem' xe hPreg
    have h2 : (2 : ℤ) ≤ 1 + xe.ord (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l)) := by
      have : μ (p : (AlgebraicClosure ℚ)) ^ ((1 + xe.ord (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l))) : ℤ) ≤ μ (p : (AlgebraicClosure ℚ)) ^ ((2 : ℕ) : ℤ) := by
        rw [zpow_natCast]; exact hb
      exact (zpow_le_zpow_iff_right_of_lt_one₀ hμp0 hμp1).1 this
    have hpos : 0 < xe.ord (Polynomial.aeval (jBar (IsLocalRing.ResidueField ↥A)) (P l)) := by omega
    rw [← hPval]
    by_contra hne0
    have := Place.ord_eq_zero_of_evalAt_ne_zero' xe hPreg hne0
    omega

  set S1 : Finset (Fin (mAnnuli p)) := Finset.univ.filter (fun ε => jWidth (ssValue Γ ε) = 1) with hS1
  set PiW : Polynomial (IsLocalRing.ResidueField ↥A) := ∏ ε ∈ S1, (Polynomial.X - Polynomial.C (ssValue Γ ε)) with hPiW
  have hinj : Function.Injective (ssValue Γ) := ssValue_injective Γ
  have hPiWdvd : ∀ (l : Fin r), 1 ≤ (l : ℕ) → hasseExp Φ.toFamData l = 2 → PiW ∣ P l := by
    intro l hl hn
    refine Finset.prod_dvd_of_coprime ?_ (fun ε hε => Polynomial.dvd_iff_isRoot.2 ?_)
    · exact (Polynomial.pairwise_coprime_X_sub_C hinj).set_pairwise _
    · rw [Polynomial.IsRoot.def]; exact vanish ε (Finset.mem_filter.1 hε).2 l hl hn
  have hPiW0 : PiW ≠ 0 := (Polynomial.monic_prod_of_monic _ _ (fun ε _ => Polynomial.monic_X_sub_C (ssValue Γ ε))).ne_zero
  have hPiWdeg : PiW.natDegree = S1.card := by
    rw [hPiW, Polynomial.natDegree_prod _ _ (fun ε _ => Polynomial.X_sub_C_ne_zero _)]
    simp

  have hl₂ : 1 ≤ (l₂ : ℕ) := by
    by_contra hlt; push_neg at hlt
    have := hasseExp_zero Φ l₂ (by omega); omega
  have hl₃ : 1 ≤ (l₃ : ℕ) := by
    by_contra hlt; push_neg at hlt
    have := hasseExp_zero Φ l₃ (by omega); omega
  obtain ⟨Q₂, hQ₂⟩ := hPiWdvd l₂ hl₂ hn₂
  obtain ⟨Q₃, hQ₃⟩ := hPiWdvd l₃ hl₃ hn₃

  have hwide2 : Finset.univ.filter (fun ε : Fin (mAnnuli p) => ¬ jWidth (ssValue Γ ε) = 1) = {e, e'} := by
    ext ε
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hε

      have hv : ∀ {x : Fin (mAnnuli p)}, jWidth (ssValue Γ x) ≠ 1 → ssValue Γ x = 0 ∨ ssValue Γ x = 1728 := by
        intro x hx
        by_contra hno; push_neg at hno
        exact hx (jWidth_of_ne hno.1 hno.2)
      rcases hv hε with h | h <;> rcases hv hw with h1 | h1 <;> rcases hv hw' with h2 | h2
      all_goals first
        | exact Or.inl (hinj (h.trans h1.symm))
        | exact Or.inr (hinj (h.trans h2.symm))
        | exact absurd (hinj (h1.trans h2.symm)) hne
    · rintro (rfl | rfl)
      · exact hw
      · exact hw'
  have hcardS1 : S1.card + 2 = mAnnuli p := by
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (mAnnuli p))))
      (fun ε => jWidth (ssValue Γ ε) = 1)
    rw [hwide2, Finset.card_pair hne, Finset.card_univ, Fintype.card_fin] at h1
    exact h1
  have hQdeg : ∀ (l : Fin r) (Q : Polynomial (IsLocalRing.ResidueField ↥A)), 1 ≤ (l : ℕ) → P l = PiW * Q → Q.natDegree ≤ 1 := by
    intro l Q hl hPQ
    have hPl0 : P l ≠ 0 := hPind.ne_zero ⟨l, hl⟩
    have hQ0 : Q ≠ 0 := by rintro rfl; rw [mul_zero] at hPQ; exact hPl0 hPQ
    have hdeg := (hP l hl).1
    rw [hPQ, Polynomial.natDegree_mul hPiW0 hQ0, hPiWdeg] at hdeg
    omega
  have hdQ₂ := hQdeg l₂ Q₂ hl₂ hQ₂
  have hdQ₃ := hQdeg l₃ Q₃ hl₃ hQ₃

  have hQind : ∀ a b : (IsLocalRing.ResidueField ↥A), a • Q₂ + b • Q₃ = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have hPab : a • P l₂ + b • P l₃ = 0 := by
      have : a • P l₂ + b • P l₃ = PiW * (a • Q₂ + b • Q₃) := by
        rw [hQ₂, hQ₃, mul_add, mul_smul_comm, mul_smul_comm]
      rw [this, hab, mul_zero]

    let i₂ : {l : Fin r // 1 ≤ (l : ℕ)} := ⟨l₂, hl₂⟩
    let i₃ : {l : Fin r // 1 ≤ (l : ℕ)} := ⟨l₃, hl₃⟩
    have h23' : i₂ ≠ i₃ := fun h => h23 (congrArg Subtype.val h)
    let g : {l : Fin r // 1 ≤ (l : ℕ)} → (IsLocalRing.ResidueField ↥A) := fun i => if i = i₂ then a else if i = i₃ then b else 0
    have hg : ∑ i, g i • P (i : Fin r) = 0 := by
      have hsplit : ∀ i, g i • P (i : Fin r) = (if i = i₂ then a • P l₂ else 0) + (if i = i₃ then b • P l₃ else 0) := by
        intro i
        by_cases h2 : i = i₂
        · subst h2; simp [g, h23']; rfl
        · by_cases h3 : i = i₃
          · subst h3; simp [g, h2]; rfl
          · simp [g, h2, h3]
      rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
      simp only [Finset.mem_univ, if_true]
      exact hPab
    have hz := (Fintype.linearIndependent_iff.1 hPind) g hg
    have ha := hz i₂
    have hb := hz i₃
    simp only [g, if_true] at ha
    simp only [g, if_neg h23'.symm, if_true] at hb
    exact ⟨ha, hb⟩

  set u := ssValue Γ e with hu_def
  set v := ssValue Γ e' with hv_def
  have huv : u ≠ v := fun h => hne (hinj h)
  have hlin : ∀ (R : Polynomial (IsLocalRing.ResidueField ↥A)), R.natDegree ≤ 1 → R.eval u = 0 → R.eval v = 0 → R = 0 := by
    intro R hR hu0 hv0
    have hform := Polynomial.eq_X_add_C_of_natDegree_le_one hR
    rw [hform] at hu0 hv0
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at hu0 hv0
    have h1 : R.coeff 1 * (u - v) = 0 := by linear_combination hu0 - hv0
    have hc1 : R.coeff 1 = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd (sub_eq_zero.1 h) huv
    have hc0 : R.coeff 0 = 0 := by rw [hc1, zero_mul, zero_add] at hu0; exact hu0
    rw [hform, hc1, hc0]; simp
  have hdetQ : Q₂.eval u * Q₃.eval v ≠ Q₃.eval u * Q₂.eval v := by
    intro heq

    have hR0 : Q₃.eval v • Q₂ + (-(Q₂.eval v)) • Q₃ = 0 := by
      apply hlin
      · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_) <;>
          exact (Polynomial.natDegree_smul_le _ _).trans (by assumption)
      · simp only [Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]; linear_combination heq
      · simp only [Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]; ring
    obtain ⟨h3v, h2v⟩ := hQind _ _ hR0
    have h2v' : Q₂.eval v = 0 := neg_eq_zero.1 h2v

    have hroot : ∀ (R : Polynomial (IsLocalRing.ResidueField ↥A)), R.natDegree ≤ 1 → R.eval v = 0 → R = R.coeff 1 • (Polynomial.X - Polynomial.C v) := by
      intro R hR hv0
      have hform := Polynomial.eq_X_add_C_of_natDegree_le_one hR
      have hv1 := hv0
      rw [hform] at hv1
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at hv1
      have hc0 : R.coeff 0 = -(R.coeff 1 * v) := by linear_combination hv1
      conv_lhs => rw [hform, hc0]
      rw [Polynomial.smul_eq_C_mul, mul_sub, map_neg, map_mul]; ring
    set c₂ := Q₂.coeff 1 with hc₂
    set c₃ := Q₃.coeff 1 with hc₃
    have e2 := hroot Q₂ hdQ₂ h2v'
    have e3 := hroot Q₃ hdQ₃ h3v
    rw [← hc₂] at e2
    rw [← hc₃] at e3
    have hcomb : c₃ • Q₂ + (-c₂) • Q₃ = 0 := by
      rw [e2, e3, smul_smul, smul_smul, ← add_smul, show c₃ * c₂ + -c₂ * c₃ = 0 by ring, zero_smul]
    obtain ⟨-, hc20⟩ := hQind _ _ hcomb
    have hQ20 : Q₂ = 0 := by rw [e2, neg_eq_zero.1 hc20, zero_smul]
    have hPl0 : P l₂ ≠ 0 := hPind.ne_zero ⟨l₂, hl₂⟩
    apply hPl0; rw [hQ₂, hQ20, mul_zero]

  obtain ⟨κe, hκe0, hte⟩ := tangent e hz
  obtain ⟨κe', hκe'0, hte'⟩ := tangent e' hz'
  rw [hte l₂ hl₂, hte l₃ hl₃, hte' l₂ hl₂, hte' l₃ hl₃]
  have hPiWeval : ∀ (x : Fin (mAnnuli p)), jWidth (ssValue Γ x) ≠ 1 → PiW.eval (ssValue Γ x) ≠ 0 := by
    intro x hx
    rw [hPiW, Polynomial.eval_prod]
    refine Finset.prod_ne_zero_iff.2 fun ε hε => ?_
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
    intro h
    have := hinj h
    subst this
    exact hx (Finset.mem_filter.1 hε).2
  have hPiWu : PiW.eval u ≠ 0 := hPiWeval e hw
  have hPiWv : PiW.eval v ≠ 0 := hPiWeval e' hw'
  rw [← hu_def, ← hv_def, hQ₂, hQ₃]
  simp only [Polynomial.eval_mul]
  intro heq
  apply hdetQ
  have hK : κe * κe' * PiW.eval u * PiW.eval v ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hκe0 hκe'0) hPiWu) hPiWv
  apply mul_left_cancel₀ hK
  linear_combination heq

end S_ModularCurve_MultCovering_tangentDet_ne_zero_of_hasseExp_two
end P2MW
export P2MW.S_ModularCurve_MultCovering_tangentDet_ne_zero_of_hasseExp_two (solution)
