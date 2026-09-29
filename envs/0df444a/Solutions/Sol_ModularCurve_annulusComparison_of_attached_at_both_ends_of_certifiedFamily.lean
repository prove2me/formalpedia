-- Prove2me | solution 1 for ModularCurve.annulusComparison_of_attached_at_both_ends_of_certifiedFamily
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/38d8c062-788d-5809-9ae3-4f9e657dc37a

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Theorems.Thm_AlgebraicCurve_Annulus_sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends
import Theorems.Thm_AlgebraicCurve_Annulus_abv_evalAt_le_max_of_isAttached_both_ends
import Theorems.Thm_AlgebraicCurve_Annulus_abv_evalAt_sub_eq_abv_param_sub_of_ord_residue_eq_one_of_abv_le
import Theorems.Thm_AlgebraicCurve_Annulus_exists_abv_evalAt_sub_mul_eq_of_ord_residue_eq_one_of_abv_lt
import Theorems.Thm_AlgebraicCurve_prox_eq_neg_log_iSup_sub_of_chart
import Theorems.Thm_AlgebraicCurve_exists_evalVec_eq_smul_mulVec_of_eq_sum_smul
import Theorems.Thm_AlgebraicCurve_prox_smul_smul
import Theorems.Thm_AlgebraicCurve_abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_annulusComparison_of_attached_at_both_ends_of_certifiedFamily
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_annulusComparison_of_attached_at_both_ends_of_certifiedFamily.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_annulusComparison_of_attached_at_both_ends_of_certifiedFamily.ModularCurve IsLocalRing"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.ord Place.ord_zero Place.ord_one Place.ord_inv HasPrincipalDivisors Place.evalAt_one prox evalVec Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends Annulus.abv_evalAt_le_max_of_isAttached_both_ends Annulus.abv_evalAt_sub_eq_abv_param_sub_of_ord_residue_eq_one_of_abv_le Annulus.exists_abv_evalAt_sub_mul_eq_of_ord_residue_eq_one_of_abv_lt prox_eq_neg_log_iSup_sub_of_chart exists_evalVec_eq_smul_mulVec_of_eq_sum_smul prox_smul_smul abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le"
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

namespace Place p2m_export "AlgebraicCurve.Place" "ext coe_algebraMap ResidueField ord ord_zero ord_one ord_mul ord_inv ord_coe_unit ord_zpow ord_unit_smul_zpow exists_unit_mul_zpow algebraMap_mem' toValuationSubring adicValuation_le_one_of_mem adicValuation_le_one_iff IsRational algebraMap_residueField_injective residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt evalAt_one" end Place
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

namespace ComponentChart p2m_export "AlgebraicCurve.ComponentChart" "integers algebraMap_mem_iff residue residue_algebraMap ker_residue dom" end ComponentChart
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
p2m_export "ModularCurve" "modularFunctionFieldBar IsEmbBasis hasPrincipalDivisors_modularFunctionFieldBar_unconditional"
namespace MultCovering
p2m_open "ModularCurve"
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

end ModularCurve.MultCovering

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_annulusComparison_of_attached_at_both_ends_of_certifiedFamily.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_annulusComparison_of_attached_at_both_ends_of_certifiedFamily.ModularCurve IsLocalRing P2MW.S_ModularCurve_annulusComparison_of_attached_at_both_ends_of_certifiedFamily.ModularCurve.MultCovering"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ComponentChart Annulus Place Place.ord Place.ord_zero Place.ord_one Place.ord_inv HasPrincipalDivisors Place.evalAt_one prox evalVec Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends Annulus.abv_evalAt_le_max_of_isAttached_both_ends Annulus.abv_evalAt_sub_eq_abv_param_sub_of_ord_residue_eq_one_of_abv_le Annulus.exists_abv_evalAt_sub_mul_eq_of_ord_residue_eq_one_of_abv_lt prox_eq_neg_log_iSup_sub_of_chart exists_evalVec_eq_smul_mulVec_of_eq_sum_smul prox_smul_smul abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le"
p2m_open "AlgebraicCurve"

open IsLocalRing

section IsometryHelpers

namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.exists_isUnit_of_ord_eq_zero_G {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (hf : f ≠ 0) (h : v.ord f = 0) :
    ∃ hm : f ∈ v.toValuationSubring, IsUnit (⟨f, hm⟩ : v.toValuationSubring) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [h, zpow_zero, mul_one] at hu
  subst hu
  exact ⟨(u : v.toValuationSubring).2, u.isUnit⟩

end Place
p2m_export "AlgebraicCurve" "Place.exists_isUnit_of_ord_eq_zero_G"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.ord_nonneg_of_mem_G {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

end Place
p2m_export "AlgebraicCurve" "Place.ord_nonneg_of_mem_G"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.mem_of_ord_nonneg_G {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

end Place
p2m_export "AlgebraicCurve" "Place.mem_of_ord_nonneg_G"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.evalAt_mul_G {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (mul_mem hf hg), map_mul, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_mul]
  rfl

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_mul_G"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.evalAt_sub_G {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (sub_mem hf hg), map_sub, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_sub]
  rfl

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_sub_G"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in
private theorem _root_.AlgebraicCurve.Place.evalAt_algebraMap_G {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have h : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring a := Subtype.ext (v.coe_algebraMap a).symm
  rw [h, ← IsLocalRing.ResidueField.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
    v.residueInv_algebraMap]

end Place
p2m_export "AlgebraicCurve" "Place.evalAt_algebraMap_G"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.ord_eq_zero_of_evalAt_ne_zero_G {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) :
    v.ord f = 0 := by
  have h0 : 0 ≤ v.ord f := v.ord_nonneg_of_mem_G hf
  by_contra hne
  have hpos : 0 < v.ord f := lt_of_le_of_ne h0 (Ne.symm hne)
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

end Place
p2m_export "AlgebraicCurve" "Place.ord_eq_zero_of_evalAt_ne_zero_G"
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.ord_pos_of_evalAt_eq_zero_G {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) (h : v.evalAt f = 0) :
    0 < v.ord f := by
  have h0 := v.ord_nonneg_of_mem_G hf
  rcases h0.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero_G hf0 heq.symm
    have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hm⟩ ≠ 0 :=
      (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hu
    apply hres
    rw [← v.algebraMap_evalAt hv hm, h, map_zero]

end Place
p2m_export "AlgebraicCurve" "Place.ord_pos_of_evalAt_eq_zero_G"
namespace ComponentChart
p2m_open_scoped "AlgebraicCurve.ComponentChart" in

private theorem _root_.AlgebraicCurve.ComponentChart.isUnit_of_residue_ne_zero_G
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0) :
    IsUnit (⟨f, hf⟩ : C.integers) := by
  by_contra hnu
  apply hres
  have : (⟨f, hf⟩ : C.integers) ∈ RingHom.ker C.residue := by
    rw [C.ker_residue]; exact (IsLocalRing.mem_maximalIdeal _).2 hnu
  exact this

end ComponentChart
p2m_export "AlgebraicCurve" "ComponentChart.isUnit_of_residue_ne_zero_G"

theorem inv_mem_of_isUnit_G {F : Type*} [Field F] {O : ValuationSubring F} {x : F}
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

p2m_open_scoped "AlgebraicCurve.ComponentChart" in

theorem ComponentChart.residue_inv_G
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {f : F} (hf : f ∈ C.integers) (hres : C.residue ⟨f, hf⟩ ≠ 0)
    (hfi : f⁻¹ ∈ C.integers) : C.residue ⟨f⁻¹, hfi⟩ = (C.residue ⟨f, hf⟩)⁻¹ := by
  have hf0 : f ≠ 0 := by
    rintro rfl; apply hres
    have : (⟨(0 : F), hf⟩ : C.integers) = 0 := rfl
    rw [this, map_zero]
  have h1 : C.residue ⟨f⁻¹, hfi⟩ * C.residue ⟨f, hf⟩ = 1 := by
    rw [← map_mul]
    have : (⟨f⁻¹, hfi⟩ : C.integers) * ⟨f, hf⟩ = 1 := Subtype.ext (inv_mul_cancel₀ hf0)
    rw [this, map_one]
  exact eq_inv_of_mul_eq_one_left h1

namespace ComponentChart
p2m_open_scoped "AlgebraicCurve.ComponentChart" in

private theorem _root_.AlgebraicCurve.ComponentChart.residue_algebraMap_eq_zero_G
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A)
    (h : algebraMap L F a ∈ C.integers) : C.residue ⟨algebraMap L F a, h⟩ = 0 := by
  have e1 : (⟨algebraMap L F a, h⟩ : C.integers) = ⟨algebraMap L F a, (C.algebraMap_mem_iff a).mpr a.2⟩ := rfl
  rw [e1, C.residue_algebraMap a, (IsLocalRing.residue_eq_zero_iff _).2 ha, map_zero]

end ComponentChart
p2m_export "AlgebraicCurve" "ComponentChart.residue_algebraMap_eq_zero_G"

theorem abv_lt_one_of_mem_maximalIdeal_G {L : Type*} [Field L] {A : ValuationSubring L}
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    {m : ↥A} (hm : m ∈ IsLocalRing.maximalIdeal ↥A) : μ (m : L) < 1 := by
  have hle : μ (m : L) ≤ 1 := (hμA _).1 m.2
  refine lt_of_le_of_ne hle fun h1 => ?_
  apply (IsLocalRing.mem_maximalIdeal _).1 hm
  have hm0 : (m : L) ≠ 0 := fun h0 => by rw [h0, map_zero] at h1; exact zero_ne_one h1
  have hinv : (m : L)⁻¹ ∈ A := (hμA _).2 (by rw [map_inv₀, h1, inv_one])
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hm0)⟩

theorem mem_maximalIdeal_of_abv_lt_one_G {L : Type*} [Field L] {A : ValuationSubring L}
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    {x : L} (hx : x ∈ A) (h : μ x < 1) : (⟨x, hx⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨u, hu⟩ := hu
  have hx0 : x ≠ 0 := by
    intro h0
    have : (u : ↥A) = 0 := by rw [hu]; exact Subtype.ext h0
    exact u.ne_zero this
  have hinv : ((u⁻¹ : (↥A)ˣ) : ↥A).1 = x⁻¹ := by
    have h1 := congrArg (fun t : ↥A => (t : L)) u.mul_inv
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
    rw [hu] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hxinv : μ x⁻¹ ≤ 1 := (hμA _).1 (hinv ▸ ((u⁻¹ : (↥A)ˣ) : ↥A).2)
  rw [map_inv₀] at hxinv
  have : 1 < (μ x)⁻¹ := (one_lt_inv₀ (μ.pos hx0)).2 h
  linarith

theorem residue_ne_zero_of_abv_eq_one_G {L : Type*} [Field L] {A : ValuationSubring L}
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    {x : L} (hx : x ∈ A) (h : μ x = 1) : IsLocalRing.residue ↥A ⟨x, hx⟩ ≠ 0 := by
  rw [IsLocalRing.residue_ne_zero_iff_isUnit]
  have hx0 : x ≠ 0 := fun h0 => by rw [h0, map_zero] at h; exact zero_ne_one h
  have hinv : x⁻¹ ∈ A := (hμA _).2 (by rw [map_inv₀, h, inv_one])
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩

p2m_open_scoped "AlgebraicCurve.Place" in
theorem Place.evalAt_add_G {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)
    (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (add_mem hf hg), map_add, v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

namespace Annulus p2m_export "AlgebraicCurve.Annulus" "IsAttached existsUnique_evalAt_eq modulus modulus_mem dom mem_dom param ord_param_sub sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends abv_evalAt_le_max_of_isAttached_both_ends abv_evalAt_sub_eq_abv_param_sub_of_ord_residue_eq_one_of_abv_le exists_abv_evalAt_sub_mul_eq_of_ord_residue_eq_one_of_abv_lt" end Annulus
p2m_open_scoped "AlgebraicCurve.Annulus" in

theorem Annulus.exists_mem_dom_abv_evalAt_param_ne_G {L : Type*} [Field L] [IsAlgClosed L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F]
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An : Annulus A F) (hmod0 : (An.modulus : L) ≠ 0) :
    ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, μ (Q₁.evalAt An.param) ≠ μ (Q₂.evalAt An.param) := by
  set π : L := (An.modulus : L) with hπ
  have hμπ0 : 0 < μ π := μ.pos hmod0
  have hμπ1 : μ π < 1 := abv_lt_one_of_mem_maximalIdeal_G μ hμA An.modulus_mem
  obtain ⟨c₂, hc₂⟩ := IsAlgClosed.exists_pow_nat_eq π (by norm_num : 0 < 2)
  obtain ⟨c₃, hc₃⟩ := IsAlgClosed.exists_pow_nat_eq π (by norm_num : 0 < 3)
  have hμc₂ : μ c₂ ^ 2 = μ π := by rw [← map_pow, hc₂]
  have hμc₃ : μ c₃ ^ 3 = μ π := by rw [← map_pow, hc₃]
  have hc₂0 : c₂ ≠ 0 := by rintro rfl; apply hmod0; rw [← hc₂]; norm_num
  have hc₃0 : c₃ ≠ 0 := by rintro rfl; apply hmod0; rw [← hc₃]; norm_num
  have hμc₂1 : μ c₂ < 1 := by
    by_contra h; push Not at h
    have : 1 ≤ μ c₂ ^ 2 := one_le_pow₀ h
    linarith
  have hμc₃1 : μ c₃ < 1 := by
    by_contra h; push Not at h
    have : 1 ≤ μ c₃ ^ 3 := one_le_pow₀ h
    linarith
  have hc₂A : c₂ ∈ A := (hμA _).2 hμc₂1.le
  have hc₃A : c₃ ∈ A := (hμA _).2 hμc₃1.le
  have hc₂𝔪 := mem_maximalIdeal_of_abv_lt_one_G μ hμA hc₂A hμc₂1
  have hc₃𝔪 := mem_maximalIdeal_of_abv_lt_one_G μ hμA hc₃A hμc₃1
  have hc₃sqA : c₃ ^ 2 ∈ A := pow_mem hc₃A 2
  have hc₃sq𝔪 : (⟨c₃ ^ 2, hc₃sqA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    have e1 : (⟨c₃ ^ 2, hc₃sqA⟩ : ↥A) = (⟨c₃, hc₃A⟩ : ↥A) ^ 2 := Subtype.ext (by simp)
    rw [e1]; exact Ideal.pow_mem_of_mem _ hc₃𝔪 2 (by norm_num)
  obtain ⟨Q₂, ⟨hQ₂, hzQ₂⟩, -⟩ := An.existsUnique_evalAt_eq ⟨c₂, hc₂A⟩ hc₂𝔪 hc₂0
    ⟨⟨c₂, hc₂A⟩, hc₂𝔪, by rw [← hπ, ← hc₂]; ring⟩
  obtain ⟨Q₃, ⟨hQ₃, hzQ₃⟩, -⟩ := An.existsUnique_evalAt_eq ⟨c₃, hc₃A⟩ hc₃𝔪 hc₃0
    ⟨⟨c₃ ^ 2, hc₃sqA⟩, hc₃sq𝔪, by rw [← hπ, ← hc₃]; ring⟩
  refine ⟨Q₂, hQ₂, Q₃, hQ₃, ?_⟩
  rw [hzQ₂, hzQ₃]
  show μ c₂ ≠ μ c₃
  intro heq
  have h0 : 0 < μ c₂ := μ.pos hc₂0
  have h23 : μ c₂ ^ 2 = μ c₂ ^ 3 := by rw [hμc₂, ← hμc₃, heq]
  have : μ c₂ ^ 2 * (1 - μ c₂) = 0 := by ring_nf; linarith [h23]
  rcases mul_eq_zero.1 this with h | h
  · exact (pow_pos h0 2).ne' h
  · exact hμc₂1.ne (by linarith)

end IsometryHelpers

end AlgebraicCurve

namespace WideCore
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_annulusComparison_of_attached_at_both_ends_of_certifiedFamily.AlgebraicCurve IsLocalRing"

theorem abv_evalAt_sub_mul_abv_param_le
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    [HasPrincipalDivisors L F]
    {Fbar Fbar' : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [Field Fbar'] [Algebra (ResidueField A) Fbar']
    (μ : AbsoluteValue L ℝ) (hμA : ∀ a : L, a ∈ A ↔ μ a ≤ 1)
    (An An' : Annulus A F) (hdom : An'.dom = An.dom) (hmod : An'.modulus = An.modulus)
    (hmod0 : (An.modulus : L) ≠ 0)
    (htwo : An'.param * An.param = algebraMap L F (An.modulus : L))
    (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar) (hatt : An.IsAttached C x)
    (C' : ComponentChart A F Fbar') (x' : Place (ResidueField A) Fbar') (hatt' : An'.IsAttached C' x')
    (hwide : ∃ Q₁ ∈ An.dom, ∃ Q₂ ∈ An.dom, μ (Q₁.evalAt An.param) ≠ μ (Q₂.evalAt An.param))
    (g : F) (hreg : ∀ R ∈ An.dom, g ∈ R.toValuationSubring) (hgC : g ∈ C.integers) (hgC' : g ∈ C'.integers) :
    ∀ P ∈ An.dom, ∀ Q ∈ An.dom,
      μ (Q.evalAt g - P.evalAt g) * μ (P.evalAt An.param) ≤ μ (Q.evalAt An.param - P.evalAt An.param) := by
  classical
  obtain ⟨-, hzC, hzord, -⟩ := id hatt
  obtain ⟨-, hz'C', hz'ord, -⟩ := id hatt'
  set z := An.param with hz_def
  set z' := An'.param with hz'_def
  set π : L := (An.modulus : L) with hπ
  have hzres0 : C.residue ⟨z, hzC⟩ ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hzord; exact zero_ne_one hzord
  have hz'res0 : C'.residue ⟨z', hz'C'⟩ ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hz'ord; exact zero_ne_one hz'ord
  have hz0 : z ≠ 0 := by
    intro h0; apply hzres0
    have : (⟨z, hzC⟩ : C.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hz'0 : z' ≠ 0 := by
    intro h0; apply hz'res0
    have : (⟨z', hz'C'⟩ : C'.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hdomR : ∀ R ∈ An.dom,
      R.IsRational ∧ z ∈ R.toValuationSubring ∧ z' ∈ R.toValuationSubring ∧
      R.evalAt z ∈ A ∧ R.evalAt z ≠ 0 ∧ μ (R.evalAt z) < 1 ∧ ∃ m : ↥A, m ∈ IsLocalRing.maximalIdeal ↥A ∧ π = R.evalAt z * m := by
    intro R hR
    obtain ⟨hrat, hzR, ⟨hzA, hz𝔪⟩, hzR0, m, hm𝔪, hm⟩ := An.mem_dom R hR
    obtain ⟨-, hz'R, -, -, -⟩ := An'.mem_dom R (hdom ▸ hR)
    exact ⟨hrat, hzR, hz'R, hzA, hzR0, abv_lt_one_of_mem_maximalIdeal_G μ hμA hz𝔪, m, hm𝔪, hm⟩
  have hinj : ∀ R ∈ An.dom, ∀ R' ∈ An.dom, R.evalAt z = R'.evalAt z → R = R' := by
    intro R hR R' hR' hRR'
    obtain ⟨-, -, ⟨haA, ha𝔪⟩, ha0, hm⟩ := An.mem_dom R' hR'
    obtain ⟨P₀, -, huniq⟩ := An.existsUnique_evalAt_eq ⟨R'.evalAt z, haA⟩ ha𝔪 ha0 hm
    exact (huniq R ⟨hR, hRR'⟩).trans (huniq R' ⟨hR', rfl⟩).symm
  have hz_eq : z = algebraMap L F π * z'⁻¹ := by
    rw [← htwo, mul_comm z' z, mul_inv_cancel_right₀ hz'0]
  have hz'inv : z'⁻¹ ∈ C'.integers := inv_mem_of_isUnit_G hz'C' (C'.isUnit_of_residue_ne_zero_G hz'C' hz'res0)
  intro P hP Q hQ
  obtain ⟨hPrat, hzP, -, hbA, hb0, hμb1, mP, hmP𝔪, hπbm⟩ := hdomR P hP
  obtain ⟨hQrat, hzQ, -, -, -, -, -⟩ := hdomR Q hQ
  by_cases hPQ : P = Q
  · subst hPQ; rw [sub_self, sub_self, map_zero, zero_mul]
  have hΔz0 : Q.evalAt z - P.evalAt z ≠ 0 := sub_ne_zero.2 fun h1 => hPQ (hinj P hP Q hQ h1.symm)

  by_cases hg0 : g = 0
  · subst hg0
    have : ∀ R : Place L F, R.evalAt (0 : F) = 0 := by
      intro R
      rw [R.evalAt_of_mem (zero_mem _)]
      have : (⟨(0 : F), zero_mem _⟩ : R.toValuationSubring) = 0 := rfl
      rw [this, map_zero, ← map_zero (algebraMap L R.ResidueField), R.residueInv_algebraMap]
    rw [this, this, sub_self, map_zero, zero_mul]; exact μ.nonneg _
  have hpole : ∀ R ∈ An.dom, 0 ≤ R.ord g := fun R hR => R.ord_nonneg_of_mem_G (hreg R hR)
  have hgPA : P.evalAt g ∈ A := by
    have hg1 : (algebraMap L F (1 : L))⁻¹ * g ∈ C'.integers := by rw [map_one, inv_one, one_mul g]; exact hgC'
    obtain ⟨hle, -⟩ := AlgebraicCurve.Annulus.abv_evalAt_le_max_of_isAttached_both_ends μ hμA
      An An' hdom hmod hmod0 htwo C x hatt C' x' hatt' hwide g hg0 hpole hgC 1 one_ne_zero hg1 P hP
    rw [map_one, max_self] at hle
    exact (hμA _).2 hle

  obtain ⟨cP, hcP⟩ : ∃ cP : L, cP = P.evalAt g := ⟨_, rfl⟩
  obtain ⟨bP, hbP⟩ : ∃ bP : L, bP = P.evalAt z := ⟨_, rfl⟩
  have hcPA : cP ∈ A := hcP ▸ hgPA
  have hbPA : bP ∈ A := hbP ▸ hbA
  have hbP0 : bP ≠ 0 := hbP ▸ hb0
  have hμbP : μ bP < 1 := hbP ▸ hμb1
  have hbP𝔪 : (⟨bP, hbPA⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := mem_maximalIdeal_of_abv_lt_one_G μ hμA hbPA hμbP
  obtain ⟨φ, hφ⟩ : ∃ φ : F, φ = g - algebraMap L F cP := ⟨_, rfl⟩
  obtain ⟨gP, hgP⟩ : ∃ gP : F, gP = z - algebraMap L F bP := ⟨_, rfl⟩
  by_cases hφ0 : φ = 0
  · have hev : Q.evalAt φ = Q.evalAt g - cP := by
      rw [hφ, Q.evalAt_sub_G hQrat (hreg Q hQ) (Q.algebraMap_mem' _), Q.evalAt_algebraMap_G]
    have h0 : Q.evalAt φ = 0 := by
      rw [hφ0, Q.evalAt_of_mem (zero_mem _)]
      have : (⟨(0 : F), zero_mem _⟩ : Q.toValuationSubring) = 0 := rfl
      rw [this, map_zero, ← map_zero (algebraMap L Q.ResidueField), Q.residueInv_algebraMap]
    rw [h0, hcP] at hev
    rw [← hev, map_zero, zero_mul]; exact μ.nonneg _
  obtain ⟨ψ, hψ⟩ : ∃ ψ : F, ψ = φ * gP⁻¹ := ⟨_, rfl⟩

  have hφC : φ ∈ C.integers := by rw [hφ]; exact sub_mem hgC ((C.algebraMap_mem_iff _).2 hcPA)
  have hbPC : algebraMap L F bP ∈ C.integers := (C.algebraMap_mem_iff _).2 hbPA
  have hgPC : gP ∈ C.integers := by rw [hgP]; exact sub_mem hzC hbPC
  have hgPres : C.residue ⟨gP, hgPC⟩ = C.residue ⟨z, hzC⟩ := by
    have e1 : (⟨gP, hgPC⟩ : C.integers) = ⟨z, hzC⟩ - ⟨_, hbPC⟩ := Subtype.ext (by show gP = _; exact hgP)
    rw [e1, map_sub, C.residue_algebraMap_eq_zero_G ⟨bP, hbPA⟩ hbP𝔪 hbPC, sub_zero]
  have hgPres0 : C.residue ⟨gP, hgPC⟩ ≠ 0 := by rw [hgPres]; exact hzres0
  have hgP0 : gP ≠ 0 := by
    intro h0; apply hgPres0
    have : (⟨gP, hgPC⟩ : C.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hgPinv : gP⁻¹ ∈ C.integers := inv_mem_of_isUnit_G hgPC (C.isUnit_of_residue_ne_zero_G hgPC hgPres0)
  have hψC : ψ ∈ C.integers := by rw [hψ]; exact mul_mem hφC hgPinv

  have hnbP0 : (-bP) ≠ 0 := neg_ne_zero.2 hbP0
  have keygP : (algebraMap L F (-bP))⁻¹ * gP = 1 - algebraMap L F (mP : L) * z'⁻¹ := by
    have hbL : algebraMap L F bP ≠ 0 := (map_ne_zero _).2 hbP0
    have hπbm' : π = bP * mP := by rw [hbP]; exact hπbm
    rw [hgP, hz_eq, hπbm', map_mul, map_neg]
    first | (field_simp; done) | (field_simp; ring)
  have hCmC' : algebraMap L F (mP : L) ∈ C'.integers := (C'.algebraMap_mem_iff _).2 mP.2
  have hgPC' : (algebraMap L F (-bP))⁻¹ * gP ∈ C'.integers := by
    rw [keygP]; exact sub_mem (one_mem _) (mul_mem hCmC' hz'inv)
  have hgPres' : C'.residue ⟨_, hgPC'⟩ = 1 := by
    have e1 : (⟨_, hgPC'⟩ : C'.integers) = 1 - ⟨_, hCmC'⟩ * ⟨z'⁻¹, hz'inv⟩ := Subtype.ext keygP
    rw [e1, map_sub, map_one, map_mul, C'.residue_algebraMap_eq_zero_G mP hmP𝔪 hCmC', zero_mul, sub_zero]
  have hgPunit : IsUnit (⟨_, hgPC'⟩ : C'.integers) := C'.isUnit_of_residue_ne_zero_G hgPC' (by rw [hgPres']; exact one_ne_zero)
  have hgP'inv : ((algebraMap L F (-bP))⁻¹ * gP)⁻¹ ∈ C'.integers := inv_mem_of_isUnit_G hgPC' hgPunit
  have hφC' : φ ∈ C'.integers := by rw [hφ]; exact sub_mem hgC' ((C'.algebraMap_mem_iff _).2 hcPA)
  obtain ⟨b, hb⟩ : ∃ b : L, b = (-bP)⁻¹ := ⟨_, rfl⟩
  have hb00 : b ≠ 0 := by rw [hb]; exact inv_ne_zero hnbP0
  have hμb : μ b = (μ (P.evalAt z))⁻¹ := by rw [hb, map_inv₀, AbsoluteValue.map_neg, hbP]
  have hμb1 : 1 < μ b := by rw [hμb]; exact (one_lt_inv₀ (μ.pos hb0)).2 hμb1
  have keyψ : (algebraMap L F b)⁻¹ * ψ = φ * ((algebraMap L F (-bP))⁻¹ * gP)⁻¹ := by
    rw [hψ, hb, map_inv₀]
    have h2 : algebraMap L F (-bP) ≠ 0 := (map_ne_zero _).2 hnbP0
    field_simp
  have hψC' : (algebraMap L F b)⁻¹ * ψ ∈ C'.integers := by rw [keyψ]; exact mul_mem hφC' hgP'inv

  have hψ0 : ψ ≠ 0 := by rw [hψ]; exact mul_ne_zero hφ0 (inv_ne_zero hgP0)
  have hψpole : ∀ X ∈ An.dom, 0 ≤ X.ord ψ := by
    intro X hX
    obtain ⟨hXrat, hzX, -⟩ := hdomR X hX
    have hφX : φ ∈ X.toValuationSubring := by rw [hφ]; exact sub_mem (hreg X hX) (X.algebraMap_mem' _)
    have hgX : gP ∈ X.toValuationSubring := by rw [hgP]; exact sub_mem hzX (X.algebraMap_mem' _)
    rw [hψ, X.ord_mul hφ0 (inv_ne_zero hgP0), Place.ord_inv]
    by_cases hXP : X = P
    · subst hXP
      have hg1 : X.ord gP = 1 := by rw [hgP, hbP]; exact An.ord_param_sub X hX
      have hφ1 : 0 < X.ord φ := by
        apply X.ord_pos_of_evalAt_eq_zero_G hXrat hφX hφ0
        rw [hφ, X.evalAt_sub_G hXrat (hreg X hX) (X.algebraMap_mem' _), X.evalAt_algebraMap_G, hcP, sub_self]
      omega
    · have hg00 : X.ord gP = 0 := by
        apply X.ord_eq_zero_of_evalAt_ne_zero_G hgX
        rw [hgP, X.evalAt_sub_G hXrat hzX (X.algebraMap_mem' _), X.evalAt_algebraMap_G, hbP, sub_ne_zero]
        exact fun h1 => hXP (hinj X hX P hP h1)
      have := X.ord_nonneg_of_mem_G hφX
      omega
  obtain ⟨hMle, -⟩ := AlgebraicCurve.Annulus.abv_evalAt_le_max_of_isAttached_both_ends μ hμA
    An An' hdom hmod hmod0 htwo C x hatt C' x' hatt' hwide ψ hψ0 hψpole hψC b hb00 hψC' Q hQ
  rw [max_eq_right hμb1.le, hμb] at hMle

  have hψQ : ψ ∈ Q.toValuationSubring := Q.mem_of_ord_nonneg_G hψ0 (hψpole Q hQ)
  have hgPQ : gP ∈ Q.toValuationSubring := by rw [hgP]; exact sub_mem hzQ (Q.algebraMap_mem' _)
  have hφev : Q.evalAt φ = Q.evalAt g - P.evalAt g := by
    rw [hφ, Q.evalAt_sub_G hQrat (hreg Q hQ) (Q.algebraMap_mem' _), Q.evalAt_algebraMap_G, hcP]
  have hgPev : Q.evalAt gP = Q.evalAt z - P.evalAt z := by
    rw [hgP, Q.evalAt_sub_G hQrat hzQ (Q.algebraMap_mem' _), Q.evalAt_algebraMap_G, hbP]
  have hfac : Q.evalAt g - P.evalAt g = Q.evalAt ψ * (Q.evalAt z - P.evalAt z) := by
    rw [← hφev, ← hgPev, ← Q.evalAt_mul_G hQrat hψQ hgPQ, hψ, inv_mul_cancel_right₀ hgP0]
  rw [hfac, map_mul]
  calc μ (Q.evalAt ψ) * μ (Q.evalAt z - P.evalAt z) * μ (P.evalAt z)
      ≤ (μ (P.evalAt z))⁻¹ * μ (Q.evalAt z - P.evalAt z) * μ (P.evalAt z) := by
        apply mul_le_mul_of_nonneg_right _ (μ.nonneg _)
        exact mul_le_mul_of_nonneg_right hMle (μ.nonneg _)
    _ = μ (Q.evalAt z - P.evalAt z) := by
        have := (μ.pos hb0).ne'
        field_simp

end WideCore

namespace WideCore
p2m_open "AlgebraicCurve P2MW.S_ModularCurve_annulusComparison_of_attached_at_both_ends_of_certifiedFamily.AlgebraicCurve IsLocalRing"

theorem wide_hUP
    {F : Type*} [Field F] [Algebra (AlgebraicClosure ℚ) F] [HasPrincipalDivisors (AlgebraicClosure ℚ) F]
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {Fbar Fbar' : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    [Field Fbar'] [Algebra (ResidueField A) Fbar']
    (p : ℕ) (hp : p.Prime)
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1)
    (An An' : Annulus A F) (hdom : An'.dom = An.dom) (hmod : An'.modulus = An.modulus)
    (hmod0 : (An.modulus : AlgebraicClosure ℚ) ≠ 0)
    (htwo : An'.param * An.param = algebraMap (AlgebraicClosure ℚ) F (An.modulus : AlgebraicClosure ℚ))
    (C : ComponentChart A F Fbar) (x : Place (ResidueField A) Fbar) (hatt : An.IsAttached C x)
    (C' : ComponentChart A F Fbar') (x' : Place (ResidueField A) Fbar') (hatt' : An'.IsAttached C' x')
    (g : F) (n : ℕ)
    (hint : (algebraMap (AlgebraicClosure ℚ) F ((p : AlgebraicClosure ℚ) ^ n))⁻¹ * g ∈ C.integers)
    (hnear : g ∈ C'.integers) (hreg : ∀ R ∈ An.dom, g ∈ R.toValuationSubring) :
    ∀ P ∈ An.dom, ∀ Q ∈ An.dom,
      μ (P.evalAt g - Q.evalAt g) * μ (P.evalAt An'.param) ≤ μ (P.evalAt An'.param - Q.evalAt An'.param) := by
  have hp0 : (p : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpA : (p : AlgebraicClosure ℚ) ∈ A := natCast_mem A p
  have hmod0c : ((An'.modulus : AlgebraicClosure ℚ)) ≠ 0 := by rw [hmod]; exact hmod0
  have htwoc : An.param * An'.param = algebraMap (AlgebraicClosure ℚ) F ((An'.modulus : AlgebraicClosure ℚ)) := by
    rw [mul_comm, htwo, hmod]
  have hwidec := Annulus.exists_mem_dom_abv_evalAt_param_ne_G μ hμA An' hmod0c
  have hfarC : g ∈ C.integers := by
    have hpnC : algebraMap (AlgebraicClosure ℚ) F ((p : AlgebraicClosure ℚ) ^ n) ∈ C.integers :=
      (C.algebraMap_mem_iff _).2 (pow_mem hpA n)
    have e1 : g = algebraMap (AlgebraicClosure ℚ) F ((p : AlgebraicClosure ℚ) ^ n)
        * ((algebraMap (AlgebraicClosure ℚ) F ((p : AlgebraicClosure ℚ) ^ n))⁻¹ * g) := by
      rw [← mul_assoc, mul_inv_cancel₀ ((map_ne_zero _).2 (pow_ne_zero _ hp0)), one_mul g]
    rw [e1]; exact mul_mem hpnC hint
  intro P hP Q hQ
  have h1 := abv_evalAt_sub_mul_abv_param_le μ hμA An' An hdom.symm hmod.symm hmod0c htwoc C' x' hatt' C x hatt hwidec
    g (fun R hR => hreg R (hdom ▸ hR)) hnear hfarC P (hdom ▸ hP) Q (hdom ▸ hQ)
  rw [← neg_sub, AbsoluteValue.map_neg] at h1
  rw [← neg_sub (P.evalAt An'.param) (Q.evalAt An'.param), AbsoluteValue.map_neg] at h1
  exact h1

end WideCore

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

theorem solution (N : ℕ) [NeZero N]
    {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (p : ℕ) (hp : p.Prime)
    (hpN : p ∣ N) (hp2 : ¬ p ^ 2 ∣ N) :
    ∀ (k₀ : ℕ) (t : Fin r → modularFunctionFieldBar N)
      (M Minv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)) (nexp : Fin r → ℕ) (Bl : ℕ),
    (∀ l : Fin r, (l : ℕ) = 0 → t l = 1) →
    (∀ i, s i = ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (M i j) * t j) →
    Minv * M = 1 → M * Minv = 1 →
    (∀ l : Fin r, (l : ℕ) = 0 → nexp l = 0) → (∀ l : Fin r, 1 ≤ (l : ℕ) → 1 ≤ nexp l) →
    (∀ l, nexp l ≤ k₀) →
    ∃ (Cc : ℝ), ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∀ {Fbar Fbar' : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
      [Field Fbar'] [Algebra (ResidueField ↥A) Fbar']
      (C : ComponentChart A (modularFunctionFieldBar N) Fbar)
      (C' : ComponentChart A (modularFunctionFieldBar N) Fbar')
      (x : Place (ResidueField ↥A) Fbar) (x' : Place (ResidueField ↥A) Fbar')
      (An An' : Annulus A (modularFunctionFieldBar N)),
    An.IsAttached C x → An'.IsAttached C' x' →
    (An'.dom = An.dom ∧ An'.modulus = An.modulus ∧
      ((An.modulus : AlgebraicClosure ℚ)) ≠ 0 ∧
      An'.param * An.param
        = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((An.modulus : AlgebraicClosure ℚ))) →
    ∀ (πx : AlgebraicClosure ℚ), πx ≠ 0 → (∃ hmem : πx ∈ A, (⟨πx, hmem⟩ : A) ∈ maximalIdeal A) →
    (∃ u : AlgebraicClosure ℚ, u ∈ A ∧ u⁻¹ ∈ A ∧
      ((An.modulus : AlgebraicClosure ℚ)) * u = πx) →
    (∃ a : AlgebraicClosure ℚ, a ∈ A ∧ (p : AlgebraicClosure ℚ) ^ k₀ = πx * a) →
    (∃ b : AlgebraicClosure ℚ, b ∈ A ∧ πx = (p : AlgebraicClosure ℚ) * b) →

    ∀ (U Uinv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)) (f : Fin r → modularFunctionFieldBar N),
    (∀ i j, U i j ∈ A ∧ Uinv i j ∈ A) → Uinv * U = 1 ∧ U * Uinv = 1 →
    (∀ l, f l = ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (U l j) * t j) →

    ∀ (w : ℕ), 2 ≤ w →
    (∃ u : AlgebraicClosure ℚ, u ∈ A ∧ u⁻¹ ∈ A ∧
      ((An.modulus : AlgebraicClosure ℚ)) = (p : AlgebraicClosure ℚ) ^ w * u) →

    (∃ hint : ∀ l : Fin r, (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
        ((p : AlgebraicClosure ℚ) ^ nexp l))⁻¹ * f l ∈ C.integers,
      (∀ l : Fin r, C.residue ⟨_, hint l⟩ ≠ 0) ∧
      (∀ l : Fin r, x.ord (C.residue ⟨_, hint l⟩) = -((nexp l / w : ℕ) : ℤ)) ∧
      LinearIndependent (ResidueField ↥A) (fun l => C.residue ⟨_, hint l⟩)) →

    (∀ i j, (p : AlgebraicClosure ℚ) ^ Bl * M i j ∈ A ∧ (p : AlgebraicClosure ℚ) ^ Bl * Minv i j ∈ A) →

    (∀ l : Fin r, ∃ h : f l ∈ C'.integers,
      C'.residue ⟨f l, h⟩ ≠ 0 ∧ (1 ≤ (l : ℕ) → 1 ≤ x'.ord (C'.residue ⟨f l, h⟩))) →
    (∃ l : Fin r, 1 ≤ (l : ℕ) ∧ ∃ h : f l ∈ C'.integers, x'.ord (C'.residue ⟨f l, h⟩) = 1) →

    (∀ l : Fin r, (l : ℕ) = 0 → f l = 1) →
    (∀ R ∈ An.dom, ∀ l : Fin r, 1 ≤ (l : ℕ) →
      f l ∈ R.toValuationSubring ∧
        ∃ h : R.evalAt (f l) ∈ A, (⟨R.evalAt (f l), h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A) →

    ((∃ l : Fin r, 1 ≤ (l : ℕ) ∧ (∃ h : f l ∈ C'.integers, x'.ord (C'.residue ⟨f l, h⟩) = 1) ∧ nexp l = w) ∨
     (∃ m₁ m₂ : Fin r, 1 ≤ (m₁ : ℕ) ∧ 1 ≤ (m₂ : ℕ) ∧
        (∃ h : f m₁ ∈ C'.integers, x'.ord (C'.residue ⟨f m₁, h⟩) = 1) ∧
        (∃ h : f m₂ ∈ C'.integers, x'.ord (C'.residue ⟨f m₂, h⟩) = 1) ∧
        nexp m₁ < nexp m₂ ∧ nexp m₂ < w ∧ nexp m₁ + w ≤ 2 * nexp m₂ ∧
        (∃ (h : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              ((p : AlgebraicClosure ℚ) ^ nexp m₁))⁻¹ * f m₁ ∈ C.integers) (c : ResidueField ↥A),
          x.ord (C.residue ⟨_, h⟩ - algebraMap (ResidueField ↥A) Fbar c) = 1))) →

    (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ P ∈ An.dom, ∀ Q ∈ An.dom, P ≠ Q →
        (∃ i j, evalVec s P i * evalVec s Q j ≠ evalVec s P j * evalVec s Q i) →
        |prox μ (evalVec s P) (evalVec s Q)
            + Real.log (μ (P.evalAt An.param - Q.evalAt An.param))|
          ≤ Cc * (-Real.log (μ ((An.modulus : AlgebraicClosure ℚ))))) := by
  classical
  intro k₀ t M Minv nexp Bl ht0 hsM hM1 hM2 hn0 hn1 hnk
  refine ⟨4 * (Bl : ℝ) + 2, ?_⟩
  intro A hA Fbar Fbar' _ _ _ _ C C' x x' An An' hatt hatt' htwoEnd πx hπ0 hπmax hπu hπk hπp U Uinv f hUA hUU hf w hw2 hwu
    hW23 hBl hW5 hpiv hf0 hsmall hW8 μ hμ hμA P hP Q hQ hPQ hnonprop
  obtain ⟨hdom, hmod, hmod0, htwo⟩ := htwoEnd
  have hp0 : (p : (AlgebraicClosure ℚ)) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  have hr0 : 0 < r := by obtain ⟨l, -, -⟩ := hpiv; exact Fin.pos l
  set o : Fin r := ⟨0, hr0⟩ with ho

  set L : ℝ := -Real.log (μ ((An.modulus : (AlgebraicClosure ℚ)))) with hL_def
  have hPd' : P ∈ An'.dom := by rw [hdom]; exact hP
  have hQd' : Q ∈ An'.dom := by rw [hdom]; exact hQ
  obtain ⟨hPrat, hz'P, ⟨hz'PA, -⟩, hz'P0, mP, hmP, hπP⟩ := An'.mem_dom P hPd'
  obtain ⟨hQrat, hz'Q, ⟨hz'QA, -⟩, hz'Q0, mQ, hmQ, hπQ⟩ := An'.mem_dom Q hQd'
  obtain ⟨-, hzP, ⟨hzPA, -⟩, hzP0, -⟩ := An.mem_dom P hP
  obtain ⟨-, hzQ, ⟨hzQA, -⟩, hzQ0, -⟩ := An.mem_dom Q hQ
  have hmodpos : 0 < μ ((An.modulus : (AlgebraicClosure ℚ))) := μ.pos hmod0
  have hmodlt : ∀ R ∈ An'.dom, μ ((An.modulus : (AlgebraicClosure ℚ))) < μ (R.evalAt An'.param) := by
    intro R hR
    obtain ⟨-, -, -, hz0, mR, hmR, hπR⟩ := An'.mem_dom R hR
    rw [← hmod, hπR, map_mul]
    have hμm : μ (mR : (AlgebraicClosure ℚ)) < 1 := abv_lt_one_of_mem_maximalIdeal_vs μ hμA mR.2 (by simpa using hmR)
    calc μ (R.evalAt An'.param) * μ (mR : (AlgebraicClosure ℚ)) < μ (R.evalAt An'.param) * 1 := mul_lt_mul_of_pos_left hμm (μ.pos hz0)
      _ = _ := mul_one _
  have hz'lt1 : ∀ R ∈ An'.dom, μ (R.evalAt An'.param) < 1 := by
    intro R hR
    obtain ⟨-, -, ⟨hA', hmax⟩, -⟩ := An'.mem_dom R hR
    exact abv_lt_one_of_mem_maximalIdeal_vs μ hμA hA' hmax
  have hmodlt1 : μ ((An.modulus : (AlgebraicClosure ℚ))) < 1 := (hmodlt P hPd').trans (hz'lt1 P hPd')
  have hLpos : 0 < L := neg_pos.2 (Real.log_neg hmodpos hmodlt1)

  have hμmod_le_p : μ ((An.modulus : (AlgebraicClosure ℚ))) ≤ μ (p : (AlgebraicClosure ℚ)) := by
    obtain ⟨u, huA, huinvA, hu⟩ := hπu
    obtain ⟨b, hbA, hb⟩ := hπp
    have : (An.modulus : (AlgebraicClosure ℚ)) = (p : (AlgebraicClosure ℚ)) * b * u⁻¹ := by
      have hu0 : u ≠ 0 := by rintro rfl; rw [mul_zero] at hu; exact hπ0 hu.symm
      field_simp; rw [hu, hb]
    rw [this, map_mul, map_mul]
    calc μ (p : (AlgebraicClosure ℚ)) * μ b * μ u⁻¹ ≤ μ (p : (AlgebraicClosure ℚ)) * 1 * 1 := by
          gcongr
          · exact (hμA _).1 hbA
          · exact (hμA _).1 huinvA
      _ = μ (p : (AlgebraicClosure ℚ)) := by ring
  have hμp0 : 0 < μ (p : (AlgebraicClosure ℚ)) := μ.pos hp0
  have hμp1 : μ (p : (AlgebraicClosure ℚ)) ≤ 1 := (hμA _).1 (natCast_mem A p)
  have hlamL : -Real.log (μ (p : (AlgebraicClosure ℚ))) ≤ L := by
    rw [hL_def]; exact neg_le_neg (Real.log_le_log hmodpos hμmod_le_p)
  have hlam0 : 0 ≤ -Real.log (μ (p : (AlgebraicClosure ℚ))) := by linarith [Real.log_nonpos hμp0.le hμp1]

  have hΔ' : P.evalAt An'.param ≠ Q.evalAt An'.param := by
    intro heq
    obtain ⟨-, -, ⟨hQA', hQmax⟩, hQ0', mQ', hmQ', hπQ'⟩ := An'.mem_dom Q hQd'
    obtain ⟨R, -, huniq⟩ := An'.existsUnique_evalAt_eq ⟨Q.evalAt An'.param, hQA'⟩ hQmax hQ0' ⟨mQ', hmQ', hπQ'⟩
    exact hPQ ((huniq P ⟨hPd', heq⟩).trans (huniq Q ⟨hQd', rfl⟩).symm)
  have hΔ'pos : 0 < μ (P.evalAt An'.param - Q.evalAt An'.param) := μ.pos (sub_ne_zero.2 hΔ')

  have hfreg : ∀ (R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), R ∈ An.dom → ∀ i, f i ∈ R.toValuationSubring := by
    intro R hR i
    by_cases hi : 1 ≤ (i : ℕ)
    · exact (hsmall R hR i hi).1
    · have : i = o := Fin.ext (by push_neg at hi; simp [ho]; omega)
      rw [hf0 i (by rw [this])]; exact one_mem _
  have hfo : f o = 1 := hf0 o rfl
  set xr : Fin r → (AlgebraicClosure ℚ) := fun i => P.evalAt (f i * (f o)⁻¹) with hxr
  set yr : Fin r → (AlgebraicClosure ℚ) := fun i => Q.evalAt (f i * (f o)⁻¹) with hyr
  have hxeval : ∀ i, xr i = P.evalAt (f i) := fun i => by simp [hxr, hfo]
  have hyeval : ∀ i, yr i = Q.evalAt (f i) := fun i => by simp [hyr, hfo]
  have hxo : xr o = 1 := by rw [hxeval, hfo, Place.evalAt_one]
  have hyo : yr o = 1 := by rw [hyeval, hfo, Place.evalAt_one]
  have hxA : ∀ i, xr i ∈ A := by
    intro i; rw [hxeval]
    by_cases hi : 1 ≤ (i : ℕ)
    · exact (hsmall P hP i hi).2.1
    · have : i = o := Fin.ext (by push_neg at hi; simp [ho]; omega)
      rw [this, hfo, Place.evalAt_one]; exact one_mem _
  have hyA : ∀ i, yr i ∈ A := by
    intro i; rw [hyeval]
    by_cases hi : 1 ≤ (i : ℕ)
    · exact (hsmall Q hQ i hi).2.1
    · have : i = o := Fin.ext (by push_neg at hi; simp [ho]; omega)
      rw [this, hfo, Place.evalAt_one]; exact one_mem _
  have hxle : ∀ i, μ (xr i) ≤ 1 := fun i => (hμA _).1 (hxA i)
  have hyle : ∀ i, μ (yr i) ≤ 1 := fun i => (hμA _).1 (hyA i)

  obtain ⟨hint, hresF, hordF, hLI⟩ := hW23
  have hUP : ∀ i : Fin r, μ (xr i - yr i) * μ (P.evalAt An'.param) ≤ μ (P.evalAt An'.param - Q.evalAt An'.param) := by
    intro i
    by_cases hi : 1 ≤ (i : ℕ)
    · obtain ⟨hnear, -⟩ := hW5 i
      rw [hxeval, hyeval]
      exact WideCore.wide_hUP p hp μ hμA An An' hdom hmod hmod0 htwo C x hatt C' x' hatt' (f i) (nexp i) (hint i) hnear
        (fun R hR => (hsmall R hR i hi).1) P hP Q hQ
    · have : i = o := Fin.ext (by push_neg at hi; simp [ho]; omega)
      rw [this, hxo, hyo, sub_self, map_zero, zero_mul]; exact μ.nonneg _

  have hmod0' : ((An'.modulus : ↥A) : (AlgebraicClosure ℚ)) ≠ 0 := by rw [hmod]; exact hmod0
  have htwo' : An.param * An'.param = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((An'.modulus : ↥A) : (AlgebraicClosure ℚ)) := by
    rw [mul_comm, hmod]; exact htwo
  have hμmod : μ ((An.modulus : (AlgebraicClosure ℚ))) = μ (p : (AlgebraicClosure ℚ)) ^ w := by
    obtain ⟨u, huA, huiA, hu⟩ := hwu
    have hu0 : u ≠ 0 := by rintro rfl; rw [mul_zero] at hu; exact hmod0 hu
    have hμu : μ u = 1 := by
      apply le_antisymm ((hμA _).1 huA)
      have h1 : μ u⁻¹ ≤ 1 := (hμA _).1 huiA
      rwa [map_inv₀, inv_le_one₀ (μ.pos hu0)] at h1
    rw [hu, map_mul, map_pow, hμu, mul_one]
  have hμmod' : μ (((An'.modulus : ↥A) : (AlgebraicClosure ℚ))) = μ (p : (AlgebraicClosure ℚ)) ^ w := by rw [hmod]; exact hμmod
  have hμp_lt1 : μ (p : (AlgebraicClosure ℚ)) < 1 := by
    by_contra hge; push_neg at hge
    have : 1 ≤ μ ((An.modulus : (AlgebraicClosure ℚ))) := by rw [hμmod]; exact one_le_pow₀ hge
    exact absurd hmodlt1 (not_lt.2 this)
  have hwpos : 1 ≤ w := by omega
  have hmaxI : ∀ {a : (AlgebraicClosure ℚ)} (ha : a ∈ A), μ a < 1 → (⟨a, ha⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A := by
    intro a ha hlt
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; intro hunit
    have := abv_eq_one_of_isUnit_vs μ hμA ha hunit; linarith

  have hwide' : ∃ Q₁ ∈ An'.dom, ∃ Q₂ ∈ An'.dom, μ (Q₁.evalAt An'.param) ≠ μ (Q₂.evalAt An'.param) := by
    obtain ⟨u, huA, huiA, hu⟩ := hwu
    obtain ⟨ρ, hρ⟩ := IsAlgClosed.exists_pow_nat_eq (p : (AlgebraicClosure ℚ)) two_pos
    have hρ0 : ρ ≠ 0 := by rintro rfl; rw [zero_pow two_ne_zero] at hρ; exact hp0 hρ.symm
    have hμρ : μ ρ ^ 2 = μ (p : (AlgebraicClosure ℚ)) := by rw [← map_pow, hρ]
    have hμρ1 : μ ρ < 1 := by
      by_contra hge; push_neg at hge
      have : 1 ≤ μ ρ ^ 2 := one_le_pow₀ hge
      rw [hμρ] at this; exact absurd hμp_lt1 (not_lt.2 this)
    have hρA : ρ ∈ A := (hμA _).2 hμρ1.le
    have hpA' : (p : (AlgebraicClosure ℚ)) ∈ A := natCast_mem A p
    have hval : ∀ (c : (AlgebraicClosure ℚ)) (hcA : c ∈ A), c ≠ 0 → μ c < 1 →
        (∃ m : (AlgebraicClosure ℚ), m ∈ A ∧ μ m < 1 ∧ ((An'.modulus : ↥A) : (AlgebraicClosure ℚ)) = c * m) →
        ∃ Q ∈ An'.dom, Q.evalAt An'.param = c := by
      intro c hcA hc0 hclt hm
      obtain ⟨m, hmA, hmlt, hcm⟩ := hm
      obtain ⟨Q, ⟨hQd, hQv⟩, -⟩ := An'.existsUnique_evalAt_eq ⟨c, hcA⟩ (hmaxI hcA hclt) hc0 ⟨⟨m, hmA⟩, hmaxI hmA hmlt, hcm⟩
      exact ⟨Q, hQd, hQv⟩
    have hmodeq : ((An'.modulus : ↥A) : (AlgebraicClosure ℚ)) = (p : (AlgebraicClosure ℚ)) ^ w * u := by rw [hmod]; exact hu
    have hμu : μ u ≤ 1 := (hμA _).1 huA
    obtain ⟨Q₁, hQ₁, hQ₁v⟩ := hval (p : (AlgebraicClosure ℚ)) hpA' hp0 hμp_lt1 ⟨(p : (AlgebraicClosure ℚ)) ^ (w - 1) * u,
      mul_mem (pow_mem hpA' _) huA,
      lt_of_le_of_lt (by rw [map_mul, map_pow]; exact mul_le_of_le_one_right (pow_nonneg (μ.nonneg _) _) hμu)
        (pow_lt_one₀ (μ.nonneg _) hμp_lt1 (by omega)),
      by rw [hmodeq, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hwpos]⟩
    obtain ⟨Q₂, hQ₂, hQ₂v⟩ := hval ((p : (AlgebraicClosure ℚ)) * ρ) (mul_mem hpA' hρA) (mul_ne_zero hp0 hρ0)
      (by rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_left (μ.nonneg _) hμp_lt1 hμρ1.le)
      ⟨(p : (AlgebraicClosure ℚ)) ^ (w - 2) * ρ * u, mul_mem (mul_mem (pow_mem hpA' _) hρA) huA,
        lt_of_le_of_lt (by
          rw [map_mul, map_mul, map_pow]
          calc μ (p : (AlgebraicClosure ℚ)) ^ (w - 2) * μ ρ * μ u ≤ 1 * μ ρ * 1 := by
                gcongr; exact pow_le_one₀ (μ.nonneg _) hμp_lt1.le
            _ = μ ρ := by ring) hμρ1,
        by
          have h2 : (p : (AlgebraicClosure ℚ)) ^ w = (p : (AlgebraicClosure ℚ)) ^ (w - 2) * (p : (AlgebraicClosure ℚ)) * (p : (AlgebraicClosure ℚ)) := by
            rw [← pow_succ, ← pow_succ]; congr 1; omega
          rw [hmodeq, h2, ← hρ]; ring⟩
    refine ⟨Q₁, hQ₁, Q₂, hQ₂, ?_⟩
    rw [hQ₁v, hQ₂v, map_mul]
    intro heq
    have : μ ρ = 1 := by
      have h0 : μ (p : (AlgebraicClosure ℚ)) ≠ 0 := hμp0.ne'
      field_simp at heq; linarith
    exact absurd this hμρ1.ne
  have hsmallres : ∀ (R : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), R ∈ An.dom → ∀ (l : Fin r), 1 ≤ (l : ℕ) →
      ∀ (hA' : R.evalAt (f l) ∈ A), IsLocalRing.residue ↥A ⟨R.evalAt (f l), hA'⟩ = 0 := by
    intro R hR l hl hA'
    obtain ⟨-, h, hm⟩ := hsmall R hR l hl
    exact (IsLocalRing.residue_eq_zero_iff _).2 hm
  have hpoleF : ∀ (l : Fin r), 1 ≤ (l : ℕ) → ∀ R ∈ An'.dom, 0 ≤ R.ord (f l) := by
    intro l hl R hR; rw [hdom] at hR; exact Place.ord_nonneg_of_mem' R (hsmall R hR l hl).1

  have hshift : ∀ (l : Fin r) (hl : 1 ≤ (l : ℕ)) (hC'l : f l ∈ C'.integers) (hordl : x'.ord (C'.residue ⟨f l, hC'l⟩) = 1)
      (Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hQ : Q ∈ An.dom),
      ∃ (hfQA : Q.evalAt (f l) ∈ A) (hhC' : f l - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (Q.evalAt (f l)) ∈ C'.integers),
        C'.residue ⟨_, hhC'⟩ = C'.residue ⟨f l, hC'l⟩ ∧ C'.residue ⟨_, hhC'⟩ ≠ 0 ∧ x'.ord (C'.residue ⟨_, hhC'⟩) = 1 ∧
        (∀ R ∈ An'.dom, 0 ≤ R.ord (f l - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (Q.evalAt (f l)))) ∧
        (∀ R ∈ An'.dom, R.evalAt (f l - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (Q.evalAt (f l))) = R.evalAt (f l) - Q.evalAt (f l)) := by
    intro l hl hC'l hordl Q hQ
    have hfQA : Q.evalAt (f l) ∈ A := (hsmall Q hQ l hl).2.1
    have hresl : C'.residue ⟨f l, hC'l⟩ ≠ 0 := by obtain ⟨h', hres', -⟩ := hW5 l; exact hres'
    have hcC' : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (Q.evalAt (f l)) ∈ C'.integers := (C'.algebraMap_mem_iff _).2 hfQA
    have hhC' : f l - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (Q.evalAt (f l)) ∈ C'.integers := sub_mem hC'l hcC'
    have hres : C'.residue ⟨_, hhC'⟩ = C'.residue ⟨f l, hC'l⟩ := by
      have e1 : (⟨_, hhC'⟩ : C'.integers) = ⟨f l, hC'l⟩ - ⟨_, hcC'⟩ := Subtype.ext rfl
      have e2 : (⟨_, hcC'⟩ : C'.integers) = ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((⟨Q.evalAt (f l), hfQA⟩ : ↥A) : (AlgebraicClosure ℚ)),
          (C'.algebraMap_mem_iff _).2 (⟨Q.evalAt (f l), hfQA⟩ : ↥A).2⟩ := rfl
      rw [e1, map_sub, e2, C'.residue_algebraMap, hsmallres Q hQ l hl hfQA, map_zero, sub_zero]
    refine ⟨hfQA, hhC', hres, by rw [hres]; exact hresl, by rw [hres]; exact hordl, fun R hR => ?_, fun R hR => ?_⟩
    · have hR' : R ∈ An.dom := by rw [← hdom]; exact hR
      exact Place.ord_nonneg_of_mem' R (sub_mem (hsmall R hR' l hl).1 (R.algebraMap_mem' _))
    · have hR' : R ∈ An.dom := by rw [← hdom]; exact hR
      obtain ⟨hRrat, -⟩ := An.mem_dom R hR'
      rw [Place.evalAt_sub' R hRrat (hsmall R hR' l hl).1 (R.algebraMap_mem' _), Place.evalAt_algebraMap']

  have key : ∀ (P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), P ∈ An.dom → Q ∈ An.dom →
      μ (P.evalAt An'.param) ≤ μ (Q.evalAt An'.param) →
      ∃ i : Fin r, μ (P.evalAt An'.param - Q.evalAt An'.param) ≤ μ (P.evalAt (f i) - Q.evalAt (f i)) := by
    intro P Q hP hQ hPQle
    have hPd' : P ∈ An'.dom := by rw [hdom]; exact hP
    have hQd' : Q ∈ An'.dom := by rw [hdom]; exact hQ
    obtain ⟨hQrat, hz'Q, ⟨hz'QA, hz'Qmax⟩, hz'Q0, -⟩ := An'.mem_dom Q hQd'
    obtain ⟨hPrat, hz'P, -, hz'P0, -⟩ := An'.mem_dom P hPd'
    rcases hW8 with ⟨l, hl1, ⟨hC'l, hordl⟩, hnl⟩ | ⟨m₁, m₂, hm₁, hm₂, ⟨hC'1, hord1⟩, ⟨hC'2, hord2⟩, hn12, hn2w, hnum, ⟨hC1, c, hunr⟩⟩
    ·
      have hresl : C'.residue ⟨f l, hC'l⟩ ≠ 0 := by obtain ⟨h', hres', -⟩ := hW5 l; exact hres'
      have hord'l : x.ord (C.residue ⟨_, hint l⟩) = -1 := by
        rw [hordF l, hnl, Nat.div_self (by omega)]; norm_num
      obtain ⟨D, hD0, hDdom, hDord, hDsum, -⟩ :=
        AlgebraicCurve.Annulus.sum_ord_mul_log_abv_param_eq_of_isAttached_both_ends μ hμA
          An' An hdom.symm hmod.symm hmod0' htwo' C' x' hatt' C x hatt hwide'
          (f l) hC'l hresl ((p : (AlgebraicClosure ℚ)) ^ nexp l) (pow_ne_zero _ hp0) (pow_mem (natCast_mem A p) _)
          (hint l) (hresF l) (hpoleF l hl1)
      rw [hordl, hord'l] at hDsum
      have hDz : ∀ R, D R = 0 := by
        intro R; by_contra hne
        have hpos : 0 < D R := lt_of_le_of_ne (hD0 R) (Ne.symm hne)
        have hsumZ : (D.sum fun _ m => m : ℤ) = ∑ Q ∈ D.support, D Q := rfl
        have : 0 < (D.sum fun _ m => m : ℤ) := by
          rw [hsumZ]; exact Finset.sum_pos' (fun P _ => hD0 P) ⟨R, Finsupp.mem_support_iff.2 hne, hpos⟩
        omega
      have hzf : ∀ R ∈ An'.dom, R.ord (f l) = 0 := fun R hR => by rw [← hDord R hR, hDz R]
      have hatt'' := hatt'
      obtain ⟨-, hz'C, hz'ord, hlaw⟩ := hatt''
      have habs : ∀ R ∈ An'.dom, μ (R.evalAt (f l)) = μ (R.evalAt An'.param) := by
        intro R hR
        obtain ⟨-, -, -, hz'R0, -⟩ := An'.mem_dom R hR
        obtain ⟨hm, hu⟩ := hlaw (f l) hC'l hresl hzf R hR
        have e1 : R.evalAt (f l) * (R.evalAt An'.param) ^ (-(x'.ord (C'.residue ⟨f l, hC'l⟩)))
            = R.evalAt (f l) * (R.evalAt An'.param)⁻¹ := by rw [hordl, zpow_neg_one]
        have hm' : R.evalAt (f l) * (R.evalAt An'.param)⁻¹ ∈ A := e1 ▸ hm
        have hu' : IsUnit (⟨_, hm'⟩ : ↥A) := by
          have : (⟨_, hm⟩ : ↥A) = ⟨_, hm'⟩ := Subtype.ext e1
          rw [← this]; exact hu
        have h1 := abv_eq_one_of_isUnit_vs μ hμA hm' hu'
        rw [map_mul, map_inv₀] at h1
        have hz : μ (R.evalAt An'.param) ≠ 0 := (μ.pos hz'R0).ne'
        field_simp at h1; linarith
      obtain ⟨hfQA, hhC', hres, hres0, hord1, hhpole, hval⟩ := hshift l hl1 hC'l hordl Q hQ
      set fQ : (AlgebraicClosure ℚ) := Q.evalAt (f l) with hfQ_def
      have hμfQ : μ fQ = μ (Q.evalAt An'.param) := habs Q hQd'
      have hfQ0 : fQ ≠ 0 := by
        intro h0; rw [h0, map_zero] at hμfQ; exact (μ.pos hz'Q0).ne' hμfQ.symm

      have hμpn : μ ((p : (AlgebraicClosure ℚ)) ^ nexp l) < μ fQ := by
        rw [hμfQ, map_pow, hnl, ← hμmod]; exact hmodlt Q hQd'
      have hsA : (p : (AlgebraicClosure ℚ)) ^ nexp l * fQ⁻¹ ∈ A := (hμA _).2 (by
        rw [map_mul, map_inv₀]; exact (mul_inv_le_iff₀ (μ.pos hfQ0)).2 (by rw [one_mul]; exact hμpn.le))
      have hsres : IsLocalRing.residue ↥A ⟨_, hsA⟩ = 0 := (IsLocalRing.residue_eq_zero_iff _).2 (hmaxI hsA (by
        rw [map_mul, map_inv₀]; exact (mul_inv_lt_iff₀ (μ.pos hfQ0)).2 (by rw [one_mul]; exact hμpn)))
      have hαfQ : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) fQ ≠ 0 := (map_ne_zero _).2 hfQ0
      have hαpn : algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((p : (AlgebraicClosure ℚ)) ^ nexp l) ≠ 0 := (map_ne_zero _).2 (pow_ne_zero _ hp0)
      have hident : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (-fQ))⁻¹ * (f l - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) fQ)
          = 1 - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((p : (AlgebraicClosure ℚ)) ^ nexp l * fQ⁻¹) * ((algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((p : (AlgebraicClosure ℚ)) ^ nexp l))⁻¹ * f l) := by
        rw [map_neg, map_mul, map_inv₀]
        field_simp
        ring
      have hC'' : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (-fQ))⁻¹ * (f l - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) fQ) ∈ C.integers := by
        rw [hident]; exact sub_mem (one_mem _) (mul_mem ((C.algebraMap_mem_iff _).2 hsA) (hint l))
      have hres'' : C.residue ⟨_, hC''⟩ = 1 := by
        have e1 : (⟨_, hC''⟩ : C.integers) = 1 - ⟨algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((⟨_, hsA⟩ : ↥A) : (AlgebraicClosure ℚ)),
            (C.algebraMap_mem_iff _).2 (⟨_, hsA⟩ : ↥A).2⟩ * ⟨_, hint l⟩ := Subtype.ext hident
        rw [e1, map_sub, map_one, map_mul, C.residue_algebraMap, hsres, map_zero, zero_mul, sub_zero]
      have hres''0 : C.residue ⟨_, hC''⟩ ≠ 0 := by rw [hres'']; exact one_ne_zero
      have hord'' : x.ord (C.residue ⟨_, hC''⟩) = 0 := by rw [hres'']; exact Place.ord_one _
      have hiso := AlgebraicCurve.Annulus.abv_evalAt_sub_eq_abv_param_sub_of_ord_residue_eq_one_of_abv_le μ hμ hμA An' An hdom.symm hmod.symm hmod0' htwo' C' x' hatt' C x hatt hwide'
        (f l - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) fQ) hhC' hres0 hord1 (-fQ) (neg_ne_zero.2 hfQ0) (neg_mem hfQA) hC'' hres''0 hord'' hhpole
        P hPd' Q hQd' (by rw [AbsoluteValue.map_neg, hμfQ])
      refine ⟨l, le_of_eq ?_⟩
      rw [← hiso, hval P hPd', hval Q hQd', sub_sub_sub_cancel_right]
    ·
      have hres1 : C'.residue ⟨f m₁, hC'1⟩ ≠ 0 := by obtain ⟨h', hres', -⟩ := hW5 m₁; exact hres'
      have hres2 : C'.residue ⟨f m₂, hC'2⟩ ≠ 0 := by obtain ⟨h', hres', -⟩ := hW5 m₂; exact hres'
      have hn1w : nexp m₁ < w := hn12.trans hn2w
      have hord'1 : x.ord (C.residue ⟨_, hint m₁⟩) = 0 := by rw [hordF m₁, Nat.div_eq_of_lt hn1w]; norm_num
      have hord'2 : x.ord (C.residue ⟨_, hint m₂⟩) = 0 := by rw [hordF m₂, Nat.div_eq_of_lt hn2w]; norm_num
      by_cases hA2 : μ (p : (AlgebraicClosure ℚ)) ^ nexp m₂ ≤ μ (Q.evalAt An'.param)
      ·
        have hiso := AlgebraicCurve.Annulus.abv_evalAt_sub_eq_abv_param_sub_of_ord_residue_eq_one_of_abv_le μ hμ hμA An' An hdom.symm hmod.symm hmod0' htwo' C' x' hatt' C x hatt hwide'
          (f m₂) hC'2 hres2 hord2 ((p : (AlgebraicClosure ℚ)) ^ nexp m₂) (pow_ne_zero _ hp0) (pow_mem (natCast_mem A p) _)
          (hint m₂) (hresF m₂) hord'2 (hpoleF m₂ hm₂) P hPd' Q hQd' (by rw [map_pow]; exact hA2)
        exact ⟨m₂, le_of_eq hiso.symm⟩
      ·
        push_neg at hA2
        have hresC1 : C.residue ⟨_, hC1⟩ ≠ 0 := hresF m₁
        have hordC1 : x.ord (C.residue ⟨_, hC1⟩) = 0 := hord'1
        have hQlt : μ (Q.evalAt An'.param) < μ ((p : (AlgebraicClosure ℚ)) ^ nexp m₁) := by
          rw [map_pow]; exact hA2.trans (pow_lt_pow_right_of_lt_one₀ hμp0 hμp_lt1 hn12)
        obtain ⟨Qs, hQs, hprod, hmir⟩ := AlgebraicCurve.Annulus.exists_abv_evalAt_sub_mul_eq_of_ord_residue_eq_one_of_abv_lt μ hμ hμA An' An hdom.symm hmod.symm hmod0' htwo' C' x' hatt' C x hatt hwide'
          (f m₁) hC'1 hres1 hord1 ((p : (AlgebraicClosure ℚ)) ^ nexp m₁) (pow_ne_zero _ hp0) (pow_mem (natCast_mem A p) _)
          hC1 hresC1 hordC1 (hpoleF m₁ hm₁) c hunr Q hQd' hQlt
        have hmirP := hmir P hPd'

        have hQsd : Qs ∈ An.dom := by rw [← hdom]; exact hQs
        obtain ⟨-, -, -, hz'Qs0, -⟩ := An'.mem_dom Qs hQs
        obtain ⟨-, -, -, hzQs0, -⟩ := An.mem_dom Qs hQsd
        obtain ⟨-, -, -, hzP0, -⟩ := An.mem_dom P hP
        have hpw : μ (p : (AlgebraicClosure ℚ)) ^ (2 * nexp m₂) ≤ μ (p : (AlgebraicClosure ℚ)) ^ (nexp m₁ + w) :=
          pow_le_pow_of_le_one hμp0.le hμp_lt1.le hnum
        have hkey : μ (P.evalAt An'.param) < μ (Qs.evalAt An'.param) := by
          have h1 : μ (P.evalAt An'.param) * μ (Q.evalAt An'.param) < μ (p : (AlgebraicClosure ℚ)) ^ (nexp m₁ + w) := by
            calc μ (P.evalAt An'.param) * μ (Q.evalAt An'.param)
                ≤ μ (Q.evalAt An'.param) * μ (Q.evalAt An'.param) := by gcongr
              _ < μ (p : (AlgebraicClosure ℚ)) ^ nexp m₂ * μ (p : (AlgebraicClosure ℚ)) ^ nexp m₂ :=
                  mul_lt_mul'' hA2 hA2 (μ.nonneg _) (μ.nonneg _)
              _ = μ (p : (AlgebraicClosure ℚ)) ^ (2 * nexp m₂) := by rw [← pow_add]; ring_nf
              _ ≤ _ := hpw
          have h2 : μ (Q.evalAt An'.param) * μ (Qs.evalAt An'.param) = μ (p : (AlgebraicClosure ℚ)) ^ (nexp m₁ + w) := by
            rw [hprod, map_pow, hμmod', ← pow_add]
          rw [← h2, mul_comm (μ (Q.evalAt An'.param))] at h1
          exact lt_of_mul_lt_mul_right h1 (μ.nonneg _)

        have hzprod : ∀ R ∈ An.dom, μ (R.evalAt An.param) * μ (R.evalAt An'.param) = μ ((An.modulus : (AlgebraicClosure ℚ))) := by
          intro R hR
          obtain ⟨hRrat, hzR, -, -, -⟩ := An.mem_dom R hR
          obtain ⟨-, hz'R, -, -, -⟩ := An'.mem_dom R (by rw [hdom]; exact hR)
          have h1 : R.evalAt (An'.param * An.param) = R.evalAt An'.param * R.evalAt An.param := Place.evalAt_mul' R hRrat hz'R hzR
          rw [htwo, Place.evalAt_algebraMap'] at h1
          rw [← map_mul, mul_comm, ← h1]
        have hzlt : μ (Qs.evalAt An.param) < μ (P.evalAt An.param) := by
          have e1 := hzprod P hP
          have e2 := hzprod Qs hQsd
          have hmpos := hmodpos
          by_contra hge; push_neg at hge
          have : μ (P.evalAt An.param) * μ (P.evalAt An'.param) < μ (Qs.evalAt An.param) * μ (Qs.evalAt An'.param) :=
            mul_lt_mul' hge hkey (μ.nonneg _) (μ.pos hzQs0)
          rw [e1, e2] at this; exact lt_irrefl _ this
        have hzdiff : μ (P.evalAt An.param - Qs.evalAt An.param) = μ (P.evalAt An.param) := abv_sub_eq_of_abv_lt μ hμ hzlt
        refine ⟨m₁, ?_⟩
        rw [hzdiff] at hmirP

        have hzQs : 0 < μ (Qs.evalAt An.param) := μ.pos hzQs0
        nlinarith [hmirP, hzlt, μ.nonneg (P.evalAt An'.param - Q.evalAt An'.param), μ.nonneg (P.evalAt (f m₁) - Q.evalAt (f m₁))]
  have hLOW : ∃ i : Fin r, μ (P.evalAt An'.param - Q.evalAt An'.param) ≤ μ (xr i - yr i) := by
    rcases le_total (μ (P.evalAt An'.param)) (μ (Q.evalAt An'.param)) with hle | hle
    · obtain ⟨i, hi⟩ := key P Q hP hQ hle
      exact ⟨i, by rw [hxeval, hyeval]; exact hi⟩
    · obtain ⟨i, hi⟩ := key Q P hQ hP hle
      refine ⟨i, ?_⟩
      rw [hxeval, hyeval, AbsoluteValue.map_sub μ (P.evalAt (f i)), AbsoluteValue.map_sub μ (P.evalAt An'.param)]
      exact hi

  have hpf := AlgebraicCurve.prox_eq_neg_log_iSup_sub_of_chart μ hμ xr yr o hxo hyo hxle hyle
  set S : ℝ := ⨆ i, μ (xr i - yr i) with hS
  have hSbdd := Finite.bddAbove_range (fun i : Fin r => μ (xr i - yr i))
  obtain ⟨i0, hi0⟩ := hLOW
  have hSge : μ (P.evalAt An'.param - Q.evalAt An'.param) ≤ S := hi0.trans (le_ciSup hSbdd i0)
  have hSpos : 0 < S := hΔ'pos.trans_le hSge
  have hSle : S ≤ μ (P.evalAt An'.param - Q.evalAt An'.param) / μ (P.evalAt An'.param) := by
    haveI : Nonempty (Fin r) := ⟨o⟩
    refine ciSup_le fun i => ?_
    rw [le_div_iff₀ (μ.pos hz'P0)]; exact hUP i

  have hpf_up : prox μ xr yr + Real.log (μ (P.evalAt An'.param - Q.evalAt An'.param)) ≤ 0 := by
    rw [hpf]; have := Real.log_le_log hΔ'pos hSge; linarith
  have hpf_lo : Real.log (μ (P.evalAt An'.param)) ≤ prox μ xr yr + Real.log (μ (P.evalAt An'.param - Q.evalAt An'.param)) := by
    rw [hpf]
    have := Real.log_le_log hSpos hSle
    rw [Real.log_div hΔ'pos.ne' (μ.pos hz'P0).ne'] at this
    linarith

  have hzz : ∀ R ∈ An.dom, R.evalAt An.param * R.evalAt An'.param = (An.modulus : (AlgebraicClosure ℚ)) := by
    intro R hR
    obtain ⟨hRrat, hzR, -, -, -⟩ := An.mem_dom R hR
    obtain ⟨-, hz'R, -, -, -⟩ := An'.mem_dom R (by rw [hdom]; exact hR)
    have h1 : R.evalAt (An'.param * An.param) = R.evalAt An'.param * R.evalAt An.param := Place.evalAt_mul' R hRrat hz'R hzR
    rw [htwo, Place.evalAt_algebraMap'] at h1
    rw [mul_comm]; exact h1.symm
  have hΔz : P.evalAt An.param - Q.evalAt An.param
      = (An.modulus : (AlgebraicClosure ℚ)) * (Q.evalAt An'.param - P.evalAt An'.param) * ((P.evalAt An'.param)⁻¹ * (Q.evalAt An'.param)⁻¹) := by
    have e1 := hzz P hP
    have e2 := hzz Q hQ
    field_simp
    linear_combination (Q.evalAt An'.param) * e1 - (P.evalAt An'.param) * e2
  have hlogΔ : Real.log (μ (P.evalAt An.param - Q.evalAt An.param))
      = Real.log (μ ((An.modulus : (AlgebraicClosure ℚ)))) + Real.log (μ (P.evalAt An'.param - Q.evalAt An'.param))
        - Real.log (μ (P.evalAt An'.param)) - Real.log (μ (Q.evalAt An'.param)) := by
    rw [hΔz, map_mul, map_mul, map_mul, map_inv₀, map_inv₀, ← μ.map_neg (Q.evalAt An'.param - _), neg_sub,
      Real.log_mul (mul_ne_zero hmodpos.ne' hΔ'pos.ne') (mul_ne_zero (inv_ne_zero (μ.pos hz'P0).ne') (inv_ne_zero (μ.pos hz'Q0).ne')),
      Real.log_mul hmodpos.ne' hΔ'pos.ne', Real.log_mul (inv_ne_zero (μ.pos hz'P0).ne') (inv_ne_zero (μ.pos hz'Q0).ne'),
      Real.log_inv, Real.log_inv]
    ring
  have hlogz'P : -L < Real.log (μ (P.evalAt An'.param)) ∧ Real.log (μ (P.evalAt An'.param)) < 0 :=
    ⟨by rw [hL_def, neg_neg]; exact Real.log_lt_log hmodpos (hmodlt P hPd'), Real.log_neg (μ.pos hz'P0) (hz'lt1 P hPd')⟩
  have hlogz'Q : -L < Real.log (μ (Q.evalAt An'.param)) ∧ Real.log (μ (Q.evalAt An'.param)) < 0 :=
    ⟨by rw [hL_def, neg_neg]; exact Real.log_lt_log hmodpos (hmodlt Q hQd'), Real.log_neg (μ.pos hz'Q0) (hz'lt1 Q hQd')⟩
  have hcoreAbs : |prox μ xr yr + Real.log (μ (P.evalAt An.param - Q.evalAt An.param))| ≤ 2 * L := by
    rw [hlogΔ, abs_le]
    have hLm : Real.log (μ ((An.modulus : (AlgebraicClosure ℚ)))) = -L := by rw [hL_def, neg_neg]
    rw [hLm]
    constructor <;> nlinarith [hpf_up, hpf_lo, hlogz'P.1, hlogz'P.2, hlogz'Q.1, hlogz'Q.2]

  set M2 : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ) := M * Uinv with hM2_def
  set M2inv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ) := U * Minv with hM2inv_def
  have hM2_1 : M2inv * M2 = 1 := by
    rw [hM2_def, hM2inv_def, Matrix.mul_assoc, ← Matrix.mul_assoc Minv, hM1, Matrix.one_mul, hUU.2]
  have hM2_2 : M2 * M2inv = 1 := by
    rw [hM2_def, hM2inv_def, Matrix.mul_assoc, ← Matrix.mul_assoc Uinv, hUU.1, Matrix.one_mul, hM2]
  have htf : ∀ j, t j = ∑ k, Uinv j k • f k := by
    intro j
    simp_rw [hf, Finset.smul_sum, ← Algebra.smul_def, smul_smul]
    rw [Finset.sum_comm]
    have : ∀ k, (∑ i, Uinv j i * U i k) • t k = (if j = k then (1 : (AlgebraicClosure ℚ)) else 0) • t k := by
      intro k
      have h1 := congrFun (congrFun hUU.1 j) k
      simp only [Matrix.mul_apply, Matrix.one_apply] at h1
      rw [h1]
    simp_rw [← Finset.sum_smul, this, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hsM2 : ∀ i, s i = ∑ k, M2 i k • f k := by
    intro i
    rw [hsM i]
    simp_rw [← Algebra.smul_def, htf, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_smul, hM2_def, Matrix.mul_apply]
  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hfne : ∀ i, f i ≠ 0 := by
    intro i h0
    obtain ⟨h, hres, -⟩ := hW5 i
    apply hres
    have : (⟨f i, h⟩ : C'.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hM2B : ∀ i j, (p : (AlgebraicClosure ℚ)) ^ Bl * M2 i j ∈ A ∧ (p : (AlgebraicClosure ℚ)) ^ Bl * M2inv i j ∈ A := by
    intro i j
    constructor
    · rw [hM2_def, Matrix.mul_apply, Finset.mul_sum]
      exact sum_mem fun k _ => by rw [← mul_assoc]; exact mul_mem (hBl i k).1 (hUA k j).2
    · rw [hM2inv_def, Matrix.mul_apply, Finset.mul_sum]
      exact sum_mem fun k _ => by rw [mul_left_comm]; exact mul_mem (hUA i k).1 (hBl k j).2
  obtain ⟨dP, hdP0, hdP⟩ := AlgebraicCurve.exists_evalVec_eq_smul_mulVec_of_eq_sum_smul hr0 s f hs0 hfne M2 M2inv hM2_1 hM2_2 hsM2
    P hPrat o (fun j => by rw [hfo, inv_one, mul_one]; exact hfreg P hP j)
  obtain ⟨dQ, hdQ0, hdQ⟩ := AlgebraicCurve.exists_evalVec_eq_smul_mulVec_of_eq_sum_smul hr0 s f hs0 hfne M2 M2inv hM2_1 hM2_2 hsM2
    Q hQrat o (fun j => by rw [hfo, inv_one, mul_one]; exact hfreg Q hQ j)
  obtain ⟨i', j', hij⟩ := hnonprop
  have hminor : ∀ i j, evalVec s P i * evalVec s Q j - evalVec s P j * evalVec s Q i
      = dP * dQ * (M2.mulVec xr i * M2.mulVec yr j - M2.mulVec xr j * M2.mulVec yr i) := by
    intro i j; rw [hdP, hdQ]; simp only [Pi.smul_apply, smul_eq_mul]; ring
  have hMm : M2.mulVec xr i' * M2.mulVec yr j' - M2.mulVec xr j' * M2.mulVec yr i' ≠ 0 := by
    intro h0; apply hij; exact sub_eq_zero.1 (by rw [hminor, h0, mul_zero])
  have hsupM : (⨆ q : Fin r × Fin r, μ (M2.mulVec xr q.1 * M2.mulVec yr q.2 - M2.mulVec xr q.2 * M2.mulVec yr q.1)) ≠ 0 :=
    ((μ.pos hMm).trans_le (le_ciSup (Finite.bddAbove_range
      (fun q : Fin r × Fin r => μ (M2.mulVec xr q.1 * M2.mulVec yr q.2 - M2.mulVec xr q.2 * M2.mulVec yr q.1))) (i', j'))).ne'
  have hrowminor : ∃ i j, xr i * yr j - xr j * yr i ≠ 0 := by
    by_contra hall; push_neg at hall; apply hMm
    rw [minor_mulVec_D]; exact Finset.sum_eq_zero fun q _ => by rw [hall q.1 q.2, mul_zero]
  obtain ⟨i1, j1, hm1⟩ := hrowminor
  have hx0 : xr ≠ 0 := by
    intro h0; have := congrFun h0 o
    rw [hxo] at this; exact one_ne_zero this
  have hy0 : yr ≠ 0 := by
    intro h0; have := congrFun h0 o
    rw [hyo] at this; exact one_ne_zero this
  set β : ℝ := (μ (p : (AlgebraicClosure ℚ)))⁻¹ ^ Bl with hβ
  have hβ1 : 1 ≤ β := one_le_pow₀ ((one_le_inv₀ hμp0).2 hμp1)
  have hlogβ : Real.log β = (Bl : ℝ) * (-Real.log (μ (p : (AlgebraicClosure ℚ)))) := by rw [hβ, Real.log_pow, Real.log_inv]
  have hentry : ∀ m : (AlgebraicClosure ℚ), (p : (AlgebraicClosure ℚ)) ^ Bl * m ∈ A → μ m ≤ β := by
    intro m hm
    have h1 : μ ((p : (AlgebraicClosure ℚ)) ^ Bl * m) ≤ 1 := (hμA _).1 hm
    rw [map_mul, map_pow] at h1
    have hpB : 0 < μ (p : (AlgebraicClosure ℚ)) ^ Bl := pow_pos hμp0 _
    rw [hβ, inv_pow]
    calc μ m = (μ (p : (AlgebraicClosure ℚ)) ^ Bl * μ m) * (μ (p : (AlgebraicClosure ℚ)) ^ Bl)⁻¹ := by field_simp
      _ ≤ 1 * (μ (p : (AlgebraicClosure ℚ)) ^ Bl)⁻¹ := mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 hpB.le)
      _ = (μ (p : (AlgebraicClosure ℚ)) ^ Bl)⁻¹ := one_mul _
  have hMβ : ∀ i j, μ (M2 i j) ≤ β := fun i j => hentry _ (hM2B i j).1
  have hMβ' : ∀ i j, μ (M2inv i j) ≤ β := fun i j => hentry _ (hM2B i j).2
  have hprox1 : prox μ (evalVec s P) (evalVec s Q) = prox μ (M2.mulVec xr) (M2.mulVec yr) := by
    rw [hdP, hdQ]; exact AlgebraicCurve.prox_smul_smul μ _ _ hdP0 hdQ0 hsupM
  have hLk := AlgebraicCurve.abs_prox_mulVec_mulVec_sub_prox_le_of_abv_le μ hμ M2 M2inv hM2_1 β hβ1 hMβ hMβ' xr yr hx0 hy0 ⟨i1, j1, hm1⟩
  rw [hlogβ, ← hprox1] at hLk

  calc |prox μ (evalVec s P) (evalVec s Q) + Real.log (μ (P.evalAt An.param - Q.evalAt An.param))|
      = |(prox μ (evalVec s P) (evalVec s Q) - prox μ xr yr)
          + (prox μ xr yr + Real.log (μ (P.evalAt An.param - Q.evalAt An.param)))| := by ring_nf
    _ ≤ |prox μ (evalVec s P) (evalVec s Q) - prox μ xr yr|
          + |prox μ xr yr + Real.log (μ (P.evalAt An.param - Q.evalAt An.param))| := abs_add_le _ _
    _ ≤ 4 * ((Bl : ℝ) * -Real.log (μ (p : (AlgebraicClosure ℚ)))) + 2 * L := add_le_add hLk hcoreAbs
    _ ≤ (4 * (Bl : ℝ) + 2) * L := by nlinarith [hlamL, hlam0, hLpos.le]
    _ = (4 * (Bl : ℝ) + 2) * (-Real.log (μ ((An.modulus : (AlgebraicClosure ℚ))))) := by rw [hL_def]

end S_ModularCurve_annulusComparison_of_attached_at_both_ends_of_certifiedFamily
end P2MW
export P2MW.S_ModularCurve_annulusComparison_of_attached_at_both_ends_of_certifiedFamily (solution)
