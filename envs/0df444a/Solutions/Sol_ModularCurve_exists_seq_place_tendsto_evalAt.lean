-- Prove2me | solution 1 for ModularCurve.exists_seq_place_tendsto_evalAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/80c4df5f-b1f6-56d6-81b1-bcb6f3f8717c

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_ModularCurve_ComplexPlaceDictionary
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_exists_complexPlaceDictionary
import Theorems.Thm_ModularCurve_ComplexPlaceDictionary_exists_analyticAt_eventuallyEq_realize
import Theorems.Thm_AlgebraicCurve_Place_evalAt_map_eq_of_comap_eq
import Theorems.Thm_ModularCurve_tendsto_realize_atImInfty_coeff_zero
import Theorems.Thm_ModularCurve_exists_analyticAt_realize_eq_qParam_zpow_mul
import Theorems.Thm_ModularCurve_evalAt_qInftyPlaceBar_eq_coeff_zero
import Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_full
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import Theorems.Thm_ModularCurve_coeffMap_mem_laurentBaseChange_of_ringHom
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_iff_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_ModularCurve_exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange
import Theorems.Thm_ModularCurve_realize_eq_div
import Theorems.Thm_AlgebraicCurve_Place_exists_place_laurentBaseChange_of_deg_eq_one
import Theorems.Thm_ModularCurve_ComplexPlaceDictionary_exists_pt_eq_of_mem
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_seq_place_tendsto_evalAt
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply"

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 80000

set_option autoImplicit false

open UpperHalfPlane Filter AlgebraicCurve ModularCurve
open scoped Topology

noncomputable section

namespace APPR

abbrev FB (N : ℕ) : Type := ↥(modularFunctionFieldBar N)

abbrev FC (N : ℕ) : Type := ↥(laurentBaseChange ℂ (modularFunctionFieldFull N))

def jB (N : ℕ) [NeZero N] : FB N :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩

def jC (N : ℕ) [NeZero N] : FC N :=
  ⟨coeffEmb ℂ jq, coeffEmb_mem_laurentBaseChange ℂ (jq_mem_full N)⟩

def phi (N : ℕ) (σ : AlgebraicClosure ℚ →+* ℂ) : FB N →+* FC N where
  toFun y := ⟨coeffMap σ (y : LaurentSeries (AlgebraicClosure ℚ)),
    coeffMap_mem_laurentBaseChange_of_ringHom σ (modularFunctionFieldFull N) y.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

variable {N : ℕ}

@[scoped simp] theorem coe_phi (σ : AlgebraicClosure ℚ →+* ℂ) (y : FB N) :
    ((phi N σ y : FC N) : LaurentSeries ℂ) = coeffMap σ (y : LaurentSeries (AlgebraicClosure ℚ)) := rfl

theorem coeff_phi (σ : AlgebraicClosure ℚ →+* ℂ) (y : FB N) (m : ℤ) :
    ((phi N σ y : FC N) : LaurentSeries ℂ).coeff m = σ ((y : LaurentSeries (AlgebraicClosure ℚ)).coeff m) :=
  rfl

theorem phi_algebraMap (σ : AlgebraicClosure ℚ →+* ℂ) (c : AlgebraicClosure ℚ) :
    phi N σ (algebraMap (AlgebraicClosure ℚ) (FB N) c) = algebraMap ℂ (FC N) (σ c) := by
  apply Subtype.ext
  show coeffMap σ (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c) =
    algebraMap ℂ (LaurentSeries ℂ) (σ c)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem phi_ne_zero (σ : AlgebraicClosure ℚ →+* ℂ) {y : FB N} (hy : y ≠ 0) : phi N σ y ≠ 0 :=
  (map_ne_zero_iff _ (phi N σ).injective).mpr hy

theorem order_phi (σ : AlgebraicClosure ℚ →+* ℂ) (y : FB N) :
    ((phi N σ y : FC N) : LaurentSeries ℂ).order = (y : LaurentSeries (AlgebraicClosure ℚ)).order := by
  by_cases hy : y = 0
  · subst hy; simp
  have hy' : (y : LaurentSeries (AlgebraicClosure ℚ)) ≠ 0 := by
    rwa [Ne, ZeroMemClass.coe_eq_zero]
  have hpy : ((phi N σ y : FC N) : LaurentSeries ℂ) ≠ 0 := by
    rw [Ne, ZeroMemClass.coe_eq_zero]; exact phi_ne_zero σ hy
  apply le_antisymm
  · apply HahnSeries.order_le_of_coeff_ne_zero
    rw [coe_phi, coeffMap_coeff, map_ne_zero_iff _ σ.injective, ← HahnSeries.leadingCoeff_eq]
    exact HahnSeries.leadingCoeff_ne_zero.mpr hy'
  · apply HahnSeries.order_le_of_coeff_ne_zero
    have h := HahnSeries.leadingCoeff_ne_zero.mpr hpy
    rw [HahnSeries.leadingCoeff_eq, coe_phi, coeffMap_coeff, map_ne_zero_iff _ σ.injective] at h
    exact h

theorem phi_jB [NeZero N] (σ : AlgebraicClosure ℚ →+* ℂ) : phi N σ (jB N) = jC N := by
  apply Subtype.ext
  show coeffMap σ (coeffEmb (AlgebraicClosure ℚ) jq) = coeffEmb ℂ jq
  rw [coeffEmb, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) jq

theorem mem_cuspInftyBar_iff [NeZero N] (y : FB N) :
    y ∈ (cuspInftyBar N).toValuationSubring ↔ 0 ≤ (y : LaurentSeries (AlgebraicClosure ℚ)).order := by
  unfold cuspInftyBar
  rw [qInftyPlaceBar_toValuationSubring, mem_qIntegersBar_iff]
  rfl

theorem evalAt_cuspInftyBar [NeZero N] {y : FB N} (hy : y ∈ (cuspInftyBar N).toValuationSubring) :
    (cuspInftyBar N).evalAt y = (y : LaurentSeries (AlgebraicClosure ℚ)).coeff 0 := by
  have hy' := (mem_cuspInftyBar_iff y).mp hy
  unfold cuspInftyBar
  exact ModularCurve.evalAt_qInftyPlaceBar_eq_coeff_zero (AlgebraicClosure ℚ) _ y hy'

theorem jB_notMem [NeZero N] : jB N ∉ (cuspInftyBar N).toValuationSubring := by
  unfold cuspInftyBar
  rw [qInftyPlaceBar_toValuationSubring]
  exact notMem_qIntegersBar_of_order_eq_neg_one (order_coeffEmb_jq (AlgebraicClosure ℚ))

theorem order_jC [NeZero N] : ((jC N : FC N) : LaurentSeries ℂ).order = -1 :=
  order_coeffEmb_jq ℂ

theorem jC_ne_zero [NeZero N] : jC N ≠ 0 := by
  intro h
  have := order_jC (N := N)
  rw [h] at this
  simp at this

theorem coeff_jC_neg_one [NeZero N] : ((jC N : FC N) : LaurentSeries ℂ).coeff (-1) = 1 := by
  show (coeffEmb ℂ jq).coeff (-1) = 1
  rw [coeffEmb_coeff, coeff_jq_neg_one, map_one]

theorem hasFPowerSeriesAt_cuspFunction (N : ℕ) {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) :
    HasFPowerSeriesAt (cuspFunction 1 (f : ℍ → ℂ)) (qExpansionFormalMultilinearSeries 1 f) 0 := by
  have hΓ : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N).map
      (Matrix.SpecialLinearGroup.mapGL ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples _
  haveI : Fact (IsCusp OnePoint.infty ((CongruenceSubgroup.Gamma0 N).map
      (Matrix.SpecialLinearGroup.mapGL ℝ))) := ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  exact (UpperHalfPlane.hasFPowerSeries_cuspFunction f
    (c := fun m => PowerSeries.coeff m (qExpansion 1 (f : ℍ → ℂ))) one_pos
    (ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ) fun τ =>
      UpperHalfPlane.hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
        (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ).hasFPowerSeriesAt

theorem exists_forall_ne_zero_of_le_im (N : ℕ) {k : ℤ}
    (h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh0 : h ≠ 0) :
    ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im → (h : ℍ → ℂ) τ ≠ 0 := by
  have hΓ : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N).map
      (Matrix.SpecialLinearGroup.mapGL ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples _
  have hP := hasFPowerSeriesAt_cuspFunction N h
  have hph : qExpansionFormalMultilinearSeries 1 h ≠ 0 := by
    intro h0
    apply hh0
    rw [← ModularForm.qExpansion_eq_zero_iff one_pos hΓ]
    ext m
    rw [← UpperHalfPlane.qExpansionFormalMultilinearSeries_coeff, h0]
    simp [FormalMultilinearSeries.coeff]
  have hloc := hP.locally_ne_zero hph
  obtain ⟨ε, hε, hεne⟩ : ∃ ε > 0, ∀ q : ℂ, q ≠ 0 → ‖q‖ < ε → cuspFunction 1 (h : ℍ → ℂ) q ≠ 0 := by
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hloc
    obtain ⟨ε, hε, hh⟩ := hloc
    exact ⟨ε, hε, fun q hq0 hq => hh (by simpa using hq) hq0⟩
  refine ⟨1 - Real.log ε / (2 * Real.pi), fun τ hτ => ?_⟩
  have hexp : Real.exp (-2 * Real.pi * (1 - Real.log ε / (2 * Real.pi))) < ε := by
    calc Real.exp (-2 * Real.pi * (1 - Real.log ε / (2 * Real.pi)))
        = Real.exp (-2 * Real.pi) * ε := by
          rw [show -2 * Real.pi * (1 - Real.log ε / (2 * Real.pi)) = -2 * Real.pi + Real.log ε by
            field_simp; ring, Real.exp_add, Real.exp_log hε]
      _ < ε := (mul_lt_iff_lt_one_left hε).mpr (Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos]))
  rw [← SlashInvariantFormClass.eq_cuspFunction h τ hΓ one_ne_zero]
  refine hεne _ (by first | exact Complex.exp_ne_zero _ | simp [Function.Periodic.qParam]) ?_
  rw [Function.Periodic.norm_qParam, div_one, UpperHalfPlane.coe_im]
  exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hτ (by linarith [Real.pi_pos]))).trans_lt hexp

theorem realize_zero [NeZero N] (τ : ℍ) : realize N (0 : LaurentSeries ℂ) τ = 0 := by
  have h := ModularCurve.realize_eq_div N (0 : ModularForm (CongruenceSubgroup.Gamma0 N) 0) 1 0
    (by simp [UpperHalfPlane.qExpansion_zero]) τ (by simp)
  simpa using h

theorem chart [NeZero N] (x : FC N) (hx : x ≠ 0) :
    ∃ (G : ℂ → ℂ) (A : ℝ), 0 < A ∧ G 0 = (x : LaurentSeries ℂ).coeff (x : LaurentSeries ℂ).order ∧
      (∀ q : ℂ, ‖q‖ ≤ Real.exp (-2 * Real.pi * A) → AnalyticAt ℂ G q ∧ G q ≠ 0) ∧
      ∀ z : ℂ, A ≤ z.im → realize N (x : LaurentSeries ℂ) (ofComplex z) =
        Function.Periodic.qParam 1 z ^ (x : LaurentSeries ℂ).order * G (Function.Periodic.qParam 1 z) := by
  obtain ⟨G, hG, hG0, hev⟩ := ModularCurve.exists_analyticAt_realize_eq_qParam_zpow_mul N x hx
  obtain ⟨A₁, hA₁⟩ := (UpperHalfPlane.atImInfty_mem _).mp hev
  have hGne : G 0 ≠ 0 := by
    rw [hG0, ← HahnSeries.leadingCoeff_eq]
    exact HahnSeries.leadingCoeff_ne_zero.mpr (by rwa [Ne, ZeroMemClass.coe_eq_zero])
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, ∀ q : ℂ, ‖q‖ < ε → AnalyticAt ℂ G q ∧ G q ≠ 0 := by
    have h := hG.eventually_analyticAt.and (hG.continuousAt.eventually_ne hGne)
    obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.mp h
    exact ⟨ε, hε, fun q hq => h (by simpa using hq)⟩
  set A : ℝ := max (max A₁ 1) (1 - Real.log ε / (2 * Real.pi)) with hA_def
  have hA1 : 1 ≤ A := (le_max_right _ _).trans (le_max_left _ _)
  have hAA₁ : A₁ ≤ A := (le_max_left _ _).trans (le_max_left _ _)
  have hexp : Real.exp (-2 * Real.pi * A) < ε := by
    have hB : 1 - Real.log ε / (2 * Real.pi) ≤ A := le_max_right _ _
    have hle : -2 * Real.pi * A ≤ -2 * Real.pi * (1 - Real.log ε / (2 * Real.pi)) :=
      mul_le_mul_of_nonpos_left hB (by linarith [Real.pi_pos])
    calc Real.exp (-2 * Real.pi * A)
        ≤ Real.exp (-2 * Real.pi * (1 - Real.log ε / (2 * Real.pi))) := Real.exp_le_exp.mpr hle
      _ = Real.exp (-2 * Real.pi) * ε := by
          rw [show -2 * Real.pi * (1 - Real.log ε / (2 * Real.pi)) = -2 * Real.pi + Real.log ε by
            field_simp; ring, Real.exp_add, Real.exp_log hε]
      _ < ε := (mul_lt_iff_lt_one_left hε).mpr (Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos]))
  refine ⟨G, A, by linarith, hG0, fun q hq => hball q (hq.trans_lt hexp), fun z hz => ?_⟩
  have hz0 : 0 < z.im := by linarith
  have hc : ((ofComplex z : ℍ) : ℂ) = z := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz0]; try rfl
  have h := hA₁ (ofComplex z) (by rw [← UpperHalfPlane.coe_im, hc]; exact hAA₁.trans hz)
  simp only [Set.mem_setOf_eq] at h
  rw [hc] at h
  exact h

theorem regular_high [NeZero N] (x : FC N) (hx : x ≠ 0) (h0 : 0 ≤ (x : LaurentSeries ℂ).order) :
    ∃ A : ℝ, ∀ τ : ℍ, A ≤ τ.im →
      realize N (x : LaurentSeries ℂ) τ ≠ 0 ∧
      ContinuousAt (fun z : ℍ => realize N (x : LaurentSeries ℂ) z) τ ∧
      ContinuousAt (fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ) := by
  obtain ⟨G, A, hApos, hG0, hball, hchart⟩ := chart x hx
  obtain ⟨e, he⟩ := Int.eq_ofNat_of_zero_le h0
  have hqc : Continuous (Function.Periodic.qParam 1) := by
    first
      | exact Function.Periodic.continuous_qParam
      | exact Function.Periodic.differentiable_qParam.continuous
      | (unfold Function.Periodic.qParam; fun_prop)
  set R : ℂ → ℂ := fun z => Function.Periodic.qParam 1 z ^ e * G (Function.Periodic.qParam 1 z) with hR
  have hRq : ∀ z : ℂ, A ≤ z.im → realize N (x : LaurentSeries ℂ) (ofComplex z) = R z := fun z hz => by
    rw [hchart z hz, he, zpow_natCast]
  have hsmall : ∀ z : ℂ, A ≤ z.im → ‖Function.Periodic.qParam 1 z‖ ≤ Real.exp (-2 * Real.pi * A) :=
    fun z hz => by
      rw [Function.Periodic.norm_qParam, div_one]
      exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have hRcont : ∀ z : ℂ, A ≤ z.im → ContinuousAt R z := fun z hz =>
    (hqc.continuousAt.pow e).mul ((hball _ (hsmall z hz)).1.continuousAt.comp hqc.continuousAt)
  refine ⟨A + 1, fun τ hτ => ?_⟩
  have hτA : A ≤ (τ : ℂ).im := by rw [UpperHalfPlane.coe_im]; linarith
  have hev : (fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)) =ᶠ[𝓝 (τ : ℂ)] R := by
    have hopen : IsOpen {z : ℂ | A < z.im} := isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [hopen.mem_nhds (show A < (τ : ℂ).im by rw [UpperHalfPlane.coe_im]; linarith)]
      with z hz
    exact hRq z (le_of_lt hz)
  have hcC : ContinuousAt (fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ) :=
    (continuousAt_congr hev).mpr (hRcont _ hτA)
  refine ⟨?_, ?_, hcC⟩
  · have h1 := hRq (τ : ℂ) hτA
    rw [ofComplex_apply] at h1
    rw [h1]
    exact mul_ne_zero (pow_ne_zero _ (by
      first | exact Complex.exp_ne_zero _ | simp [Function.Periodic.qParam])) (hball _ (hsmall _ hτA)).2
  · have h2 : (fun z : ℍ => realize N (x : LaurentSeries ℂ) z) =
        (fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)) ∘ ((↑) : ℍ → ℂ) := by
      ext z
      simp [ofComplex_apply]
    rw [h2]
    exact hcC.comp UpperHalfPlane.continuous_coe.continuousAt

theorem tendsto_realize_comp [NeZero N] (x : FC N) (h0 : 0 ≤ (x : LaurentSeries ℂ).order)
    {τ_ : ℕ → ℍ} (hτ : Tendsto τ_ atTop atImInfty) :
    Tendsto (fun n => realize N (x : LaurentSeries ℂ) (τ_ n)) atTop
      (𝓝 ((x : LaurentSeries ℂ).coeff 0)) :=
  (ModularCurve.tendsto_realize_atImInfty_coeff_zero N x h0).comp hτ

theorem realize_sub_const [NeZero N] (x : FC N) :
    ∃ A : ℝ, ∀ (c : ℂ) (τ : ℍ), A ≤ τ.im →
      realize N ((x - algebraMap ℂ (FC N) c : FC N) : LaurentSeries ℂ) τ =
        realize N (x : LaurentSeries ℂ) τ - c := by
  obtain ⟨k, g, h, hh0, hxhg⟩ :=
    ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange N (x : LaurentSeries ℂ) x.2
  have hΓ : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N).map
      (Matrix.SpecialLinearGroup.mapGL ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples _
  obtain ⟨A, hne⟩ := exists_forall_ne_zero_of_le_im N h hh0
  refine ⟨A, fun c τ hτ => ?_⟩
  have hτ0 := hne τ hτ
  have hfun1 : ((g - c • h : ModularForm _ k) : ℍ → ℂ) =
      (g : ℍ → ℂ) - ((c • h : ModularForm _ k) : ℍ → ℂ) := by
    ext; simp
  have hfun2 : ((c • h : ModularForm _ k) : ℍ → ℂ) = c • (h : ℍ → ℂ) := by
    ext; simp
  have hpres : ((x - algebraMap ℂ (FC N) c : FC N) : LaurentSeries ℂ) *
      ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((qExpansion 1 ((g - c • h : ModularForm _ k) : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
    have hcoe : ((x - algebraMap ℂ (FC N) c : FC N) : LaurentSeries ℂ) =
        (x : LaurentSeries ℂ) - algebraMap ℂ (LaurentSeries ℂ) c := by
      first | rfl | simp
    rw [hcoe, sub_mul, hxhg, hfun1, ModularFormClass.qExpansion_sub one_pos hΓ, hfun2,
      ModularFormClass.qExpansion_smul one_pos hΓ, map_sub, PowerSeries.smul_eq_C_mul, map_mul,
      HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, ← algebraMap_laurentSeries_eq_single]
  rw [ModularCurve.realize_eq_div N (g - c • h) h _ hpres τ hτ0,
    ModularCurve.realize_eq_div N g h _ hxhg τ hτ0, hfun1, hfun2]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [sub_div, mul_div_cancel_right₀ _ hτ0]

theorem exists_high_point_J_eq [NeZero N] (A : ℝ) :
    ∃ R : ℤ, ∀ r : ℤ, R ≤ r → ∃ τ : ℍ, A ≤ τ.im ∧ realize N ((jC N : FC N) : LaurentSeries ℂ) τ = r := by
  obtain ⟨G, A₁, hA₁pos, hG0, hball, hchart⟩ := chart (jC N) jC_ne_zero
  rw [order_jC, coeff_jC_neg_one] at hG0
  have hG00 : G 0 ≠ 0 := by rw [hG0]; exact one_ne_zero
  have hball0 := hball 0 (by simpa using (Real.exp_pos _).le)
  have hΦan : AnalyticAt ℂ (fun q : ℂ => q * (G q)⁻¹) 0 := analyticAt_id.mul (hball0.1.inv hG00)
  rcases hΦan.eventually_constant_or_nhds_le_map_nhds with hconst | hopen
  · exfalso
    obtain ⟨ε, hε, hε'⟩ := Metric.eventually_nhds_iff.mp hconst
    have hzpos : 0 < min (ε / 2) (Real.exp (-2 * Real.pi * A₁)) := lt_min (by linarith) (Real.exp_pos _)
    set z : ℂ := ((min (ε / 2) (Real.exp (-2 * Real.pi * A₁)) : ℝ) : ℂ) with hz
    have hzn : ‖z‖ = min (ε / 2) (Real.exp (-2 * Real.pi * A₁)) := by
      rw [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hzpos]
    have hz0 : z ≠ 0 := by
      rw [← norm_pos_iff, hzn]; exact hzpos
    have h3 := hε' (show dist z 0 < ε by
      rw [dist_zero_right, hzn]; exact (min_le_left _ _).trans_lt (by linarith))
    have hGz := (hball z (by rw [hzn]; exact min_le_right _ _)).2
    simp only [zero_mul, mul_eq_zero, inv_eq_zero] at h3
    rcases h3 with h3 | h3
    · exact hz0 h3
    · exact hGz h3
  · have hopen' : 𝓝 (0 : ℂ) ≤ Filter.map (fun q : ℂ => q * (G q)⁻¹) (𝓝 0) := by simpa using hopen
    set A' : ℝ := max (max A A₁) 1 with hA'
    have hAA' : A ≤ A' := (le_max_left _ _).trans (le_max_left _ _)
    have hA₁A' : A₁ ≤ A' := (le_max_right _ _).trans (le_max_left _ _)
    have h1A' : (1 : ℝ) ≤ A' := le_max_right _ _
    set ε : ℝ := Real.exp (-2 * Real.pi * A') with hεdef
    have hε : 0 < ε := Real.exp_pos _
    have hV : (fun q : ℂ => q * (G q)⁻¹) '' Metric.ball 0 ε ∈ 𝓝 (0 : ℂ) :=
      hopen' (Filter.image_mem_map (Metric.ball_mem_nhds 0 hε))
    obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.mp hV
    refine ⟨⌈δ⁻¹⌉ + 1, fun r hr => ?_⟩
    have hrδ : δ⁻¹ < (r : ℝ) := by
      have h1 := Int.le_ceil δ⁻¹
      have h2 : ((⌈δ⁻¹⌉ + 1 : ℤ) : ℝ) ≤ r := by exact_mod_cast hr
      push_cast at h2
      linarith
    have hrpos : (0 : ℝ) < r := (inv_pos.mpr hδ).trans hrδ
    have hrne : r ≠ 0 := by rintro rfl; simp at hrpos
    have hr0 : (r : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hrne
    have hrinv : ‖((r : ℂ))⁻¹‖ < δ := by
      rw [norm_inv, Complex.norm_intCast, abs_of_pos (by exact_mod_cast hrpos)]
      exact inv_lt_of_inv_lt₀ hδ hrδ
    obtain ⟨q, hqball, hq⟩ := hδball (show ((r : ℂ))⁻¹ ∈ Metric.ball (0 : ℂ) δ by simpa using hrinv)
    have hqn : ‖q‖ < ε := by simpa using hqball
    have hq0 : q ≠ 0 := by
      rintro rfl
      simp only [zero_mul] at hq
      exact hr0 (inv_eq_zero.mp hq.symm)
    have hqε : ‖q‖ ≤ Real.exp (-2 * Real.pi * A₁) :=
      hqn.le.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hA₁A' (by linarith [Real.pi_pos])))
    have hGq : G q ≠ 0 := (hball q hqε).2
    set z : ℂ := Function.Periodic.invQParam 1 q with hz
    have hzq : Function.Periodic.qParam 1 z = q := Function.Periodic.qParam_right_inv one_ne_zero hq0
    have hzim : A' < z.im := by
      rw [hz, Function.Periodic.im_invQParam]
      have hlog : Real.log ‖q‖ < -2 * Real.pi * A' := by
        have := Real.log_lt_log (norm_pos_iff.mpr hq0) hqn
        rwa [hεdef, Real.log_exp] at this
      rw [show -1 / (2 * Real.pi) * Real.log ‖q‖ = (-Real.log ‖q‖) / (2 * Real.pi) by ring,
        lt_div_iff₀ (by positivity)]
      linarith
    have hzpos : 0 < z.im := by linarith
    refine ⟨⟨z, hzpos⟩, ?_, ?_⟩
    · show A ≤ z.im
      linarith
    · have h5 := hchart z (by linarith)
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hzpos] at h5
      rw [h5, hzq, order_jC, zpow_neg_one]
      have h6 := congrArg Inv.inv hq
      simp only [mul_inv, inv_inv] at h6
      exact h6

theorem J_sub_analytic [NeZero N] :
    ∃ A : ℝ, ∀ (τ₀ : ℍ) (r : ℂ), A ≤ τ₀.im → realize N ((jC N : FC N) : LaurentSeries ℂ) τ₀ = r →
      ∃ F : ℂ → ℂ, AnalyticAt ℂ F (τ₀ : ℂ) ∧ F (τ₀ : ℂ) = 0 ∧
        (fun z : ℂ => realize N ((jC N - algebraMap ℂ (FC N) r : FC N) : LaurentSeries ℂ) (ofComplex z))
          =ᶠ[𝓝 (τ₀ : ℂ)] F := by
  obtain ⟨G, A₁, hA₁, hG0, hball, hchart⟩ := chart (jC N) jC_ne_zero
  obtain ⟨A₂, hsub⟩ := realize_sub_const (jC N)
  have hqd : Differentiable ℂ (Function.Periodic.qParam 1) := by
    first
      | exact Function.Periodic.differentiable_qParam
      | (unfold Function.Periodic.qParam; fun_prop)
  have hsmall : ∀ z : ℂ, A₁ ≤ z.im → ‖Function.Periodic.qParam 1 z‖ ≤ Real.exp (-2 * Real.pi * A₁) :=
    fun z hz => by
      rw [Function.Periodic.norm_qParam, div_one]
      exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  refine ⟨max A₁ A₂ + 2, fun τ₀ r hτ₀ hJ => ?_⟩
  have hm1 := le_max_left A₁ A₂
  have hm2 := le_max_right A₁ A₂
  set F : ℂ → ℂ := fun z =>
    (Function.Periodic.qParam 1 z)⁻¹ * G (Function.Periodic.qParam 1 z) - r with hFdef
  have hFeq : ∀ z : ℂ, max A₁ A₂ + 1 ≤ z.im →
      realize N ((jC N - algebraMap ℂ (FC N) r : FC N) : LaurentSeries ℂ) (ofComplex z) = F z := by
    intro z hz
    have hz0 : 0 < z.im := by linarith
    have hc : ((ofComplex z : ℍ) : ℂ) = z := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz0]; try rfl
    have him : A₂ ≤ (ofComplex z).im := by
      rw [← UpperHalfPlane.coe_im, hc]; linarith
    rw [hsub r (ofComplex z) him, hchart z (by linarith), order_jC, zpow_neg_one]
  refine ⟨F, ?_, ?_, ?_⟩
  · have hq : AnalyticAt ℂ (Function.Periodic.qParam 1) (τ₀ : ℂ) := hqd.analyticAt (τ₀ : ℂ)
    have hτim : A₁ ≤ (τ₀ : ℂ).im := by rw [UpperHalfPlane.coe_im]; linarith
    exact ((hq.inv (by first | exact Complex.exp_ne_zero _ | simp [Function.Periodic.qParam])).mul
      ((hball _ (hsmall _ hτim)).1.comp hq)).sub analyticAt_const
  · have h5 := hchart (τ₀ : ℂ) (by rw [UpperHalfPlane.coe_im]; linarith)
    rw [ofComplex_apply, hJ, order_jC, zpow_neg_one] at h5
    show (Function.Periodic.qParam 1 (τ₀ : ℂ))⁻¹ * G (Function.Periodic.qParam 1 (τ₀ : ℂ)) - r = 0
    rw [← h5, sub_self]
  · have hopen : IsOpen {z : ℂ | max A₁ A₂ + 1 < z.im} := isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [hopen.mem_nhds (show max A₁ A₂ + 1 < (τ₀ : ℂ).im by
      rw [UpperHalfPlane.coe_im]; linarith)] with z hz
    exact hFeq z (le_of_lt hz)

theorem mem_pt_of_continuousAt [NeZero N] (D : ComplexPlaceDictionary N) (τ : ℍ) (x : FC N)
    (hc : ContinuousAt (fun z : ℍ => realize N (x : LaurentSeries ℂ) z) τ) :
    x ∈ (D.pt τ).toValuationSubring := by
  rw [D.mem_pt_iff]
  exact Filter.IsBoundedUnder.mono nhdsWithin_le_nhds hc.norm.isBoundedUnder_le

theorem evalAt_pt_eq_realize [NeZero N] (D : ComplexPlaceDictionary N) (τ : ℍ) (x : FC N)
    (hx : x ∈ (D.pt τ).toValuationSubring)
    (hc : ContinuousAt (fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ)) :
    (D.pt τ).evalAt x = realize N (x : LaurentSeries ℂ) τ := by
  obtain ⟨g, hg, heq, hval⟩ := D.exists_analyticAt_eventuallyEq_realize τ x hx
  have h1 : Tendsto (fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)) (𝓝[≠] (τ : ℂ))
      (𝓝 (realize N (x : LaurentSeries ℂ) (ofComplex (τ : ℂ)))) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)) (𝓝[≠] (τ : ℂ))
      (𝓝 (g τ)) :=
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm
  rw [← hval, ← tendsto_nhds_unique h1 h2, ofComplex_apply]

theorem ord_pt_pos [NeZero N] (D : ComplexPlaceDictionary N) (τ : ℍ) (x : FC N) (hx : x ≠ 0)
    (F : ℂ → ℂ) (hF : AnalyticAt ℂ F (τ : ℂ)) (hF0 : F (τ : ℂ) = 0)
    (heq : (fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)) =ᶠ[𝓝 (τ : ℂ)] F) :
    0 < (D.pt τ).ord x := by
  have hmer := D.meromorphicOrderAt_realize τ x hx
  rw [meromorphicOrderAt_congr (heq.filter_mono nhdsWithin_le_nhds), hF.meromorphicOrderAt_eq] at hmer
  have hne0 : analyticOrderAt F (τ : ℂ) ≠ 0 := by
    rw [Ne, hF.analyticOrderAt_eq_zero]
    exact fun h => h hF0
  have he : 0 < (D.ramification τ : ℤ) := by exact_mod_cast D.ramification_pos τ
  induction ha : analyticOrderAt F (τ : ℂ) using ENat.recTopCoe with
  | top =>
    exfalso
    rw [ha, ENat.map_top] at hmer
    exact WithTop.top_ne_coe hmer
  | coe n =>
    rw [ha] at hmer hne0
    have hn0 : n ≠ 0 := by simpa using hne0
    have hn' : (n : ℤ) = (D.ramification τ : ℤ) * (D.pt τ).ord x := by
      have h2 : ((n : ℤ) : WithTop ℤ) = (((D.ramification τ : ℤ) * (D.pt τ).ord x : ℤ) : WithTop ℤ) := by
        simpa using hmer
      exact_mod_cast h2
    exact pos_of_mul_pos_right (by rw [← hn']; exact_mod_cast Nat.pos_of_ne_zero hn0) he.le

theorem isRational_FB [NeZero N] (v : Place (AlgebraicClosure ℚ) (FB N)) : v.IsRational := by
  haveI := ModularCurve.isCurveOver_modularFunctionFieldBar N
  exact (AlgebraicCurve.Place.isRational_iff_deg_eq_one v).mpr (IsCurveOver.deg_eq_one_of_isAlgClosed v)

set_option synthInstance.maxHeartbeats 800000 in

theorem exists_place_comap [NeZero N] (σ : AlgebraicClosure ℚ →+* ℂ)
    (w : Place ℂ (FC N)) (hw : ∃ y : FB N, phi N σ y ∉ w.toValuationSubring) :
    ∃ v : Place (AlgebraicClosure ℚ) (FB N),
      v.toValuationSubring = w.toValuationSubring.comap (phi N σ) := by
  haveI : FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({jB N} : Set (FB N))) (FB N) :=
    ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_full (AlgebraicClosure ℚ) N
  haveI : Algebra.IsSeparable
      (IntermediateField.adjoin (AlgebraicClosure ℚ) ({jB N} : Set (FB N))) (FB N) := by
    first
      | infer_instance
      | exact Algebra.IsSeparable.of_finite _ _
      | exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable (jB N) (phi N σ)
    w.toValuationSubring (fun a => by rw [phi_algebraMap]; exact w.algebraMap_mem' _) hw

theorem evalAt_transport [NeZero N] (σ : AlgebraicClosure ℚ →+* ℂ)
    (v : Place (AlgebraicClosure ℚ) (FB N)) (w : Place ℂ (FC N))
    (h : v.toValuationSubring = w.toValuationSubring.comap (phi N σ))
    {y : FB N} (hy : y ∈ v.toValuationSubring) :
    σ (v.evalAt y) = w.evalAt (phi N σ y) :=
  (AlgebraicCurve.Place.evalAt_map_eq_of_comap_eq σ (phi N σ) (phi_algebraMap σ) v w h.symm
    (isRational_FB v) hy).symm

theorem step [NeZero N] (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ) :
    ∃ A : ℝ, ∀ (τ : ℍ) (r : ℤ), A ≤ τ.im → realize N ((jC N : FC N) : LaurentSeries ℂ) τ = r →
      ∃ v : Place (AlgebraicClosure ℚ) (FB N),
        v.toValuationSubring = (D.pt τ).toValuationSubring.comap (phi N σ) ∧
        0 < (D.pt τ).ord (phi N σ (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) (r : AlgebraicClosure ℚ))) ∧
        v ≠ cuspInftyBar N := by
  obtain ⟨A, hA⟩ := J_sub_analytic (N := N)
  refine ⟨A, fun τ r hτ hJ => ?_⟩
  obtain ⟨F, hF, hF0, heq⟩ := hA τ (r : ℂ) hτ hJ
  set x : FC N := jC N - algebraMap ℂ (FC N) (r : ℂ) with hx_def
  have hx0 : x ≠ 0 := by
    intro h0
    have h1 : ((jC N : FC N) : LaurentSeries ℂ) = algebraMap ℂ (LaurentSeries ℂ) (r : ℂ) :=
      congrArg (fun y : FC N => (y : LaurentSeries ℂ)) (sub_eq_zero.mp h0)
    have h2 := coeff_jC_neg_one (N := N)
    rw [h1, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_of_ne (by norm_num)] at h2
    exact zero_ne_one h2
  have hord : 0 < (D.pt τ).ord x := ord_pt_pos D τ x hx0 F hF hF0 heq
  have hphi : phi N σ (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) (r : AlgebraicClosure ℚ)) = x := by
    rw [map_sub, phi_jB, phi_algebraMap, map_intCast]
  have hxmem : x ∈ (D.pt τ).toValuationSubring :=
    (AlgebraicCurve.Place.mem_iff_ord_nonneg _ hx0).mpr hord.le
  have hxinv : x⁻¹ ∉ (D.pt τ).toValuationSubring := by
    rw [AlgebraicCurve.Place.mem_iff_ord_nonneg _ (inv_ne_zero hx0), Place.ord_inv]
    omega
  obtain ⟨v, hv⟩ := exists_place_comap σ (D.pt τ)
    ⟨(jB N - algebraMap (AlgebraicClosure ℚ) (FB N) (r : AlgebraicClosure ℚ))⁻¹, by rwa [map_inv₀, hphi]⟩
  refine ⟨v, hv, by rw [hphi]; exact hord, ?_⟩
  intro hvinf
  apply jB_notMem (N := N)
  rw [← hvinf, hv, ValuationSubring.mem_comap, phi_jB]
  have : (jC N : FC N) = x + algebraMap ℂ (FC N) (r : ℂ) := by rw [hx_def, sub_add_cancel]
  rw [this]
  exact add_mem hxmem ((D.pt τ).algebraMap_mem' _)

set_option maxHeartbeats 1600000 in

theorem ne_of_ord_pos [NeZero N] (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ)
    {τ₁ τ₂ : ℍ} {r₁ r₂ : ℤ} (hr : r₁ ≠ r₂)
    (v₁ v₂ : Place (AlgebraicClosure ℚ) (FB N))
    (h₁ : v₁.toValuationSubring = (D.pt τ₁).toValuationSubring.comap (phi N σ))
    (h₂ : v₂.toValuationSubring = (D.pt τ₂).toValuationSubring.comap (phi N σ))
    (o₁ : 0 < (D.pt τ₁).ord (phi N σ (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) (r₁ : AlgebraicClosure ℚ))))
    (o₂ : 0 < (D.pt τ₂).ord (phi N σ (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) (r₂ : AlgebraicClosure ℚ)))) :
    v₁ ≠ v₂ := by
  intro heqv
  have hx₁ : phi N σ (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) (r₁ : AlgebraicClosure ℚ)) ≠ 0 :=
    fun h => by rw [h, Place.ord_zero] at o₁; exact lt_irrefl _ o₁
  have hx₂ : phi N σ (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) (r₂ : AlgebraicClosure ℚ)) ≠ 0 :=
    fun h => by rw [h, Place.ord_zero] at o₂; exact lt_irrefl _ o₂
  have h1 : (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) (r₂ : AlgebraicClosure ℚ))⁻¹ ∉
      v₂.toValuationSubring := by
    rw [h₂, ValuationSubring.mem_comap, map_inv₀,
      AlgebraicCurve.Place.mem_iff_ord_nonneg _ (inv_ne_zero hx₂), Place.ord_inv]
    omega
  rw [← heqv, h₁, ValuationSubring.mem_comap, map_inv₀,
    AlgebraicCurve.Place.mem_iff_ord_nonneg _ (inv_ne_zero hx₂), Place.ord_inv, not_le] at h1
  have o₂' : 0 < (D.pt τ₁).ord (phi N σ (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) (r₂ : AlgebraicClosure ℚ))) := by
    omega
  set x₁ : FC N := phi N σ (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) (r₁ : AlgebraicClosure ℚ)) with hx₁def
  set x₂ : FC N := phi N σ (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) (r₂ : AlgebraicClosure ℚ)) with hx₂def
  have hdiff : x₁ - x₂ = algebraMap ℂ (FC N) (((r₂ - r₁ : ℤ) : ℂ)) := by
    have hin : jB N - algebraMap (AlgebraicClosure ℚ) (FB N) (r₁ : AlgebraicClosure ℚ) -
        (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) (r₂ : AlgebraicClosure ℚ)) =
        algebraMap (AlgebraicClosure ℚ) (FB N) ((r₂ - r₁ : ℤ) : AlgebraicClosure ℚ) := by
      rw [Int.cast_sub, map_sub]; abel
    rw [hx₁def, hx₂def, ← map_sub, hin, phi_algebraMap]
    congr 1
    exact map_intCast σ _
  have hc0 : algebraMap ℂ (FC N) (((r₂ - r₁ : ℤ) : ℂ)) ≠ 0 := by
    rw [map_ne_zero_iff _ (algebraMap ℂ (FC N)).injective]
    exact_mod_cast sub_ne_zero.mpr hr.symm
  set O := (D.pt τ₁).toValuationSubring with hO
  have hx₁i : x₁⁻¹ ∉ O := by
    rw [hO, AlgebraicCurve.Place.mem_iff_ord_nonneg _ (inv_ne_zero hx₁), Place.ord_inv]
    omega
  have hx₂i : x₂⁻¹ ∉ O := by
    rw [hO, AlgebraicCurve.Place.mem_iff_ord_nonneg _ (inv_ne_zero hx₂), Place.ord_inv]
    omega
  have hval : ∀ a : FC N, a⁻¹ ∉ O → O.valuation a < 1 := fun a ha => by
    rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, not_le] at ha
    have h0 : O.valuation a ≠ 0 := fun h => by simp [h] at ha
    exact (one_lt_inv₀ (zero_lt_iff.mpr h0)).mp ha
  have h1 : O.valuation (x₁ - x₂) ≤ 1 :=
    (ValuationSubring.valuation_le_one_iff _ _).mpr (by rw [hdiff, hO]; exact (D.pt τ₁).algebraMap_mem' _)
  have h2 : (O.valuation (x₁ - x₂))⁻¹ ≤ 1 := by
    rw [← map_inv₀]
    exact (ValuationSubring.valuation_le_one_iff _ _).mpr
      (by rw [hdiff, ← map_inv₀, hO]; exact (D.pt τ₁).algebraMap_mem' _)
  have h0 : O.valuation (x₁ - x₂) ≠ 0 := by
    rw [Valuation.ne_zero_iff, hdiff]; exact hc0
  have hge : 1 ≤ O.valuation (x₁ - x₂) := (inv_le_one₀ (zero_lt_iff.mpr h0)).mp h2
  have hlt : O.valuation (x₁ - x₂) < 1 :=
    (Valuation.map_sub _ _ _).trans_lt (max_lt (hval _ hx₁i) (hval _ hx₂i))
  exact absurd (le_antisymm h1 hge) hlt.ne

theorem modularForm_eventually_ne_zero (N : ℕ) {k : ℤ}
    (h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh0 : h ≠ 0) (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), (h : ℍ → ℂ) (ofComplex z) ≠ 0 := by
  set f : ℂ → ℂ := (h : ℍ → ℂ) ∘ ofComplex with hf
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hdiff : DifferentiableOn ℂ f {z : ℂ | 0 < z.im} := fun z hz =>
    (UpperHalfPlane.mdifferentiableAt_iff.mp (ModularFormClass.holo h ⟨z, hz⟩)).differentiableWithinAt
  have hana : AnalyticOnNhd ℂ f {z : ℂ | 0 < z.im} := hdiff.analyticOnNhd hU
  have hτ : (τ : ℂ) ∈ {z : ℂ | 0 < z.im} := τ.im_pos
  rcases (hana _ hτ).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · exfalso
    apply hh0
    have hEq := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_halfSpace_im_gt 0).isPreconnected hτ hzero
    apply DFunLike.ext
    intro τ'
    have := hEq τ'.im_pos
    simp only [hf, Function.comp_apply, ofComplex_apply, Pi.zero_apply] at this
    simpa using this
  · exact hne

theorem realize_sub_const_nhds [NeZero N] (x : FC N) (c : ℂ) (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ),
      realize N ((x - algebraMap ℂ (FC N) c : FC N) : LaurentSeries ℂ) (ofComplex z) =
        realize N (x : LaurentSeries ℂ) (ofComplex z) - c := by
  obtain ⟨k, g, h, hh0, hxhg⟩ :=
    ModularCurve.exists_modularForm_mul_qExpansion_eq_of_mem_laurentBaseChange N (x : LaurentSeries ℂ) x.2
  have hΓ : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N).map
      (Matrix.SpecialLinearGroup.mapGL ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples _
  have hfun1 : ((g - c • h : ModularForm _ k) : ℍ → ℂ) =
      (g : ℍ → ℂ) - ((c • h : ModularForm _ k) : ℍ → ℂ) := by
    ext; simp
  have hfun2 : ((c • h : ModularForm _ k) : ℍ → ℂ) = c • (h : ℍ → ℂ) := by
    ext; simp
  have hpres : ((x - algebraMap ℂ (FC N) c : FC N) : LaurentSeries ℂ) *
      ((qExpansion 1 (h : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((qExpansion 1 ((g - c • h : ModularForm _ k) : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
    have hcoe : ((x - algebraMap ℂ (FC N) c : FC N) : LaurentSeries ℂ) =
        (x : LaurentSeries ℂ) - algebraMap ℂ (LaurentSeries ℂ) c := by
      first | rfl | simp
    rw [hcoe, sub_mul, hxhg, hfun1, ModularFormClass.qExpansion_sub one_pos hΓ, hfun2,
      ModularFormClass.qExpansion_smul one_pos hΓ, map_sub, PowerSeries.smul_eq_C_mul, map_mul,
      HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, ← algebraMap_laurentSeries_eq_single]
  filter_upwards [modularForm_eventually_ne_zero N h hh0 τ] with z hz
  rw [ModularCurve.realize_eq_div N (g - c • h) h _ hpres _ hz,
    ModularCurve.realize_eq_div N g h _ hxhg _ hz, hfun1, hfun2]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [sub_div, mul_div_cancel_right₀ _ hz]

theorem germ [NeZero N] (D : ComplexPlaceDictionary N) (τ : ℍ) (x : FC N)
    (hx : x ∈ (D.pt τ).toValuationSubring) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧ g (τ : ℂ) = (D.pt τ).evalAt x ∧
      ((fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)] g) ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ), ∃ hz : 0 < z.im,
        x ∈ (D.pt ⟨z, hz⟩).toValuationSubring ∧ (D.pt ⟨z, hz⟩).evalAt x = g z := by
  obtain ⟨g, hg, heq, hval⟩ := D.exists_analyticAt_eventuallyEq_realize τ x hx
  refine ⟨g, hg, hval, heq, ?_⟩

  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, ∀ z : ℂ, dist z (τ : ℂ) < ε → z ≠ (τ : ℂ) →
      realize N (x : LaurentSeries ℂ) (ofComplex z) = g z := by
    have h1 := heq
    rw [Filter.EventuallyEq, eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h1
    obtain ⟨ε, hε, h1⟩ := h1
    exact ⟨ε, hε, fun z hz hne => h1 hz hne⟩
  have hpos : ∀ᶠ z in 𝓝 (τ : ℂ), 0 < z.im :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos
  have hball' : ∀ᶠ z in 𝓝 (τ : ℂ), dist z (τ : ℂ) < ε := Metric.ball_mem_nhds _ hε
  have hmem : ∀ᶠ z in 𝓝[≠] (τ : ℂ), z ≠ (τ : ℂ) := eventually_mem_nhdsWithin
  filter_upwards [(hg.eventually_analyticAt.and (hpos.and hball')).filter_mono nhdsWithin_le_nhds, hmem]
    with z ⟨hgz, hzim, hzd⟩ hzne
  refine ⟨hzim, ?_⟩

  have hloc : (fun w : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex w)) =ᶠ[𝓝 z] g := by
    have hopen : IsOpen (Metric.ball (τ : ℂ) ε ∩ {(τ : ℂ)}ᶜ) := Metric.isOpen_ball.inter isOpen_compl_singleton
    filter_upwards [hopen.mem_nhds ⟨hzd, hzne⟩] with w ⟨hw1, hw2⟩
    exact hball w hw1 hw2
  have hcC : ContinuousAt (fun w : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex w)) z :=
    (continuousAt_congr hloc).mpr hgz.continuousAt
  have hzc : ((⟨z, hzim⟩ : ℍ) : ℂ) = z := rfl
  have hcH : ContinuousAt (fun w : ℍ => realize N (x : LaurentSeries ℂ) w) ⟨z, hzim⟩ := by
    have h2 : (fun w : ℍ => realize N (x : LaurentSeries ℂ) w) =
        (fun w : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex w)) ∘ ((↑) : ℍ → ℂ) := by
      ext w
      simp [ofComplex_apply]
    rw [h2]
    exact hcC.comp UpperHalfPlane.continuous_coe.continuousAt
  have hxmem : x ∈ (D.pt ⟨z, hzim⟩).toValuationSubring := mem_pt_of_continuousAt D _ _ hcH
  refine ⟨hxmem, ?_⟩
  rw [evalAt_pt_eq_realize D _ _ hxmem hcC, ← hball z hzd hzne, UpperHalfPlane.ofComplex_apply_of_im_pos hzim]

theorem germ_eventually_ne_zero [NeZero N] (D : ComplexPlaceDictionary N) (τ : ℍ) (x : FC N)
    (hx0 : x ≠ 0) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g (τ : ℂ))
    (heq : (fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)] g) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), g z ≠ 0 := by
  rcases hg.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · exfalso
    have hmer := D.meromorphicOrderAt_realize τ x hx0
    rw [meromorphicOrderAt_congr heq] at hmer
    have htop : meromorphicOrderAt g (τ : ℂ) = ⊤ :=
      meromorphicOrderAt_eq_top_iff.mpr (hzero.filter_mono nhdsWithin_le_nhds)
    rw [htop] at hmer
    exact WithTop.top_ne_coe hmer
  · exact hne

theorem ord_pt_pos' [NeZero N] (D : ComplexPlaceDictionary N) (τ : ℍ) (x : FC N) (hx : x ≠ 0)
    (F : ℂ → ℂ) (hF : AnalyticAt ℂ F (τ : ℂ)) (hF0 : F (τ : ℂ) = 0)
    (heq : (fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)] F) :
    0 < (D.pt τ).ord x := by
  have hmer := D.meromorphicOrderAt_realize τ x hx
  rw [meromorphicOrderAt_congr heq, hF.meromorphicOrderAt_eq] at hmer
  have hne0 : analyticOrderAt F (τ : ℂ) ≠ 0 := by
    rw [Ne, hF.analyticOrderAt_eq_zero]
    exact fun h => h hF0
  have he : 0 < (D.ramification τ : ℤ) := by exact_mod_cast D.ramification_pos τ
  induction ha : analyticOrderAt F (τ : ℂ) using ENat.recTopCoe with
  | top =>
    exfalso
    rw [ha, ENat.map_top] at hmer
    exact WithTop.top_ne_coe hmer
  | coe n =>
    rw [ha] at hmer hne0
    have hn0 : n ≠ 0 := by simpa using hne0
    have hn' : (n : ℤ) = (D.ramification τ : ℤ) * (D.pt τ).ord x := by
      have h2 : ((n : ℤ) : WithTop ℤ) = (((D.ramification τ : ℤ) * (D.pt τ).ord x : ℤ) : WithTop ℤ) := by
        simpa using hmer
      exact_mod_cast h2
    exact pos_of_mul_pos_right (by rw [← hn']; exact_mod_cast Nat.pos_of_ne_zero hn0) he.le

theorem evalAt_pt_sub_const [NeZero N] (D : ComplexPlaceDictionary N) (τ : ℍ) (x : FC N)
    (hx : x ∈ (D.pt τ).toValuationSubring) (c : ℂ) :
    (x - algebraMap ℂ (FC N) c : FC N) ∈ (D.pt τ).toValuationSubring ∧
    (D.pt τ).evalAt (x - algebraMap ℂ (FC N) c : FC N) = (D.pt τ).evalAt x - c := by
  have hmem : (x - algebraMap ℂ (FC N) c : FC N) ∈ (D.pt τ).toValuationSubring :=
    sub_mem hx ((D.pt τ).algebraMap_mem' _)
  refine ⟨hmem, ?_⟩
  obtain ⟨g, hg, hgval, hgeq, -⟩ := germ D τ x hx
  obtain ⟨g', hg', hg'val, hg'eq, -⟩ := germ D τ _ hmem
  have h3 : g' =ᶠ[𝓝[≠] (τ : ℂ)] fun z => g z - c := by
    filter_upwards [hgeq, hg'eq, realize_sub_const_nhds x c τ] with z h1 h2 h3
    rw [← h2, h3, h1]
  have h4 : Tendsto g' (𝓝[≠] (τ : ℂ)) (𝓝 (g' τ)) := hg'.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h5 : Tendsto g' (𝓝[≠] (τ : ℂ)) (𝓝 (g τ - c)) :=
    ((hg.continuousAt.sub continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds).congr' h3.symm
  rw [← hg'val, ← hgval, tendsto_nhds_unique h4 h5]

theorem main (N : ℕ) [NeZero N] (σ : AlgebraicClosure ℚ →+* ℂ)
    (S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)))
    (Y : Finset ↥(modularFunctionFieldBar N))
    (hY : ∀ y ∈ Y, y ∈ (cuspInftyBar N).toValuationSubring) :
    ∃ v : ℕ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
      (∀ n, v n ∉ S) ∧ (∀ n, v n ≠ cuspInftyBar N) ∧
      ∀ y ∈ Y, (∀ n, y ∈ (v n).toValuationSubring) ∧ (y ≠ 0 → ∀ n, (v n).evalAt y ≠ 0) ∧
        Filter.Tendsto (fun n => σ ((v n).evalAt y)) Filter.atTop
          (nhds (σ ((cuspInftyBar N).evalAt y))) := by
  classical
  obtain ⟨D⟩ := ModularCurve.exists_complexPlaceDictionary N

  have hreg : ∀ y : FB N, ∃ A : ℝ, y ≠ 0 → y ∈ (cuspInftyBar N).toValuationSubring →
      ∀ τ : ℍ, A ≤ τ.im →
        realize N ((phi N σ y : FC N) : LaurentSeries ℂ) τ ≠ 0 ∧
        ContinuousAt (fun z : ℍ => realize N ((phi N σ y : FC N) : LaurentSeries ℂ) z) τ ∧
        ContinuousAt (fun z : ℂ => realize N ((phi N σ y : FC N) : LaurentSeries ℂ) (ofComplex z))
          (τ : ℂ) := by
    intro y
    by_cases hy : y = 0
    · exact ⟨0, fun h => absurd hy h⟩
    by_cases hy' : y ∈ (cuspInftyBar N).toValuationSubring
    · obtain ⟨A, hA⟩ := regular_high (phi N σ y) (phi_ne_zero σ hy)
        (by rw [order_phi]; exact (mem_cuspInftyBar_iff y).mp hy')
      exact ⟨A, fun _ _ => hA⟩
    · exact ⟨0, fun _ h => absurd h hy'⟩
  choose Areg hAreg using hreg
  obtain ⟨Astep, hstep⟩ := step D σ

  set A0 : ℝ := |Astep| + ∑ y ∈ Y, |Areg y| with hA0_def
  have hA0step : Astep ≤ A0 :=
    (le_abs_self _).trans (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _))
  have hA0reg : ∀ y ∈ Y, Areg y ≤ A0 := fun y hy =>
    (le_abs_self _).trans ((Finset.single_le_sum (f := fun y => |Areg y|)
      (fun _ _ => abs_nonneg _) hy).trans (le_add_of_nonneg_left (abs_nonneg _)))

  have hpt : ∀ n : ℕ, ∃ R : ℤ, ∀ r : ℤ, R ≤ r →
      ∃ τ : ℍ, A0 + n ≤ τ.im ∧ realize N ((jC N : FC N) : LaurentSeries ℂ) τ = r :=
    fun n => exists_high_point_J_eq (A0 + n)
  choose R hR using hpt
  set r : ℕ → ℤ := fun n => (∑ i ∈ Finset.range (n + 1), |R i|) + n with hr_def
  have hRr : ∀ n, R n ≤ r n := fun n =>
    (le_abs_self _).trans ((Finset.single_le_sum (f := fun i => |R i|) (fun _ _ => abs_nonneg _)
      (Finset.self_mem_range_succ n)).trans (le_add_of_nonneg_right (by positivity)))
  have hr_mono : StrictMono r := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    simp only [hr_def]
    rw [Finset.sum_range_succ _ (n + 1)]
    push_cast
    linarith [abs_nonneg (R (n + 1))]
  have hτ : ∀ n : ℕ, ∃ τ : ℍ, A0 + n ≤ τ.im ∧ realize N ((jC N : FC N) : LaurentSeries ℂ) τ = r n :=
    fun n => hR n (r n) (hRr n)
  choose τ hτim hτJ using hτ

  have hv : ∀ n, ∃ v : Place (AlgebraicClosure ℚ) (FB N),
      v.toValuationSubring = (D.pt (τ n)).toValuationSubring.comap (phi N σ) ∧
      0 < (D.pt (τ n)).ord (phi N σ (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) (r n : AlgebraicClosure ℚ))) ∧
      v ≠ cuspInftyBar N :=
    fun n => hstep (τ n) (r n)
      (hA0step.trans ((le_add_of_nonneg_right (Nat.cast_nonneg n)).trans (hτim n))) (hτJ n)
  choose v hvcomap hvord hvne using hv
  have hinj : Function.Injective v := by
    intro m n hmn
    by_contra hne
    exact ne_of_ord_pos D σ (hr_mono.injective.ne hne) (v m) (v n) (hvcomap m) (hvcomap n)
      (hvord m) (hvord n) hmn

  have hfin : (v ⁻¹' (S : Set (Place (AlgebraicClosure ℚ) (FB N)))).Finite :=
    S.finite_toSet.preimage fun _ _ _ _ h => hinj h
  obtain ⟨n₀, hn₀⟩ := hfin.bddAbove
  refine ⟨fun n => v (n + n₀ + 1), ?_, fun n => hvne _, ?_⟩
  · intro n hn
    have := hn₀ (show n + n₀ + 1 ∈ v ⁻¹' (S : Set (Place (AlgebraicClosure ℚ) (FB N))) from hn)
    omega
  · intro y hy
    by_cases hy0 : y = 0
    · subst hy0
      have h1 : ∀ w : Place (AlgebraicClosure ℚ) (FB N), w.evalAt (0 : FB N) = 0 := fun w => by
        simpa using AlgebraicCurve.Place.evalAt_algebraMap w (0 : AlgebraicClosure ℚ)
      refine ⟨fun n => zero_mem _, fun h => absurd rfl h, ?_⟩
      simp only [h1, map_zero]
      exact tendsto_const_nhds
    · have hyreg := hAreg y hy0 (hY y hy)
      have hhigh : ∀ n, Areg y ≤ (τ (n + n₀ + 1)).im := fun n =>
        (hA0reg y hy).trans ((le_add_of_nonneg_right (Nat.cast_nonneg _)).trans (hτim _))
      have hmemC : ∀ n, phi N σ y ∈ (D.pt (τ (n + n₀ + 1))).toValuationSubring := fun n =>
        mem_pt_of_continuousAt D _ _ (hyreg _ (hhigh n)).2.1
      have hmem : ∀ n, y ∈ (v (n + n₀ + 1)).toValuationSubring := fun n => by
        rw [hvcomap, ValuationSubring.mem_comap]
        exact hmemC n
      have hval : ∀ n, σ ((v (n + n₀ + 1)).evalAt y) =
          realize N ((phi N σ y : FC N) : LaurentSeries ℂ) (τ (n + n₀ + 1)) := fun n => by
        rw [evalAt_transport σ _ _ (hvcomap _) (hmem n),
          evalAt_pt_eq_realize D _ _ (hmemC n) (hyreg _ (hhigh n)).2.2]
      refine ⟨hmem, fun _ n h0 => ?_, ?_⟩
      · have := hval n
        rw [h0, map_zero] at this
        exact (hyreg _ (hhigh n)).1 this.symm
      · have hT : Tendsto (fun n => τ (n + n₀ + 1)) atTop atImInfty := by
          rw [UpperHalfPlane.atImInfty, Filter.tendsto_comap_iff]
          refine tendsto_atTop_atTop.mpr fun b => ⟨⌈b - A0⌉₊, fun a ha => ?_⟩
          show b ≤ (τ (a + n₀ + 1)).im
          have h1 := hτim (a + n₀ + 1)
          have h2 : b - A0 ≤ (a : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast ha)
          push_cast at h1
          linarith
        have hlim := tendsto_realize_comp (phi N σ y)
          (by rw [order_phi]; exact (mem_cuspInftyBar_iff y).mp (hY y hy)) hT
        rw [show σ ((cuspInftyBar N).evalAt y) = ((phi N σ y : FC N) : LaurentSeries ℂ).coeff 0 by
          rw [evalAt_cuspInftyBar (hY y hy), coeff_phi]]
        exact hlim.congr fun n => (hval n).symm

set_option maxHeartbeats 1600000 in

theorem ne_of_ord_pos' [NeZero N] (D : ComplexPlaceDictionary N) (σ : AlgebraicClosure ℚ →+* ℂ)
    {τ₁ τ₂ : ℍ} {c₁ c₂ : AlgebraicClosure ℚ} (hc : c₁ ≠ c₂)
    (v₁ v₂ : Place (AlgebraicClosure ℚ) (FB N))
    (h₁ : v₁.toValuationSubring = (D.pt τ₁).toValuationSubring.comap (phi N σ))
    (h₂ : v₂.toValuationSubring = (D.pt τ₂).toValuationSubring.comap (phi N σ))
    (o₁ : 0 < (D.pt τ₁).ord (phi N σ (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) c₁)))
    (o₂ : 0 < (D.pt τ₂).ord (phi N σ (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) c₂))) :
    v₁ ≠ v₂ := by
  intro heqv
  have hx₁ : phi N σ (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) c₁) ≠ 0 :=
    fun h => by rw [h, Place.ord_zero] at o₁; exact lt_irrefl _ o₁
  have hx₂ : phi N σ (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) c₂) ≠ 0 :=
    fun h => by rw [h, Place.ord_zero] at o₂; exact lt_irrefl _ o₂
  have h1 : (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) c₂)⁻¹ ∉ v₂.toValuationSubring := by
    rw [h₂, ValuationSubring.mem_comap, map_inv₀,
      AlgebraicCurve.Place.mem_iff_ord_nonneg _ (inv_ne_zero hx₂), Place.ord_inv]
    omega
  rw [← heqv, h₁, ValuationSubring.mem_comap, map_inv₀,
    AlgebraicCurve.Place.mem_iff_ord_nonneg _ (inv_ne_zero hx₂), Place.ord_inv, not_le] at h1
  have o₂' : 0 < (D.pt τ₁).ord (phi N σ (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) c₂)) := by
    omega
  set x₁ : FC N := phi N σ (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) c₁) with hx₁def
  set x₂ : FC N := phi N σ (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) c₂) with hx₂def
  have hdiff : x₁ - x₂ = algebraMap ℂ (FC N) (σ (c₂ - c₁)) := by
    have hin : jB N - algebraMap (AlgebraicClosure ℚ) (FB N) c₁ -
        (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) c₂) =
        algebraMap (AlgebraicClosure ℚ) (FB N) (c₂ - c₁) := by
      rw [map_sub]; abel
    rw [hx₁def, hx₂def, ← map_sub, hin, phi_algebraMap]
  have hc0 : algebraMap ℂ (FC N) (σ (c₂ - c₁)) ≠ 0 := by
    rw [map_ne_zero_iff _ (algebraMap ℂ (FC N)).injective, map_ne_zero_iff _ σ.injective]
    exact sub_ne_zero.mpr hc.symm
  set O := (D.pt τ₁).toValuationSubring with hO
  have hx₁i : x₁⁻¹ ∉ O := by
    rw [hO, AlgebraicCurve.Place.mem_iff_ord_nonneg _ (inv_ne_zero hx₁), Place.ord_inv]
    omega
  have hx₂i : x₂⁻¹ ∉ O := by
    rw [hO, AlgebraicCurve.Place.mem_iff_ord_nonneg _ (inv_ne_zero hx₂), Place.ord_inv]
    omega
  have hval : ∀ a : FC N, a⁻¹ ∉ O → O.valuation a < 1 := fun a ha => by
    rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, not_le] at ha
    have h0 : O.valuation a ≠ 0 := fun h => by simp [h] at ha
    exact (one_lt_inv₀ (zero_lt_iff.mpr h0)).mp ha
  have h1' : O.valuation (x₁ - x₂) ≤ 1 :=
    (ValuationSubring.valuation_le_one_iff _ _).mpr (by rw [hdiff, hO]; exact (D.pt τ₁).algebraMap_mem' _)
  have h2 : (O.valuation (x₁ - x₂))⁻¹ ≤ 1 := by
    rw [← map_inv₀]
    exact (ValuationSubring.valuation_le_one_iff _ _).mpr
      (by rw [hdiff, ← map_inv₀, hO]; exact (D.pt τ₁).algebraMap_mem' _)
  have h0 : O.valuation (x₁ - x₂) ≠ 0 := by
    rw [Valuation.ne_zero_iff, hdiff]; exact hc0
  have hge : 1 ≤ O.valuation (x₁ - x₂) := (inv_le_one₀ (zero_lt_iff.mpr h0)).mp h2
  have hlt : O.valuation (x₁ - x₂) < 1 :=
    (Valuation.map_sub _ _ _).trans_lt (max_lt (hval _ hx₁i) (hval _ hx₂i))
  exact absurd (le_antisymm h1' hge) hlt.ne

theorem jC_sub_const_ne_zero [NeZero N] (c : ℂ) : (jC N - algebraMap ℂ (FC N) c : FC N) ≠ 0 := by
  intro h0
  have h1 : ((jC N : FC N) : LaurentSeries ℂ) = algebraMap ℂ (LaurentSeries ℂ) c :=
    congrArg (fun y : FC N => (y : LaurentSeries ℂ)) (sub_eq_zero.mp h0)
  have h2 := coeff_jC_neg_one (N := N)
  rw [h1, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_of_ne (by norm_num)] at h2
  exact zero_ne_one h2

set_option maxHeartbeats 4000000 in
theorem main_int (N : ℕ) [NeZero N]
    (v₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N))
    (hj : jB N ∈ v₀.toValuationSubring)
    (σ : AlgebraicClosure ℚ →+* ℂ)
    (S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)))
    (Y : Finset ↥(modularFunctionFieldBar N))
    (hY : ∀ y ∈ Y, y ∈ v₀.toValuationSubring) :
    ∃ v : ℕ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
      (∀ n, v n ∉ S) ∧ (∀ n, v n ≠ v₀) ∧
      ∀ y ∈ Y, (∀ n, y ∈ (v n).toValuationSubring) ∧ (y ≠ 0 → ∀ n, (v n).evalAt y ≠ 0) ∧
        Filter.Tendsto (fun n => σ ((v n).evalAt y)) Filter.atTop (nhds (σ (v₀.evalAt y))) := by
  classical
  obtain ⟨D⟩ := ModularCurve.exists_complexPlaceDictionary N

  obtain ⟨w₀, hw₀ord, -⟩ := AlgebraicCurve.Place.exists_place_laurentBaseChange_of_deg_eq_one.{0, 0, 0} σ
    (modularFunctionFieldFull N) v₀ (ModularCurve.deg_eq_one_modularFunctionFieldBar N v₀)
  have hordφ : ∀ y : FB N, w₀.ord (phi N σ y) = v₀.ord y := fun y => hw₀ord y (phi N σ y) rfl
  have hcomap : v₀.toValuationSubring = w₀.toValuationSubring.comap (phi N σ) := by
    ext y
    rw [ValuationSubring.mem_comap]
    by_cases hy : y = 0
    · subst hy
      simp only [map_zero]
      exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
    · rw [AlgebraicCurve.Place.mem_iff_ord_nonneg _ hy,
        AlgebraicCurve.Place.mem_iff_ord_nonneg _ (phi_ne_zero σ hy), hordφ]

  have hjC : jC N ∈ w₀.toValuationSubring := by
    have h := hj
    rw [hcomap, ValuationSubring.mem_comap, phi_jB] at h
    exact h
  obtain ⟨τ₀, hτ₀⟩ := D.exists_pt_eq_of_mem w₀ hjC
  rw [← hτ₀] at hcomap hjC

  obtain ⟨gJ, hgJ, hgJval, hgJeq, hgJnear⟩ := germ D τ₀ (jC N) hjC
  have hJ₀ : gJ (τ₀ : ℂ) = σ (v₀.evalAt (jB N)) := by
    rw [hgJval, evalAt_transport σ v₀ (D.pt τ₀) hcomap hj, phi_jB]
  set j₀ : ℂ := gJ (τ₀ : ℂ) with hj₀def
  have hj₀ : j₀ = σ (v₀.evalAt (jB N)) := hJ₀
  have hnc : ¬ (∀ᶠ z in 𝓝 (τ₀ : ℂ), gJ z = gJ (τ₀ : ℂ)) := by
    intro hconst
    set x : FC N := jC N - algebraMap ℂ (FC N) j₀ with hxdef
    have hx0 : x ≠ 0 := jC_sub_const_ne_zero j₀
    obtain ⟨hxmem, -⟩ := evalAt_pt_sub_const D τ₀ (jC N) hjC j₀
    obtain ⟨gx, hgx, -, hgxeq, -⟩ := germ D τ₀ x hxmem
    have hne := germ_eventually_ne_zero D τ₀ x hx0 hgx hgxeq
    have hsub := realize_sub_const_nhds (jC N) j₀ τ₀
    have hfalse : ∀ᶠ z in 𝓝[≠] (τ₀ : ℂ), False := by
      filter_upwards [hne, hsub, hgxeq, hgJeq, hconst.filter_mono nhdsWithin_le_nhds]
        with z h1 h2 h3 h4 h5
      apply h1
      rw [← h3]
      show realize N ((jC N - algebraMap ℂ (FC N) j₀ : FC N) : LaurentSeries ℂ) (ofComplex z) = 0
      rw [h2, h4, h5, hj₀def, sub_self]
    obtain ⟨z, hz⟩ := hfalse.exists
    exact hz
  have hopen : 𝓝 j₀ ≤ Filter.map gJ (𝓝 (τ₀ : ℂ)) :=
    (hgJ.eventually_constant_or_nhds_le_map_nhds).resolve_left hnc

  obtain ⟨ρ, hρ, hρJ⟩ : ∃ ρ > 0, ∀ z : ℂ, dist z (τ₀ : ℂ) < ρ → z ≠ (τ₀ : ℂ) →
      ∃ hz : 0 < z.im, jC N ∈ (D.pt ⟨z, hz⟩).toValuationSubring ∧
        (D.pt ⟨z, hz⟩).evalAt (jC N) = gJ z := by
    have h1 := hgJnear
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h1
    obtain ⟨ρ, hρ, h1⟩ := h1
    exact ⟨ρ, hρ, fun z hz hne => h1 hz hne⟩

  have hδ : ∀ m : ℕ, ∃ δ > 0, Metric.ball j₀ δ ⊆ gJ '' Metric.ball (τ₀ : ℂ) (min ρ (1 / ((m : ℝ) + 1))) :=
    fun m => Metric.mem_nhds_iff.mp
      (hopen (Filter.image_mem_map (Metric.ball_mem_nhds _ (lt_min hρ (by positivity)))))
  choose δ hδpos hδsub using hδ
  set T : ℕ → ℕ := fun m => ⌈(δ m)⁻¹⌉₊ with hTdef
  set M : ℕ → ℕ := fun m => (∑ i ∈ Finset.range (m + 1), T i) + m + 1 with hMdef
  have hMT : ∀ m, T m < M m := fun m => by
    have : T m ≤ ∑ i ∈ Finset.range (m + 1), T i :=
      Finset.single_le_sum (f := T) (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ m)
    simp only [hMdef]
    omega
  have hMmono : StrictMono M := by
    refine strictMono_nat_of_lt_succ fun m => ?_
    simp only [hMdef]
    rw [Finset.sum_range_succ _ (m + 1)]
    omega
  have hMpos : ∀ m, (0 : ℝ) < M m := fun m => by
    have := hMT m
    exact_mod_cast (Nat.zero_le _).trans_lt this
  have hMδ : ∀ m, ((M m : ℝ))⁻¹ < δ m := fun m =>
    inv_lt_of_inv_lt₀ (hδpos m) (by
      calc (δ m)⁻¹ ≤ T m := Nat.le_ceil _
        _ < M m := by exact_mod_cast hMT m)
  set cB : ℕ → AlgebraicClosure ℚ := fun m => v₀.evalAt (jB N) + ((M m : AlgebraicClosure ℚ))⁻¹ with hcBdef
  have hσc : ∀ m, σ (cB m) = j₀ + ((M m : ℂ))⁻¹ := fun m => by
    simp only [hcBdef, map_add, map_inv₀, map_natCast, hj₀]
  have hz : ∀ m : ℕ, ∃ z : ℂ, dist z (τ₀ : ℂ) < min ρ (1 / ((m : ℝ) + 1)) ∧ gJ z = j₀ + ((M m : ℂ))⁻¹ := by
    intro m
    have hmem : j₀ + ((M m : ℂ))⁻¹ ∈ Metric.ball j₀ (δ m) := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_inv, Complex.norm_natCast]
      exact hMδ m
    obtain ⟨z, hzb, hz⟩ := hδsub m hmem
    exact ⟨z, by simpa using hzb, hz⟩
  choose z hzd hzJ using hz
  have hzne : ∀ m, z m ≠ (τ₀ : ℂ) := fun m h => by
    have h1 := hzJ m
    rw [h, ← hj₀def] at h1
    have h2 : ((M m : ℂ))⁻¹ = 0 := by
      have := congrArg (fun t => t - j₀) h1
      simpa using this.symm
    rw [inv_eq_zero] at h2
    exact (hMpos m).ne' (by exact_mod_cast h2)
  have hzρ : ∀ m, dist (z m) (τ₀ : ℂ) < ρ := fun m => (hzd m).trans_le (min_le_left _ _)
  have hJm : ∀ m, ∃ hz : 0 < (z m).im, jC N ∈ (D.pt ⟨z m, hz⟩).toValuationSubring ∧
      (D.pt ⟨z m, hz⟩).evalAt (jC N) = gJ (z m) := fun m => hρJ (z m) (hzρ m) (hzne m)
  choose hzim hjCm hjCval using hJm
  set τ_ : ℕ → ℍ := fun m => ⟨z m, hzim m⟩ with hτdef
  have hzT : Tendsto z atTop (𝓝[≠] (τ₀ : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall hzne⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨m₀, hm₀⟩ := exists_nat_gt ε⁻¹
    refine ⟨m₀, fun m hm => (hzd m).trans_le ((min_le_right _ _).trans ?_)⟩
    rw [one_div]
    have h1 : ε⁻¹ < (m : ℝ) + 1 := hm₀.trans_le (by exact_mod_cast Nat.le_succ_of_le hm)
    exact (inv_lt_of_inv_lt₀ hε h1).le
  have hzT' : Tendsto z atTop (𝓝 (τ₀ : ℂ)) := tendsto_nhdsWithin_iff.mp hzT |>.1

  have hvm : ∀ m, ∃ v : Place (AlgebraicClosure ℚ) (FB N),
      v.toValuationSubring = (D.pt (τ_ m)).toValuationSubring.comap (phi N σ) ∧
      0 < (D.pt (τ_ m)).ord (phi N σ (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) (cB m))) := by
    intro m
    set x : FC N := jC N - algebraMap ℂ (FC N) (σ (cB m)) with hxdef
    have hphi : phi N σ (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) (cB m)) = x := by
      rw [map_sub, phi_jB, phi_algebraMap]
    have hx0 : x ≠ 0 := jC_sub_const_ne_zero _
    obtain ⟨hxmem, hxval⟩ := evalAt_pt_sub_const D (τ_ m) (jC N) (hjCm m) (σ (cB m))
    have hx00 : (D.pt (τ_ m)).evalAt x = 0 := by
      rw [hxdef, hxval, hjCval, hσc, hzJ, sub_self]
    obtain ⟨gx, hgx, hgxval, hgxeq, -⟩ := germ D (τ_ m) x hxmem
    have hord : 0 < (D.pt (τ_ m)).ord x :=
      ord_pt_pos' D (τ_ m) x hx0 gx hgx (by rw [hgxval, hx00]) hgxeq
    obtain ⟨v, hv⟩ := exists_place_comap σ (D.pt (τ_ m))
      ⟨(jB N - algebraMap (AlgebraicClosure ℚ) (FB N) (cB m))⁻¹, by
        rw [map_inv₀, hphi, AlgebraicCurve.Place.mem_iff_ord_nonneg _ (inv_ne_zero hx0), Place.ord_inv]
        omega⟩
    exact ⟨v, hv, by rw [hphi]; exact hord⟩
  choose v hvcomap hvord using hvm
  have hinj : Function.Injective v := by
    intro m n hmn
    by_contra hne
    have hc : cB m ≠ cB n := by
      intro h
      have h2 : ((M m : AlgebraicClosure ℚ))⁻¹ = ((M n : AlgebraicClosure ℚ))⁻¹ := add_left_cancel h
      rw [inv_inj, Nat.cast_inj] at h2
      exact hne (hMmono.injective h2)
    exact ne_of_ord_pos' D σ hc (v m) (v n) (hvcomap m) (hvcomap n) (hvord m) (hvord n) hmn

  have hord₀ : 0 < (D.pt τ₀).ord (phi N σ (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) (v₀.evalAt (jB N)))) := by
    set x : FC N := jC N - algebraMap ℂ (FC N) j₀ with hxdef
    have hphi : phi N σ (jB N - algebraMap (AlgebraicClosure ℚ) (FB N) (v₀.evalAt (jB N))) = x := by
      rw [map_sub, phi_jB, phi_algebraMap, ← hj₀]
    have hx0 : x ≠ 0 := jC_sub_const_ne_zero _
    obtain ⟨hxmem, hxval⟩ := evalAt_pt_sub_const D τ₀ (jC N) hjC j₀
    have hx00 : (D.pt τ₀).evalAt x = 0 := by
      rw [hxdef, hxval, ← hgJval, hj₀def, sub_self]
    obtain ⟨gx, hgx, hgxval, hgxeq, -⟩ := germ D τ₀ x hxmem
    rw [hphi]
    exact ord_pt_pos' D τ₀ x hx0 gx hgx (by rw [hgxval, hx00]) hgxeq
  have hne₀ : ∀ m, v m ≠ v₀ := fun m => by
    have hc : cB m ≠ v₀.evalAt (jB N) := by
      intro h
      have h2 : ((M m : AlgebraicClosure ℚ))⁻¹ = 0 := by
        have := congrArg (fun t => t - v₀.evalAt (jB N)) h
        simpa [hcBdef] using this
      rw [inv_eq_zero, Nat.cast_eq_zero] at h2
      exact (hMpos m).ne' (by exact_mod_cast h2)
    exact ne_of_ord_pos' D σ hc (v m) v₀ (hvcomap m) hcomap (hvord m) hord₀

  have hyf : ∀ y : FB N, ∃ m₀ : ℕ, y ≠ 0 → y ∈ v₀.toValuationSubring →
      ∃ gy : ℂ → ℂ, ContinuousAt gy (τ₀ : ℂ) ∧ gy (τ₀ : ℂ) = σ (v₀.evalAt y) ∧
        ∀ m, m₀ ≤ m → y ∈ (v m).toValuationSubring ∧ σ ((v m).evalAt y) = gy (z m) ∧ gy (z m) ≠ 0 := by
    intro y
    by_cases hy0 : y = 0
    · exact ⟨0, fun h => absurd hy0 h⟩
    by_cases hyv : y ∈ v₀.toValuationSubring
    · have hφy : phi N σ y ∈ (D.pt τ₀).toValuationSubring := by
        have h := hyv
        rw [hcomap, ValuationSubring.mem_comap] at h
        exact h
      obtain ⟨gy, hgy, hgyval, hgyeq, hgynear⟩ := germ D τ₀ (phi N σ y) hφy
      have hne := germ_eventually_ne_zero D τ₀ (phi N σ y) (phi_ne_zero σ hy0) hgy hgyeq
      obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.mp (hzT.eventually (hgynear.and hne))
      refine ⟨m₀, fun _ _ => ⟨gy, hgy.continuousAt, ?_, fun m hm => ?_⟩⟩
      · rw [hgyval, evalAt_transport σ v₀ (D.pt τ₀) hcomap hyv]
      · obtain ⟨⟨hz', hmem, hval⟩, hne'⟩ := hm₀ m hm
        have hmem' : phi N σ y ∈ (D.pt (τ_ m)).toValuationSubring := hmem
        have hval' : (D.pt (τ_ m)).evalAt (phi N σ y) = gy (z m) := hval
        have hyvm : y ∈ (v m).toValuationSubring := by
          rw [hvcomap, ValuationSubring.mem_comap]; exact hmem'
        refine ⟨hyvm, ?_, hne'⟩
        rw [evalAt_transport σ (v m) (D.pt (τ_ m)) (hvcomap m) hyvm, hval']
    · exact ⟨0, fun _ h => absurd h hyv⟩
  choose m₀ hm₀ using hyf

  have hfin : (v ⁻¹' (S : Set (Place (AlgebraicClosure ℚ) (FB N)))).Finite :=
    S.finite_toSet.preimage fun _ _ _ _ h => hinj h
  obtain ⟨n₀, hn₀⟩ := hfin.bddAbove
  set K : ℕ := (∑ y ∈ Y, m₀ y) + n₀ + 1 with hKdef
  have hKm : ∀ y ∈ Y, m₀ y ≤ K := fun y hy => by
    have : m₀ y ≤ ∑ y ∈ Y, m₀ y := Finset.single_le_sum (f := m₀) (fun _ _ => Nat.zero_le _) hy
    omega
  refine ⟨fun n => v (n + K), ?_, fun n => hne₀ _, ?_⟩
  · intro n hn
    have := hn₀ (show n + K ∈ v ⁻¹' (S : Set (Place (AlgebraicClosure ℚ) (FB N))) from hn)
    omega
  · intro y hy
    by_cases hy0 : y = 0
    · subst hy0
      have h1 : ∀ w : Place (AlgebraicClosure ℚ) (FB N), w.evalAt (0 : FB N) = 0 := fun w => by
        simpa using AlgebraicCurve.Place.evalAt_algebraMap w (0 : AlgebraicClosure ℚ)
      refine ⟨fun n => zero_mem _, fun h => absurd rfl h, ?_⟩
      simp only [h1, map_zero]
      exact tendsto_const_nhds
    · obtain ⟨gy, hgyc, hgy₀, hfacts⟩ := hm₀ y hy0 (hY y hy)
      have hK : ∀ n, m₀ y ≤ n + K := fun n => (hKm y hy).trans (Nat.le_add_left _ _)
      refine ⟨fun n => (hfacts _ (hK n)).1, fun _ n => ?_, ?_⟩
      · intro h0
        have h1 := (hfacts _ (hK n)).2.1
        rw [h0, map_zero] at h1
        exact (hfacts _ (hK n)).2.2 h1.symm
      · have hlim : Tendsto (fun n => gy (z (n + K))) atTop (𝓝 (gy (τ₀ : ℂ))) :=
          hgyc.tendsto.comp (hzT'.comp (tendsto_add_atTop_nat K))
        rw [← hgy₀]
        exact hlim.congr fun n => ((hfacts _ (hK n)).2.1).symm

end APPR
p2m_reactivate "P2MW.S_ModularCurve_exists_seq_place_tendsto_evalAt.APPR"

theorem solution (N : ℕ) [NeZero N]
    (v₀ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N))
    (hj : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        modularFunctionFieldBar N) ∈ v₀.toValuationSubring)
    (σ : AlgebraicClosure ℚ →+* ℂ)
    (S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)))
    (Y : Finset ↥(modularFunctionFieldBar N))
    (hY : ∀ y ∈ Y, y ∈ v₀.toValuationSubring) :
    ∃ v : ℕ → Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
      (∀ n, v n ∉ S) ∧ (∀ n, v n ≠ v₀) ∧
      ∀ y ∈ Y, (∀ n, y ∈ (v n).toValuationSubring) ∧ (y ≠ 0 → ∀ n, (v n).evalAt y ≠ 0) ∧
        Filter.Tendsto (fun n => σ ((v n).evalAt y)) Filter.atTop (nhds (σ (v₀.evalAt y))) :=
  APPR.main_int N v₀ hj σ S Y hY

end
p2m_reactivate "P2MW.S_ModularCurve_exists_seq_place_tendsto_evalAt.APPR"

end S_ModularCurve_exists_seq_place_tendsto_evalAt
end P2MW
export P2MW.S_ModularCurve_exists_seq_place_tendsto_evalAt (solution)
