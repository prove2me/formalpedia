-- Prove2me | solution 1 for ModularCurve.atkinLehner_complement_laws_of_fricke_of_atkinLehner_p
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/e057e58c-93db-5e8a-b306-2efd23267782

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_eq_self_of_coe_eq_coeffEmb_of_mem_gamma0
import Theorems.Thm_ModularCurve_atkinLehner_qExpand_pin_of_pin
import Theorems.Thm_ModularCurve_algEquiv_diamondAutHBar_comm_of_qExpand_of_diamondAutHBar_div
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_atkinLehner_complement_laws_of_fricke_of_atkinLehner_p
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.baseAut_x1ArithFrobC_apply"
p2m_attr_erase "simp" "ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_jqNGen ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow"
p2m_attr_erase "simp" "ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false

noncomputable section

namespace W0B1

p2m_open "UpperHalfPlane CongruenceSubgroup ModularCurve~coeffMap_injective~coeffMap_intSeriesC P2MW.S_ModularCurve_atkinLehner_complement_laws_of_fricke_of_atkinLehner_p.ModularCurve Matrix IntermediateField HahnSeries AlgebraicCurve"

open scoped MatrixGroups ModularForm Pointwise

section Groups

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

abbrev ΓGL (Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ) :=
  ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods_of_T_mem {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (ΓGL Γ).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples _

variable (M) in

def frickeGL [NeZero M] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne M])

@[scoped simp]
theorem val_frickeGL [NeZero M] :
    ((frickeGL M : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0] := rfl

theorem det_frickeGL [NeZero M] : ((frickeGL M).det : ℝ) = M := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_frickeGL, Matrix.det_fin_two_of]; ring

theorem det_frickeGL_pos [NeZero M] : 0 < ((frickeGL M).det : ℝ) := by
  rw [det_frickeGL]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)

theorem eq_frickeGL [NeZero M] {W : GL (Fin 2) ℝ}
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0]) : W = frickeGL M :=
  Units.ext (by rw [hW]; rfl)

theorem mapGL_eq_coe (γ : SL(2, ℤ)) : Matrix.SpecialLinearGroup.mapGL ℝ γ = (γ : GL (Fin 2) ℝ) := rfl

def scalarGL (a : ℝ) (ha : a ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, 0; 0, a]
    (by rw [Matrix.det_fin_two_of]; simpa using ha)

@[scoped simp]
theorem val_scalarGL (a : ℝ) (ha : a ≠ 0) :
    ((scalarGL a ha : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![a, 0; 0, a] := rfl

theorem det_scalarGL (a : ℝ) (ha : a ≠ 0) : ((scalarGL a ha).det : ℝ) = a * a := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_scalarGL, Matrix.det_fin_two_of]; ring

theorem scalarGL_smul (a : ℝ) (ha : a ≠ 0) (τ : ℍ) : scalarGL a ha • τ = τ := by
  have hdet : 0 < ((scalarGL a ha).det : ℝ) := by rw [det_scalarGL]; exact mul_self_pos.mpr ha
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos hdet]
  simp only [num, denom, val_scalarGL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.ofReal_zero, zero_mul, add_zero, zero_add]
  rw [mul_div_assoc, mul_div_cancel₀ _ (by exact_mod_cast ha)]

theorem slash_scalarGL (k : ℤ) (a : ℝ) (ha : a ≠ 0) (φ : ℍ → ℂ) :
    φ ∣[k] scalarGL a ha = (fun _ => ((|a * a| : ℝ) : ℂ) ^ (k - 1) * (a : ℂ) ^ (-k)) * φ := by
  have hdet : 0 < ((scalarGL a ha).det : ℝ) := by rw [det_scalarGL]; exact mul_self_pos.mpr ha
  funext τ
  rw [ModularForm.slash_apply, scalarGL_smul, Pi.mul_apply]
  have hσ : σ (scalarGL a ha) = ContinuousAlgEquiv.refl ℝ ℂ := by
    rw [σ, if_pos hdet]
  rw [hσ, ContinuousAlgEquiv.refl_apply, det_scalarGL]
  simp only [denom, val_scalarGL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.ofReal_zero, zero_mul, zero_add]
  ring

end Groups

section QExp

variable {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ)

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

include hT

theorem qC_mul {k₁ k₂ : ℤ} (f : ModularForm (ΓGL Γ) k₁) (g : ModularForm (ΓGL Γ) k₂) :
    qC (⇑f * ⇑g) = qC f * qC g := by
  rw [qC, qC, qC, ← map_mul, ← ModularForm.coe_mul,
    ModularForm.qExpansion_mul one_pos (one_mem_strictPeriods_of_T_mem hT)]

theorem qC_add {k : ℤ} (f g : ModularForm (ΓGL Γ) k) : qC (⇑f + ⇑g) = qC f + qC g := by
  rw [qC, qC, qC, ← map_add,
    ModularForm.qExpansion_add one_pos (one_mem_strictPeriods_of_T_mem hT) f g]

theorem qC_smul {k : ℤ} (c : ℂ) (f : ModularForm (ΓGL Γ) k) :
    qC (c • ⇑f) = HahnSeries.C c * qC f := by
  rw [qC, qC, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_of_T_mem hT) c f,
    ← HahnSeries.ofPowerSeries_C, ← map_mul, PowerSeries.smul_eq_C_mul]

theorem qC_neg {k : ℤ} (f : ModularForm (ΓGL Γ) k) : qC (-⇑f) = -qC f := by
  rw [qC, qC, ModularForm.qExpansion_neg one_pos (one_mem_strictPeriods_of_T_mem hT) f, map_neg]

theorem qC_eq_zero_iff {k : ℤ} (f : ModularForm (ΓGL Γ) k) : qC f = 0 ↔ f = 0 := by
  rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos (one_mem_strictPeriods_of_T_mem hT) f]
  exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective

omit hT in
theorem qC_zero : qC (0 : ℍ → ℂ) = 0 := by rw [qC, qExpansion_zero, map_zero]

omit hT in
theorem qC_one : qC (1 : ℍ → ℂ) = 1 := by rw [qC, qExpansion_one, map_one]

omit hT in

theorem coe_smul_form {k : ℤ} (c : ℂ) (f : ModularForm (ΓGL Γ) k) : ⇑(c • f) = c • ⇑f := by
  first | rfl | simp

theorem qC_const_mul {k : ℤ} (c : ℂ) (f : ModularForm (ΓGL Γ) k) :
    qC ((fun _ => c) * ⇑f) = HahnSeries.C c * qC f := by
  rw [show ((fun _ => c) * ⇑f : ℍ → ℂ) = c • ⇑f from rfl, qC_smul hT]

omit hT in
theorem intSeriesC_add' {K : Type*} [Field K] (p p' : PowerSeries ℤ) :
    intSeriesC K (p + p') = intSeriesC K p + intSeriesC K p' := by
  simp [intSeriesC]

omit hT in
theorem intSeriesC_neg' {K : Type*} [Field K] (p : PowerSeries ℤ) :
    intSeriesC K (-p) = -intSeriesC K p := by
  simp [intSeriesC]

theorem mul_mem_ratios {a b : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ)
    (hb : b ∈ intFormRatiosC ℚ Γ) : a * b ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, hg₁0, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, rfl⟩ := hb
  have h1 := one_mem_strictPeriods_of_T_mem hT
  refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, pf₁ * pf₂, pg₁ * pg₂, ?_, ?_, ?_, ?_⟩
  · rw [IsIntegralQExp, map_mul, hf₁, hf₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos h1 f₁ f₂).symm
  · rw [IsIntegralQExp, map_mul, hg₁, hg₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos h1 g₁ g₂).symm
  · rw [intSeriesC_mul]; exact mul_ne_zero hg₁0 hg₂0
  · rw [intSeriesC_mul, intSeriesC_mul, div_mul_div_comm]

theorem add_mem_ratios {a b : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ)
    (hb : b ∈ intFormRatiosC ℚ Γ) : a + b ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, hg₁0, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, rfl⟩ := hb
  have h1 := one_mem_strictPeriods_of_T_mem hT
  refine ⟨k₁ + k₂, f₁.mul g₂ + (g₁.mul f₂), g₁.mul g₂, pf₁ * pg₂ + pg₁ * pf₂, pg₁ * pg₂,
    ?_, ?_, ?_, ?_⟩
  · rw [IsIntegralQExp, map_add, map_mul, map_mul, hf₁, hf₂, hg₁, hg₂, ModularForm.coe_add,
      ModularForm.qExpansion_add one_pos h1, ModularForm.coe_mul, ModularForm.coe_mul,
      ModularForm.qExpansion_mul_coe one_pos h1, ModularForm.qExpansion_mul_coe one_pos h1]
  · rw [IsIntegralQExp, map_mul, hg₁, hg₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos h1 g₁ g₂).symm
  · rw [intSeriesC_mul]; exact mul_ne_zero hg₁0 hg₂0
  · rw [intSeriesC_add', intSeriesC_mul, intSeriesC_mul, intSeriesC_mul,
      div_add_div _ _ hg₁0 hg₂0]

theorem neg_mem_ratios {a : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ) :
    -a ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := ha
  refine ⟨k, -f, g, -pf, pg, ?_, hg, hg0, ?_⟩
  · rw [IsIntegralQExp, map_neg, hf, ModularForm.coe_neg]
    exact (ModularForm.qExpansion_neg one_pos (one_mem_strictPeriods_of_T_mem hT) f).symm
  · rw [intSeriesC_neg', neg_div]

omit hT in
theorem inv_mem_ratios {a : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ) :
    a⁻¹ ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := ha
  by_cases hf0 : intSeriesC ℚ pf = 0
  · rw [hf0, zero_div, _root_.inv_zero, ← zero_div (intSeriesC ℚ pg), ← hf0]
    exact ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
  · exact ⟨k, g, f, pg, pf, hg, hf, hf0, by rw [inv_div]⟩

theorem isIntegralQExp_const (n : ℤ) :
    IsIntegralQExp ((ModularForm.const (n : ℂ) : ModularForm (ΓGL Γ) 0) : ℍ → ℂ)
      (PowerSeries.C n) := by
  have hc : ((ModularForm.const (n : ℂ) : ModularForm (ΓGL Γ) 0) : ℍ → ℂ) =
      (n : ℂ) • ((1 : ModularForm (ΓGL Γ) 0) : ℍ → ℂ) := by
    funext z
    rw [Pi.smul_apply, ModularForm.const_apply, ModularForm.one_coe_eq_one, Pi.one_apply,
      smul_eq_mul, mul_one]
  rw [IsIntegralQExp, PowerSeries.map_C, hc,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_of_T_mem hT),
    ModularForm.qExpansion_one, PowerSeries.smul_eq_C_mul, mul_one, eq_intCast]

theorem algebraMap_mem_ratios (c : ℚ) : algebraMap ℚ (LaurentSeries ℚ) c ∈ intFormRatiosC ℚ Γ := by
  have hden : ((c.den : ℤ) : ℚ) ≠ 0 := by exact_mod_cast c.den_nz
  refine ⟨0, ModularForm.const (c.num : ℂ), ModularForm.const (c.den : ℂ),
    PowerSeries.C (c.num : ℤ), PowerSeries.C (c.den : ℤ), isIntegralQExp_const hT _, ?_, ?_, ?_⟩
  · have := isIntegralQExp_const (Γ := Γ) hT (c.den : ℤ)
    push_cast at this
    exact this
  · rw [intSeriesC, PowerSeries.map_C, HahnSeries.ofPowerSeries_C, eq_intCast]
    exact (map_ne_zero_iff _ HahnSeries.C_injective).mpr hden
  · rw [intSeriesC, intSeriesC, PowerSeries.map_C, PowerSeries.map_C, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_C, LaurentSeries.algebraMap_apply, eq_intCast,
      eq_intCast, eq_div_iff ((map_ne_zero_iff _ HahnSeries.C_injective).mpr hden), ← map_mul]
    congr 1
    push_cast
    exact Rat.mul_den_eq_num c

def ratioField : IntermediateField ℚ (LaurentSeries ℚ) where
  carrier := intFormRatiosC ℚ Γ
  mul_mem' ha hb := mul_mem_ratios hT ha hb
  one_mem' := by simpa using algebraMap_mem_ratios (Γ := Γ) hT 1
  add_mem' ha hb := add_mem_ratios hT ha hb
  zero_mem' := by simpa using algebraMap_mem_ratios (Γ := Γ) hT 0
  algebraMap_mem' c := algebraMap_mem_ratios hT c
  inv_mem' a ha := inv_mem_ratios ha

theorem mem_ratios_of_mem {y : LaurentSeries ℚ} (hy : y ∈ qExpFunctionFieldC ℚ Γ) :
    y ∈ intFormRatiosC ℚ Γ := by
  have hle : qExpFunctionFieldC ℚ Γ ≤ ratioField (Γ := Γ) hT :=
    IntermediateField.adjoin_le_iff.mpr (fun _ h => h)
  exact hle hy

end QExp

section Coeff

local notation "Qb" => AlgebraicClosure ℚ

variable (ι : Qb →+* ℂ)

theorem coeffMap_injective : Function.Injective (coeffMap ι) := fun x y h => by
  ext k
  exact ι.injective (by simpa using congrArg (fun z => z.coeff k) h)

theorem coeffMap_coeffEmb (y : LaurentSeries ℚ) :
    coeffMap ι (coeffEmb Qb y) = coeffMap (algebraMap ℚ ℂ) y := by
  rw [coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (Subsingleton.elim _ _) y

omit ι in
theorem coeffMap_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    coeffMap (algebraMap ℚ ℂ) (intSeriesC ℚ p) = qC F := by
  rw [qC, ← h]
  ext n
  simp only [intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

theorem coeffMap_coeffEmb_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    coeffMap ι (coeffEmb Qb (intSeriesC ℚ p)) = qC F := by
  rw [coeffMap_coeffEmb, coeffMap_intSeriesC h]

theorem coeffMap_C {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (c : R) :
    coeffMap f (HahnSeries.C c) = HahnSeries.C (f c) := by
  rw [HahnSeries.C_apply, HahnSeries.C_apply, coeffMap_single]

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

theorem ofPowerSeries_eq_qExpand {ℓ : ℕ} [NeZero ℓ] (p p' : PowerSeries ℂ)
    (h : ∀ n, PowerSeries.coeff n p' = if ℓ ∣ n then PowerSeries.coeff (n / ℓ) p else 0) :
    ofPowerSeries ℤ ℂ p' = qExpand ℂ ℓ (ofPowerSeries ℤ ℂ p) := by
  ext m
  by_cases hdvd : (ℓ : ℤ) ∣ m
  · obtain ⟨j, rfl⟩ := hdvd
    rw [qExpand_coeff_mul, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
    have hℓ0 : (0 : ℤ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
    by_cases hj : j < 0
    · rw [if_pos hj, if_pos (mul_neg_of_pos_of_neg hℓ0 hj)]
    · rw [if_neg hj, if_neg (by push Not at hj ⊢; positivity), h]
      have h1 : ((ℓ : ℤ) * j).natAbs = ℓ * j.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      rw [h1, if_pos (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne ℓ))]
  · rw [qExpand_coeff_of_not_dvd ℓ _ hdvd, PowerSeries.coeff_coe]
    split_ifs with hm
    · rfl
    · rw [h, if_neg]
      rintro ⟨c, hc⟩
      apply hdvd
      refine ⟨c, ?_⟩
      have : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg (le_of_not_gt hm)
      rw [← this, hc]; push_cast; ring

theorem qC_comp_heckeDiag {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (F : ModularForm (ΓGL Γ) k) (ℓ : ℕ) [NeZero ℓ] :
    qC (fun τ => F (ModularForm.heckeDiagMatrix ℓ • τ)) = qExpand ℂ ℓ (qC F) :=
  ofPowerSeries_eq_qExpand _ _ fun n =>
    ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul F (one_mem_strictPeriods_of_T_mem hT)
      (NeZero.ne ℓ) n

end Coeff

section Degeneracy

theorem gamma0_le_of_dvd {a b : ℕ} (h : a ∣ b) : Gamma0 b ≤ Gamma0 a := by
  intro A hA
  rw [Gamma0_mem] at hA ⊢
  have := congrArg (ZMod.castHom h (ZMod a)) hA
  rwa [map_intCast, map_zero] at this

theorem qExpand_mem_gamma0 (n : ℕ) : ∀ (hn : n ≠ 0) (m : ℕ) [NeZero m] (y : LaurentSeries ℚ),
    y ∈ qExpFunctionFieldC ℚ (Gamma0 m) →
      haveI : NeZero n := ⟨hn⟩; qExpand ℚ n y ∈ qExpFunctionFieldC ℚ (Gamma0 (m * n)) := by
  induction n using Nat.recOnMul with
  | zero => intro hn; exact absurd rfl hn
  | one =>
    intro _ m _ y hy
    rw [qExpand_one_apply, mul_one]
    exact hy
  | prime ℓ hℓ =>
    intro _ m _ y hy
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hβ : HeckeBetaHDefined m ⊤ ℓ :=
      ((ModularCurve.heckeDiamondInputsHAll m ⊤).heckeInputsHAlong ℓ hℓ).betaHDefined
    have hy' : y ∈ xHFunctionField m ⊤ := by
      show y ∈ qExpFunctionFieldC ℚ (CohCarrier.GammaH m ⊤)
      rw [CohCarrier.GammaH_top]
      exact hy
    have h : qExpand ℚ ℓ y ∈ qExpFunctionFieldC ℚ (CohCarrier.GammaH m ⊤ ⊓ Gamma0 (m * ℓ)) := hβ y hy'
    have hle : Gamma0 (m * ℓ) ≤ CohCarrier.GammaH m ⊤ ⊓ Gamma0 (m * ℓ) := by
      rw [CohCarrier.GammaH_top]
      exact le_inf (gamma0_le_of_dvd (dvd_mul_right m ℓ)) le_rfl
    exact qExpFunctionFieldC_mono ℚ hle h
  | mul a b iha ihb =>
    intro hab m _ y hy
    have ha : a ≠ 0 := left_ne_zero_of_mul hab
    have hb : b ≠ 0 := right_ne_zero_of_mul hab
    haveI : NeZero a := ⟨ha⟩
    haveI : NeZero b := ⟨hb⟩
    have h1 := iha ha m y hy
    have h2 := ihb hb (m * a) (qExpand ℚ a y) h1
    have e : qExpand ℚ b (qExpand ℚ a y) = (haveI : NeZero (a * b) := ⟨hab⟩; qExpand ℚ (a * b) y) := by
      rw [qExpand_qExpand, qExpand_congr (mul_comm b a)]
    rw [← mul_assoc, ← e]
    exact h2

end Degeneracy

section B1Top

local notation "Qb" => AlgebraicClosure ℚ

theorem qC_ne_zero_of_witness {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {g : ModularForm (ΓGL Γ) k}
    {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : qC g ≠ 0 := by
  rw [← coeffMap_intSeriesC hg]
  exact (map_ne_zero_iff _ (RingHom.injective _)).mpr hg0

theorem coe_trans_symm_apply_eq_coeffEmb_qExpand_of_level_one
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (ι : AlgebraicClosure ℚ →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0])
    (w : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hw₁ : ∀ (x : ↥(xHFunctionFieldBar M H)) (k : ℤ)
        (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k),
        coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) →
        coeffMap ι ((w x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] W)) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] W)))
    (θp : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθp : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
          (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
          ((θp f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
            qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ))) :
    ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (u : LaurentSeries ℚ) →
        (((w.trans θp.symm) f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (M / p) (u : LaurentSeries ℚ)) := by
  haveI hp0 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro f u hfu
  have hM : p * (M / p) = M := Nat.mul_div_cancel' hpM
  have hT1 : ModularGroup.T ∈ (⊤ : Subgroup SL(2, ℤ)) := Subgroup.mem_top _
  have hTM : ModularGroup.T ∈ CohCarrier.GammaH M H := translation_mem_GammaH M H
  obtain ⟨k, F, G, pf, pg, hF, hG, hg0, hu⟩ := mem_ratios_of_mem hT1 u.2
  have hle : ΓGL (CohCarrier.GammaH M H) ≤ ΓGL (⊤ : Subgroup SL(2, ℤ)) := Subgroup.map_mono le_top
  have hqG : qC (⇑G) ≠ 0 := qC_ne_zero_of_witness hG hg0

  have h0 : coeffMap ι (f : LaurentSeries Qb) *
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(restrictForm hle G)) =
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(restrictForm hle F)) := by
    show coeffMap ι (f : LaurentSeries Qb) * qC (⇑G) = qC (⇑F)
    rw [hfu, hu, map_div₀, map_div₀, coeffMap_coeffEmb_intSeriesC ι hF, coeffMap_coeffEmb_intSeriesC ι hG]
    exact div_mul_cancel₀ _ hqG
  have h1 := hw₁ f k (restrictForm hle F) (restrictForm hle G) h0
  change coeffMap ι ((w f : ↥(xHFunctionFieldBar M H)) : LaurentSeries Qb) * qC (⇑(restrictForm hle G) ∣[k] W) =
    qC (⇑(restrictForm hle F) ∣[k] W) at h1

  have hWS : W = Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S * ModularForm.heckeDiagMatrix M := by
    refine Units.ext ?_
    rw [hW, Units.val_mul, ModularForm.val_heckeDiagMatrix (NeZero.ne M), mapGL_eq_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_S]
  have hslash : ∀ (Φ : ModularForm (ΓGL (⊤ : Subgroup SL(2, ℤ))) k),
      (⇑Φ ∣[k] W) = (fun _ => ((M : ℂ) ^ (k - 1))) * fun τ => Φ (ModularForm.heckeDiagMatrix M • τ) := by
    intro Φ
    rw [hWS, SlashAction.slash_mul,
      SlashInvariantForm.slash_action_eqn Φ _
        (Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) (Subgroup.mem_top ModularGroup.S))]
    funext τ
    rw [ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne M)]
    rfl
  have hqexp : ∀ (Φ : ModularForm (ΓGL (⊤ : Subgroup SL(2, ℤ))) k),
      qC (⇑(restrictForm hle Φ) ∣[k] W) = qExpand ℂ M (HahnSeries.C ((M : ℂ) ^ (k - 1)) * qC (⇑Φ)) := by
    intro Φ
    have e1 : (⇑(restrictForm hle Φ) ∣[k] W) =
        fun τ => ((((M : ℂ) ^ (k - 1)) • restrictForm hle Φ) (ModularForm.heckeDiagMatrix M • τ)) := by
      rw [coe_restrictForm, hslash]
      funext τ
      rw [coe_smul_form]
      rfl
    rw [e1, qC_comp_heckeDiag hTM, coe_smul_form, qC_smul hTM]
    rfl
  rw [hqexp F, hqexp G, map_mul, map_mul, ← (show coeffMap ι (f : LaurentSeries Qb) * qC (⇑G) = qC (⇑F) from h0),
    map_mul, mul_left_comm] at h1
  have hc : (HahnSeries.C ((M : ℂ) ^ (k - 1)) : LaurentSeries ℂ) ≠ 0 :=
    (map_ne_zero_iff _ HahnSeries.C_injective).mpr (zpow_ne_zero _ (by exact_mod_cast NeZero.ne M))
  have hne : qExpand ℂ M (qC (⇑G)) ≠ 0 := (map_ne_zero_iff _ (qExpand_injective M)).mpr hqG
  have hne' : qExpand ℂ M (HahnSeries.C ((M : ℂ) ^ (k - 1))) ≠ 0 :=
    (map_ne_zero_iff _ (qExpand_injective M)).mpr hc
  have hX : coeffMap ι ((w f : ↥(xHFunctionFieldBar M H)) : LaurentSeries Qb) =
      qExpand ℂ M (coeffMap ι (f : LaurentSeries Qb)) :=
    mul_right_cancel₀ hne (mul_left_cancel₀ hne' h1)
  have hwf : ((w f : ↥(xHFunctionFieldBar M H)) : LaurentSeries Qb) =
      coeffEmb Qb (qExpand ℚ M (u : LaurentSeries ℚ)) := by
    apply coeffMap_injective ι
    rw [hX, hfu]
    simp only [coeffEmb, coeffMap_qExpand]

  have huQ : qExpand ℚ (M / p) (u : LaurentSeries ℚ) ∈ qExpFunctionFieldC ℚ (Gamma0 (M / p)) := by
    have hu1 : (u : LaurentSeries ℚ) ∈ qExpFunctionFieldC ℚ (Gamma0 1) := qExpFunctionFieldC_mono ℚ le_top u.2
    have := qExpand_mem_gamma0 (M / p) (NeZero.ne _) 1 (u : LaurentSeries ℚ) hu1
    rwa [one_mul] at this
  have hGH : CohCarrier.GammaH M H ≤ Gamma0 (M / p) :=
    (CohCarrier.GammaH_le_Gamma0 H).trans (gamma0_le_of_dvd (Nat.div_dvd_of_dvd hpM))
  have hGN : CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) ≤ Gamma0 (M / p) := CohCarrier.GammaH_le_Gamma0 _
  have huM : qExpand ℚ (M / p) (u : LaurentSeries ℚ) ∈ xHFunctionField M H := qExpFunctionFieldC_mono ℚ hGH huQ
  have huN : qExpand ℚ (M / p) (u : LaurentSeries ℚ) ∈ xHFunctionField (M / p) (infSubgroup p M H hpM) :=
    qExpFunctionFieldC_mono ℚ hGN huQ

  let g : ↥(xHFunctionFieldBar M H) :=
    ⟨coeffEmb Qb (qExpand ℚ (M / p) (u : LaurentSeries ℚ)), coeffEmb_mem_laurentBaseChange Qb huM⟩
  have h2 := hθp g ⟨coeffEmb Qb (qExpand ℚ (M / p) (u : LaurentSeries ℚ)), coeffEmb_mem_laurentBaseChange Qb huN⟩ rfl
  have h3 : θp g = w f := by
    apply Subtype.ext
    rw [h2, hwf]
    show qExpand Qb p (coeffEmb Qb (qExpand ℚ (M / p) (u : LaurentSeries ℚ))) = _
    rw [coeffEmb, ← coeffMap_qExpand, qExpand_qExpand, qExpand_congr hM]
  rw [AlgEquiv.trans_apply, ← h3, AlgEquiv.symm_apply_apply]

end B1Top

section B1Delta

local notation "Qb" => AlgebraicClosure ℚ

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {p : ℕ} [NeZero p]

def dilMat (p : ℕ) [NeZero p] (γ : SL(2, ℤ)) (h : (p : ℤ) ∣ γ 1 0) : SL(2, ℤ) :=
  ⟨!![γ 0 0, p * γ 0 1; γ 1 0 / p, γ 1 1], by
    obtain ⟨c, hc⟩ := h
    have hp : (p : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne p
    have hd := γ.prop
    rw [Matrix.det_fin_two] at hd
    rw [Matrix.det_fin_two_of, hc, Int.mul_ediv_cancel_left _ hp]
    linear_combination hd + γ 0 1 * hc⟩

theorem heckeDiag_mul_mapGL_mul_inv (γ : SL(2, ℤ)) (h : (p : ℤ) ∣ γ 1 0) :
    ModularForm.heckeDiagMatrix p * Matrix.SpecialLinearGroup.mapGL ℝ γ * (ModularForm.heckeDiagMatrix p)⁻¹ =
      Matrix.SpecialLinearGroup.mapGL ℝ (dilMat p γ h) := by
  rw [mul_inv_eq_iff_eq_mul, mapGL_eq_coe, mapGL_eq_coe]
  ext i j
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  obtain ⟨c, hc⟩ := h
  have hc' : (γ 1 0 / p : ℤ) = c := by rw [hc, Int.mul_ediv_cancel_left _ (by exact_mod_cast NeZero.ne p)]
  simp only [Units.val_mul, ModularForm.val_heckeDiagMatrix (NeZero.ne p)]
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_two, dilMat, hc, hc']; try ring)

theorem le_conj_heckeDiag (hpM : p ∣ M) :
    ΓGL (CohCarrier.GammaH M H) ≤
      ConjAct.toConjAct (ModularForm.heckeDiagMatrix p)⁻¹ • ΓGL (⊤ : Subgroup SL(2, ℤ)) := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  have hM0 : ((δ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp (CohCarrier.GammaH_le_Gamma0 H hδ)
  have h10 : (p : ℤ) ∣ δ 1 0 :=
    (Int.natCast_dvd_natCast.mpr hpM).trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hM0)
  exact ⟨dilMat p δ h10, Subgroup.mem_top _, (heckeDiag_mul_mapGL_mul_inv δ h10).symm⟩

def dilForm (hpM : p ∣ M) {k : ℤ} (F : ModularForm (ΓGL (⊤ : Subgroup SL(2, ℤ))) k) :
    ModularForm (ΓGL (CohCarrier.GammaH M H)) k :=
  restrictForm (le_conj_heckeDiag (H := H) hpM) (ModularForm.translate F (ModularForm.heckeDiagMatrix p))

@[scoped simp]
theorem coe_dilForm (hpM : p ∣ M) {k : ℤ} (F : ModularForm (ΓGL (⊤ : Subgroup SL(2, ℤ))) k) :
    ⇑(dilForm (H := H) hpM F) = ⇑F ∣[k] ModularForm.heckeDiagMatrix p := rfl

omit [NeZero p] in

theorem coe_trans_symm_apply_eq_coeffEmb_qExpand_of_qExpand_level_one
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (ι : AlgebraicClosure ℚ →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0])
    (w : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hw₁ : ∀ (x : ↥(xHFunctionFieldBar M H)) (k : ℤ)
        (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k),
        coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) →
        coeffMap ι ((w x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] W)) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] W)))
    (θp : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθp₂ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        ∀ (c : (ZMod (M / p))ˣ), (c : ZMod (M / p)) = (p : ZMod (M / p)) →
          ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
            (f : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)) →
            ((θp f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
              ((diamondAutHBar (M / p) (infSubgroup p M H hpM) c u :
                  ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ))) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))),
      (f : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p (u : LaurentSeries ℚ)) →
        (((w.trans θp.symm) f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M (u : LaurentSeries ℚ)) := by
  haveI hp0 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro f u hfu
  have hp : p.Prime := Fact.out
  have hM : p * (M / p) = M := Nat.mul_div_cancel' hpM
  have hMR : (p : ℝ) * ((M / p : ℕ) : ℝ) = (M : ℝ) := by exact_mod_cast hM
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hT1 : ModularGroup.T ∈ (⊤ : Subgroup SL(2, ℤ)) := Subgroup.mem_top _
  have hTM : ModularGroup.T ∈ CohCarrier.GammaH M H := translation_mem_GammaH M H
  obtain ⟨k, F, G, pf, pg, hF, hG, hg0, hu⟩ := mem_ratios_of_mem hT1 u.2
  have hle : ΓGL (CohCarrier.GammaH M H) ≤ ΓGL (⊤ : Subgroup SL(2, ℤ)) := Subgroup.map_mono le_top
  have hqG : qC (⇑G) ≠ 0 := qC_ne_zero_of_witness hG hg0

  have hY : coeffMap ι (coeffEmb Qb (u : LaurentSeries ℚ)) * qC (⇑G) = qC (⇑F) := by
    rw [hu, map_div₀, map_div₀, coeffMap_coeffEmb_intSeriesC ι hF, coeffMap_coeffEmb_intSeriesC ι hG]
    exact div_mul_cancel₀ _ hqG
  have hqdil : ∀ Φ : ModularForm (ΓGL (⊤ : Subgroup SL(2, ℤ))) k,
      qC (⇑(dilForm (H := H) hpM Φ)) = qExpand ℂ p (HahnSeries.C ((p : ℂ) ^ (k - 1)) * qC (⇑Φ)) := by
    intro Φ
    have e1 : (⇑(dilForm (H := H) hpM Φ)) =
        fun τ => ((((p : ℂ) ^ (k - 1)) • restrictForm hle Φ) (ModularForm.heckeDiagMatrix p • τ)) := by
      rw [coe_dilForm]
      funext τ
      rw [ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne p), coe_smul_form]
      rfl
    rw [e1, qC_comp_heckeDiag hTM, coe_smul_form, qC_smul hTM]
    rfl
  have hιδ : coeffMap ι (f : LaurentSeries Qb) = qExpand ℂ p (coeffMap ι (coeffEmb Qb (u : LaurentSeries ℚ))) := by
    rw [hfu]
    simp only [coeffEmb, coeffMap_qExpand]
  have h0 : coeffMap ι (f : LaurentSeries Qb) *
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(dilForm (H := H) hpM G)) =
      HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(dilForm (H := H) hpM F)) := by
    show coeffMap ι (f : LaurentSeries Qb) * qC (⇑(dilForm (H := H) hpM G)) = qC (⇑(dilForm (H := H) hpM F))
    rw [hιδ, hqdil F, hqdil G, map_mul, map_mul, ← hY, map_mul]
    ring
  have h1 := hw₁ f k (dilForm (H := H) hpM F) (dilForm (H := H) hpM G) h0
  change coeffMap ι ((w f : ↥(xHFunctionFieldBar M H)) : LaurentSeries Qb) * qC (⇑(dilForm (H := H) hpM G) ∣[k] W) =
    qC (⇑(dilForm (H := H) hpM F) ∣[k] W) at h1

  have hmat : ModularForm.heckeDiagMatrix p * W =
      Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S * ModularForm.heckeDiagMatrix (M / p) * scalarGL (p : ℝ) hpR := by
    refine Units.ext ?_
    rw [Units.val_mul, hW, Units.val_mul, Units.val_mul, ModularForm.val_heckeDiagMatrix (NeZero.ne p),
      ModularForm.val_heckeDiagMatrix (NeZero.ne (M / p)), val_scalarGL, mapGL_eq_coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_S]; try (rw [← hMR]; ring))
  set κ : ℂ := ((|(p : ℝ) * (p : ℝ)| : ℝ) : ℂ) ^ (k - 1) * ((p : ℝ) : ℂ) ^ (-k) with hκ
  have hslashW : ∀ Φ : ModularForm (ΓGL (⊤ : Subgroup SL(2, ℤ))) k,
      (⇑(dilForm (H := H) hpM Φ) ∣[k] W) =
        fun τ => (((κ * ((M / p : ℕ) : ℂ) ^ (k - 1))) • restrictForm hle Φ) (ModularForm.heckeDiagMatrix (M / p) • τ) := by
    intro Φ
    rw [coe_dilForm, ← SlashAction.slash_mul, hmat, SlashAction.slash_mul, SlashAction.slash_mul,
      SlashInvariantForm.slash_action_eqn Φ _
        (Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) (Subgroup.mem_top ModularGroup.S)),
      slash_scalarGL]
    funext τ
    rw [Pi.mul_apply, ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne (M / p)), coe_smul_form, Pi.smul_apply,
      smul_eq_mul, coe_restrictForm]
    simp only [hκ]
    ring
  have hqW : ∀ Φ : ModularForm (ΓGL (⊤ : Subgroup SL(2, ℤ))) k,
      qC (⇑(dilForm (H := H) hpM Φ) ∣[k] W) =
        qExpand ℂ (M / p) (HahnSeries.C (κ * ((M / p : ℕ) : ℂ) ^ (k - 1)) * qC (⇑Φ)) := by
    intro Φ
    rw [hslashW, qC_comp_heckeDiag hTM, coe_smul_form, qC_smul hTM]
    rfl
  rw [hqW F, hqW G, map_mul (qExpand ℂ (M / p)), map_mul (qExpand ℂ (M / p)), ← hY, map_mul (qExpand ℂ (M / p)),
    mul_left_comm] at h1
  have hκ0 : κ * ((M / p : ℕ) : ℂ) ^ (k - 1) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (zpow_ne_zero _ ?_) (zpow_ne_zero _ ?_)) (zpow_ne_zero _ ?_)
    · exact_mod_cast (abs_ne_zero.mpr (mul_ne_zero hpR hpR))
    · exact_mod_cast hpR
    · exact_mod_cast NeZero.ne (M / p)
  have hc : (HahnSeries.C (κ * ((M / p : ℕ) : ℂ) ^ (k - 1)) : LaurentSeries ℂ) ≠ 0 :=
    (map_ne_zero_iff _ HahnSeries.C_injective).mpr hκ0
  have hne : qExpand ℂ (M / p) (qC (⇑G)) ≠ 0 := (map_ne_zero_iff _ (qExpand_injective (M / p))).mpr hqG
  have hne' : qExpand ℂ (M / p) (HahnSeries.C (κ * ((M / p : ℕ) : ℂ) ^ (k - 1))) ≠ 0 :=
    (map_ne_zero_iff _ (qExpand_injective (M / p))).mpr hc
  have hX : coeffMap ι ((w f : ↥(xHFunctionFieldBar M H)) : LaurentSeries Qb) =
      qExpand ℂ (M / p) (coeffMap ι (coeffEmb Qb (u : LaurentSeries ℚ))) :=
    mul_right_cancel₀ hne (mul_left_cancel₀ hne' h1)
  have hwf : ((w f : ↥(xHFunctionFieldBar M H)) : LaurentSeries Qb) =
      coeffEmb Qb (qExpand ℚ (M / p) (u : LaurentSeries ℚ)) := by
    apply coeffMap_injective ι
    rw [hX]
    simp only [coeffEmb, coeffMap_qExpand]

  have hu1 : (u : LaurentSeries ℚ) ∈ qExpFunctionFieldC ℚ (Gamma0 1) := qExpFunctionFieldC_mono ℚ le_top u.2
  have huQ : qExpand ℚ (M / p) (u : LaurentSeries ℚ) ∈ qExpFunctionFieldC ℚ (Gamma0 (M / p)) := by
    have := qExpand_mem_gamma0 (M / p) (NeZero.ne _) 1 (u : LaurentSeries ℚ) hu1
    rwa [one_mul] at this
  have huMM : qExpand ℚ M (u : LaurentSeries ℚ) ∈ qExpFunctionFieldC ℚ (Gamma0 M) := by
    have := qExpand_mem_gamma0 M (NeZero.ne _) 1 (u : LaurentSeries ℚ) hu1
    rwa [one_mul] at this
  have hGN : CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) ≤ Gamma0 (M / p) := CohCarrier.GammaH_le_Gamma0 _
  have huN : qExpand ℚ (M / p) (u : LaurentSeries ℚ) ∈ xHFunctionField (M / p) (infSubgroup p M H hpM) :=
    qExpFunctionFieldC_mono ℚ hGN huQ
  have huM : qExpand ℚ M (u : LaurentSeries ℚ) ∈ xHFunctionField M H :=
    qExpFunctionFieldC_mono ℚ (CohCarrier.GammaH_le_Gamma0 H) huMM

  have hcop : Nat.Coprime p (M / p) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hpM2 ?_
    rw [pow_two, ← hM]
    exact Nat.mul_dvd_mul_left p h
  let c : (ZMod (M / p))ˣ := ZMod.unitOfCoprime p hcop
  have hcp : (c : ZMod (M / p)) = (p : ZMod (M / p)) := ZMod.coe_unitOfCoprime p hcop
  let g : ↥(xHFunctionFieldBar M H) :=
    ⟨coeffEmb Qb (qExpand ℚ M (u : LaurentSeries ℚ)), coeffEmb_mem_laurentBaseChange Qb huM⟩
  let x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :=
    ⟨coeffEmb Qb (qExpand ℚ (M / p) (u : LaurentSeries ℚ)), coeffEmb_mem_laurentBaseChange Qb huN⟩
  have h2 := hθp₂ c hcp g x' (by
    show coeffEmb Qb (qExpand ℚ M (u : LaurentSeries ℚ)) = qExpand Qb p (coeffEmb Qb (qExpand ℚ (M / p) (u : LaurentSeries ℚ)))
    rw [coeffEmb, ← coeffMap_qExpand, qExpand_qExpand, qExpand_congr hM])
  have hdia : diamondAutHBar (M / p) (infSubgroup p M H hpM) c x' = x' :=
    diamondAutHBar_apply_eq_self_of_coe_eq_coeffEmb_of_mem_gamma0 (M / p) (infSubgroup p M H hpM) c x'
      (qExpand ℚ (M / p) (u : LaurentSeries ℚ)) huQ rfl
  have h3 : θp g = w f := by
    apply Subtype.ext
    rw [h2, hdia, hwf]
  rw [AlgEquiv.trans_apply, ← h3, AlgEquiv.symm_apply_apply]

end B1Delta

end W0B1
p2m_reactivate "P2MW.S_ModularCurve_atkinLehner_complement_laws_of_fricke_of_atkinLehner_p.W0B1"

noncomputable section

open UpperHalfPlane IntermediateField HahnSeries AlgebraicCurve CongruenceSubgroup
open scoped ModularForm MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "IsDiamondAutHBar diamondAutHBar isDiamondAutHBar_diamondAutHBar diamondAutHBar_of_not HeckeBetaHDefined translation_mem_GammaH xHFunctionField xHFunctionFieldBar restrictForm coe_restrictForm IsIntegralQExp intSeriesC intSeriesC_mul intFormRatiosC qExpFunctionFieldC qExpFunctionFieldC_mono arithmeticGalois qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_single qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand algebraMap_apply_eq_single jq divisorExpansions modularFunctionFieldFull jqd_mem_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffMap_coeffEmb coeffEmb_mem_laurentBaseChange infSubgroup coeffMap_ofPowerSeries coeffMap_qExpand heckeDiamondInputsHAll diamondAutHBar_apply_eq_self_of_coe_eq_coeffEmb_of_mem_gamma0 atkinLehner_qExpand_pin_of_pin algEquiv_diamondAutHBar_comm_of_qExpand_of_diamondAutHBar_div qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull"
namespace DiaTrivAux
p2m_open "ModularCurve~coeffMap_injective~coeffMap_intSeriesC"

p2m_open "ModularCurve~coeffMap_injective~coeffMap_intSeriesC P2MW.S_ModularCurve_atkinLehner_complement_laws_of_fricke_of_atkinLehner_p.ModularCurve CongruenceSubgroup"

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  apply hf
  rw [← coeffMap_coeff, ← coeffMap_coeff, h]

theorem coeffMap_intSeriesC (K L : Type*) [Field K] [Field L] (φ : K →+* L) (p : PowerSeries ℤ) :
    coeffMap φ (intSeriesC K p) = intSeriesC L p := by
  rw [intSeriesC, coeffMap_ofPowerSeries, intSeriesC]
  congr 1
  have h := PowerSeries.map_comp (Int.castRingHom K) φ
  rw [RingHom.ext_int (φ.comp (Int.castRingHom K)) (Int.castRingHom L)] at h
  rw [h]
  rfl

theorem ofPowerSeries_qExpansion_eq {Γ : Subgroup SL(2, ℤ)} {k : ℤ} (f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k)
    {pf : PowerSeries ℤ} (hf : IsIntegralQExp f pf) :
    HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑f) = coeffMap (algebraMap ℚ ℂ) (intSeriesC ℚ pf) := by
  rw [coeffMap_intSeriesC]
  unfold IsIntegralQExp at hf
  rw [← hf]
  rfl

theorem coeffEmb_algebraMap (L : Type*) [Field L] [Algebra ℚ L] (c : ℚ) :
    coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) c) = algebraMap L (LaurentSeries L) (algebraMap ℚ L c) := by
  rw [algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single, ← algebraMap_laurentSeries_eq_single]

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)

theorem diamondAutHBar_eq_refl {d : (ZMod M)ˣ} (hd : d ∈ H) :
    diamondAutHBar M H d = AlgEquiv.refl := by
  haveI := Classical.dec (∃ σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
    IsDiamondAutHBar M H d σ)
  by_cases hex : ∃ σ : xHFunctionFieldBar M H ≃ₐ[AlgebraicClosure ℚ] xHFunctionFieldBar M H,
      IsDiamondAutHBar M H d σ
  swap
  · exact diamondAutHBar_of_not hex
  have hσ := isDiamondAutHBar_diamondAutHBar hex
  set σ := diamondAutHBar M H d with hσdef

  obtain ⟨γ0, hγ0⟩ := CohCarrier.gamma0Units_surjective M d⁻¹
  have h11 : ((γ0.1 1 1 : ℤ) : ZMod M) = ((d⁻¹ : (ZMod M)ˣ) : ZMod M) := by
    rw [← hγ0]; rfl
  have h00 : ((γ0.1 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
    have hmul := CohCarrier.Gamma0_d_mul_a M γ0
    rw [h11] at hmul
    calc ((γ0.1 0 0 : ℤ) : ZMod M)
        = (d : ZMod M) * (((d⁻¹ : (ZMod M)ˣ) : ZMod M) * ((γ0.1 0 0 : ℤ) : ZMod M)) := by
          rw [← mul_assoc, Units.mul_inv, one_mul]
      _ = (d : ZMod M) := by rw [hmul, mul_one]
  have hγH : (γ0.1 : SL(2, ℤ)) ∈ CohCarrier.GammaH M H :=
    CohCarrier.mem_GammaH_iff.2 ⟨γ0.2, by
      rw [show (⟨γ0.1, γ0.2⟩ : Gamma0 M) = γ0 from rfl, hγ0]; exact H.inv_mem hd⟩
  have hγH' : ((γ0.1 : SL(2, ℤ)) : GL (Fin 2) ℝ) ∈
      ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.mem_map_of_mem _ hγH

  have hgen : ∀ z ∈ intFormRatiosC ℚ (CohCarrier.GammaH M H), ∀ hz' : coeffEmb (AlgebraicClosure ℚ) z ∈ xHFunctionFieldBar M H,
      σ ⟨coeffEmb (AlgebraicClosure ℚ) z, hz'⟩ = ⟨coeffEmb (AlgebraicClosure ℚ) z, hz'⟩ := by
    rintro z ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ hz'
    obtain ⟨y, -, hσy, hrel⟩ := hσ k f g pf pg hf hg hg0 γ0.1 γ0.2 h00
    apply Subtype.ext
    refine hσy.trans ?_
    rw [SlashInvariantForm.slash_action_eqn _ _ hγH', SlashInvariantForm.slash_action_eqn _ _ hγH',
      ofPowerSeries_qExpansion_eq f hf, ofPowerSeries_qExpansion_eq g hg, ← map_mul] at hrel
    have hy : y * intSeriesC ℚ pg = intSeriesC ℚ pf :=
      coeffMap_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective hrel
    rw [(eq_div_iff hg0).2 hy]

  have hinner : ∀ z : LaurentSeries ℚ, z ∈ xHFunctionField M H →
      ∀ hz' : coeffEmb (AlgebraicClosure ℚ) z ∈ xHFunctionFieldBar M H,
        σ ⟨coeffEmb (AlgebraicClosure ℚ) z, hz'⟩ = ⟨coeffEmb (AlgebraicClosure ℚ) z, hz'⟩ := by
    intro z hz
    replace hz : z ∈ IntermediateField.adjoin ℚ (intFormRatiosC ℚ (CohCarrier.GammaH M H)) := hz
    induction hz using IntermediateField.adjoin_induction with
    | mem x hx => exact hgen x hx
    | algebraMap c =>
        intro hz'
        have e : (⟨coeffEmb (AlgebraicClosure ℚ) (algebraMap ℚ (LaurentSeries ℚ) c), hz'⟩ : xHFunctionFieldBar M H) =
            algebraMap (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) (algebraMap ℚ (AlgebraicClosure ℚ) c) := by
          apply Subtype.ext
          show coeffEmb (AlgebraicClosure ℚ) (algebraMap ℚ (LaurentSeries ℚ) c) = _
          rw [coeffEmb_algebraMap]
          rfl
        rw [e, AlgEquiv.commutes]
    | add x y hx hy ihx ihy =>
        intro hz'
        have e : (⟨coeffEmb (AlgebraicClosure ℚ) (x + y), hz'⟩ : xHFunctionFieldBar M H) =
            ⟨coeffEmb (AlgebraicClosure ℚ) x, coeffEmb_mem_laurentBaseChange _ hx⟩ +
              ⟨coeffEmb (AlgebraicClosure ℚ) y, coeffEmb_mem_laurentBaseChange _ hy⟩ :=
          Subtype.ext (map_add _ _ _)
        rw [e, map_add, ihx, ihy]
    | inv x hx ih =>
        intro hz'
        have e : (⟨coeffEmb (AlgebraicClosure ℚ) x⁻¹, hz'⟩ : xHFunctionFieldBar M H) =
            (⟨coeffEmb (AlgebraicClosure ℚ) x, coeffEmb_mem_laurentBaseChange _ hx⟩ : xHFunctionFieldBar M H)⁻¹ :=
          Subtype.ext (map_inv₀ _ _)
        rw [e, map_inv₀, ih]
    | mul x y hx hy ihx ihy =>
        intro hz'
        have e : (⟨coeffEmb (AlgebraicClosure ℚ) (x * y), hz'⟩ : xHFunctionFieldBar M H) =
            ⟨coeffEmb (AlgebraicClosure ℚ) x, coeffEmb_mem_laurentBaseChange _ hx⟩ *
              ⟨coeffEmb (AlgebraicClosure ℚ) y, coeffEmb_mem_laurentBaseChange _ hy⟩ :=
          Subtype.ext (map_mul _ _ _)
        rw [e, map_mul, ihx, ihy]

  have houter : ∀ (x : LaurentSeries (AlgebraicClosure ℚ)) (hx : x ∈ xHFunctionFieldBar M H), σ ⟨x, hx⟩ = ⟨x, hx⟩ := by
    intro x hx
    have hx0 : x ∈ IntermediateField.adjoin (AlgebraicClosure ℚ)
        (⇑(coeffEmb (AlgebraicClosure ℚ)) '' (xHFunctionField M H : Set (LaurentSeries ℚ))) := hx
    revert hx
    induction hx0 using IntermediateField.adjoin_induction with
    | mem x hx =>
        obtain ⟨z, hz, rfl⟩ := hx
        exact hinner z hz
    | algebraMap c =>
        intro hx
        have e : (⟨algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c, hx⟩ : xHFunctionFieldBar M H) =
            algebraMap (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) c := rfl
        rw [e, AlgEquiv.commutes]
    | add x y hx hy ihx ihy =>
        intro h'
        have e : (⟨x + y, h'⟩ : xHFunctionFieldBar M H) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
        rw [e, map_add, ihx, ihy]
    | inv x hx ih =>
        intro h'
        have e : (⟨x⁻¹, h'⟩ : xHFunctionFieldBar M H) = (⟨x, hx⟩ : xHFunctionFieldBar M H)⁻¹ := rfl
        rw [e, map_inv₀, ih]
    | mul x y hx hy ihx ihy =>
        intro h'
        have e : (⟨x * y, h'⟩ : xHFunctionFieldBar M H) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
        rw [e, map_mul, ihx, ihy]
  apply AlgEquiv.ext
  intro x
  exact houter x.1 x.2

end ModularCurve.DiaTrivAux
p2m_reactivate "P2MW.S_ModularCurve_atkinLehner_complement_laws_of_fricke_of_atkinLehner_p.W0B1"
p2m_reactivate "P2MW.S_ModularCurve_atkinLehner_complement_laws_of_fricke_of_atkinLehner_p.W0B1"

end
p2m_reactivate "P2MW.S_ModularCurve_atkinLehner_complement_laws_of_fricke_of_atkinLehner_p.W0B1"

p2m_open "ModularCurve~coeffMap_injective~coeffMap_intSeriesC P2MW.S_ModularCurve_atkinLehner_complement_laws_of_fricke_of_atkinLehner_p.ModularCurve ModularCurve.XHDRLevel"
open scoped MatrixGroups ModularForm

namespace W0B

open AlgebraicCurve

theorem exists_modEq_and_forall_pow_eq_one_apply_eq_pow
    {F K : Type*} [Field F] [Field K] [Algebra F K] (σ : K ≃ₐ[F] K)
    (p N' a : ℕ) (hcop : p.Coprime N') (hpN : p * N' ≠ 0)
    (h1 : ∀ μ : K, μ ^ p = 1 → σ μ = μ ^ a) (h2 : ∀ μ : K, μ ^ N' = 1 → σ μ = μ) :
    ∃ c : ℕ, c ≡ a [MOD p] ∧ c ≡ 1 [MOD N'] ∧ ∀ ζ : K, ζ ^ (p * N') = 1 → σ ζ = ζ ^ c := by
  obtain ⟨c, hc₁, hc₂⟩ := Nat.chineseRemainder hcop a 1
  refine ⟨c, hc₁, hc₂, fun ζ hζ => ?_⟩
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hpN] at hζ
    exact zero_ne_one hζ

  have hbez : (N' : ℤ) * Nat.gcdA N' p + (p : ℤ) * Nat.gcdB N' p = 1 := by
    have h := Nat.gcd_eq_gcd_ab N' p
    rw [Nat.Coprime.gcd_eq_one hcop.symm] at h
    exact_mod_cast h.symm
  set s : ℤ := Nat.gcdA N' p with hs
  set t : ℤ := Nat.gcdB N' p with ht
  have hζ₁ : (ζ ^ N') ^ p = 1 := by rw [← pow_mul, mul_comm, hζ]
  have hζ₂ : (ζ ^ p) ^ N' = 1 := by rw [← pow_mul, hζ]
  have hdec : ζ = (ζ ^ N') ^ s * (ζ ^ p) ^ t := by
    rw [← zpow_natCast ζ N', ← zpow_natCast ζ p, ← zpow_mul, ← zpow_mul, ← zpow_add₀ hζ0, hbez, zpow_one]

  have hc₁' : (ζ ^ N') ^ c = (ζ ^ N') ^ a := by
    rw [pow_eq_pow_mod c hζ₁, pow_eq_pow_mod a hζ₁, hc₁]
  have hc₂' : (ζ ^ p) ^ c = ζ ^ p := by
    conv_rhs => rw [← pow_one (ζ ^ p)]
    rw [pow_eq_pow_mod c hζ₂, pow_eq_pow_mod 1 hζ₂, hc₂]
  calc σ ζ = σ ((ζ ^ N') ^ s * (ζ ^ p) ^ t) := by rw [← hdec]
    _ = (σ (ζ ^ N')) ^ s * (σ (ζ ^ p)) ^ t := by rw [map_mul, map_zpow₀, map_zpow₀]
    _ = ((ζ ^ N') ^ a) ^ s * (ζ ^ p) ^ t := by rw [h1 _ hζ₁, h2 _ hζ₂]
    _ = ((ζ ^ N') ^ c) ^ s * ((ζ ^ p) ^ c) ^ t := by rw [hc₁', hc₂']
    _ = ((ζ ^ N') ^ s * (ζ ^ p) ^ t) ^ c := by
      rw [mul_pow, ← zpow_natCast ((ζ ^ N') ^ s) c, ← zpow_natCast ((ζ ^ p) ^ t) c, ← zpow_mul, ← zpow_mul,
        ← zpow_natCast (ζ ^ N') c, ← zpow_natCast (ζ ^ p) c, ← zpow_mul, ← zpow_mul, mul_comm s, mul_comm t]
    _ = ζ ^ c := by rw [← hdec]

theorem diamondAutHBar_apply_eq_self_of_mem (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    {d : (ZMod M)ˣ} (hd : d ∈ H) (x : ↥(xHFunctionFieldBar M H)) :
    diamondAutHBar M H d x = x := by
  rw [ModularCurve.DiaTrivAux.diamondAutHBar_eq_refl M H hd]
  rfl

end W0B
p2m_reactivate "P2MW.S_ModularCurve_atkinLehner_complement_laws_of_fricke_of_atkinLehner_p.W0B1"

section LevelP
open IntermediateField CongruenceSubgroup

namespace W0BP

local notation "Qb" => AlgebraicClosure ℚ

theorem gamma0_le_of_dvd {a b : ℕ} (h : a ∣ b) : Gamma0 b ≤ Gamma0 a := by
  intro A hA
  rw [Gamma0_mem] at hA ⊢
  have := congrArg (ZMod.castHom h (ZMod a)) hA
  rwa [map_intCast, map_zero] at this

theorem coeffEmb_algebraMap (L : Type*) [Field L] [Algebra ℚ L] (c : ℚ) :
    coeffEmb L (algebraMap ℚ (LaurentSeries ℚ) c) = algebraMap L (LaurentSeries L) (algebraMap ℚ L c) := by
  rw [algebraMap_laurentSeries_eq_single, coeffEmb, coeffMap_single, ← algebraMap_laurentSeries_eq_single]

theorem map_unitsMap_eq_top (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hpM2 : ¬ p ^ 2 ∣ M) (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    H.map (ZMod.unitsMap hpM) = ⊤ := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [eq_top_iff]
  rintro a -
  have hM : p * (M / p) = M := Nat.mul_div_cancel' hpM
  have hcop : p.Coprime (M / p) := (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h => hpM2 (by
    rw [pow_two, ← hM]; exact Nat.mul_dvd_mul_left p h))
  obtain ⟨c, hca, hc1⟩ := Nat.chineseRemainder hcop (a : ZMod p).val 1
  have ha₀ : ((a : ZMod p).val).Coprime p := ZMod.val_coe_unit_coprime a
  have hcM : c.Coprime M := by
    rw [← hM]
    refine Nat.Coprime.mul_right ?_ ?_
    · unfold Nat.Coprime at ha₀ ⊢
      rw [hca.gcd_eq]
      exact ha₀
    · unfold Nat.Coprime
      rw [hc1.gcd_eq]
      exact Nat.gcd_one_left _
  refine ⟨ZMod.unitOfCoprime c hcM, hHp _ ?_, ?_⟩
  · ext
    rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.coe_unitOfCoprime, ZMod.castHom_apply,
      ZMod.cast_natCast (Nat.div_dvd_of_dvd hpM), Units.val_one, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
    exact hc1
  · ext
    rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.coe_unitOfCoprime, ZMod.castHom_apply,
      ZMod.cast_natCast hpM, ← ZMod.natCast_zmod_val (a : ZMod p), ZMod.natCast_eq_natCast_iff]
    exact hca

theorem gamma0_one_eq_top : Gamma0 1 = ⊤ := by
  refine eq_top_iff.mpr fun A _ => ?_
  rw [Gamma0_mem]
  exact Subsingleton.elim _ _

theorem jq_mem_top : jq ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)) := by
  have h : jq ∈ modularFunctionFieldFull 1 := by
    have := jqd_mem_full 1 (one_dvd 1) (d := 1)
    rwa [qExpand_one_apply] at this
  rwa [← ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull, gamma0_one_eq_top] at h

theorem level_p_of_level_one
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (htop : ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (u : LaurentSeries ℚ) →
          ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
            coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (M / p) (u : LaurentSeries ℚ)))
    (hdil : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p (u : LaurentSeries ℚ)) →
          ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
            coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M (u : LaurentSeries ℚ))) :
    ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(qExpFunctionFieldC ℚ (ΓM p (H.map (ZMod.unitsMap hpM))))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (u : LaurentSeries ℚ) →
          ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
            coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (M / p) (u : LaurentSeries ℚ)) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro f u hfu
  obtain ⟨u, hu0⟩ := u
  simp only [Subtype.coe_mk] at hfu ⊢
  have hmap := map_unitsMap_eq_top p M H hpM hpM2 hHp

  have hu : u ∈ modularFunctionFieldFull p := by
    rw [hmap, show ΓM p (⊤ : Subgroup (ZMod p)ˣ) = Gamma0 p from CohCarrier.GammaH_top,
      ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull] at hu0
    exact hu0

  have hle : modularFunctionFieldFull p ≤ xHFunctionField M H := by
    rw [← ModularCurve.qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]
    exact qExpFunctionFieldC_mono ℚ ((CohCarrier.GammaH_le_Gamma0 H).trans (gamma0_le_of_dvd hpM))
  let J : ↥(qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) := ⟨jq, jq_mem_top⟩

  have key : ∀ y : LaurentSeries ℚ, y ∈ modularFunctionFieldFull p →
      ∀ hy' : coeffEmb Qb y ∈ xHFunctionFieldBar M H,
        ((θ ⟨coeffEmb Qb y, hy'⟩ : ↥(xHFunctionFieldBar M H)) : LaurentSeries Qb) =
          coeffEmb Qb (qExpand ℚ (M / p) y) := by
    intro y hy
    change y ∈ IntermediateField.adjoin ℚ (divisorExpansions p) at hy
    induction hy using IntermediateField.adjoin_induction with
    | mem x hx =>
        intro hx'
        obtain ⟨d, hne, hdvd, rfl⟩ := hx
        haveI := hne
        rcases (Nat.dvd_prime hp).mp hdvd with h1 | h2
        ·
          subst d
          have e1 : qExpand ℚ 1 jq = jq := qExpand_one_apply jq
          have := htop ⟨coeffEmb Qb (qExpand ℚ 1 jq), hx'⟩ J (congrArg (coeffEmb Qb) e1)
          rw [this, e1]
        ·
          subst d
          have := hdil ⟨coeffEmb Qb (qExpand ℚ p jq), hx'⟩ J rfl
          rw [this]
          show coeffEmb Qb (qExpand ℚ M jq) = coeffEmb Qb (qExpand ℚ (M / p) (qExpand ℚ p jq))
          rw [qExpand_qExpand, qExpand_congr (Nat.div_mul_cancel hpM)]
    | algebraMap c =>
        intro hx'
        have e : (⟨coeffEmb Qb (algebraMap ℚ (LaurentSeries ℚ) c), hx'⟩ : ↥(xHFunctionFieldBar M H)) =
            algebraMap Qb (↥(xHFunctionFieldBar M H)) (algebraMap ℚ Qb c) := by
          apply Subtype.ext
          show coeffEmb Qb (algebraMap ℚ (LaurentSeries ℚ) c) = _
          rw [coeffEmb_algebraMap]
          rfl
        rw [e, AlgEquiv.commutes, algebraMap_apply_eq_single, qExpand_single, mul_zero,
          ← algebraMap_apply_eq_single, coeffEmb_algebraMap]
        rfl
    | add x y hx hy ihx ihy =>
        intro hz'
        have hxM : coeffEmb Qb x ∈ xHFunctionFieldBar M H := coeffEmb_mem_laurentBaseChange _ (hle hx)
        have hyM : coeffEmb Qb y ∈ xHFunctionFieldBar M H := coeffEmb_mem_laurentBaseChange _ (hle hy)
        have e : (⟨coeffEmb Qb (x + y), hz'⟩ : ↥(xHFunctionFieldBar M H)) = ⟨coeffEmb Qb x, hxM⟩ + ⟨coeffEmb Qb y, hyM⟩ :=
          Subtype.ext (map_add _ _ _)
        rw [e, map_add, map_add, map_add]
        show ((θ ⟨coeffEmb Qb x, hxM⟩ : ↥(xHFunctionFieldBar M H)) : LaurentSeries Qb) +
            ((θ ⟨coeffEmb Qb y, hyM⟩ : ↥(xHFunctionFieldBar M H)) : LaurentSeries Qb) = _
        rw [ihx, ihy]
    | inv x hx ih =>
        intro hz'
        have hxM : coeffEmb Qb x ∈ xHFunctionFieldBar M H := coeffEmb_mem_laurentBaseChange _ (hle hx)
        have e : (⟨coeffEmb Qb x⁻¹, hz'⟩ : ↥(xHFunctionFieldBar M H)) = (⟨coeffEmb Qb x, hxM⟩ : ↥(xHFunctionFieldBar M H))⁻¹ :=
          Subtype.ext (map_inv₀ _ _)
        rw [e, map_inv₀, map_inv₀, map_inv₀]
        show ((θ ⟨coeffEmb Qb x, hxM⟩ : ↥(xHFunctionFieldBar M H)) : LaurentSeries Qb)⁻¹ = _
        rw [ih]
    | mul x y hx hy ihx ihy =>
        intro hz'
        have hxM : coeffEmb Qb x ∈ xHFunctionFieldBar M H := coeffEmb_mem_laurentBaseChange _ (hle hx)
        have hyM : coeffEmb Qb y ∈ xHFunctionFieldBar M H := coeffEmb_mem_laurentBaseChange _ (hle hy)
        have e : (⟨coeffEmb Qb (x * y), hz'⟩ : ↥(xHFunctionFieldBar M H)) = ⟨coeffEmb Qb x, hxM⟩ * ⟨coeffEmb Qb y, hyM⟩ :=
          Subtype.ext (map_mul _ _ _)
        rw [e, map_mul, map_mul, map_mul]
        show ((θ ⟨coeffEmb Qb x, hxM⟩ : ↥(xHFunctionFieldBar M H)) : LaurentSeries Qb) *
            ((θ ⟨coeffEmb Qb y, hyM⟩ : ↥(xHFunctionFieldBar M H)) : LaurentSeries Qb) = _
        rw [ihx, ihy]
  have hf : f = ⟨coeffEmb Qb u, hfu ▸ f.2⟩ := Subtype.ext hfu
  rw [hf]
  exact key u hu _

end W0BP
p2m_reactivate "P2MW.S_ModularCurve_atkinLehner_complement_laws_of_fricke_of_atkinLehner_p.W0B1"

end LevelP
p2m_reactivate "P2MW.S_ModularCurve_atkinLehner_complement_laws_of_fricke_of_atkinLehner_p.W0B1"

set_option maxHeartbeats 3200000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (ι : AlgebraicClosure ℚ →+* ℂ) (W : GL (Fin 2) ℝ)
    (hW : (W : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0])

    (w : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hw₁ : ∀ (x : ↥(xHFunctionFieldBar M H)) (k : ℤ)
        (f g : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k),
        coeffMap ι (x : LaurentSeries (AlgebraicClosure ℚ)) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) →
        coeffMap ι ((w x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) *
            HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑g ∣[k] W)) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 (⇑f ∣[k] W)))
    (hw₂ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
        ∀ x : ↥(xHFunctionFieldBar M H),
          w (arithmeticGalois (xHFunctionField M H) σ • x) =
            arithmeticGalois (xHFunctionField M H) σ • diamondAutHBar M H (ZMod.unitOfCoprime c hc) (w x))

    (θp : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθp : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
          (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
          ((θp f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
            qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hθp_rat : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : ↥(xHFunctionFieldBar M H)),
        θp (arithmeticGalois (xHFunctionField M H) σ • x) = arithmeticGalois (xHFunctionField M H) σ • θp x) :
    letI θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H) := w.trans θp.symm

    (∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (u : LaurentSeries ℚ) →
          ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
            coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (M / p) (u : LaurentSeries ℚ))) ∧

    (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p (u : LaurentSeries ℚ)) →
          ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
            coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ M (u : LaurentSeries ℚ))) ∧

    (∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(qExpFunctionFieldC ℚ (ΓM p (H.map (ZMod.unitsMap hpM))))),
        (f : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (u : LaurentSeries ℚ) →
          ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
            coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (M / p) (u : LaurentSeries ℚ))) ∧

    (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
        ∀ x : ↥(xHFunctionFieldBar M H),
          θ (arithmeticGalois (xHFunctionField M H) σ • x) =
            arithmeticGalois (xHFunctionField M H) σ • diamondAutHBar M H (ZMod.unitOfCoprime c hc) (θ x)) ∧

    (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ (M / p) = 1 → σ ζ = ζ) →
        ∀ x : ↥(xHFunctionFieldBar M H),
          θ (arithmeticGalois (xHFunctionField M H) σ • x) = arithmeticGalois (xHFunctionField M H) σ • θ x) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp : p.Prime := Fact.out

  have hθp₂ := ModularCurve.atkinLehner_qExpand_pin_of_pin p M H hpM hpM2 hHp
    (ModularCurve.heckeDiamondInputsHAll (M / p) (infSubgroup p M H hpM)) θp hθp
  have hθp_dia : ∀ (d : (ZMod M)ˣ) (x : ↥(xHFunctionFieldBar M H)),
      θp (diamondAutHBar M H d x) = diamondAutHBar M H d (θp x) := fun d x =>
    ModularCurve.algEquiv_diamondAutHBar_comm_of_qExpand_of_diamondAutHBar_div p M H hpM hpM2 hHp θp hθp hθp₂ d x

  have hθp_rat' : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (y : ↥(xHFunctionFieldBar M H)),
      θp.symm (arithmeticGalois (xHFunctionField M H) σ • y) = arithmeticGalois (xHFunctionField M H) σ • θp.symm y := by
    intro σ y
    apply θp.injective
    rw [hθp_rat, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  have hθp_dia' : ∀ (d : (ZMod M)ˣ) (y : ↥(xHFunctionFieldBar M H)),
      θp.symm (diamondAutHBar M H d y) = diamondAutHBar M H d (θp.symm y) := by
    intro d y
    apply θp.injective
    rw [hθp_dia, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

  have hb2 : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ) (hc : c.Coprime M),
      (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) →
      ∀ x : ↥(xHFunctionFieldBar M H),
        (w.trans θp.symm) (arithmeticGalois (xHFunctionField M H) σ • x) =
          arithmeticGalois (xHFunctionField M H) σ • diamondAutHBar M H (ZMod.unitOfCoprime c hc) ((w.trans θp.symm) x) := by
    intro σ c hc hζ x
    rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, hw₂ σ c hc hζ x, hθp_rat', hθp_dia']

  have hb1top := W0B1.coe_trans_symm_apply_eq_coeffEmb_qExpand_of_level_one p M H hpM ι W hW w hw₁ θp hθp

  have hb1dil := W0B1.coe_trans_symm_apply_eq_coeffEmb_qExpand_of_qExpand_level_one p M H hpM hpM2 ι W hW w hw₁ θp hθp₂
  refine ⟨hb1top, hb1dil, ?_, hb2, ?_⟩
  ·
    exact W0BP.level_p_of_level_one p M H hpM hpM2 hHp (w.trans θp.symm) hb1top hb1dil
  ·
    intro σ hσQ x
    obtain ⟨N', hN'⟩ := hpM
    have hN'p : ¬ p ∣ N' := fun h => hpM2 (by rw [hN', pow_two]; exact Nat.mul_dvd_mul_left p h)
    have hcop : p.Coprime N' := (Nat.Prime.coprime_iff_not_dvd hp).mpr hN'p
    have hM0 : p * N' ≠ 0 := by rw [← hN']; exact NeZero.ne M
    have hdiv : M / p = N' := by rw [hN']; exact Nat.mul_div_cancel_left N' hp.pos

    obtain ⟨a, ha, hap⟩ : ∃ a : ℕ, (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) ∧ a.Coprime p := by
      obtain ⟨m, hm⟩ := rootsOfUnity.integer_power_of_ringEquiv' p (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)
      have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
      set a₀ : ℕ := (m % p).toNat with ha₀
      have ha₀m : ((a₀ : ℕ) : ℤ) = m % p := by rw [ha₀, Int.toNat_of_nonneg (Int.emod_nonneg _ hp0.ne')]
      have hpow : ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a₀ := by
        intro μ hμ
        have hμ0 : μ ≠ 0 := by rintro rfl; rw [zero_pow hp.ne_zero] at hμ; exact zero_ne_one hμ
        let t : (AlgebraicClosure ℚ)ˣ := Units.mk0 μ hμ0
        have ht : t ∈ rootsOfUnity p (AlgebraicClosure ℚ) := by
          rw [mem_rootsOfUnity]; ext; simp [t, hμ]
        have h1 := hm t ht
        have h2 : (((t ^ m : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) = μ ^ m := by
          rw [Units.val_zpow_eq_zpow_val]; rfl
        have h3 : μ ^ m = μ ^ a₀ := by
          have e : m % (p : ℤ) + (p : ℤ) * (m / (p : ℤ)) = m := Int.emod_add_mul_ediv m p
          calc μ ^ m = μ ^ (m % (p : ℤ) + (p : ℤ) * (m / (p : ℤ))) := by rw [e]
            _ = μ ^ (m % (p : ℤ)) * (μ ^ (p : ℤ)) ^ (m / (p : ℤ)) := by rw [zpow_add₀ hμ0, zpow_mul]
            _ = μ ^ (m % (p : ℤ)) := by rw [zpow_natCast, hμ, one_zpow, mul_one]
            _ = μ ^ a₀ := by rw [← ha₀m, zpow_natCast]
        have : σ μ = ((σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (t : AlgebraicClosure ℚ)) := rfl
        rw [this, h1, h2, h3]
      by_cases hdvd : p ∣ a₀
      ·
        refine ⟨1, fun μ hμ => ?_, Nat.coprime_one_left p⟩
        obtain ⟨k, hk⟩ := hdvd
        have h1 : σ μ = 1 := by rw [hpow μ hμ, hk, pow_mul, hμ, one_pow]
        have h2 : μ = 1 := by
          have := congrArg σ.symm h1
          rwa [AlgEquiv.symm_apply_apply, map_one] at this
        rw [h2, one_pow, map_one]
      · exact ⟨a₀, hpow, ((Nat.Prime.coprime_iff_not_dvd hp).mpr hdvd).symm⟩
    obtain ⟨c, hca, hc1, hζc⟩ := W0B.exists_modEq_and_forall_pow_eq_one_apply_eq_pow σ p N' a hcop hM0 ha
      (fun μ hμ => hσQ μ (by rw [hdiv]; exact hμ))
    have hcM : c.Coprime M := by
      rw [hN']
      refine Nat.Coprime.mul_right ?_ ?_
      · unfold Nat.Coprime at hap ⊢
        rw [hca.gcd_eq]
        exact hap
      · unfold Nat.Coprime
        rw [hc1.gcd_eq]
        exact Nat.gcd_one_left N'
    have hζ : ∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c := fun ζ h => hζc ζ (by rw [← hN']; exact h)
    have hmem : ZMod.unitOfCoprime c hcM ∈ H := by
      apply hHp
      have hc1' : c ≡ 1 [MOD M / p] := hdiv ▸ hc1
      ext
      rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.coe_unitOfCoprime, ZMod.castHom_apply,
        ZMod.cast_natCast (Nat.div_dvd_of_dvd ⟨N', hN'⟩), Units.val_one, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
      exact hc1'
    have key : ∀ y : ↥(xHFunctionFieldBar M H),
        arithmeticGalois (xHFunctionField M H) σ • diamondAutHBar M H (ZMod.unitOfCoprime c hcM) y =
          arithmeticGalois (xHFunctionField M H) σ • y := fun y =>
      congrArg (fun z => arithmeticGalois (xHFunctionField M H) σ • z) (W0B.diamondAutHBar_apply_eq_self_of_mem M H hmem y)
    exact (hb2 σ c hcM hζ x).trans (key _)

end
end S_ModularCurve_atkinLehner_complement_laws_of_fricke_of_atkinLehner_p
end P2MW
export P2MW.S_ModularCurve_atkinLehner_complement_laws_of_fricke_of_atkinLehner_p (solution)
