-- Prove2me | solution 1 for ModularCurve.coe_diamondAutHBar_eq_qExpand_coe_diamondAutHBar_div_of_coe_eq_qExpand
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/350ae92b-b560-5b4f-ba8c-c40eb0039ffd

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coe_diamondAutHBar_eq_qExpand_coe_diamondAutHBar_div_of_coe_eq_qExpand
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm Pointwise

namespace DBetaBar

open UpperHalfPlane CongruenceSubgroup ModularCurve Matrix IntermediateField HahnSeries

section Group

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ}

abbrev ΓtSL (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) : Subgroup SL(2, ℤ) :=
  CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)

abbrev Γt (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  ((ΓtSL M H ℓ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

abbrev Γb (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Subgroup (GL (Fin 2) ℝ) :=
  ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem T_mem_top : ModularGroup.T ∈ ΓtSL M H ℓ := by
  refine Subgroup.mem_inf.mpr ⟨translation_mem_GammaH M H, ?_⟩
  rw [Gamma0_mem]
  simp [ModularGroup.T]

theorem one_mem_strictPeriods_top : (1 : ℝ) ∈ (Γt M H ℓ).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem T_mem_top]
  exact AddSubgroup.mem_zmultiples _

theorem one_mem_strictPeriods_bot : (1 : ℝ) ∈ (Γb M H).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples _

scoped instance [NeZero M] : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

scoped instance [NeZero M] [NeZero ℓ] : (ΓtSL M H ℓ).FiniteIndex := by
  haveI : NeZero (M * ℓ) := NeZero.mul
  refine Subgroup.finiteIndex_of_le (H := Gamma1 (M * ℓ)) (le_inf ?_ (Gamma1_in_Gamma0 _))
  exact (Gamma1_le_of_dvd (dvd_mul_right M ℓ)).trans (Gamma1_le_GammaH M H)

theorem top_le_bot : ΓtSL M H ℓ ≤ CohCarrier.GammaH M H := inf_le_left

theorem Γt_le_Γb : Γt M H ℓ ≤ Γb M H := Subgroup.map_mono top_le_bot

def conjMat (ℓ : ℕ) (δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![δ 0 0, (ℓ : ℤ) * δ 0 1; δ 1 0 / ℓ, δ 1 1]

theorem det_conjMat (δ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ δ 1 0) : (conjMat ℓ δ).det = 1 := by
  obtain ⟨c, hc⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet ⊢
  rcases eq_or_ne (ℓ : ℤ) 0 with h0 | h0
  · simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, hc, h0, zero_mul, Int.zero_ediv,
      mul_zero, sub_zero] at hdet ⊢
    linear_combination hdet
  · have h1 : (ℓ : ℤ) * c / ℓ = c := by rw [mul_comm]; exact Int.mul_ediv_cancel c h0
    simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, hc, h1] at hdet ⊢
    linear_combination hdet

def conjSL (δ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ δ 1 0) : SL(2, ℤ) := ⟨conjMat ℓ δ, det_conjMat δ h⟩

@[scoped simp] theorem conjSL_apply_00 (δ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ δ 1 0) : conjSL δ h 0 0 = δ 0 0 := rfl
@[scoped simp] theorem conjSL_apply_01 (δ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ δ 1 0) :
    conjSL δ h 0 1 = (ℓ : ℤ) * δ 0 1 := rfl
@[scoped simp] theorem conjSL_apply_10 (δ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ δ 1 0) :
    conjSL δ h 1 0 = δ 1 0 / ℓ := rfl
@[scoped simp] theorem conjSL_apply_11 (δ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ δ 1 0) : conjSL δ h 1 1 = δ 1 1 := rfl

theorem dvd_of_mem_Gamma0_mul {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 (M * ℓ)) : (ℓ : ℤ) ∣ δ 1 0 := by
  rw [Gamma0_mem] at hδ
  have : ((M * ℓ : ℕ) : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hδ
  exact (show (ℓ : ℤ) ∣ ((M * ℓ : ℕ) : ℤ) from ⟨M, by push_cast; ring⟩).trans this

theorem conjSL_mem_Gamma0 {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 (M * ℓ)) (hℓ : ℓ ≠ 0) :
    conjSL δ (dvd_of_mem_Gamma0_mul hδ) ∈ Gamma0 M := by
  rw [Gamma0_mem]
  have hd : ((M * ℓ : ℕ) : ℤ) ∣ δ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hδ)
  obtain ⟨c, hc⟩ := hd
  have hℓ' : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ
  have : (conjSL δ (dvd_of_mem_Gamma0_mul hδ)) 1 0 = M * c := by
    show δ 1 0 / ℓ = M * c
    rw [hc]; push_cast
    rw [show (M : ℤ) * ℓ * c = ℓ * (M * c) by ring]
    exact Int.mul_ediv_cancel_left _ hℓ'
  rw [this]; push_cast
  simp

theorem conjSL_apply_10_eq {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 (M * ℓ)) (hℓ : ℓ ≠ 0) :
    ∃ c : ℤ, (conjSL δ (dvd_of_mem_Gamma0_mul hδ)) 1 0 = M * c := by
  have hd : ((M * ℓ : ℕ) : ℤ) ∣ δ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hδ)
  obtain ⟨c, hc⟩ := hd
  have hℓ' : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ
  refine ⟨c, ?_⟩
  show δ 1 0 / ℓ = M * c
  rw [hc]; push_cast
  rw [show (M : ℤ) * ℓ * c = ℓ * (M * c) by ring]
  exact Int.mul_ediv_cancel_left _ hℓ'

theorem conjSL_mem_GammaH {δ : SL(2, ℤ)} (hδH : δ ∈ CohCarrier.GammaH M H)
    (hδ : δ ∈ Gamma0 (M * ℓ)) (hℓ : ℓ ≠ 0) :
    conjSL δ (dvd_of_mem_Gamma0_mul hδ) ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff] at hδH ⊢
  obtain ⟨hδ0, hH⟩ := hδH
  refine ⟨conjSL_mem_Gamma0 hδ hℓ, ?_⟩
  convert hH using 1
  rfl

theorem heckeDiag_mul_mul_inv {δ : SL(2, ℤ)} (h : (ℓ : ℤ) ∣ δ 1 0) (hℓ : ℓ ≠ 0) :
    ModularForm.heckeDiagMatrix ℓ * Matrix.SpecialLinearGroup.mapGL ℝ δ *
        (ModularForm.heckeDiagMatrix ℓ)⁻¹ =
      Matrix.SpecialLinearGroup.mapGL ℝ (conjSL δ h) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  obtain ⟨c, hc⟩ := h
  have hℓ' : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ
  have h10 : (conjSL δ ⟨c, hc⟩ : SL(2, ℤ)) 1 0 = c := by
    show δ 1 0 / ℓ = c
    rw [hc]; exact Int.mul_ediv_cancel_left _ hℓ'
  simp only [Matrix.GeneralLinearGroup.coe_mul, ModularForm.val_heckeDiagMatrix hℓ]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, hc] <;> ring

theorem conj_apply_10 (γ z : SL(2, ℤ)) :
    (γ * z * γ⁻¹) 1 0 = γ 1 0 * z 0 0 * γ 1 1 + γ 1 1 * z 1 0 * γ 1 1
      - γ 1 0 * z 0 1 * γ 1 0 - γ 1 1 * z 1 1 * γ 1 0 := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl γ]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

variable (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1)

abbrev alGL (γ : SL(2, ℤ)) (ℓ : ℕ) : GL (Fin 2) ℝ :=
  Matrix.SpecialLinearGroup.mapGL ℝ γ * ModularForm.heckeDiagMatrix ℓ

include hγ hγℓ in

theorem alConj_mem {δ : SL(2, ℤ)} (hδH : δ ∈ CohCarrier.GammaH M H) (hδ : δ ∈ Gamma0 (M * ℓ))
    (hℓ : ℓ ≠ 0) : γ * conjSL δ (dvd_of_mem_Gamma0_mul hδ) * γ⁻¹ ∈ ΓtSL M H ℓ := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact CohCarrier.conj_mem_GammaH M H ⟨γ, hγ⟩ ⟨_, conjSL_mem_GammaH hδH hδ hℓ⟩
  · rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, conj_apply_10]
    obtain ⟨r, hr⟩ : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
    obtain ⟨s, hs⟩ := hγℓ
    obtain ⟨c, hc⟩ := conjSL_apply_10_eq (M := M) hδ hℓ
    rw [hc, conjSL_apply_00, conjSL_apply_01, conjSL_apply_11, hr, hs]
    exact ⟨r * δ 0 0 * s + s * c * ℓ * s - r * δ 0 1 * M * r - s * δ 1 1 * r, by push_cast; ring⟩

include hγ hγℓ in

theorem le_conj_al (hℓ : ℓ ≠ 0) :
    Γt M H ℓ ≤ ConjAct.toConjAct (alGL γ ℓ)⁻¹ • Γt M H ℓ := by
  rintro x ⟨δ, hδ, rfl⟩
  obtain ⟨hδH, hδ0⟩ := Subgroup.mem_inf.mp hδ
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  refine ⟨_, alConj_mem γ hγ hγℓ hδH hδ0 hℓ, ?_⟩
  rw [map_mul, map_mul, map_inv, ← heckeDiag_mul_mul_inv (dvd_of_mem_Gamma0_mul hδ0) hℓ]
  simp only [alGL, _root_.mul_inv_rev, mul_assoc]

variable {k : ℤ} [NeZero ℓ]

def alForm (f : ModularForm (Γt M H ℓ) k) : ModularForm (Γt M H ℓ) k :=
  ((ℓ : ℂ) ^ (k - 1))⁻¹ •
    restrictForm (le_conj_al γ hγ hγℓ (NeZero.ne ℓ)) (ModularForm.translate f (alGL γ ℓ))

theorem alForm_apply (f : ModularForm (Γt M H ℓ) k) (τ : ℍ) :
    alForm γ hγ hγℓ f τ = (⇑f ∣[k] γ) (ModularForm.heckeDiagMatrix ℓ • τ) := by
  have hℓ : (ℓ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  show ((ℓ : ℂ) ^ (k - 1))⁻¹ • ((⇑f ∣[k] alGL γ ℓ) τ) = _
  rw [alGL, SlashAction.slash_mul, ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne ℓ),
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ hℓ), one_mul]
  rfl

theorem coe_alForm (f : ModularForm (Γt M H ℓ) k) :
    ⇑(alForm γ hγ hγℓ f) = fun τ => (⇑f ∣[k] γ) (ModularForm.heckeDiagMatrix ℓ • τ) :=
  funext (alForm_apply γ hγ hγℓ f)

theorem alForm_mul_apply {k₁ k₂ : ℤ} (f : ModularForm (Γt M H ℓ) k₁) (g : ModularForm (Γt M H ℓ) k₂) :
    ⇑(alForm γ hγ hγℓ (f.mul g)) = ⇑(alForm γ hγ hγℓ f) * ⇑(alForm γ hγ hγℓ g) := by
  funext τ
  simp only [coe_alForm, Pi.mul_apply, ModularForm.coe_mul, ModularForm.mul_slash_SL2]

theorem alForm_add (f g : ModularForm (Γt M H ℓ) k) :
    alForm γ hγ hγℓ (f + g) = alForm γ hγ hγℓ f + alForm γ hγ hγℓ g := by
  ext τ
  simp only [alForm_apply, ModularForm.coe_add, SlashAction.add_slash, Pi.add_apply,
    ModularForm.add_apply]

theorem alForm_smul (c : ℂ) (f : ModularForm (Γt M H ℓ) k) :
    ⇑(alForm γ hγ hγℓ (c • f)) = c • ⇑(alForm γ hγ hγℓ f) := by
  funext τ
  simp only [coe_alForm, ModularForm.IsGLPos.coe_smul, ModularForm.SL_smul_slash, Pi.smul_apply]

theorem alForm_neg (f : ModularForm (Γt M H ℓ) k) :
    ⇑(alForm γ hγ hγℓ (-f)) = -⇑(alForm γ hγ hγℓ f) := by
  funext τ
  simp only [coe_alForm, ModularForm.coe_neg, SlashAction.neg_slash, Pi.neg_apply]

theorem alForm_zero : alForm γ hγ hγℓ (0 : ModularForm (Γt M H ℓ) k) = 0 := by
  ext τ; simp [alForm_apply]

theorem alForm_one : alForm γ hγ hγℓ (1 : ModularForm (Γt M H ℓ) 0) = 1 := by
  ext τ
  simp only [alForm_apply, ModularForm.one_coe_eq_one]
  rw [ModularForm.is_invariant_one γ]
  rfl

end Group

section Compose

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ} [NeZero ℓ] {k : ℤ}

theorem heckeDiag_smul_heckeMatrix_smul (τ : ℍ) :
    ModularForm.heckeDiagMatrix ℓ • (ModularForm.heckeMatrix ℓ 0 • τ) = τ := by
  apply UpperHalfPlane.ext
  rw [ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne ℓ), ModularForm.coe_heckeMatrix_smul (NeZero.ne ℓ) 0]
  have : (ℓ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  field_simp
  push_cast
  ring

theorem slash_diag_diag (k : ℤ) (F : ℍ → ℂ) :
    F ∣[k] (ModularForm.heckeDiagMatrix ℓ * ModularForm.heckeMatrix ℓ 0) = ((ℓ : ℂ) ^ (k - 2)) • F := by
  have hℓ : (ℓ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  funext τ
  rw [SlashAction.slash_mul, ModularForm.slash_heckeMatrix_apply k (NeZero.ne ℓ) 0,
    ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne ℓ), heckeDiag_smul_heckeMatrix_smul,
    Pi.smul_apply, smul_eq_mul, show k - 2 = (k - 1) + (-1) by ring, zpow_add₀ hℓ, _root_.zpow_neg_one]
  ring

theorem real_smul_slash (k : ℤ) (r : ℝ) (F : ℍ → ℂ) (g : GL (Fin 2) ℝ) :
    ((r : ℂ) • F) ∣[k] g = (r : ℂ) • (F ∣[k] g) := by
  rw [ModularForm.smul_slash, UpperHalfPlane.σ_ofReal]

omit [NeZero ℓ] in
theorem inv_pow_eq_real (k : ℤ) : ((ℓ : ℂ) ^ (k - 1))⁻¹ = ((((ℓ : ℝ) ^ (k - 1))⁻¹ : ℝ) : ℂ) := by
  push_cast; rfl

variable (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1)

theorem coe_alForm_eq_smul_slash (f : ModularForm (Γt M H ℓ) k) :
    ⇑(alForm γ hγ hγℓ f) = ((ℓ : ℂ) ^ (k - 1))⁻¹ • (⇑f ∣[k] alGL γ ℓ) := by
  have hℓ : (ℓ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  funext τ
  rw [alForm_apply, Pi.smul_apply, SlashAction.slash_mul,
    ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne ℓ), smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (zpow_ne_zero _ hℓ), one_mul]
  rfl

theorem alForm_alForm_of_mul_eq (γ' : SL(2, ℤ)) (hγ' : γ' ∈ Gamma0 M) (hγ'ℓ : (ℓ : ℤ) ∣ γ' 1 1)
    (hmul : alGL γ ℓ * alGL γ' ℓ = ModularForm.heckeDiagMatrix ℓ * ModularForm.heckeMatrix ℓ 0)
    (f : ModularForm (Γt M H ℓ) k) :
    ⇑(alForm γ' hγ' hγ'ℓ (alForm γ hγ hγℓ f)) = ((ℓ : ℂ) ^ k)⁻¹ • ⇑f := by
  have hℓ : (ℓ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  rw [coe_alForm_eq_smul_slash, coe_alForm_eq_smul_slash, inv_pow_eq_real, real_smul_slash,
    ← SlashAction.slash_mul, hmul, slash_diag_diag, smul_smul, smul_smul, ← inv_pow_eq_real]
  congr 1
  rw [← _root_.zpow_neg, ← zpow_add₀ hℓ, ← zpow_add₀ hℓ, ← _root_.zpow_neg]
  congr 1; ring

theorem top_le_conj_bot :
    Γt M H ℓ ≤ ConjAct.toConjAct (ModularForm.heckeDiagMatrix ℓ)⁻¹ • Γb M H := by
  rintro x ⟨δ, hδ, rfl⟩
  obtain ⟨hδH, hδ0⟩ := Subgroup.mem_inf.mp hδ
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  exact ⟨_, conjSL_mem_GammaH hδH hδ0 (NeZero.ne ℓ),
    (heckeDiag_mul_mul_inv (dvd_of_mem_Gamma0_mul hδ0) (NeZero.ne ℓ)).symm⟩

def levelRaise (f : ModularForm (Γb M H) k) : ModularForm (Γt M H ℓ) k :=
  ((ℓ : ℂ) ^ (k - 1))⁻¹ •
    restrictForm top_le_conj_bot (ModularForm.translate f (ModularForm.heckeDiagMatrix ℓ))

theorem levelRaise_apply (f : ModularForm (Γb M H) k) (τ : ℍ) :
    levelRaise (ℓ := ℓ) f τ = f (ModularForm.heckeDiagMatrix ℓ • τ) := by
  have hℓ : (ℓ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  show ((ℓ : ℂ) ^ (k - 1))⁻¹ • ((⇑f ∣[k] ModularForm.heckeDiagMatrix ℓ) τ) = _
  rw [ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne ℓ), smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (zpow_ne_zero _ hℓ), one_mul]

theorem coe_levelRaise (f : ModularForm (Γb M H) k) :
    ⇑(levelRaise (ℓ := ℓ) f) = fun τ => f (ModularForm.heckeDiagMatrix ℓ • τ) :=
  funext (levelRaise_apply f)

theorem coe_levelRaise_eq_smul_slash (f : ModularForm (Γb M H) k) :
    ⇑(levelRaise (ℓ := ℓ) f) = ((ℓ : ℂ) ^ (k - 1))⁻¹ • (⇑f ∣[k] ModularForm.heckeDiagMatrix ℓ) := rfl

end Compose

section QExp

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ}

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem qC_mul {k₁ k₂ : ℤ} (f : ModularForm (Γt M H ℓ) k₁) (g : ModularForm (Γt M H ℓ) k₂) :
    qC (⇑f * ⇑g) = qC f * qC g := by
  rw [qC, qC, qC, ← map_mul, ← ModularForm.coe_mul,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_top]

theorem qC_add {k : ℤ} (f g : ModularForm (Γt M H ℓ) k) : qC (⇑f + ⇑g) = qC f + qC g := by
  rw [qC, qC, qC, ← map_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods_top f g]

theorem qC_smul {k : ℤ} (c : ℂ) (f : ModularForm (Γt M H ℓ) k) : qC (c • ⇑f) = HahnSeries.C c * qC f := by
  rw [qC, qC, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_top c f,
    ← HahnSeries.ofPowerSeries_C, ← map_mul, PowerSeries.smul_eq_C_mul]

theorem qC_neg {k : ℤ} (f : ModularForm (Γt M H ℓ) k) : qC (-⇑f) = -qC f := by
  rw [qC, qC, ModularForm.qExpansion_neg one_pos one_mem_strictPeriods_top f, map_neg]

theorem qC_eq_zero_iff {k : ℤ} (f : ModularForm (Γt M H ℓ) k) : qC f = 0 ↔ f = 0 := by
  rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods_top f]
  exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective

theorem qC_eq_zero_iff_bot {k : ℤ} (f : ModularForm (Γb M H) k) : qC f = 0 ↔ f = 0 := by
  rw [qC, ← ModularForm.qExpansion_eq_zero_iff one_pos one_mem_strictPeriods_bot f]
  exact map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective

theorem qC_zero : qC (0 : ℍ → ℂ) = 0 := by rw [qC, qExpansion_zero, map_zero]

theorem qC_one : qC (1 : ℍ → ℂ) = 1 := by rw [qC, qExpansion_one, map_one]

abbrev ιC : LaurentSeries ℚ →+* LaurentSeries ℂ := coeffMap (algebraMap ℚ ℂ)

theorem ιC_injective : Function.Injective ιC :=
  RingHom.injective _

theorem ιC_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    ιC (intSeriesC ℚ p) = qC F := by
  rw [qC, ← h]
  ext n
  simp only [intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

theorem ιC_C (c : ℚ) : ιC (HahnSeries.C c) = HahnSeries.C (c : ℂ) := by
  rw [ιC, coeffMap]
  ext n
  simp

theorem qC_ιC_ne_zero {k : ℤ} {g : ModularForm (Γt M H ℓ) k} {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) : qC g ≠ 0 := by
  rw [← ιC_intSeriesC hg]
  exact (map_ne_zero_iff _ ιC_injective).mpr hg0

theorem ne_zero_of_intSeriesC_ne_zero {k : ℤ} {g : ModularForm (Γt M H ℓ) k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : g ≠ 0 :=
  fun h => qC_ιC_ne_zero hg hg0 ((qC_eq_zero_iff g).mpr h)

theorem intSeriesC_add' {K : Type*} [Field K] (p p' : PowerSeries ℤ) :
    intSeriesC K (p + p') = intSeriesC K p + intSeriesC K p' := by
  simp [intSeriesC]

theorem intSeriesC_neg' {K : Type*} [Field K] (p : PowerSeries ℤ) :
    intSeriesC K (-p) = -intSeriesC K p := by
  simp [intSeriesC]

theorem intSeriesC_C_mul (K : Type*) [Field K] (n : ℤ) (p : PowerSeries ℤ) :
    intSeriesC K (PowerSeries.C n * p) = HahnSeries.C (n : K) * intSeriesC K p := by
  rw [intSeriesC_mul, intSeriesC, PowerSeries.map_C, HahnSeries.ofPowerSeries_C, eq_intCast]

section RatioGen

variable {Γ : Subgroup SL(2, ℤ)}
  (hΓ : (1 : ℝ) ∈ ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods)

include hΓ

theorem mul_mem_ratios {a b : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ) (hb : b ∈ intFormRatiosC ℚ Γ) :
    a * b ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, hg₁0, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, rfl⟩ := hb
  refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, pf₁ * pf₂, pg₁ * pg₂, ?_, ?_, ?_, ?_⟩
  · rw [IsIntegralQExp, map_mul, hf₁, hf₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos hΓ f₁ f₂).symm
  · rw [IsIntegralQExp, map_mul, hg₁, hg₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos hΓ g₁ g₂).symm
  · rw [intSeriesC_mul]; exact mul_ne_zero hg₁0 hg₂0
  · rw [intSeriesC_mul, intSeriesC_mul, div_mul_div_comm]

theorem add_mem_ratios {a b : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ) (hb : b ∈ intFormRatiosC ℚ Γ) :
    a + b ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, hg₁0, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, rfl⟩ := hb
  refine ⟨k₁ + k₂, f₁.mul g₂ + (g₁.mul f₂), g₁.mul g₂, pf₁ * pg₂ + pg₁ * pf₂, pg₁ * pg₂, ?_, ?_, ?_, ?_⟩
  · rw [IsIntegralQExp, map_add, map_mul, map_mul, hf₁, hf₂, hg₁, hg₂, ModularForm.coe_add,
      ModularForm.qExpansion_add one_pos hΓ, ModularForm.coe_mul, ModularForm.coe_mul,
      ModularForm.qExpansion_mul_coe one_pos hΓ, ModularForm.qExpansion_mul_coe one_pos hΓ]
  · rw [IsIntegralQExp, map_mul, hg₁, hg₂, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos hΓ g₁ g₂).symm
  · rw [intSeriesC_mul]; exact mul_ne_zero hg₁0 hg₂0
  · rw [intSeriesC_add', intSeriesC_mul, intSeriesC_mul, intSeriesC_mul, div_add_div _ _ hg₁0 hg₂0]

theorem neg_mem_ratios {a : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ) : -a ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := ha
  refine ⟨k, -f, g, -pf, pg, ?_, hg, hg0, ?_⟩
  · rw [IsIntegralQExp, map_neg, hf, ModularForm.coe_neg]
    exact (ModularForm.qExpansion_neg one_pos hΓ f).symm
  · rw [intSeriesC_neg', neg_div]

omit hΓ in
theorem inv_mem_ratios {a : LaurentSeries ℚ} (ha : a ∈ intFormRatiosC ℚ Γ) : a⁻¹ ∈ intFormRatiosC ℚ Γ := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := ha
  by_cases hf0 : intSeriesC ℚ pf = 0
  · rw [hf0, zero_div, _root_.inv_zero, ← zero_div (intSeriesC ℚ pg), ← hf0]
    exact ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
  · refine ⟨k, g, f, pg, pf, hg, hf, hf0, ?_⟩
    rw [inv_div]

omit hΓ in
theorem coe_const_eq_smul_one (c : ℂ) :
    ((ModularForm.const c : ModularForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 0) : ℍ → ℂ) =
      c • ((1 : ModularForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 0) : ℍ → ℂ) := by
  funext z
  rw [Pi.smul_apply, ModularForm.const_apply, ModularForm.one_coe_eq_one, Pi.one_apply, smul_eq_mul,
    mul_one]

theorem isIntegralQExp_const (n : ℤ) :
    IsIntegralQExp ((ModularForm.const (n : ℂ) :
      ModularForm ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 0) : ℍ → ℂ) (PowerSeries.C n) := by
  rw [IsIntegralQExp, PowerSeries.map_C, coe_const_eq_smul_one,
    ModularForm.qExpansion_smul one_pos hΓ, ModularForm.qExpansion_one,
    PowerSeries.smul_eq_C_mul, mul_one, eq_intCast]

theorem algebraMap_mem_ratios (c : ℚ) : algebraMap ℚ (LaurentSeries ℚ) c ∈ intFormRatiosC ℚ Γ := by
  have hden : ((c.den : ℤ) : ℚ) ≠ 0 := by exact_mod_cast c.den_nz
  refine ⟨0, ModularForm.const (c.num : ℂ), ModularForm.const (c.den : ℂ),
    PowerSeries.C (c.num : ℤ), PowerSeries.C (c.den : ℤ), isIntegralQExp_const hΓ _, ?_, ?_, ?_⟩
  · have := isIntegralQExp_const hΓ (c.den : ℤ)
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

def SFieldGen : IntermediateField ℚ (LaurentSeries ℚ) where
  carrier := intFormRatiosC ℚ Γ
  mul_mem' ha hb := mul_mem_ratios hΓ ha hb
  one_mem' := by simpa using algebraMap_mem_ratios hΓ 1
  add_mem' ha hb := add_mem_ratios hΓ ha hb
  zero_mem' := by simpa using algebraMap_mem_ratios hΓ 0
  algebraMap_mem' c := algebraMap_mem_ratios hΓ c
  inv_mem' a ha := inv_mem_ratios ha

theorem mem_ratios_of_mem {y : LaurentSeries ℚ} (hy : y ∈ qExpFunctionFieldC ℚ Γ) : y ∈ intFormRatiosC ℚ Γ := by
  have hle : qExpFunctionFieldC ℚ Γ ≤ SFieldGen hΓ := IntermediateField.adjoin_le_iff.mpr (fun _ h => h)
  exact hle hy

end RatioGen

variable (M H ℓ) in

abbrev S : Set (LaurentSeries ℚ) := intFormRatiosC ℚ (ΓtSL M H ℓ)

theorem mem_S_of_mem {y : LaurentSeries ℚ} (hy : y ∈ xHTopFunctionFieldC ℚ M H (M * ℓ)) : y ∈ S M H ℓ :=
  mem_ratios_of_mem one_mem_strictPeriods_top hy

theorem mem_Sb_of_mem {y : LaurentSeries ℚ} (hy : y ∈ xHFunctionField M H) :
    y ∈ intFormRatiosC ℚ (CohCarrier.GammaH M H) :=
  mem_ratios_of_mem one_mem_strictPeriods_bot hy

theorem exists_even_rep {x : LaurentSeries ℚ} (hx : x ∈ S M H ℓ) :
    ∃ (k : ℤ) (f g : ModularForm (Γt M H ℓ) k) (pf pg : PowerSeries ℤ), Even k ∧
      IsIntegralQExp f pf ∧ IsIntegralQExp g pg ∧ intSeriesC ℚ pg ≠ 0 ∧
        x = intSeriesC ℚ pf / intSeriesC ℚ pg := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := hx
  refine ⟨k + k, f.mul g, g.mul g, pf * pg, pg * pg, ⟨k, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rw [IsIntegralQExp, map_mul, hf, hg, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_top f g).symm
  · rw [IsIntegralQExp, map_mul, hg, ModularForm.coe_mul]
    exact (ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_top g g).symm
  · rw [intSeriesC_mul]; exact mul_ne_zero hg0 hg0
  · rw [intSeriesC_mul, intSeriesC_mul, mul_div_mul_right _ _ hg0]

theorem mul_eq_mul_of_qC {k₁ k₂ k₃ k₄ : ℤ} (f₁ : ModularForm (Γt M H ℓ) k₁) (f₂ : ModularForm (Γt M H ℓ) k₂)
    (f₃ : ModularForm (Γt M H ℓ) k₃) (f₄ : ModularForm (Γt M H ℓ) k₄) (hk : k₃ + k₄ = k₁ + k₂)
    (h : qC f₁ * qC f₂ = qC f₃ * qC f₄) : (⇑f₁ * ⇑f₂ : ℍ → ℂ) = ⇑f₃ * ⇑f₄ := by
  set D : ModularForm (Γt M H ℓ) (k₁ + k₂) := f₁.mul f₂ - ModularForm.mcast hk (f₃.mul f₄) with hD
  have hcoe : (⇑D : ℍ → ℂ) = ⇑f₁ * ⇑f₂ - ⇑f₃ * ⇑f₄ := by
    rw [hD, ModularForm.coe_sub, ModularForm.coe_mul, ModularForm.coe_mcast, ModularForm.coe_mul]
  have hq : qC (⇑D) = 0 := by
    have hsub := ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_top (f₁.mul f₂)
      (ModularForm.mcast hk (f₃.mul f₄))
    rw [ModularForm.coe_mul, ModularForm.coe_mcast, ModularForm.coe_mul] at hsub
    rw [hcoe, qC, hsub, map_sub]
    change qC (⇑f₁ * ⇑f₂) - qC (⇑f₃ * ⇑f₄) = 0
    rw [qC_mul, qC_mul, h, sub_self]
  have hD0 : D = 0 := (qC_eq_zero_iff D).mp hq
  have : (⇑D : ℍ → ℂ) = 0 := by rw [hD0, ModularForm.coe_zero]
  rw [hcoe] at this
  exact sub_eq_zero.mp this

variable [NeZero ℓ] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1)

theorem al_mul_eq {k₁ k₂ k₃ k₄ : ℤ} (f₁ : ModularForm (Γt M H ℓ) k₁) (f₂ : ModularForm (Γt M H ℓ) k₂)
    (f₃ : ModularForm (Γt M H ℓ) k₃) (f₄ : ModularForm (Γt M H ℓ) k₄) (hk : k₃ + k₄ = k₁ + k₂)
    (h : (⇑f₁ * ⇑f₂ : ℍ → ℂ) = ⇑f₃ * ⇑f₄) :
    (⇑(alForm γ hγ hγℓ f₁) * ⇑(alForm γ hγ hγℓ f₂) : ℍ → ℂ) =
      ⇑(alForm γ hγ hγℓ f₃) * ⇑(alForm γ hγ hγℓ f₄) := by
  have h' := congrArg (fun F : ℍ → ℂ => F ∣[k₁ + k₂] γ) h
  rw [ModularForm.mul_slash_SL2] at h'
  conv at h' => rhs; rw [← hk, ModularForm.mul_slash_SL2]
  funext τ
  have := congrFun h' (ModularForm.heckeDiagMatrix ℓ • τ)
  simpa only [coe_alForm, Pi.mul_apply] using this

end QExp

section Expand

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ} [NeZero ℓ] {k : ℤ}

theorem coeffMap_qExpand {R T : Type*} [CommRing R] [CommRing T] (φ : R →+* T)
    (x : LaurentSeries R) : coeffMap φ (qExpand R ℓ x) = qExpand T ℓ (coeffMap φ x) := by
  ext n
  by_cases hk : (ℓ : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd ℓ _ hk, qExpand_coeff_of_not_dvd ℓ _ hk, map_zero]

def expandPS {R : Type*} [CommRing R] (ℓ : ℕ) (P : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => if ℓ ∣ n then PowerSeries.coeff (n / ℓ) P else 0

omit [NeZero ℓ] in
theorem coeff_expandPS {R : Type*} [CommRing R] (P : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (expandPS ℓ P) = if ℓ ∣ n then PowerSeries.coeff (n / ℓ) P else 0 := by
  rw [expandPS, PowerSeries.coeff_mk]

theorem ofPowerSeries_expandPS {R : Type*} [CommRing R] (P : PowerSeries R) :
    ofPowerSeries ℤ R (expandPS ℓ P) = qExpand R ℓ (ofPowerSeries ℤ R P) := by
  ext m
  by_cases hdvd : (ℓ : ℤ) ∣ m
  · obtain ⟨j, rfl⟩ := hdvd
    rw [qExpand_coeff_mul, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
    have hℓ0 : (0 : ℤ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
    by_cases hj : j < 0
    · rw [if_pos hj, if_pos (mul_neg_of_pos_of_neg hℓ0 hj)]
    · rw [if_neg hj, if_neg (by push Not at hj ⊢; positivity)]
      simp only [coeff_expandPS]
      have h1 : ((ℓ : ℤ) * j).natAbs = ℓ * j.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      rw [h1, if_pos (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne ℓ))]
  · rw [qExpand_coeff_of_not_dvd ℓ _ hdvd, PowerSeries.coeff_coe]
    split_ifs with hm
    · rfl
    · rw [coeff_expandPS, if_neg]
      rintro ⟨c, hc⟩
      apply hdvd
      refine ⟨c, ?_⟩
      have : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg (le_of_not_gt hm)
      rw [← this, hc]; push_cast; ring

omit [NeZero ℓ] in
theorem expandPS_map (P : PowerSeries ℤ) :
    expandPS ℓ (P.map (Int.castRingHom ℂ)) = (expandPS ℓ P).map (Int.castRingHom ℂ) := by
  ext n
  simp only [coeff_expandPS, PowerSeries.coeff_map]
  split_ifs <;> simp

theorem qExpansion_comp_heckeDiag (f : ModularForm (Γb M H) k) :
    qExpansion 1 (fun τ => f (ModularForm.heckeDiagMatrix ℓ • τ)) = expandPS ℓ (qExpansion 1 f) := by
  ext n
  rw [coeff_expandPS]
  exact ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul f one_mem_strictPeriods_bot (NeZero.ne ℓ) n

theorem qC_levelRaise (f : ModularForm (Γb M H) k) :
    qC (levelRaise (ℓ := ℓ) f) = qExpand ℂ ℓ (qC f) := by
  rw [qC, coe_levelRaise, qExpansion_comp_heckeDiag, ofPowerSeries_expandPS, qC]

theorem isIntegralQExp_levelRaise {f : ModularForm (Γb M H) k} {pf : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) : IsIntegralQExp (levelRaise (ℓ := ℓ) f) (expandPS ℓ pf) := by
  rw [IsIntegralQExp, coe_levelRaise, qExpansion_comp_heckeDiag, ← hf, expandPS_map]

theorem intSeriesC_expandPS (K : Type*) [Field K] (p : PowerSeries ℤ) :
    intSeriesC K (expandPS ℓ p) = qExpand K ℓ (intSeriesC K p) := by
  rw [intSeriesC, intSeriesC, ← ofPowerSeries_expandPS]
  congr 1
  ext n
  simp only [coeff_expandPS, PowerSeries.coeff_map]
  split_ifs <;> simp

end Expand

section Conj

variable {N : ℕ} {H' : Subgroup (ZMod N)ˣ} {k : ℤ}

theorem bot_le_conj_bot (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) :
    Γb N H' ≤ ConjAct.toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ σ)⁻¹ • Γb N H' := by
  rintro x ⟨δ, hδ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  refine ⟨σ * δ * σ⁻¹, CohCarrier.conj_mem_GammaH N H' ⟨σ, hσ⟩ ⟨δ, hδ⟩, ?_⟩
  simp only [map_mul, map_inv]

def diaForm (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) (f : ModularForm (Γb N H') k) : ModularForm (Γb N H') k :=
  restrictForm (bot_le_conj_bot σ hσ) (ModularForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ σ))

theorem coe_diaForm (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) (f : ModularForm (Γb N H') k) :
    ⇑(diaForm σ hσ f) = (⇑f ∣[k] (σ : GL (Fin 2) ℝ)) := rfl

theorem diaForm_ne_zero (σ : SL(2, ℤ)) (hσ : σ ∈ Gamma0 N) {f : ModularForm (Γb N H') k} (hf : f ≠ 0) :
    diaForm σ hσ f ≠ 0 := by
  intro h
  apply hf
  have h1 : (⇑f ∣[k] (σ : GL (Fin 2) ℝ)) = 0 := by
    rw [← coe_diaForm σ hσ f, h]; rfl
  have h2 : ⇑f = ((⇑f ∣[k] (σ : GL (Fin 2) ℝ)) ∣[k] ((σ : GL (Fin 2) ℝ)⁻¹)) := by
    rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]
  rw [h1, SlashAction.zero_slash] at h2
  exact DFunLike.ext' h2

theorem ne_zero_of_isIntegralQExp {g : ModularForm (Γb N H') k} {pg : PowerSeries ℤ}
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) : g ≠ 0 := by
  intro h
  apply hg0
  apply ιC_injective
  rw [ιC_intSeriesC hg, map_zero, h]
  exact qC_zero

theorem slash_levelRaise {p : ℕ} [NeZero p] (f : ModularForm (Γb N H') k) (δ : SL(2, ℤ)) (h : (p : ℤ) ∣ δ 1 0) :
    (⇑(levelRaise (ℓ := p) f) ∣[k] (δ : GL (Fin 2) ℝ)) =
      fun τ => (⇑f ∣[k] (conjSL δ h : GL (Fin 2) ℝ)) (ModularForm.heckeDiagMatrix p • τ) := by
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne p
  have hmat : ModularForm.heckeDiagMatrix p * (Matrix.SpecialLinearGroup.mapGL ℝ δ) =
      Matrix.SpecialLinearGroup.mapGL ℝ (conjSL δ h) * ModularForm.heckeDiagMatrix p := by
    rw [← heckeDiag_mul_mul_inv h (NeZero.ne p), inv_mul_cancel_right]
  rw [coe_levelRaise_eq_smul_slash, inv_pow_eq_real, real_smul_slash, ← SlashAction.slash_mul,
    show ((δ : GL (Fin 2) ℝ)) = Matrix.SpecialLinearGroup.mapGL ℝ δ from rfl, hmat, SlashAction.slash_mul]
  funext τ
  rw [Pi.smul_apply, ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne p)]
  try simp only [smul_eq_mul]
  push_cast
  rw [inv_mul_cancel_left₀ (zpow_ne_zero _ hp)]
  rfl

theorem qC_slash_levelRaise {p : ℕ} [NeZero p] (f : ModularForm (Γb N H') k) (δ : SL(2, ℤ))
    (h : (p : ℤ) ∣ δ 1 0) (hδ' : conjSL δ h ∈ Gamma0 N) :
    qC (⇑(levelRaise (ℓ := p) f) ∣[k] (δ : GL (Fin 2) ℝ)) =
      qExpand ℂ p (qC (⇑f ∣[k] (conjSL δ h : GL (Fin 2) ℝ))) := by
  rw [slash_levelRaise f δ h, ← coe_diaForm (conjSL δ h) hδ' f, ← coe_levelRaise, qC_levelRaise]

end Conj

section DBeta

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} (hpM : p ∣ M)

local notation "L" => AlgebraicClosure ℚ

omit [Fact p.Prime] [NeZero M] in
include hpM in
theorem div_mul_cancel' : M / p * p = M := Nat.div_mul_cancel hpM

omit [Fact p.Prime] [NeZero M] in
include hpM in

theorem unitsMap_gamma0Units {γ : SL(2, ℤ)} (hM : γ ∈ Gamma0 M) (hN : γ ∈ Gamma0 (M / p)) :
    ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) (CohCarrier.gamma0Units M ⟨γ, hM⟩) =
      CohCarrier.gamma0Units (M / p) ⟨γ, hN⟩ := by
  ext
  simp [CohCarrier.gamma0Units, Gamma0Map, ZMod.unitsMap]

omit [Fact p.Prime] [NeZero M] in
theorem gamma0_le_of_dvd' {N N' : ℕ} (h : N ∣ N') : Gamma0 N' ≤ Gamma0 N := fun γ hγ => by
  rw [Gamma0_mem] at hγ ⊢
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ((Int.natCast_dvd_natCast.mpr h).trans this)

omit [Fact p.Prime] [NeZero M] in
include hpM in

theorem gammaH_le_top :
    CohCarrier.GammaH M H ≤ ΓtSL (M / p) (infSubgroup p M H hpM) p := by
  intro γ hγ
  obtain ⟨hM0, hMH⟩ := CohCarrier.mem_GammaH_iff.mp hγ
  have hN0 : γ ∈ Gamma0 (M / p) := gamma0_le_of_dvd' (Nat.div_dvd_of_dvd hpM) hM0
  refine Subgroup.mem_inf.mpr ⟨CohCarrier.mem_GammaH_iff.mpr ⟨hN0, ?_⟩, ?_⟩
  · rw [← unitsMap_gamma0Units hpM hM0 hN0]
    exact unitsMap_mem_infSubgroup p M H hpM hMH
  · rw [div_mul_cancel' hpM]; exact hM0

omit [Fact p.Prime] [NeZero M] in
include hpM in

theorem Γb_le_Γt : Γb M H ≤ Γt (M / p) (infSubgroup p M H hpM) p :=
  Subgroup.map_mono (gammaH_le_top hpM)

omit [Fact p.Prime] [NeZero M] in
include hpM in

theorem xHTopFunctionFieldC_le_xHFunctionField :
    xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p) ≤ xHFunctionField M H :=
  qExpFunctionFieldC_mono ℚ (gammaH_le_top hpM)

theorem coeffEmb_qExpand {p : ℕ} [NeZero p] (y : LaurentSeries ℚ) :
    coeffEmb L (qExpand ℚ p y) = qExpand L p (coeffEmb L y) :=
  coeffMap_qExpand _ _

theorem coe_diamondAutHBar_gen (d : (ZMod M)ˣ) {k : ℤ}
    (f g : ModularForm (Γb (M / p) (infSubgroup p M H hpM)) k) (pf pg : PowerSeries ℤ)
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0)
    (hx : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      coeffEmb L (qExpand ℚ p (intSeriesC ℚ pf / intSeriesC ℚ pg)) ∈ xHFunctionFieldBar M H)
    (hu : coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg) ∈ xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ((diamondAutHBar M H d ⟨_, hx⟩ : xHFunctionFieldBar M H) : LaurentSeries L) =
      qExpand L p ((diamondAutHBar (M / p) (infSubgroup p M H hpM) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)
        ⟨_, hu⟩ : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) : LaurentSeries L) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero (M / p) := neZero_div p M hpM

  obtain ⟨γ0, hγ0⟩ := CohCarrier.gamma0Units_surjective M d⁻¹
  have hγM : (γ0 : SL(2, ℤ)) ∈ Gamma0 M := γ0.2
  have hγd : (((γ0 : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = (d : ZMod M) := by
    have h11 : (((γ0 : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ((d⁻¹ : (ZMod M)ˣ) : ZMod M) := by
      rw [← hγ0]; rfl
    have hda := CohCarrier.Gamma0_d_mul_a M γ0
    rw [h11] at hda
    have := congrArg (fun z : ZMod M => (d : ZMod M) * z) hda
    simpa [← mul_assoc] using this
  have hγMp : (γ0 : SL(2, ℤ)) ∈ Gamma0 (M / p * p) := by rw [div_mul_cancel' hpM]; exact hγM
  set γ : SL(2, ℤ) := γ0.1 with hγdef
  have h10 : (p : ℤ) ∣ γ 1 0 := dvd_of_mem_Gamma0_mul hγMp
  have hγ' : conjSL γ h10 ∈ Gamma0 (M / p) := conjSL_mem_Gamma0 hγMp (NeZero.ne p)
  have hγ'd : ((conjSL γ h10 0 0 : ℤ) : ZMod (M / p)) =
      ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) := by
    rw [conjSL_apply_00]
    show ((γ 0 0 : ℤ) : ZMod (M / p)) = ZMod.castHom (Nat.div_dvd_of_dvd hpM) (ZMod (M / p)) (d : ZMod M)
    rw [← hγd, map_intCast]

  set F : ModularForm (Γb M H) k := restrictForm (Γb_le_Γt hpM) (levelRaise (ℓ := p) f) with hFdef
  set G : ModularForm (Γb M H) k := restrictForm (Γb_le_Γt hpM) (levelRaise (ℓ := p) g) with hGdef
  have hF : IsIntegralQExp F (expandPS p pf) := isIntegralQExp_levelRaise hf
  have hG : IsIntegralQExp G (expandPS p pg) := isIntegralQExp_levelRaise hg
  have hG0 : intSeriesC ℚ (expandPS p pg) ≠ 0 := by
    rw [intSeriesC_expandPS]
    exact fun h => hg0 (qExpand_injective p (by rw [h, map_zero]))

  obtain ⟨yM, -, hyMσ, hyM⟩ := (ModularCurve.heckeDiamondInputsHAll M H).isDiamondAutHBar d k F G
    (expandPS p pf) (expandPS p pg) hF hG hG0 γ hγM hγd
  obtain ⟨yN, -, hyNσ, hyN⟩ := (ModularCurve.heckeDiamondInputsHAll (M / p) (infSubgroup p M H hpM)).isDiamondAutHBar
    (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d) k f g pf pg hf hg hg0 (conjSL γ h10) hγ' hγ'd
  change ιC yM * qC (⇑G ∣[k] (γ : GL (Fin 2) ℝ)) = qC (⇑F ∣[k] (γ : GL (Fin 2) ℝ)) at hyM
  change ιC yN * qC (⇑g ∣[k] (conjSL γ h10 : GL (Fin 2) ℝ)) = qC (⇑f ∣[k] (conjSL γ h10 : GL (Fin 2) ℝ)) at hyN

  have hFq : qC (⇑F ∣[k] (γ : GL (Fin 2) ℝ)) = qExpand ℂ p (qC (⇑f ∣[k] (conjSL γ h10 : GL (Fin 2) ℝ))) :=
    qC_slash_levelRaise f γ h10 hγ'
  have hGq : qC (⇑G ∣[k] (γ : GL (Fin 2) ℝ)) = qExpand ℂ p (qC (⇑g ∣[k] (conjSL γ h10 : GL (Fin 2) ℝ))) :=
    qC_slash_levelRaise g γ h10 hγ'
  have hne : qC (⇑g ∣[k] (conjSL γ h10 : GL (Fin 2) ℝ)) ≠ 0 := by
    rw [← coe_diaForm (conjSL γ h10) hγ' g, Ne, qC_eq_zero_iff_bot]
    exact diaForm_ne_zero _ hγ' (ne_zero_of_isIntegralQExp hg hg0)
  have hy : yM = qExpand ℚ p yN := by
    apply ιC_injective
    rw [coeffMap_qExpand]
    refine mul_right_cancel₀ ((map_ne_zero_iff _ (qExpand_injective p)).mpr hne) ?_
    rw [← hGq, hyM, hFq, ← hyN, map_mul, hGq]

  have hval : coeffEmb L (qExpand ℚ p (intSeriesC ℚ pf / intSeriesC ℚ pg)) =
      coeffEmb L (intSeriesC ℚ (expandPS p pf) / intSeriesC ℚ (expandPS p pg)) := by
    rw [intSeriesC_expandPS, intSeriesC_expandPS, map_div₀]
  have hgen : (⟨coeffEmb L (qExpand ℚ p (intSeriesC ℚ pf / intSeriesC ℚ pg)), hx⟩ : xHFunctionFieldBar M H) =
      ⟨coeffEmb L (intSeriesC ℚ (expandPS p pf) / intSeriesC ℚ (expandPS p pg)),
        coeffEmb_mem_laurentBaseChange L (div_mem_qExpFunctionFieldC F G hF hG hG0)⟩ :=
    Subtype.ext hval
  rw [hgen, hyMσ, hy, coeffEmb_qExpand]
  congr 1
  exact hyNσ.symm

def qExpandAlg (p : ℕ) [NeZero p] : LaurentSeries L →ₐ[L] LaurentSeries L :=
  { qExpand L p with
    commutes' := fun a => by
      show qExpand L p (algebraMap L (LaurentSeries L) a) = algebraMap L (LaurentSeries L) a
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }

end DBeta

end DBetaBar
p2m_reactivate "P2MW.S_ModularCurve_coe_diamondAutHBar_eq_qExpand_coe_diamondAutHBar_div_of_coe_eq_qExpand.DBetaBar"

open ModularCurve DBetaBar in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (d : (ZMod M)ˣ) (x : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (hxu : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      (x : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ))) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ((diamondAutHBar M H d x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand (AlgebraicClosure ℚ) p ((diamondAutHBar (M / p) (infSubgroup p M H hpM) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d) u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
        LaurentSeries (AlgebraicClosure ℚ)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero (M / p) := neZero_div p M hpM

  have hβ : HeckeBetaHDefined (M / p) (infSubgroup p M H hpM) p :=
    ((ModularCurve.heckeDiamondInputsHAll (M / p) (infSubgroup p M H hpM)).heckeInputsHAlong p Fact.out).betaHDefined
  have hle : laurentBaseChange (AlgebraicClosure ℚ) (xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p)) ≤
      xHFunctionFieldBar M H :=
    IntermediateField.adjoin.mono _ _ _ (Set.image_mono (xHTopFunctionFieldC_le_xHFunctionField hpM))
  let βAlg : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H) :=
    (IntermediateField.inclusion hle).comp (heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) p)
  have hβAlg : ∀ v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
      ((βAlg v : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) p (v : LaurentSeries (AlgebraicClosure ℚ)) := fun v => by
    show ((IntermediateField.inclusion hle (heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (infSubgroup p M H hpM) p v) :
      ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = _
    rw [IntermediateField.coe_inclusion, coe_heckeBetaHBar _ _ p hβ]

  let φ₁ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] LaurentSeries (AlgebraicClosure ℚ) :=
    (xHFunctionFieldBar M H).val.comp ((diamondAutHBar M H d).toAlgHom.comp βAlg)
  let φ₂ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] LaurentSeries (AlgebraicClosure ℚ) :=
    (qExpandAlg p).comp ((xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)).val.comp
      (diamondAutHBar (M / p) (infSubgroup p M H hpM) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)).toAlgHom)
  have hφ₁ : ∀ v, φ₁ v = ((diamondAutHBar M H d (βAlg v) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun _ => rfl
  have hφ₂ : ∀ v, φ₂ v = qExpand (AlgebraicClosure ℚ) p
      ((diamondAutHBar (M / p) (infSubgroup p M H hpM) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d) v :
        ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) :=
    fun _ => rfl
  have heq : φ₁ = φ₂ := by
    refine IntermediateField.algHom_ext_of_eq_adjoin (F := AlgebraicClosure ℚ)
      (S := xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))
      (s := ⇑(coeffEmb (AlgebraicClosure ℚ)) '' (xHFunctionField (M / p) (infSubgroup p M H hpM) : Set (LaurentSeries ℚ)))
      rfl fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := hz
    obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := mem_Sb_of_mem hy
    refine (hφ₁ _).trans (Eq.trans ?_ (hφ₂ _).symm)
    have hx : coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p (intSeriesC ℚ pf / intSeriesC ℚ pg)) ∈ xHFunctionFieldBar M H := by
      rw [coeffEmb_qExpand, ← hβAlg ⟨_, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hy⟩]
      exact (βAlg _).2
    have hv : βAlg ⟨_, (rfl : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) = IntermediateField.adjoin _ _).ge
        (IntermediateField.subset_adjoin _ _ ⟨_, hy, rfl⟩)⟩ = ⟨_, hx⟩ :=
      Subtype.ext (by
        show ((βAlg _ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
          coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p (intSeriesC ℚ pf / intSeriesC ℚ pg))
        rw [hβAlg, coeffEmb_qExpand])
    rw [hv]
    exact coe_diamondAutHBar_gen hpM d f g pf pg hf hg hg0 hx _

  have hxβ : x = βAlg u := Subtype.ext (by rw [hβAlg]; exact hxu)
  rw [hxβ]
  exact (hφ₁ u).symm.trans ((DFunLike.congr_fun heq u).trans (hφ₂ u))

end
end S_ModularCurve_coe_diamondAutHBar_eq_qExpand_coe_diamondAutHBar_div_of_coe_eq_qExpand
end P2MW
export P2MW.S_ModularCurve_coe_diamondAutHBar_eq_qExpand_coe_diamondAutHBar_div_of_coe_eq_qExpand (solution)
