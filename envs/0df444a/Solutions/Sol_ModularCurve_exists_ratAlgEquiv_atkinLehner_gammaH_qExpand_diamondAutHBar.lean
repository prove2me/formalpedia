-- Prove2me | solution 1 for ModularCurve.exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/ed4aaff9-f8ad-5147-9638-cd4ff31c9216

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_atkinLehnerSlash_of_even
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_ModularCurve_heckeDiamondInputsHAll
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd"

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm Pointwise

namespace WFieldH

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
  convert hH using 1 <;> first | rfl | (apply Units.ext; rfl)

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

structure ALData (M ℓ : ℕ) where

  y : ℤ

  w₀ : ℤ
  rel : (ℓ : ℤ) * w₀ - M * y = 1

theorem nonempty_alData {M ℓ : ℕ} (h : Nat.Coprime ℓ M) : Nonempty (ALData M ℓ) := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr h
  exact ⟨⟨-v, u, by linear_combination huv⟩⟩

namespace ALData

variable {M ℓ : ℕ} (d : ALData M ℓ)

def γ₁ : SL(2, ℤ) :=
  ⟨!![1, d.y; (M : ℤ), (ℓ : ℤ) * d.w₀], by rw [Matrix.det_fin_two_of]; linear_combination d.rel⟩

def γ₁' : SL(2, ℤ) :=
  ⟨!![d.w₀, -d.y; -(M : ℤ), (ℓ : ℤ)], by rw [Matrix.det_fin_two_of]; linear_combination d.rel⟩

def γ₄ : SL(2, ℤ) :=
  ⟨!![(ℓ : ℤ), d.y; (M : ℤ), d.w₀], by rw [Matrix.det_fin_two_of]; linear_combination d.rel⟩

@[scoped simp] theorem γ₁_00 : d.γ₁ 0 0 = 1 := rfl
@[scoped simp] theorem γ₁_01 : d.γ₁ 0 1 = d.y := rfl
@[scoped simp] theorem γ₁_10 : d.γ₁ 1 0 = M := rfl
@[scoped simp] theorem γ₁_11 : d.γ₁ 1 1 = (ℓ : ℤ) * d.w₀ := rfl
@[scoped simp] theorem γ₁'_00 : d.γ₁' 0 0 = d.w₀ := rfl
@[scoped simp] theorem γ₁'_01 : d.γ₁' 0 1 = -d.y := rfl
@[scoped simp] theorem γ₁'_10 : d.γ₁' 1 0 = -(M : ℤ) := rfl
@[scoped simp] theorem γ₁'_11 : d.γ₁' 1 1 = ℓ := rfl
@[scoped simp] theorem γ₄_00 : d.γ₄ 0 0 = ℓ := rfl
@[scoped simp] theorem γ₄_01 : d.γ₄ 0 1 = d.y := rfl
@[scoped simp] theorem γ₄_10 : d.γ₄ 1 0 = M := rfl
@[scoped simp] theorem γ₄_11 : d.γ₄ 1 1 = d.w₀ := rfl

theorem γ₁_mem_Gamma0 : d.γ₁ ∈ Gamma0 M := by rw [Gamma0_mem, γ₁_10]; simp
theorem γ₁'_mem_Gamma0 : d.γ₁' ∈ Gamma0 M := by rw [Gamma0_mem, γ₁'_10]; simp
theorem γ₄_mem_Gamma0 : d.γ₄ ∈ Gamma0 M := by rw [Gamma0_mem, γ₄_10]; simp

theorem γ₁_mem_Gamma1 : d.γ₁ ∈ Gamma1 M := by
  rw [Gamma1_mem, γ₁_00, γ₁_11, γ₁_10]
  refine ⟨by simp, ?_, by simp⟩
  have := congrArg (Int.cast : ℤ → ZMod M) d.rel
  push_cast at this ⊢
  rw [ZMod.natCast_self, zero_mul, sub_zero] at this
  exact this

theorem dvd_γ₁ : (ℓ : ℤ) ∣ d.γ₁ 1 1 := ⟨d.w₀, rfl⟩
theorem dvd_γ₁' : (ℓ : ℤ) ∣ d.γ₁' 1 1 := ⟨1, by simp⟩

theorem γ₄_00_zmod : ((d.γ₄ 0 0 : ℤ) : ZMod M) = (ℓ : ZMod M) := by simp

theorem rel_real : (ℓ : ℝ) * d.w₀ - M * d.y = 1 := by exact_mod_cast d.rel

theorem alGL_γ₁_mul (hℓ : ℓ ≠ 0) :
    alGL d.γ₁ ℓ * alGL d.γ₁' ℓ = ModularForm.heckeDiagMatrix ℓ * ModularForm.heckeMatrix ℓ 0 := by
  have hrel := d.rel_real
  apply Units.ext
  ext i j
  simp only [alGL, Units.val_mul, ModularForm.val_heckeDiagMatrix hℓ, ModularForm.val_heckeMatrix hℓ]
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, γ₁, γ₁']; linear_combination (ℓ : ℝ) * hrel
  · simp [Matrix.mul_apply, Fin.sum_univ_two, γ₁, γ₁']; ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, γ₁, γ₁']; ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, γ₁, γ₁']; linear_combination (ℓ : ℝ) * hrel

theorem alGL_γ₁'_mul (hℓ : ℓ ≠ 0) :
    alGL d.γ₁' ℓ * alGL d.γ₁ ℓ = ModularForm.heckeDiagMatrix ℓ * ModularForm.heckeMatrix ℓ 0 := by
  have hrel := d.rel_real
  apply Units.ext
  ext i j
  simp only [alGL, Units.val_mul, ModularForm.val_heckeDiagMatrix hℓ, ModularForm.val_heckeMatrix hℓ]
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, γ₁, γ₁']; linear_combination (ℓ : ℝ) * hrel
  · simp [Matrix.mul_apply, Fin.sum_univ_two, γ₁, γ₁']; ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, γ₁, γ₁']; ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, γ₁, γ₁']; linear_combination (ℓ : ℝ) * hrel

theorem heckeDiag_mul_alGL_γ₁ (hℓ : ℓ ≠ 0) :
    ModularForm.heckeDiagMatrix ℓ * alGL d.γ₁ ℓ =
      ModularForm.heckeDiagMatrix ℓ * ModularForm.heckeMatrix ℓ 0 *
        Matrix.SpecialLinearGroup.mapGL ℝ d.γ₄ := by
  apply Units.ext
  ext i j
  simp only [alGL, Units.val_mul, ModularForm.val_heckeDiagMatrix hℓ, ModularForm.val_heckeMatrix hℓ]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, γ₁, γ₄]
  ring

end ALData
p2m_reactivate "P2MW.S_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar.WFieldH.ALData"

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

variable (d : ALData M ℓ)

theorem alForm_γ₁'_alForm_γ₁ (f : ModularForm (Γt M H ℓ) k) :
    ⇑(alForm d.γ₁' d.γ₁'_mem_Gamma0 d.dvd_γ₁' (alForm d.γ₁ d.γ₁_mem_Gamma0 d.dvd_γ₁ f)) =
      ((ℓ : ℂ) ^ k)⁻¹ • ⇑f :=
  alForm_alForm_of_mul_eq _ _ _ _ _ _ (d.alGL_γ₁_mul (NeZero.ne ℓ)) f

theorem alForm_γ₁_alForm_γ₁' (f : ModularForm (Γt M H ℓ) k) :
    ⇑(alForm d.γ₁ d.γ₁_mem_Gamma0 d.dvd_γ₁ (alForm d.γ₁' d.γ₁'_mem_Gamma0 d.dvd_γ₁' f)) =
      ((ℓ : ℂ) ^ k)⁻¹ • ⇑f :=
  alForm_alForm_of_mul_eq _ _ _ _ _ _ (d.alGL_γ₁'_mul (NeZero.ne ℓ)) f

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

theorem alForm_γ₁_levelRaise (f : ModularForm (Γb M H) k) :
    ⇑(alForm d.γ₁ d.γ₁_mem_Gamma0 d.dvd_γ₁ (levelRaise f)) = ((ℓ : ℂ) ^ k)⁻¹ • (⇑f ∣[k] d.γ₄) := by
  have hℓ : (ℓ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  rw [coe_alForm_eq_smul_slash, coe_levelRaise_eq_smul_slash, inv_pow_eq_real, real_smul_slash,
    ← SlashAction.slash_mul, d.heckeDiag_mul_alGL_γ₁ (NeZero.ne ℓ), SlashAction.slash_mul,
    slash_diag_diag, ModularForm.smul_slash, smul_smul, smul_smul, ← inv_pow_eq_real, ModularForm.SL_slash]
  have hσ : UpperHalfPlane.σ (Matrix.SpecialLinearGroup.mapGL ℝ d.γ₄) ((ℓ : ℂ) ^ (k - 2)) =
      (ℓ : ℂ) ^ (k - 2) := by
    have : ((ℓ : ℂ) ^ (k - 2)) = (((ℓ : ℝ) ^ (k - 2) : ℝ) : ℂ) := by push_cast; rfl
    rw [this, UpperHalfPlane.σ_ofReal]
  rw [hσ]
  congr 1
  · rw [← _root_.zpow_neg, ← zpow_add₀ hℓ, ← zpow_add₀ hℓ, ← _root_.zpow_neg]
    congr 1; ring

theorem alForm_γ₁_restrict (f : ModularForm (Γb M H) k) :
    ⇑(alForm d.γ₁ d.γ₁_mem_Gamma0 d.dvd_γ₁ (restrictForm Γt_le_Γb f)) = ⇑(levelRaise (ℓ := ℓ) f) := by
  rw [coe_alForm, coe_levelRaise]
  have : (⇑(restrictForm Γt_le_Γb f : ModularForm (Γt M H ℓ) k) ∣[k] d.γ₁) = ⇑f := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantFormClass.slash_action_eq f _
      (Subgroup.mem_map_of_mem _ (Gamma1_le_GammaH M H d.γ₁_mem_Gamma1))
  rw [this]

end Compose
p2m_reactivate "P2MW.S_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar.WFieldH.ALData"

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
p2m_reactivate "P2MW.S_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar.WFieldH.ALData"

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
p2m_reactivate "P2MW.S_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar.WFieldH.ALData"

section Img

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ} [NeZero ℓ]
variable (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1)
variable (γ' : SL(2, ℤ)) (hγ' : γ' ∈ Gamma0 M) (hγ'ℓ : (ℓ : ℤ) ∣ γ' 1 1)

variable (H) in

def QuasiInv : Prop :=
  ∀ (k : ℤ) (f : ModularForm (Γt M H ℓ) k),
    ⇑(alForm γ' hγ' hγ'ℓ (alForm γ hγ hγℓ f)) = ((ℓ : ℂ) ^ k)⁻¹ • ⇑f

variable {γ hγ hγℓ γ' hγ' hγ'ℓ}

theorem alForm_ne_zero (hq : QuasiInv H γ hγ hγℓ γ' hγ' hγ'ℓ) {k : ℤ} {f : ModularForm (Γt M H ℓ) k}
    (hf : f ≠ 0) : alForm γ hγ hγℓ f ≠ 0 := by
  intro h
  apply hf
  have h1 := hq k f
  rw [h, alForm_zero, ModularForm.coe_zero] at h1
  have hc : ((ℓ : ℂ) ^ k)⁻¹ ≠ 0 := inv_ne_zero (zpow_ne_zero _ (by exact_mod_cast NeZero.ne ℓ))
  have : (⇑f : ℍ → ℂ) = 0 := by
    funext τ
    have := congrFun h1 τ
    simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hc
  exact DFunLike.ext' (by rw [this, ModularForm.coe_zero])

theorem qC_alForm_ne_zero (hq : QuasiInv H γ hγ hγℓ γ' hγ' hγ'ℓ) {k : ℤ} {g : ModularForm (Γt M H ℓ) k}
    {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    qC (alForm γ hγ hγℓ g) ≠ 0 := fun h =>
  alForm_ne_zero hq (ne_zero_of_intSeriesC_ne_zero hg hg0) ((qC_eq_zero_iff _).mp h)

variable (H γ hγ hγℓ) in

def IsImg (x y : LaurentSeries ℚ) : Prop :=
  ∃ (k : ℤ) (f g : ModularForm (Γt M H ℓ) k) (pf pg : PowerSeries ℤ),
    IsIntegralQExp f pf ∧ IsIntegralQExp g pg ∧ intSeriesC ℚ pg ≠ 0 ∧
      x = intSeriesC ℚ pf / intSeriesC ℚ pg ∧
        ιC y * qC (alForm γ hγ hγℓ g) = qC (alForm γ hγ hγℓ f)

theorem IsImg.apply_rep (hq : QuasiInv H γ hγ hγℓ γ' hγ' hγ'ℓ) {x y : LaurentSeries ℚ}
    (h : IsImg H γ hγ hγℓ x y) {k : ℤ}
    (f g : ModularForm (Γt M H ℓ) k) (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf)
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) (hx : x = intSeriesC ℚ pf / intSeriesC ℚ pg) :
    ιC y * qC (alForm γ hγ hγℓ g) = qC (alForm γ hγ hγℓ f) := by
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, hx₂, hy⟩ := h
  have hcross : intSeriesC ℚ pf * intSeriesC ℚ pg₂ = intSeriesC ℚ pf₂ * intSeriesC ℚ pg := by
    rw [← div_eq_div_iff hg0 hg₂0, ← hx, ← hx₂]
  have hqc : qC f * qC g₂ = qC f₂ * qC g := by
    have := congrArg ιC hcross
    rwa [map_mul, map_mul, ιC_intSeriesC hf, ιC_intSeriesC hg₂, ιC_intSeriesC hf₂,
      ιC_intSeriesC hg] at this
  have hfun := mul_eq_mul_of_qC f g₂ f₂ g (add_comm k₂ k) hqc
  have hsl := al_mul_eq γ hγ hγℓ f g₂ f₂ g (add_comm k₂ k) hfun
  have hqs : qC (alForm γ hγ hγℓ f) * qC (alForm γ hγ hγℓ g₂) =
      qC (alForm γ hγ hγℓ f₂) * qC (alForm γ hγ hγℓ g) := by
    rw [← qC_mul, ← qC_mul, hsl]
  have hne := qC_alForm_ne_zero hq hg₂ hg₂0
  apply mul_right_cancel₀ hne
  calc ιC y * qC (alForm γ hγ hγℓ g) * qC (alForm γ hγ hγℓ g₂)
      = ιC y * qC (alForm γ hγ hγℓ g₂) * qC (alForm γ hγ hγℓ g) := by ring
    _ = qC (alForm γ hγ hγℓ f₂) * qC (alForm γ hγ hγℓ g) := by rw [hy]
    _ = qC (alForm γ hγ hγℓ f) * qC (alForm γ hγ hγℓ g₂) := hqs.symm

theorem IsImg.unique (hq : QuasiInv H γ hγ hγℓ γ' hγ' hγ'ℓ) {x y y' : LaurentSeries ℚ}
    (h : IsImg H γ hγ hγℓ x y) (h' : IsImg H γ hγ hγℓ x y') : y = y' := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, hx, hy'⟩ := h'
  have hy := h.apply_rep hq f g pf pg hf hg hg0 hx
  rw [← hy'] at hy
  exact ιC_injective (mul_right_cancel₀ (qC_alForm_ne_zero hq hg hg0) hy)

omit [NeZero ℓ] in
theorem isIntegralQExp_mul' {k₁ k₂ : ℤ} {f : ModularForm (Γt M H ℓ) k₁} {g : ModularForm (Γt M H ℓ) k₂}
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) :
    IsIntegralQExp (f.mul g) (pf * pg) := by
  rw [IsIntegralQExp, map_mul, hf, hg, ModularForm.coe_mul]
  exact (ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_top f g).symm

theorem IsImg.mul {x₁ y₁ x₂ y₂ : LaurentSeries ℚ} (h₁ : IsImg H γ hγ hγℓ x₁ y₁)
    (h₂ : IsImg H γ hγ hγℓ x₂ y₂) : IsImg H γ hγ hγℓ (x₁ * x₂) (y₁ * y₂) := by
  obtain ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, hg₁0, rfl, hy₁⟩ := h₁
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, rfl, hy₂⟩ := h₂
  refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, pf₁ * pf₂, pg₁ * pg₂, isIntegralQExp_mul' hf₁ hf₂,
    isIntegralQExp_mul' hg₁ hg₂, ?_, ?_, ?_⟩
  · rw [intSeriesC_mul]; exact mul_ne_zero hg₁0 hg₂0
  · rw [intSeriesC_mul, intSeriesC_mul, div_mul_div_comm]
  · rw [alForm_mul_apply, alForm_mul_apply, qC_mul, qC_mul, map_mul, ← hy₁, ← hy₂]
    ring

theorem IsImg.add {x₁ y₁ x₂ y₂ : LaurentSeries ℚ} (h₁ : IsImg H γ hγ hγℓ x₁ y₁)
    (h₂ : IsImg H γ hγ hγℓ x₂ y₂) : IsImg H γ hγ hγℓ (x₁ + x₂) (y₁ + y₂) := by
  obtain ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, hg₁0, rfl, hy₁⟩ := h₁
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, rfl, hy₂⟩ := h₂
  refine ⟨k₁ + k₂, f₁.mul g₂ + (g₁.mul f₂), g₁.mul g₂, pf₁ * pg₂ + pg₁ * pf₂, pg₁ * pg₂,
    ?_, isIntegralQExp_mul' hg₁ hg₂, ?_, ?_, ?_⟩
  · rw [IsIntegralQExp, map_add, map_mul, map_mul, hf₁, hf₂, hg₁, hg₂, ModularForm.coe_add,
      ModularForm.qExpansion_add one_pos one_mem_strictPeriods_top, ModularForm.coe_mul, ModularForm.coe_mul,
      ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_top,
      ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_top]
  · rw [intSeriesC_mul]; exact mul_ne_zero hg₁0 hg₂0
  · rw [intSeriesC_add', intSeriesC_mul, intSeriesC_mul, intSeriesC_mul, div_add_div _ _ hg₁0 hg₂0]
  · rw [alForm_add, ModularForm.coe_add, qC_add, alForm_mul_apply, alForm_mul_apply,
      alForm_mul_apply, qC_mul, qC_mul, qC_mul, map_add, ← hy₁, ← hy₂]
    ring

theorem IsImg.neg {x y : LaurentSeries ℚ} (h : IsImg H γ hγ hγℓ x y) : IsImg H γ hγ hγℓ (-x) (-y) := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl, hy⟩ := h
  refine ⟨k, -f, g, -pf, pg, ?_, hg, hg0, ?_, ?_⟩
  · rw [IsIntegralQExp, map_neg, hf, ModularForm.coe_neg]
    exact (ModularForm.qExpansion_neg one_pos one_mem_strictPeriods_top f).symm
  · rw [intSeriesC_neg', neg_div]
  · rw [alForm_neg, qC_neg, map_neg, ← hy]
    ring

omit [NeZero ℓ] in
theorem isIntegralQExp_one' :
    IsIntegralQExp ((1 : ModularForm (Γt M H ℓ) 0) : ℍ → ℂ) 1 := by
  rw [ModularForm.one_coe_eq_one]; exact isIntegralQExp_one

theorem IsImg.one : IsImg H γ hγ hγℓ 1 1 := by
  refine ⟨0, 1, 1, 1, 1, isIntegralQExp_one', isIntegralQExp_one', by simp, by simp, ?_⟩
  rw [map_one, one_mul, alForm_one]

theorem IsImg.zero : IsImg H γ hγ hγℓ 0 0 := by
  refine ⟨0, 0, 1, 0, 1, ?_, isIntegralQExp_one', by simp, by simp, ?_⟩
  · rw [ModularForm.coe_zero]; exact isIntegralQExp_zero
  · rw [map_zero, zero_mul, alForm_zero, ModularForm.coe_zero, qC_zero]

theorem IsImg.symm (hq : QuasiInv H γ hγ hγℓ γ' hγ' hγ'ℓ) {x y : LaurentSeries ℚ}
    (h : IsImg H γ hγ hγℓ x y) (hyS : y ∈ S M H ℓ) : IsImg H γ' hγ' hγ'ℓ y x := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, hx, hy⟩ := h
  obtain ⟨kP, P, Q, pP, pQ, hP, hQ, hQ0, rfl⟩ := hyS
  refine ⟨kP, P, Q, pP, pQ, hP, hQ, hQ0, rfl, ?_⟩
  have hQ' : qC Q ≠ 0 := qC_ιC_ne_zero hQ hQ0
  have h1 : qC P * qC (alForm γ hγ hγℓ g) = qC (alForm γ hγ hγℓ f) * qC Q := by
    rw [← hy, map_div₀, ιC_intSeriesC hP, ιC_intSeriesC hQ, div_mul_eq_mul_div, div_mul_cancel₀ _ hQ']
  have hfun := mul_eq_mul_of_qC P (alForm γ hγ hγℓ g) (alForm γ hγ hγℓ f) Q (add_comm k kP) h1
  have hsl := al_mul_eq γ' hγ' hγ'ℓ P (alForm γ hγ hγℓ g) (alForm γ hγ hγℓ f) Q (add_comm k kP) hfun
  rw [hq k g, hq k f] at hsl
  have hc : ((ℓ : ℂ) ^ k)⁻¹ ≠ 0 := inv_ne_zero (zpow_ne_zero _ (by exact_mod_cast NeZero.ne ℓ))
  have hsl' : (⇑(alForm γ' hγ' hγ'ℓ P) * ⇑g : ℍ → ℂ) = ⇑f * ⇑(alForm γ' hγ' hγ'ℓ Q) := by
    funext τ
    have := congrFun hsl τ
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    apply mul_left_cancel₀ hc
    linear_combination this
  have hqq : qC (alForm γ' hγ' hγ'ℓ P) * qC g = qC f * qC (alForm γ' hγ' hγ'ℓ Q) := by
    rw [← qC_mul, ← qC_mul, hsl']
  rw [hx, map_div₀, ιC_intSeriesC hf, ιC_intSeriesC hg]
  have hg' : qC g ≠ 0 := qC_ιC_ne_zero hg hg0
  rw [div_mul_eq_mul_div, div_eq_iff hg']
  exact hqq.symm

variable (H γ hγ hγℓ) in

def ALRational : Prop :=
  ∀ (k : ℤ) (f : ModularForm (Γt M H ℓ) k) (pf : PowerSeries ℤ), Even k → IsIntegralQExp f pf →
    ∃ D : ℤ, D ≠ 0 ∧ ∃ p : PowerSeries ℤ, IsIntegralQExp ((D : ℂ) • ⇑(alForm γ hγ hγℓ f)) p

omit [NeZero ℓ] in

theorem isIntegralQExp_smul_smul {k : ℤ} (F : ModularForm (Γt M H ℓ) k) {D : ℤ} (E : ℤ)
    {p : PowerSeries ℤ} (hp : IsIntegralQExp ((D : ℂ) • ⇑F) p) :
    IsIntegralQExp (⇑(((E : ℂ) * D) • F)) (PowerSeries.C E * p) := by
  rw [IsIntegralQExp] at hp ⊢
  rw [map_mul, PowerSeries.map_C, hp, ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_top _ F,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_top _ F, PowerSeries.smul_eq_C_mul,
    PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul, eq_intCast]

omit [NeZero ℓ] in
theorem ιC_intSeriesC_smul {k : ℤ} {F : ModularForm (Γt M H ℓ) k} {D : ℤ} {p : PowerSeries ℤ}
    (hp : IsIntegralQExp ((D : ℂ) • ⇑F) p) : ιC (intSeriesC ℚ p) = HahnSeries.C (D : ℂ) * qC F := by
  rw [ιC_intSeriesC hp, qC_smul]

theorem exists_isImg (hq : QuasiInv H γ hγ hγℓ γ' hγ' hγ'ℓ) (hW : ALRational H γ hγ hγℓ)
    {x : LaurentSeries ℚ} (hx : x ∈ S M H ℓ) : ∃ y ∈ S M H ℓ, IsImg H γ hγ hγℓ x y := by
  obtain ⟨k, f, g, pf, pg, hk, hf, hg, hg0, rfl⟩ := exists_even_rep hx
  obtain ⟨Df, hDf, pf', hpf'⟩ := hW k f pf hk hf
  obtain ⟨Dg, hDg, pg', hpg'⟩ := hW k g pg hk hg
  have hF' := isIntegralQExp_smul_smul (alForm γ hγ hγℓ f) Dg hpf'
  have hG' := isIntegralQExp_smul_smul (alForm γ hγ hγℓ g) Df hpg'
  have hv : qC (alForm γ hγ hγℓ g) ≠ 0 := qC_alForm_ne_zero hq hg hg0
  have hDf' : (HahnSeries.C (Df : ℂ) : LaurentSeries ℂ) ≠ 0 :=
    (map_ne_zero_iff _ HahnSeries.C_injective).mpr (by exact_mod_cast hDf)
  have hDg' : (HahnSeries.C (Dg : ℂ) : LaurentSeries ℂ) ≠ 0 :=
    (map_ne_zero_iff _ HahnSeries.C_injective).mpr (by exact_mod_cast hDg)
  have hG'0 : intSeriesC ℚ (PowerSeries.C Df * pg') ≠ 0 := by
    intro h0
    have := congrArg ιC h0
    rw [intSeriesC_C_mul, map_mul, map_zero, ιC_intSeriesC_smul hpg', ιC_C] at this
    push_cast at this
    exact (mul_ne_zero hDf' (mul_ne_zero hDg' hv)) this
  refine ⟨_, ⟨k, _, _, _, _, hF', hG', hG'0, rfl⟩, k, f, g, pf, pg, hf, hg, hg0, rfl, ?_⟩
  rw [map_div₀, intSeriesC_C_mul, intSeriesC_C_mul, map_mul, map_mul, ιC_intSeriesC_smul hpf',
    ιC_intSeriesC_smul hpg', ιC_C, ιC_C]
  push_cast
  field_simp

variable (hq : QuasiInv H γ hγ hγℓ γ' hγ' hγ'ℓ) (hW : ALRational H γ hγ hγℓ)

def σfun (x : xHTopFunctionFieldC ℚ M H (M * ℓ)) : xHTopFunctionFieldC ℚ M H (M * ℓ) :=
  ⟨Classical.choose (exists_isImg hq hW (mem_S_of_mem x.2)),
    intFormRatiosC_subset ℚ _ (Classical.choose_spec (exists_isImg hq hW (mem_S_of_mem x.2))).1⟩

theorem isImg_σfun (x : xHTopFunctionFieldC ℚ M H (M * ℓ)) :
    IsImg H γ hγ hγℓ (x : LaurentSeries ℚ) (σfun hq hW x) :=
  (Classical.choose_spec (exists_isImg hq hW (mem_S_of_mem x.2))).2

def σHom : xHTopFunctionFieldC ℚ M H (M * ℓ) →+* xHTopFunctionFieldC ℚ M H (M * ℓ) where
  toFun := σfun hq hW
  map_one' := Subtype.ext ((isImg_σfun hq hW 1).unique hq IsImg.one)
  map_mul' x y := Subtype.ext
    ((isImg_σfun hq hW (x * y)).unique hq ((isImg_σfun hq hW x).mul (isImg_σfun hq hW y)))
  map_zero' := Subtype.ext ((isImg_σfun hq hW 0).unique hq IsImg.zero)
  map_add' x y := Subtype.ext
    ((isImg_σfun hq hW (x + y)).unique hq ((isImg_σfun hq hW x).add (isImg_σfun hq hW y)))

theorem isImg_σHom (x : xHTopFunctionFieldC ℚ M H (M * ℓ)) :
    IsImg H γ hγ hγℓ (x : LaurentSeries ℚ) (σHom hq hW x) :=
  isImg_σfun hq hW x

variable (hq' : QuasiInv H γ' hγ' hγ'ℓ γ hγ hγℓ) (hW' : ALRational H γ' hγ' hγ'ℓ)

theorem σHom_inv_apply (x : xHTopFunctionFieldC ℚ M H (M * ℓ)) :
    σHom hq' hW' (σHom hq hW x) = x := by
  apply Subtype.ext
  refine (isImg_σHom hq' hW' (σHom hq hW x)).unique hq' ?_
  exact (isImg_σHom hq hW x).symm hq (mem_S_of_mem (σHom hq hW x).2)

def σAlgEquiv : xHTopFunctionFieldC ℚ M H (M * ℓ) ≃ₐ[ℚ] xHTopFunctionFieldC ℚ M H (M * ℓ) :=
  AlgEquiv.ofRingEquiv (f :=
    { σHom hq hW with
      invFun := σHom hq' hW'
      left_inv := σHom_inv_apply hq hW hq' hW'
      right_inv := σHom_inv_apply hq' hW' hq hW }) fun c => by
    have := RingHom.ext_rat ((σHom hq hW).comp (algebraMap ℚ (xHTopFunctionFieldC ℚ M H (M * ℓ))))
      (algebraMap ℚ (xHTopFunctionFieldC ℚ M H (M * ℓ)))
    exact congrFun (congrArg DFunLike.coe this) c

theorem σAlgEquiv_apply (x : xHTopFunctionFieldC ℚ M H (M * ℓ)) :
    σAlgEquiv hq hW hq' hW' x = σHom hq hW x := rfl

theorem isImg_σAlgEquiv (x : xHTopFunctionFieldC ℚ M H (M * ℓ)) :
    IsImg H γ hγ hγℓ (x : LaurentSeries ℚ) (σAlgEquiv hq hW hq' hW' x) :=
  isImg_σfun hq hW x

end Img
p2m_reactivate "P2MW.S_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar.WFieldH.ALData"

section Inputs

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ} [NeZero ℓ] (d : ALData M ℓ)

omit [NeZero M] in
theorem quasiInv_γ₁ : QuasiInv H d.γ₁ d.γ₁_mem_Gamma0 d.dvd_γ₁ d.γ₁' d.γ₁'_mem_Gamma0 d.dvd_γ₁' :=
  fun _ f => alForm_γ₁'_alForm_γ₁ d f

omit [NeZero M] in
theorem quasiInv_γ₁' : QuasiInv H d.γ₁' d.γ₁'_mem_Gamma0 d.dvd_γ₁' d.γ₁ d.γ₁_mem_Gamma0 d.dvd_γ₁ :=
  fun _ f => alForm_γ₁_alForm_γ₁' d f

omit [NeZero M] [NeZero ℓ] in
theorem Γ₁t_le : ((Gamma1 M ⊓ Gamma0 (M * ℓ) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ Γt M H ℓ :=
  Subgroup.map_mono (inf_le_inf_right _ (Gamma1_le_GammaH M H))

theorem alRational (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1) :
    ALRational H γ hγ hγℓ := by
  intro k f pf hk hf
  obtain ⟨D, p₁, hD, hp₁⟩ :=
    ModularCurve.exists_isIntegralQExp_smul_atkinLehnerSlash_of_even M ℓ hk (restrictForm Γ₁t_le f) hf γ hγ hγℓ
  refine ⟨D, hD, p₁, ?_⟩
  rw [coe_alForm]
  exact hp₁

def σ₀ : xHTopFunctionFieldC ℚ M H (M * ℓ) ≃ₐ[ℚ] xHTopFunctionFieldC ℚ M H (M * ℓ) :=
  σAlgEquiv (quasiInv_γ₁ d) (alRational d.γ₁ d.γ₁_mem_Gamma0 d.dvd_γ₁)
    (quasiInv_γ₁' d) (alRational d.γ₁' d.γ₁'_mem_Gamma0 d.dvd_γ₁')

theorem isImg_σ₀ (x : xHTopFunctionFieldC ℚ M H (M * ℓ)) :
    IsImg H d.γ₁ d.γ₁_mem_Gamma0 d.dvd_γ₁ (x : LaurentSeries ℚ) (σ₀ d x) :=
  isImg_σAlgEquiv _ _ _ _ x

theorem σ₀_spec {x : xHTopFunctionFieldC ℚ M H (M * ℓ)} {k : ℤ} (f g : ModularForm (Γt M H ℓ) k)
    (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) (hx : (x : LaurentSeries ℚ) = intSeriesC ℚ pf / intSeriesC ℚ pg) :
    ιC (σ₀ d x : LaurentSeries ℚ) * qC (alForm d.γ₁ d.γ₁_mem_Gamma0 d.dvd_γ₁ g) =
      qC (alForm d.γ₁ d.γ₁_mem_Gamma0 d.dvd_γ₁ f) :=
  (isImg_σ₀ d x).apply_rep (quasiInv_γ₁ d) f g pf pg hf hg hg0 hx

end Inputs
p2m_reactivate "P2MW.S_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar.WFieldH.ALData"

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
p2m_reactivate "P2MW.S_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar.WFieldH.ALData"

section Main

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ} [NeZero ℓ] (d : ALData M ℓ)

local notation "L" => AlgebraicClosure ℚ

theorem σ₀_apply_bot {k : ℤ} (f g : ModularForm (Γb M H) k) (pf pg : PowerSeries ℤ)
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0)
    (hzt : intSeriesC ℚ pf / intSeriesC ℚ pg ∈ xHTopFunctionFieldC ℚ M H (M * ℓ)) :
    ((σ₀ d ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, hzt⟩ : xHTopFunctionFieldC ℚ M H (M * ℓ)) :
        LaurentSeries ℚ) = qExpand ℚ ℓ (intSeriesC ℚ pf / intSeriesC ℚ pg) := by
  have key := σ₀_spec d (x := ⟨_, hzt⟩) (restrictForm Γt_le_Γb f) (restrictForm Γt_le_Γb g) pf pg
    hf hg hg0 rfl
  rw [alForm_γ₁_restrict, alForm_γ₁_restrict, qC_levelRaise, qC_levelRaise, ← ιC_intSeriesC hf,
    ← ιC_intSeriesC hg, ← coeffMap_qExpand, ← coeffMap_qExpand, ← map_mul] at key
  have key' := ιC_injective key
  have hne : qExpand ℚ ℓ (intSeriesC ℚ pg) ≠ 0 := fun h => hg0 (qExpand_injective ℓ (by rw [h, map_zero]))
  rw [map_div₀, eq_div_iff hne]
  exact key'

theorem σ₀_apply_levelRaise {k : ℤ} (f g : ModularForm (Γb M H) k) (pf pg : PowerSeries ℤ)
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0)
    (hzt : qExpand ℚ ℓ (intSeriesC ℚ pf / intSeriesC ℚ pg) ∈ xHTopFunctionFieldC ℚ M H (M * ℓ)) :
    ιC ((σ₀ d ⟨qExpand ℚ ℓ (intSeriesC ℚ pf / intSeriesC ℚ pg), hzt⟩ : xHTopFunctionFieldC ℚ M H (M * ℓ)) :
        LaurentSeries ℚ) * qC (⇑g ∣[k] d.γ₄) = qC (⇑f ∣[k] d.γ₄) := by
  have hℓ : ((ℓ : ℂ) ^ k)⁻¹ ≠ 0 := inv_ne_zero (zpow_ne_zero _ (by exact_mod_cast NeZero.ne ℓ))
  have hg0' : intSeriesC ℚ (expandPS ℓ pg) ≠ 0 := by
    rw [intSeriesC_expandPS]
    exact fun h => hg0 (qExpand_injective ℓ (by rw [h, map_zero]))
  have key := σ₀_spec d (x := ⟨_, hzt⟩) (levelRaise f) (levelRaise g) (expandPS ℓ pf) (expandPS ℓ pg)
    (isIntegralQExp_levelRaise hf) (isIntegralQExp_levelRaise hg) hg0'
    (by rw [intSeriesC_expandPS, intSeriesC_expandPS, ← map_div₀])

  set F' := alForm d.γ₁ d.γ₁_mem_Gamma0 d.dvd_γ₁ (levelRaise (ℓ := ℓ) f) with hF'
  set G' := alForm d.γ₁ d.γ₁_mem_Gamma0 d.dvd_γ₁ (levelRaise (ℓ := ℓ) g) with hG'
  have hf4 : (⇑f ∣[k] d.γ₄) = ((ℓ : ℂ) ^ k)⁻¹⁻¹ • ⇑F' := by
    rw [hF', alForm_γ₁_levelRaise, smul_smul, inv_mul_cancel₀ hℓ, one_smul]
  have hg4 : (⇑g ∣[k] d.γ₄) = ((ℓ : ℂ) ^ k)⁻¹⁻¹ • ⇑G' := by
    rw [hG', alForm_γ₁_levelRaise, smul_smul, inv_mul_cancel₀ hℓ, one_smul]
  rw [hf4, hg4, qC_smul, qC_smul, ← key]
  ring

end Main
p2m_reactivate "P2MW.S_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar.WFieldH.ALData"

section Transport

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} (hpM : p ∣ M)

omit [Fact p.Prime] [NeZero M] in
theorem gamma0_le_of_dvd' {N N' : ℕ} (h : N ∣ N') : Gamma0 N' ≤ Gamma0 N := fun γ hγ => by
  rw [Gamma0_mem] at hγ ⊢
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ((Int.natCast_dvd_natCast.mpr h).trans this)

omit [Fact p.Prime] [NeZero M] in
include hpM in

theorem unitsMap_gamma0Units {γ : SL(2, ℤ)} (hM : γ ∈ Gamma0 M) (hN : γ ∈ Gamma0 (M / p)) :
    ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) (CohCarrier.gamma0Units M ⟨γ, hM⟩) =
      CohCarrier.gamma0Units (M / p) ⟨γ, hN⟩ := by
  ext
  simp [CohCarrier.gamma0Units, Gamma0Map, ZMod.unitsMap]

omit [Fact p.Prime] [NeZero M] in
include hpM in

theorem gammaH_div_inf_gamma0_eq
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    CohCarrier.GammaH (M / p) (infSubgroup p M H hpM) ⊓ Gamma0 M = CohCarrier.GammaH M H := by
  ext γ
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hγN, hγM⟩
    obtain ⟨hN0, hNH⟩ := CohCarrier.mem_GammaH_iff.mp hγN
    obtain ⟨h, hh, hhu⟩ := (mem_infSubgroup_iff p M H hpM _).mp hNH
    rw [CohCarrier.mem_GammaH_iff]
    refine ⟨hγM, ?_⟩
    have key : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM)
        (CohCarrier.gamma0Units M ⟨γ, hγM⟩ * h⁻¹) = 1 := by
      rw [map_mul, map_inv, unitsMap_gamma0Units hpM hγM hN0, ← hhu, mul_inv_cancel]
    have := H.mul_mem (hHp _ key) hh
    simpa using this
  · intro hγ
    obtain ⟨hM0, hMH⟩ := CohCarrier.mem_GammaH_iff.mp hγ
    have hN0 : γ ∈ Gamma0 (M / p) := gamma0_le_of_dvd' (Nat.div_dvd_of_dvd hpM) hM0
    refine ⟨CohCarrier.mem_GammaH_iff.mpr ⟨hN0, ?_⟩, hM0⟩
    rw [← unitsMap_gamma0Units hpM hM0 hN0]
    exact unitsMap_mem_infSubgroup p M H hpM hMH

omit [Fact p.Prime] [NeZero M] in
include hpM in

theorem xHTopFunctionFieldC_div_eq
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p) =
      qExpFunctionFieldC ℚ (CohCarrier.GammaH M H) := by
  rw [xHTopFunctionFieldC, Nat.div_mul_cancel hpM, gammaH_div_inf_gamma0_eq hpM hHp]

omit [Fact p.Prime] [NeZero M] in
theorem exists_of_eq [NeZero p] [NeZero (M / p)] (d : ALData (M / p) p)
    (T : IntermediateField ℚ (LaurentSeries ℚ))
    (hT : xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p) = T) :
    ∃ σ : ↥T ≃ₐ[ℚ] ↥T,
      (∀ (f : ↥T) (u : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
          (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) →
            ((σ f : ↥T) : LaurentSeries ℚ) = qExpand ℚ p (u : LaurentSeries ℚ)) ∧
      (∀ (c : (ZMod (M / p))ˣ), (c : ZMod (M / p)) = (p : ZMod (M / p)) →
          ∀ (f : ↥T) (u : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
            (f : LaurentSeries ℚ) = qExpand ℚ p (u : LaurentSeries ℚ) →
              coeffEmb (AlgebraicClosure ℚ) ((σ f : ↥T) : LaurentSeries ℚ) =
                ((diamondAutHBar (M / p) (infSubgroup p M H hpM) c
                    ⟨coeffEmb (AlgebraicClosure ℚ) (u : LaurentSeries ℚ),
                      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) u.2⟩ :
                    ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
                  LaurentSeries (AlgebraicClosure ℚ))) := by
  subst hT
  refine ⟨σ₀ (H := infSubgroup p M H hpM) d, ?_, ?_⟩
  · intro f u hfu
    obtain ⟨k, f₁, g₁, pf, pg, hf, hg, hg0, hu⟩ :=
      mem_Sb_of_mem (M := M / p) (H := infSubgroup p M H hpM) u.2
    have hu2 : intSeriesC ℚ pf / intSeriesC ℚ pg ∈ xHFunctionField (M / p) (infSubgroup p M H hpM) := by
      rw [← hu]; exact u.2
    have hzt : intSeriesC ℚ pf / intSeriesC ℚ pg ∈
        xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p) :=
      xHFunctionFieldC_le_top ℚ (M / p) (infSubgroup p M H hpM) (M / p * p) hu2
    have key := σ₀_apply_bot (H := infSubgroup p M H hpM) d f₁ g₁ pf pg hf hg hg0 hzt
    have hef : f = ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, hzt⟩ := Subtype.ext (hfu.trans hu)
    rw [hef, key, hu]
  · intro c hc f u hfu
    obtain ⟨k, f₁, g₁, pf, pg, hf, hg, hg0, hu⟩ :=
      mem_Sb_of_mem (M := M / p) (H := infSubgroup p M H hpM) u.2
    have hzt : qExpand ℚ p (intSeriesC ℚ pf / intSeriesC ℚ pg) ∈
        xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p) := by
      rw [← hu, ← hfu]; exact f.2
    have hef : f = ⟨qExpand ℚ p (intSeriesC ℚ pf / intSeriesC ℚ pg), hzt⟩ :=
      Subtype.ext (hfu.trans (by rw [hu]))
    have hspec := σ₀_apply_levelRaise (H := infSubgroup p M H hpM) d f₁ g₁ pf pg hf hg hg0 hzt
    have hσ := (ModularCurve.heckeDiamondInputsHAll (M / p) (infSubgroup p M H hpM)).isDiamondAutHBar c
    obtain ⟨y', -, hy'σ, hy'⟩ := hσ k f₁ g₁ pf pg hf hg hg0 d.γ₄ d.γ₄_mem_Gamma0
      (by rw [hc]; exact d.γ₄_00_zmod)
    change ιC y' * qC (⇑g₁ ∣[k] d.γ₄) = qC (⇑f₁ ∣[k] d.γ₄) at hy'
    rw [← hspec] at hy'
    have hne : qC (⇑g₁ ∣[k] d.γ₄) ≠ 0 := by
      have hℓ : ((p : ℂ) ^ k)⁻¹ ≠ 0 := inv_ne_zero (zpow_ne_zero _ (by exact_mod_cast NeZero.ne p))
      have hg4 : (⇑g₁ ∣[k] d.γ₄) =
          ((p : ℂ) ^ k)⁻¹⁻¹ • ⇑(alForm d.γ₁ d.γ₁_mem_Gamma0 d.dvd_γ₁ (levelRaise (ℓ := p) g₁)) := by
        rw [alForm_γ₁_levelRaise, smul_smul, inv_mul_cancel₀ hℓ, one_smul]
      have hg0' : intSeriesC ℚ (expandPS p pg) ≠ 0 := by
        rw [intSeriesC_expandPS]
        exact fun h => hg0 (qExpand_injective p (by rw [h, map_zero]))
      rw [hg4, qC_smul]
      exact mul_ne_zero ((map_ne_zero_iff _ HahnSeries.C_injective).mpr (inv_ne_zero hℓ))
        (qC_alForm_ne_zero (quasiInv_γ₁ d) (isIntegralQExp_levelRaise hg) hg0')
    have heq : y' = ((σ₀ (H := infSubgroup p M H hpM) d ⟨_, hzt⟩ :
        xHTopFunctionFieldC ℚ (M / p) (infSubgroup p M H hpM) (M / p * p)) : LaurentSeries ℚ) :=
      ιC_injective (mul_right_cancel₀ hne hy')
    have hu' : ((diamondAutHBar (M / p) (infSubgroup p M H hpM) c
          ⟨coeffEmb (AlgebraicClosure ℚ) (u : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) u.2⟩ :
          ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) =
        coeffEmb (AlgebraicClosure ℚ) y' := by
      rw [← hy'σ]
      congr 2
      exact Subtype.ext (by simp only [hu])
    rw [hu', heq, hef]

end Transport
p2m_reactivate "P2MW.S_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar.WFieldH.ALData"

end WFieldH
p2m_reactivate "P2MW.S_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar.WFieldH.ALData P2MW.S_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar.WFieldH"

open ModularCurve WFieldH in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) :
    ∃ σ : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ≃ₐ[ℚ]
        ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)),
      (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        ∀ (f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
          (u : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
          (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) →
            ((σ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) =
              qExpand ℚ p (u : LaurentSeries ℚ)) ∧
      (haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
        ∀ (c : (ZMod (M / p))ˣ), (c : ZMod (M / p)) = (p : ZMod (M / p)) →
          ∀ (f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
            (u : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)))),
            (f : LaurentSeries ℚ) = qExpand ℚ p (u : LaurentSeries ℚ) →
              coeffEmb (AlgebraicClosure ℚ)
                  ((σ f : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries ℚ) =
                ((diamondAutHBar (M / p) (infSubgroup p M H hpM) c
                    ⟨coeffEmb (AlgebraicClosure ℚ) (u : LaurentSeries ℚ),
                      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) u.2⟩ :
                    ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
                  LaurentSeries (AlgebraicClosure ℚ))) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero (M / p) := ModularCurve.neZero_div p M hpM
  have hcop : Nat.Coprime p (M / p) := by
    rw [Nat.Prime.coprime_iff_not_dvd Fact.out]
    rintro ⟨t, ht⟩
    apply hpM2
    refine ⟨t, ?_⟩
    calc M = M / p * p := (Nat.div_mul_cancel hpM).symm
      _ = p ^ 2 * t := by rw [ht]; ring
  obtain ⟨d⟩ := nonempty_alData (M := M / p) (ℓ := p) hcop
  exact exists_of_eq hpM d _ (xHTopFunctionFieldC_div_eq hpM hHp)

end
end S_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar
end P2MW
export P2MW.S_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar (solution)
