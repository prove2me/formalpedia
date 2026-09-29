-- Prove2me | solution 1 for ModularCurve.exists_algEquiv_laurentBaseChange_xHTopFunctionFieldC_coe_eq_qExpand_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/54823260-3f29-5033-8e80-a2b2e2e0236b

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_smul_atkinLehnerSlash_of_even
import Theorems.Thm_ModularCurve_exists_algEquiv_laurentBaseChange_cover
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_algEquiv_laurentBaseChange_xHTopFunctionFieldC_coe_eq_qExpand_of_coprime

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm Pointwise

namespace ALGenT

open UpperHalfPlane CongruenceSubgroup ModularCurve Matrix IntermediateField HahnSeries

section Group

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {t : ℕ}

abbrev ΓtSL (M : ℕ) (H : Subgroup (ZMod M)ˣ) (t : ℕ) : Subgroup SL(2, ℤ) :=
  CohCarrier.GammaH M H ⊓ Gamma0 (M * t)

abbrev Γt (M : ℕ) (H : Subgroup (ZMod M)ˣ) (t : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  ((ΓtSL M H t : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

abbrev Γb (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Subgroup (GL (Fin 2) ℝ) :=
  ((CohCarrier.GammaH M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem T_mem_top : ModularGroup.T ∈ ΓtSL M H t := by
  refine Subgroup.mem_inf.mpr ⟨translation_mem_GammaH M H, ?_⟩
  rw [Gamma0_mem]
  simp [ModularGroup.T]

theorem one_mem_strictPeriods_top : (1 : ℝ) ∈ (Γt M H t).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem T_mem_top]
  exact AddSubgroup.mem_zmultiples _

theorem one_mem_strictPeriods_bot : (1 : ℝ) ∈ (Γb M H).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (translation_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples _

scoped instance [NeZero M] : (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)

scoped instance [NeZero M] [NeZero t] : (ΓtSL M H t).FiniteIndex := by
  haveI : NeZero (M * t) := NeZero.mul
  refine Subgroup.finiteIndex_of_le (H := Gamma1 (M * t)) (le_inf ?_ (Gamma1_in_Gamma0 _))
  exact (Gamma1_le_of_dvd (dvd_mul_right M t)).trans (Gamma1_le_GammaH M H)

theorem top_le_bot : ΓtSL M H t ≤ CohCarrier.GammaH M H := inf_le_left

theorem Γt_le_Γb : Γt M H t ≤ Γb M H := Subgroup.map_mono top_le_bot

def conjMat (t : ℕ) (δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![δ 0 0, (t : ℤ) * δ 0 1; δ 1 0 / t, δ 1 1]

theorem det_conjMat (δ : SL(2, ℤ)) (h : (t : ℤ) ∣ δ 1 0) : (conjMat t δ).det = 1 := by
  obtain ⟨c, hc⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet ⊢
  rcases eq_or_ne (t : ℤ) 0 with h0 | h0
  · simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, hc, h0, zero_mul, Int.zero_ediv,
      mul_zero, sub_zero] at hdet ⊢
    linear_combination hdet
  · have h1 : (t : ℤ) * c / t = c := by rw [mul_comm]; exact Int.mul_ediv_cancel c h0
    simp only [conjMat, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, hc, h1] at hdet ⊢
    linear_combination hdet

def conjSL (δ : SL(2, ℤ)) (h : (t : ℤ) ∣ δ 1 0) : SL(2, ℤ) := ⟨conjMat t δ, det_conjMat δ h⟩

@[scoped simp] theorem conjSL_apply_00 (δ : SL(2, ℤ)) (h : (t : ℤ) ∣ δ 1 0) : conjSL δ h 0 0 = δ 0 0 := rfl
@[scoped simp] theorem conjSL_apply_01 (δ : SL(2, ℤ)) (h : (t : ℤ) ∣ δ 1 0) :
    conjSL δ h 0 1 = (t : ℤ) * δ 0 1 := rfl
@[scoped simp] theorem conjSL_apply_10 (δ : SL(2, ℤ)) (h : (t : ℤ) ∣ δ 1 0) :
    conjSL δ h 1 0 = δ 1 0 / t := rfl
@[scoped simp] theorem conjSL_apply_11 (δ : SL(2, ℤ)) (h : (t : ℤ) ∣ δ 1 0) : conjSL δ h 1 1 = δ 1 1 := rfl

theorem dvd_of_mem_Gamma0_mul {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 (M * t)) : (t : ℤ) ∣ δ 1 0 := by
  rw [Gamma0_mem] at hδ
  have : ((M * t : ℕ) : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hδ
  exact (show (t : ℤ) ∣ ((M * t : ℕ) : ℤ) from ⟨M, by push_cast; ring⟩).trans this

theorem conjSL_mem_Gamma0 {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 (M * t)) (ht : t ≠ 0) :
    conjSL δ (dvd_of_mem_Gamma0_mul hδ) ∈ Gamma0 M := by
  rw [Gamma0_mem]
  have hd : ((M * t : ℕ) : ℤ) ∣ δ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hδ)
  obtain ⟨c, hc⟩ := hd
  have ht' : (t : ℤ) ≠ 0 := by exact_mod_cast ht
  have : (conjSL δ (dvd_of_mem_Gamma0_mul hδ)) 1 0 = M * c := by
    show δ 1 0 / t = M * c
    rw [hc]; push_cast
    rw [show (M : ℤ) * t * c = t * (M * c) by ring]
    exact Int.mul_ediv_cancel_left _ ht'
  rw [this]; push_cast
  simp

theorem conjSL_apply_10_eq {δ : SL(2, ℤ)} (hδ : δ ∈ Gamma0 (M * t)) (ht : t ≠ 0) :
    ∃ c : ℤ, (conjSL δ (dvd_of_mem_Gamma0_mul hδ)) 1 0 = M * c := by
  have hd : ((M * t : ℕ) : ℤ) ∣ δ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hδ)
  obtain ⟨c, hc⟩ := hd
  have ht' : (t : ℤ) ≠ 0 := by exact_mod_cast ht
  refine ⟨c, ?_⟩
  show δ 1 0 / t = M * c
  rw [hc]; push_cast
  rw [show (M : ℤ) * t * c = t * (M * c) by ring]
  exact Int.mul_ediv_cancel_left _ ht'

theorem conjSL_mem_GammaH {δ : SL(2, ℤ)} (hδH : δ ∈ CohCarrier.GammaH M H)
    (hδ : δ ∈ Gamma0 (M * t)) (ht : t ≠ 0) :
    conjSL δ (dvd_of_mem_Gamma0_mul hδ) ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff] at hδH ⊢
  obtain ⟨hδ0, hH⟩ := hδH
  refine ⟨conjSL_mem_Gamma0 hδ ht, ?_⟩
  convert hH using 1
  rfl

theorem heckeDiag_mul_mul_inv {δ : SL(2, ℤ)} (h : (t : ℤ) ∣ δ 1 0) (ht : t ≠ 0) :
    ModularForm.heckeDiagMatrix t * Matrix.SpecialLinearGroup.mapGL ℝ δ *
        (ModularForm.heckeDiagMatrix t)⁻¹ =
      Matrix.SpecialLinearGroup.mapGL ℝ (conjSL δ h) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  obtain ⟨c, hc⟩ := h
  have ht' : (t : ℤ) ≠ 0 := by exact_mod_cast ht
  have h10 : (conjSL δ ⟨c, hc⟩ : SL(2, ℤ)) 1 0 = c := by
    show δ 1 0 / t = c
    rw [hc]; exact Int.mul_ediv_cancel_left _ ht'
  simp only [Matrix.GeneralLinearGroup.coe_mul, ModularForm.val_heckeDiagMatrix ht]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, hc] <;> ring

theorem conj_apply_10 (γ z : SL(2, ℤ)) :
    (γ * z * γ⁻¹) 1 0 = γ 1 0 * z 0 0 * γ 1 1 + γ 1 1 * z 1 0 * γ 1 1
      - γ 1 0 * z 0 1 * γ 1 0 - γ 1 1 * z 1 1 * γ 1 0 := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl γ]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

variable (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγt : (t : ℤ) ∣ γ 1 1)

abbrev alGL (γ : SL(2, ℤ)) (t : ℕ) : GL (Fin 2) ℝ :=
  Matrix.SpecialLinearGroup.mapGL ℝ γ * ModularForm.heckeDiagMatrix t

include hγ hγt in

theorem alConj_mem {δ : SL(2, ℤ)} (hδH : δ ∈ CohCarrier.GammaH M H) (hδ : δ ∈ Gamma0 (M * t))
    (ht : t ≠ 0) : γ * conjSL δ (dvd_of_mem_Gamma0_mul hδ) * γ⁻¹ ∈ ΓtSL M H t := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact CohCarrier.conj_mem_GammaH M H ⟨γ, hγ⟩ ⟨_, conjSL_mem_GammaH hδH hδ ht⟩
  · rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, conj_apply_10]
    obtain ⟨r, hr⟩ : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
    obtain ⟨s, hs⟩ := hγt
    obtain ⟨c, hc⟩ := conjSL_apply_10_eq (M := M) hδ ht
    rw [hc, conjSL_apply_00, conjSL_apply_01, conjSL_apply_11, hr, hs]
    exact ⟨r * δ 0 0 * s + s * c * t * s - r * δ 0 1 * M * r - s * δ 1 1 * r, by push_cast; ring⟩

include hγ hγt in

theorem le_conj_al (ht : t ≠ 0) :
    Γt M H t ≤ ConjAct.toConjAct (alGL γ t)⁻¹ • Γt M H t := by
  rintro x ⟨δ, hδ, rfl⟩
  obtain ⟨hδH, hδ0⟩ := Subgroup.mem_inf.mp hδ
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  refine ⟨_, alConj_mem γ hγ hγt hδH hδ0 ht, ?_⟩
  rw [map_mul, map_mul, map_inv, ← heckeDiag_mul_mul_inv (dvd_of_mem_Gamma0_mul hδ0) ht]
  simp only [alGL, _root_.mul_inv_rev, mul_assoc]

variable {k : ℤ} [NeZero t]

def alForm (f : ModularForm (Γt M H t) k) : ModularForm (Γt M H t) k :=
  ((t : ℂ) ^ (k - 1))⁻¹ •
    restrictForm (le_conj_al γ hγ hγt (NeZero.ne t)) (ModularForm.translate f (alGL γ t))

theorem alForm_apply (f : ModularForm (Γt M H t) k) (τ : ℍ) :
    alForm γ hγ hγt f τ = (⇑f ∣[k] γ) (ModularForm.heckeDiagMatrix t • τ) := by
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne t
  show ((t : ℂ) ^ (k - 1))⁻¹ • ((⇑f ∣[k] alGL γ t) τ) = _
  rw [alGL, SlashAction.slash_mul, ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne t),
    smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero _ ht), one_mul]
  rfl

theorem coe_alForm (f : ModularForm (Γt M H t) k) :
    ⇑(alForm γ hγ hγt f) = fun τ => (⇑f ∣[k] γ) (ModularForm.heckeDiagMatrix t • τ) :=
  funext (alForm_apply γ hγ hγt f)

theorem alForm_mul_apply {k₁ k₂ : ℤ} (f : ModularForm (Γt M H t) k₁) (g : ModularForm (Γt M H t) k₂) :
    ⇑(alForm γ hγ hγt (f.mul g)) = ⇑(alForm γ hγ hγt f) * ⇑(alForm γ hγ hγt g) := by
  funext τ
  simp only [coe_alForm, Pi.mul_apply, ModularForm.coe_mul, ModularForm.mul_slash_SL2]

theorem alForm_add (f g : ModularForm (Γt M H t) k) :
    alForm γ hγ hγt (f + g) = alForm γ hγ hγt f + alForm γ hγ hγt g := by
  ext τ
  simp only [alForm_apply, ModularForm.coe_add, SlashAction.add_slash, Pi.add_apply,
    ModularForm.add_apply]

theorem alForm_smul (c : ℂ) (f : ModularForm (Γt M H t) k) :
    ⇑(alForm γ hγ hγt (c • f)) = c • ⇑(alForm γ hγ hγt f) := by
  funext τ
  simp only [coe_alForm, ModularForm.IsGLPos.coe_smul, ModularForm.SL_smul_slash, Pi.smul_apply]

theorem alForm_neg (f : ModularForm (Γt M H t) k) :
    ⇑(alForm γ hγ hγt (-f)) = -⇑(alForm γ hγ hγt f) := by
  funext τ
  simp only [coe_alForm, ModularForm.coe_neg, SlashAction.neg_slash, Pi.neg_apply]

theorem alForm_zero : alForm γ hγ hγt (0 : ModularForm (Γt M H t) k) = 0 := by
  ext τ; simp [alForm_apply]

theorem alForm_one : alForm γ hγ hγt (1 : ModularForm (Γt M H t) 0) = 1 := by
  ext τ
  simp only [alForm_apply, ModularForm.one_coe_eq_one]
  rw [ModularForm.is_invariant_one γ]
  rfl

end Group

structure ALData (M t : ℕ) where

  y : ℤ

  w₀ : ℤ
  rel : (t : ℤ) * w₀ - M * y = 1

theorem nonempty_alData {M t : ℕ} (h : Nat.Coprime t M) : Nonempty (ALData M t) := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr h
  exact ⟨⟨-v, u, by linear_combination huv⟩⟩

namespace ALData

variable {M t : ℕ} (d : ALData M t)

def γ₁ : SL(2, ℤ) :=
  ⟨!![1, d.y; (M : ℤ), (t : ℤ) * d.w₀], by rw [Matrix.det_fin_two_of]; linear_combination d.rel⟩

def γ₁' : SL(2, ℤ) :=
  ⟨!![d.w₀, -d.y; -(M : ℤ), (t : ℤ)], by rw [Matrix.det_fin_two_of]; linear_combination d.rel⟩

@[scoped simp] theorem γ₁_00 : d.γ₁ 0 0 = 1 := rfl
@[scoped simp] theorem γ₁_01 : d.γ₁ 0 1 = d.y := rfl
@[scoped simp] theorem γ₁_10 : d.γ₁ 1 0 = M := rfl
@[scoped simp] theorem γ₁_11 : d.γ₁ 1 1 = (t : ℤ) * d.w₀ := rfl
@[scoped simp] theorem γ₁'_00 : d.γ₁' 0 0 = d.w₀ := rfl
@[scoped simp] theorem γ₁'_01 : d.γ₁' 0 1 = -d.y := rfl
@[scoped simp] theorem γ₁'_10 : d.γ₁' 1 0 = -(M : ℤ) := rfl
@[scoped simp] theorem γ₁'_11 : d.γ₁' 1 1 = t := rfl

theorem γ₁_mem_Gamma0 : d.γ₁ ∈ Gamma0 M := by rw [Gamma0_mem, γ₁_10]; simp
theorem γ₁'_mem_Gamma0 : d.γ₁' ∈ Gamma0 M := by rw [Gamma0_mem, γ₁'_10]; simp

theorem γ₁_mem_Gamma1 : d.γ₁ ∈ Gamma1 M := by
  rw [Gamma1_mem, γ₁_00, γ₁_11, γ₁_10]
  refine ⟨by simp, ?_, by simp⟩
  have := congrArg (Int.cast : ℤ → ZMod M) d.rel
  push_cast at this ⊢
  rw [ZMod.natCast_self, zero_mul, sub_zero] at this
  exact this

theorem dvd_γ₁ : (t : ℤ) ∣ d.γ₁ 1 1 := ⟨d.w₀, rfl⟩
theorem dvd_γ₁' : (t : ℤ) ∣ d.γ₁' 1 1 := ⟨1, by simp⟩

theorem rel_real : (t : ℝ) * d.w₀ - M * d.y = 1 := by exact_mod_cast d.rel

theorem alGL_γ₁_mul (ht : t ≠ 0) :
    alGL d.γ₁ t * alGL d.γ₁' t = ModularForm.heckeDiagMatrix t * ModularForm.heckeMatrix t 0 := by
  have hrel := d.rel_real
  apply Units.ext
  ext i j
  simp only [alGL, Units.val_mul, ModularForm.val_heckeDiagMatrix ht, ModularForm.val_heckeMatrix ht]
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, γ₁, γ₁']; linear_combination (t : ℝ) * hrel
  · simp [Matrix.mul_apply, Fin.sum_univ_two, γ₁, γ₁']; ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, γ₁, γ₁']; ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, γ₁, γ₁']; linear_combination (t : ℝ) * hrel

theorem alGL_γ₁'_mul (ht : t ≠ 0) :
    alGL d.γ₁' t * alGL d.γ₁ t = ModularForm.heckeDiagMatrix t * ModularForm.heckeMatrix t 0 := by
  have hrel := d.rel_real
  apply Units.ext
  ext i j
  simp only [alGL, Units.val_mul, ModularForm.val_heckeDiagMatrix ht, ModularForm.val_heckeMatrix ht]
  fin_cases i <;> fin_cases j
  · simp [Matrix.mul_apply, Fin.sum_univ_two, γ₁, γ₁']; linear_combination (t : ℝ) * hrel
  · simp [Matrix.mul_apply, Fin.sum_univ_two, γ₁, γ₁']; ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, γ₁, γ₁']; ring
  · simp [Matrix.mul_apply, Fin.sum_univ_two, γ₁, γ₁']; linear_combination (t : ℝ) * hrel

end ALData
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laurentBaseChange_xHTopFunctionFieldC_coe_eq_qExpand_of_coprime.ALGenT.ALData"

section Compose

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {t : ℕ} [NeZero t] {k : ℤ}

theorem heckeDiag_smul_heckeMatrix_smul (τ : ℍ) :
    ModularForm.heckeDiagMatrix t • (ModularForm.heckeMatrix t 0 • τ) = τ := by
  apply UpperHalfPlane.ext
  rw [ModularForm.coe_heckeDiagMatrix_smul (NeZero.ne t), ModularForm.coe_heckeMatrix_smul (NeZero.ne t) 0]
  have : (t : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne t
  field_simp
  push_cast
  ring

theorem slash_diag_diag (k : ℤ) (F : ℍ → ℂ) :
    F ∣[k] (ModularForm.heckeDiagMatrix t * ModularForm.heckeMatrix t 0) = ((t : ℂ) ^ (k - 2)) • F := by
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne t
  funext τ
  rw [SlashAction.slash_mul, ModularForm.slash_heckeMatrix_apply k (NeZero.ne t) 0,
    ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne t), heckeDiag_smul_heckeMatrix_smul,
    Pi.smul_apply, smul_eq_mul, show k - 2 = (k - 1) + (-1) by ring, zpow_add₀ ht, _root_.zpow_neg_one]
  ring

theorem real_smul_slash (k : ℤ) (r : ℝ) (F : ℍ → ℂ) (g : GL (Fin 2) ℝ) :
    ((r : ℂ) • F) ∣[k] g = (r : ℂ) • (F ∣[k] g) := by
  rw [ModularForm.smul_slash, UpperHalfPlane.σ_ofReal]

omit [NeZero t] in
theorem inv_pow_eq_real (k : ℤ) : ((t : ℂ) ^ (k - 1))⁻¹ = ((((t : ℝ) ^ (k - 1))⁻¹ : ℝ) : ℂ) := by
  push_cast; rfl

variable (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγt : (t : ℤ) ∣ γ 1 1)

theorem coe_alForm_eq_smul_slash (f : ModularForm (Γt M H t) k) :
    ⇑(alForm γ hγ hγt f) = ((t : ℂ) ^ (k - 1))⁻¹ • (⇑f ∣[k] alGL γ t) := by
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne t
  funext τ
  rw [alForm_apply, Pi.smul_apply, SlashAction.slash_mul,
    ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne t), smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (zpow_ne_zero _ ht), one_mul]
  rfl

theorem alForm_alForm_of_mul_eq (γ' : SL(2, ℤ)) (hγ' : γ' ∈ Gamma0 M) (hγ't : (t : ℤ) ∣ γ' 1 1)
    (hmul : alGL γ t * alGL γ' t = ModularForm.heckeDiagMatrix t * ModularForm.heckeMatrix t 0)
    (f : ModularForm (Γt M H t) k) :
    ⇑(alForm γ' hγ' hγ't (alForm γ hγ hγt f)) = ((t : ℂ) ^ k)⁻¹ • ⇑f := by
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne t
  rw [coe_alForm_eq_smul_slash, coe_alForm_eq_smul_slash, inv_pow_eq_real, real_smul_slash,
    ← SlashAction.slash_mul, hmul, slash_diag_diag, smul_smul, smul_smul, ← inv_pow_eq_real]
  congr 1
  rw [← _root_.zpow_neg, ← zpow_add₀ ht, ← zpow_add₀ ht, ← _root_.zpow_neg]
  congr 1; ring

variable (d : ALData M t)

theorem alForm_γ₁'_alForm_γ₁ (f : ModularForm (Γt M H t) k) :
    ⇑(alForm d.γ₁' d.γ₁'_mem_Gamma0 d.dvd_γ₁' (alForm d.γ₁ d.γ₁_mem_Gamma0 d.dvd_γ₁ f)) =
      ((t : ℂ) ^ k)⁻¹ • ⇑f :=
  alForm_alForm_of_mul_eq _ _ _ _ _ _ (d.alGL_γ₁_mul (NeZero.ne t)) f

theorem alForm_γ₁_alForm_γ₁' (f : ModularForm (Γt M H t) k) :
    ⇑(alForm d.γ₁ d.γ₁_mem_Gamma0 d.dvd_γ₁ (alForm d.γ₁' d.γ₁'_mem_Gamma0 d.dvd_γ₁' f)) =
      ((t : ℂ) ^ k)⁻¹ • ⇑f :=
  alForm_alForm_of_mul_eq _ _ _ _ _ _ (d.alGL_γ₁'_mul (NeZero.ne t)) f

theorem top_le_conj_bot :
    Γt M H t ≤ ConjAct.toConjAct (ModularForm.heckeDiagMatrix t)⁻¹ • Γb M H := by
  rintro x ⟨δ, hδ, rfl⟩
  obtain ⟨hδH, hδ0⟩ := Subgroup.mem_inf.mp hδ
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  exact ⟨_, conjSL_mem_GammaH hδH hδ0 (NeZero.ne t),
    (heckeDiag_mul_mul_inv (dvd_of_mem_Gamma0_mul hδ0) (NeZero.ne t)).symm⟩

def levelRaise (f : ModularForm (Γb M H) k) : ModularForm (Γt M H t) k :=
  ((t : ℂ) ^ (k - 1))⁻¹ •
    restrictForm top_le_conj_bot (ModularForm.translate f (ModularForm.heckeDiagMatrix t))

theorem levelRaise_apply (f : ModularForm (Γb M H) k) (τ : ℍ) :
    levelRaise (t := t) f τ = f (ModularForm.heckeDiagMatrix t • τ) := by
  have ht : (t : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne t
  show ((t : ℂ) ^ (k - 1))⁻¹ • ((⇑f ∣[k] ModularForm.heckeDiagMatrix t) τ) = _
  rw [ModularForm.slash_heckeDiagMatrix_apply k (NeZero.ne t), smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (zpow_ne_zero _ ht), one_mul]

theorem coe_levelRaise (f : ModularForm (Γb M H) k) :
    ⇑(levelRaise (t := t) f) = fun τ => f (ModularForm.heckeDiagMatrix t • τ) :=
  funext (levelRaise_apply f)

theorem coe_levelRaise_eq_smul_slash (f : ModularForm (Γb M H) k) :
    ⇑(levelRaise (t := t) f) = ((t : ℂ) ^ (k - 1))⁻¹ • (⇑f ∣[k] ModularForm.heckeDiagMatrix t) := rfl

theorem alForm_γ₁_restrict (f : ModularForm (Γb M H) k) :
    ⇑(alForm d.γ₁ d.γ₁_mem_Gamma0 d.dvd_γ₁ (restrictForm Γt_le_Γb f)) = ⇑(levelRaise (t := t) f) := by
  rw [coe_alForm, coe_levelRaise]
  have : (⇑(restrictForm Γt_le_Γb f : ModularForm (Γt M H t) k) ∣[k] d.γ₁) = ⇑f := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantFormClass.slash_action_eq f _
      (Subgroup.mem_map_of_mem _ (Gamma1_le_GammaH M H d.γ₁_mem_Gamma1))
  rw [this]

end Compose
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laurentBaseChange_xHTopFunctionFieldC_coe_eq_qExpand_of_coprime.ALGenT.ALData"

section QExp

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {t : ℕ}

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

theorem qC_mul {k₁ k₂ : ℤ} (f : ModularForm (Γt M H t) k₁) (g : ModularForm (Γt M H t) k₂) :
    qC (⇑f * ⇑g) = qC f * qC g := by
  rw [qC, qC, qC, ← map_mul, ← ModularForm.coe_mul,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_top]

theorem qC_add {k : ℤ} (f g : ModularForm (Γt M H t) k) : qC (⇑f + ⇑g) = qC f + qC g := by
  rw [qC, qC, qC, ← map_add, ModularForm.qExpansion_add one_pos one_mem_strictPeriods_top f g]

theorem qC_smul {k : ℤ} (c : ℂ) (f : ModularForm (Γt M H t) k) : qC (c • ⇑f) = HahnSeries.C c * qC f := by
  rw [qC, qC, ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_top c f,
    ← HahnSeries.ofPowerSeries_C, ← map_mul, PowerSeries.smul_eq_C_mul]

theorem qC_neg {k : ℤ} (f : ModularForm (Γt M H t) k) : qC (-⇑f) = -qC f := by
  rw [qC, qC, ModularForm.qExpansion_neg one_pos one_mem_strictPeriods_top f, map_neg]

theorem qC_eq_zero_iff {k : ℤ} (f : ModularForm (Γt M H t) k) : qC f = 0 ↔ f = 0 := by
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

theorem qC_ιC_ne_zero {k : ℤ} {g : ModularForm (Γt M H t) k} {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) : qC g ≠ 0 := by
  rw [← ιC_intSeriesC hg]
  exact (map_ne_zero_iff _ ιC_injective).mpr hg0

theorem ne_zero_of_intSeriesC_ne_zero {k : ℤ} {g : ModularForm (Γt M H t) k} {pg : PowerSeries ℤ}
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
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laurentBaseChange_xHTopFunctionFieldC_coe_eq_qExpand_of_coprime.ALGenT.ALData"

variable (M H t) in

abbrev S : Set (LaurentSeries ℚ) := intFormRatiosC ℚ (ΓtSL M H t)

theorem mem_S_of_mem {y : LaurentSeries ℚ} (hy : y ∈ xHTopFunctionFieldC ℚ M H (M * t)) : y ∈ S M H t :=
  mem_ratios_of_mem one_mem_strictPeriods_top hy

theorem mem_Sb_of_mem {y : LaurentSeries ℚ} (hy : y ∈ xHFunctionField M H) :
    y ∈ intFormRatiosC ℚ (CohCarrier.GammaH M H) :=
  mem_ratios_of_mem one_mem_strictPeriods_bot hy

theorem exists_even_rep {x : LaurentSeries ℚ} (hx : x ∈ S M H t) :
    ∃ (k : ℤ) (f g : ModularForm (Γt M H t) k) (pf pg : PowerSeries ℤ), Even k ∧
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

theorem mul_eq_mul_of_qC {k₁ k₂ k₃ k₄ : ℤ} (f₁ : ModularForm (Γt M H t) k₁) (f₂ : ModularForm (Γt M H t) k₂)
    (f₃ : ModularForm (Γt M H t) k₃) (f₄ : ModularForm (Γt M H t) k₄) (hk : k₃ + k₄ = k₁ + k₂)
    (h : qC f₁ * qC f₂ = qC f₃ * qC f₄) : (⇑f₁ * ⇑f₂ : ℍ → ℂ) = ⇑f₃ * ⇑f₄ := by
  set D : ModularForm (Γt M H t) (k₁ + k₂) := f₁.mul f₂ - ModularForm.mcast hk (f₃.mul f₄) with hD
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

variable [NeZero t] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγt : (t : ℤ) ∣ γ 1 1)

theorem al_mul_eq {k₁ k₂ k₃ k₄ : ℤ} (f₁ : ModularForm (Γt M H t) k₁) (f₂ : ModularForm (Γt M H t) k₂)
    (f₃ : ModularForm (Γt M H t) k₃) (f₄ : ModularForm (Γt M H t) k₄) (hk : k₃ + k₄ = k₁ + k₂)
    (h : (⇑f₁ * ⇑f₂ : ℍ → ℂ) = ⇑f₃ * ⇑f₄) :
    (⇑(alForm γ hγ hγt f₁) * ⇑(alForm γ hγ hγt f₂) : ℍ → ℂ) =
      ⇑(alForm γ hγ hγt f₃) * ⇑(alForm γ hγ hγt f₄) := by
  have h' := congrArg (fun F : ℍ → ℂ => F ∣[k₁ + k₂] γ) h
  rw [ModularForm.mul_slash_SL2] at h'
  conv at h' => rhs; rw [← hk, ModularForm.mul_slash_SL2]
  funext τ
  have := congrFun h' (ModularForm.heckeDiagMatrix t • τ)
  simpa only [coe_alForm, Pi.mul_apply] using this

end QExp
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laurentBaseChange_xHTopFunctionFieldC_coe_eq_qExpand_of_coprime.ALGenT.ALData"

section Img

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {t : ℕ} [NeZero t]
variable (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγt : (t : ℤ) ∣ γ 1 1)
variable (γ' : SL(2, ℤ)) (hγ' : γ' ∈ Gamma0 M) (hγ't : (t : ℤ) ∣ γ' 1 1)

variable (H) in

def QuasiInv : Prop :=
  ∀ (k : ℤ) (f : ModularForm (Γt M H t) k),
    ⇑(alForm γ' hγ' hγ't (alForm γ hγ hγt f)) = ((t : ℂ) ^ k)⁻¹ • ⇑f

variable {γ hγ hγt γ' hγ' hγ't}

theorem alForm_ne_zero (hq : QuasiInv H γ hγ hγt γ' hγ' hγ't) {k : ℤ} {f : ModularForm (Γt M H t) k}
    (hf : f ≠ 0) : alForm γ hγ hγt f ≠ 0 := by
  intro h
  apply hf
  have h1 := hq k f
  rw [h, alForm_zero, ModularForm.coe_zero] at h1
  have hc : ((t : ℂ) ^ k)⁻¹ ≠ 0 := inv_ne_zero (zpow_ne_zero _ (by exact_mod_cast NeZero.ne t))
  have : (⇑f : ℍ → ℂ) = 0 := by
    funext τ
    have := congrFun h1 τ
    simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hc
  exact DFunLike.ext' (by rw [this, ModularForm.coe_zero])

theorem qC_alForm_ne_zero (hq : QuasiInv H γ hγ hγt γ' hγ' hγ't) {k : ℤ} {g : ModularForm (Γt M H t) k}
    {pg : PowerSeries ℤ} (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) :
    qC (alForm γ hγ hγt g) ≠ 0 := fun h =>
  alForm_ne_zero hq (ne_zero_of_intSeriesC_ne_zero hg hg0) ((qC_eq_zero_iff _).mp h)

variable (H γ hγ hγt) in

def IsImg (x y : LaurentSeries ℚ) : Prop :=
  ∃ (k : ℤ) (f g : ModularForm (Γt M H t) k) (pf pg : PowerSeries ℤ),
    IsIntegralQExp f pf ∧ IsIntegralQExp g pg ∧ intSeriesC ℚ pg ≠ 0 ∧
      x = intSeriesC ℚ pf / intSeriesC ℚ pg ∧
        ιC y * qC (alForm γ hγ hγt g) = qC (alForm γ hγ hγt f)

theorem IsImg.apply_rep (hq : QuasiInv H γ hγ hγt γ' hγ' hγ't) {x y : LaurentSeries ℚ}
    (h : IsImg H γ hγ hγt x y) {k : ℤ}
    (f g : ModularForm (Γt M H t) k) (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf)
    (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0) (hx : x = intSeriesC ℚ pf / intSeriesC ℚ pg) :
    ιC y * qC (alForm γ hγ hγt g) = qC (alForm γ hγ hγt f) := by
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, hx₂, hy⟩ := h
  have hcross : intSeriesC ℚ pf * intSeriesC ℚ pg₂ = intSeriesC ℚ pf₂ * intSeriesC ℚ pg := by
    rw [← div_eq_div_iff hg0 hg₂0, ← hx, ← hx₂]
  have hqc : qC f * qC g₂ = qC f₂ * qC g := by
    have := congrArg ιC hcross
    rwa [map_mul, map_mul, ιC_intSeriesC hf, ιC_intSeriesC hg₂, ιC_intSeriesC hf₂,
      ιC_intSeriesC hg] at this
  have hfun := mul_eq_mul_of_qC f g₂ f₂ g (add_comm k₂ k) hqc
  have hsl := al_mul_eq γ hγ hγt f g₂ f₂ g (add_comm k₂ k) hfun
  have hqs : qC (alForm γ hγ hγt f) * qC (alForm γ hγ hγt g₂) =
      qC (alForm γ hγ hγt f₂) * qC (alForm γ hγ hγt g) := by
    rw [← qC_mul, ← qC_mul, hsl]
  have hne := qC_alForm_ne_zero hq hg₂ hg₂0
  apply mul_right_cancel₀ hne
  calc ιC y * qC (alForm γ hγ hγt g) * qC (alForm γ hγ hγt g₂)
      = ιC y * qC (alForm γ hγ hγt g₂) * qC (alForm γ hγ hγt g) := by ring
    _ = qC (alForm γ hγ hγt f₂) * qC (alForm γ hγ hγt g) := by rw [hy]
    _ = qC (alForm γ hγ hγt f) * qC (alForm γ hγ hγt g₂) := hqs.symm

theorem IsImg.unique (hq : QuasiInv H γ hγ hγt γ' hγ' hγ't) {x y y' : LaurentSeries ℚ}
    (h : IsImg H γ hγ hγt x y) (h' : IsImg H γ hγ hγt x y') : y = y' := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, hx, hy'⟩ := h'
  have hy := h.apply_rep hq f g pf pg hf hg hg0 hx
  rw [← hy'] at hy
  exact ιC_injective (mul_right_cancel₀ (qC_alForm_ne_zero hq hg hg0) hy)

omit [NeZero t] in
theorem isIntegralQExp_mul' {k₁ k₂ : ℤ} {f : ModularForm (Γt M H t) k₁} {g : ModularForm (Γt M H t) k₂}
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) :
    IsIntegralQExp (f.mul g) (pf * pg) := by
  rw [IsIntegralQExp, map_mul, hf, hg, ModularForm.coe_mul]
  exact (ModularForm.qExpansion_mul_coe one_pos one_mem_strictPeriods_top f g).symm

theorem IsImg.mul {x₁ y₁ x₂ y₂ : LaurentSeries ℚ} (h₁ : IsImg H γ hγ hγt x₁ y₁)
    (h₂ : IsImg H γ hγ hγt x₂ y₂) : IsImg H γ hγ hγt (x₁ * x₂) (y₁ * y₂) := by
  obtain ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, hg₁0, rfl, hy₁⟩ := h₁
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, rfl, hy₂⟩ := h₂
  refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, pf₁ * pf₂, pg₁ * pg₂, isIntegralQExp_mul' hf₁ hf₂,
    isIntegralQExp_mul' hg₁ hg₂, ?_, ?_, ?_⟩
  · rw [intSeriesC_mul]; exact mul_ne_zero hg₁0 hg₂0
  · rw [intSeriesC_mul, intSeriesC_mul, div_mul_div_comm]
  · rw [alForm_mul_apply, alForm_mul_apply, qC_mul, qC_mul, map_mul, ← hy₁, ← hy₂]
    ring

theorem IsImg.add {x₁ y₁ x₂ y₂ : LaurentSeries ℚ} (h₁ : IsImg H γ hγ hγt x₁ y₁)
    (h₂ : IsImg H γ hγ hγt x₂ y₂) : IsImg H γ hγ hγt (x₁ + x₂) (y₁ + y₂) := by
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

theorem IsImg.neg {x y : LaurentSeries ℚ} (h : IsImg H γ hγ hγt x y) : IsImg H γ hγ hγt (-x) (-y) := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl, hy⟩ := h
  refine ⟨k, -f, g, -pf, pg, ?_, hg, hg0, ?_, ?_⟩
  · rw [IsIntegralQExp, map_neg, hf, ModularForm.coe_neg]
    exact (ModularForm.qExpansion_neg one_pos one_mem_strictPeriods_top f).symm
  · rw [intSeriesC_neg', neg_div]
  · rw [alForm_neg, qC_neg, map_neg, ← hy]
    ring

omit [NeZero t] in
theorem isIntegralQExp_one' :
    IsIntegralQExp ((1 : ModularForm (Γt M H t) 0) : ℍ → ℂ) 1 := by
  rw [ModularForm.one_coe_eq_one]; exact isIntegralQExp_one

theorem IsImg.one : IsImg H γ hγ hγt 1 1 := by
  refine ⟨0, 1, 1, 1, 1, isIntegralQExp_one', isIntegralQExp_one', by simp, by simp, ?_⟩
  rw [map_one, one_mul, alForm_one]

theorem IsImg.zero : IsImg H γ hγ hγt 0 0 := by
  refine ⟨0, 0, 1, 0, 1, ?_, isIntegralQExp_one', by simp, by simp, ?_⟩
  · rw [ModularForm.coe_zero]; exact isIntegralQExp_zero
  · rw [map_zero, zero_mul, alForm_zero, ModularForm.coe_zero, qC_zero]

theorem IsImg.symm (hq : QuasiInv H γ hγ hγt γ' hγ' hγ't) {x y : LaurentSeries ℚ}
    (h : IsImg H γ hγ hγt x y) (hyS : y ∈ S M H t) : IsImg H γ' hγ' hγ't y x := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, hx, hy⟩ := h
  obtain ⟨kP, P, Q, pP, pQ, hP, hQ, hQ0, rfl⟩ := hyS
  refine ⟨kP, P, Q, pP, pQ, hP, hQ, hQ0, rfl, ?_⟩
  have hQ' : qC Q ≠ 0 := qC_ιC_ne_zero hQ hQ0
  have h1 : qC P * qC (alForm γ hγ hγt g) = qC (alForm γ hγ hγt f) * qC Q := by
    rw [← hy, map_div₀, ιC_intSeriesC hP, ιC_intSeriesC hQ, div_mul_eq_mul_div, div_mul_cancel₀ _ hQ']
  have hfun := mul_eq_mul_of_qC P (alForm γ hγ hγt g) (alForm γ hγ hγt f) Q (add_comm k kP) h1
  have hsl := al_mul_eq γ' hγ' hγ't P (alForm γ hγ hγt g) (alForm γ hγ hγt f) Q (add_comm k kP) hfun
  rw [hq k g, hq k f] at hsl
  have hc : ((t : ℂ) ^ k)⁻¹ ≠ 0 := inv_ne_zero (zpow_ne_zero _ (by exact_mod_cast NeZero.ne t))
  have hsl' : (⇑(alForm γ' hγ' hγ't P) * ⇑g : ℍ → ℂ) = ⇑f * ⇑(alForm γ' hγ' hγ't Q) := by
    funext τ
    have := congrFun hsl τ
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    apply mul_left_cancel₀ hc
    linear_combination this
  have hqq : qC (alForm γ' hγ' hγ't P) * qC g = qC f * qC (alForm γ' hγ' hγ't Q) := by
    rw [← qC_mul, ← qC_mul, hsl']
  rw [hx, map_div₀, ιC_intSeriesC hf, ιC_intSeriesC hg]
  have hg' : qC g ≠ 0 := qC_ιC_ne_zero hg hg0
  rw [div_mul_eq_mul_div, div_eq_iff hg']
  exact hqq.symm

variable (H γ hγ hγt) in

def ALRational : Prop :=
  ∀ (k : ℤ) (f : ModularForm (Γt M H t) k) (pf : PowerSeries ℤ), Even k → IsIntegralQExp f pf →
    ∃ D : ℤ, D ≠ 0 ∧ ∃ p : PowerSeries ℤ, IsIntegralQExp ((D : ℂ) • ⇑(alForm γ hγ hγt f)) p

omit [NeZero t] in

theorem isIntegralQExp_smul_smul {k : ℤ} (F : ModularForm (Γt M H t) k) {D : ℤ} (E : ℤ)
    {p : PowerSeries ℤ} (hp : IsIntegralQExp ((D : ℂ) • ⇑F) p) :
    IsIntegralQExp (⇑(((E : ℂ) * D) • F)) (PowerSeries.C E * p) := by
  rw [IsIntegralQExp] at hp ⊢
  rw [map_mul, PowerSeries.map_C, hp, ModularForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_top _ F,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_top _ F, PowerSeries.smul_eq_C_mul,
    PowerSeries.smul_eq_C_mul, ← mul_assoc, ← map_mul, eq_intCast]

omit [NeZero t] in
theorem ιC_intSeriesC_smul {k : ℤ} {F : ModularForm (Γt M H t) k} {D : ℤ} {p : PowerSeries ℤ}
    (hp : IsIntegralQExp ((D : ℂ) • ⇑F) p) : ιC (intSeriesC ℚ p) = HahnSeries.C (D : ℂ) * qC F := by
  rw [ιC_intSeriesC hp, qC_smul]

theorem exists_isImg (hq : QuasiInv H γ hγ hγt γ' hγ' hγ't) (hW : ALRational H γ hγ hγt)
    {x : LaurentSeries ℚ} (hx : x ∈ S M H t) : ∃ y ∈ S M H t, IsImg H γ hγ hγt x y := by
  obtain ⟨k, f, g, pf, pg, hk, hf, hg, hg0, rfl⟩ := exists_even_rep hx
  obtain ⟨Df, hDf, pf', hpf'⟩ := hW k f pf hk hf
  obtain ⟨Dg, hDg, pg', hpg'⟩ := hW k g pg hk hg
  have hF' := isIntegralQExp_smul_smul (alForm γ hγ hγt f) Dg hpf'
  have hG' := isIntegralQExp_smul_smul (alForm γ hγ hγt g) Df hpg'
  have hv : qC (alForm γ hγ hγt g) ≠ 0 := qC_alForm_ne_zero hq hg hg0
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

variable (hq : QuasiInv H γ hγ hγt γ' hγ' hγ't) (hW : ALRational H γ hγ hγt)

def σfun (x : xHTopFunctionFieldC ℚ M H (M * t)) : xHTopFunctionFieldC ℚ M H (M * t) :=
  ⟨Classical.choose (exists_isImg hq hW (mem_S_of_mem x.2)),
    intFormRatiosC_subset ℚ _ (Classical.choose_spec (exists_isImg hq hW (mem_S_of_mem x.2))).1⟩

theorem isImg_σfun (x : xHTopFunctionFieldC ℚ M H (M * t)) :
    IsImg H γ hγ hγt (x : LaurentSeries ℚ) (σfun hq hW x) :=
  (Classical.choose_spec (exists_isImg hq hW (mem_S_of_mem x.2))).2

def σHom : xHTopFunctionFieldC ℚ M H (M * t) →+* xHTopFunctionFieldC ℚ M H (M * t) where
  toFun := σfun hq hW
  map_one' := Subtype.ext ((isImg_σfun hq hW 1).unique hq IsImg.one)
  map_mul' x y := Subtype.ext
    ((isImg_σfun hq hW (x * y)).unique hq ((isImg_σfun hq hW x).mul (isImg_σfun hq hW y)))
  map_zero' := Subtype.ext ((isImg_σfun hq hW 0).unique hq IsImg.zero)
  map_add' x y := Subtype.ext
    ((isImg_σfun hq hW (x + y)).unique hq ((isImg_σfun hq hW x).add (isImg_σfun hq hW y)))

theorem isImg_σHom (x : xHTopFunctionFieldC ℚ M H (M * t)) :
    IsImg H γ hγ hγt (x : LaurentSeries ℚ) (σHom hq hW x) :=
  isImg_σfun hq hW x

variable (hq' : QuasiInv H γ' hγ' hγ't γ hγ hγt) (hW' : ALRational H γ' hγ' hγ't)

theorem σHom_inv_apply (x : xHTopFunctionFieldC ℚ M H (M * t)) :
    σHom hq' hW' (σHom hq hW x) = x := by
  apply Subtype.ext
  refine (isImg_σHom hq' hW' (σHom hq hW x)).unique hq' ?_
  exact (isImg_σHom hq hW x).symm hq (mem_S_of_mem (σHom hq hW x).2)

def σAlgEquiv : xHTopFunctionFieldC ℚ M H (M * t) ≃ₐ[ℚ] xHTopFunctionFieldC ℚ M H (M * t) :=
  AlgEquiv.ofRingEquiv (f :=
    { σHom hq hW with
      invFun := σHom hq' hW'
      left_inv := σHom_inv_apply hq hW hq' hW'
      right_inv := σHom_inv_apply hq' hW' hq hW }) fun c => by
    have := RingHom.ext_rat ((σHom hq hW).comp (algebraMap ℚ (xHTopFunctionFieldC ℚ M H (M * t))))
      (algebraMap ℚ (xHTopFunctionFieldC ℚ M H (M * t)))
    exact congrFun (congrArg DFunLike.coe this) c

theorem σAlgEquiv_apply (x : xHTopFunctionFieldC ℚ M H (M * t)) :
    σAlgEquiv hq hW hq' hW' x = σHom hq hW x := rfl

theorem isImg_σAlgEquiv (x : xHTopFunctionFieldC ℚ M H (M * t)) :
    IsImg H γ hγ hγt (x : LaurentSeries ℚ) (σAlgEquiv hq hW hq' hW' x) :=
  isImg_σfun hq hW x

end Img
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laurentBaseChange_xHTopFunctionFieldC_coe_eq_qExpand_of_coprime.ALGenT.ALData"

section Inputs

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {t : ℕ} [NeZero t] (d : ALData M t)

omit [NeZero M] in
theorem quasiInv_γ₁ : QuasiInv H d.γ₁ d.γ₁_mem_Gamma0 d.dvd_γ₁ d.γ₁' d.γ₁'_mem_Gamma0 d.dvd_γ₁' :=
  fun _ f => alForm_γ₁'_alForm_γ₁ d f

omit [NeZero M] in
theorem quasiInv_γ₁' : QuasiInv H d.γ₁' d.γ₁'_mem_Gamma0 d.dvd_γ₁' d.γ₁ d.γ₁_mem_Gamma0 d.dvd_γ₁ :=
  fun _ f => alForm_γ₁_alForm_γ₁' d f

omit [NeZero M] [NeZero t] in
theorem Γ₁t_le : ((Gamma1 M ⊓ Gamma0 (M * t) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ Γt M H t :=
  Subgroup.map_mono (inf_le_inf_right _ (Gamma1_le_GammaH M H))

theorem alRational (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) (hγt : (t : ℤ) ∣ γ 1 1) :
    ALRational H γ hγ hγt := by
  intro k f pf hk hf
  obtain ⟨D, p₁, hD, hp₁⟩ :=
    ModularCurve.exists_isIntegralQExp_smul_atkinLehnerSlash_of_even M t hk (restrictForm Γ₁t_le f) hf γ hγ hγt
  refine ⟨D, hD, p₁, ?_⟩
  rw [coe_alForm]
  exact hp₁

def σ₀ : xHTopFunctionFieldC ℚ M H (M * t) ≃ₐ[ℚ] xHTopFunctionFieldC ℚ M H (M * t) :=
  σAlgEquiv (quasiInv_γ₁ d) (alRational d.γ₁ d.γ₁_mem_Gamma0 d.dvd_γ₁)
    (quasiInv_γ₁' d) (alRational d.γ₁' d.γ₁'_mem_Gamma0 d.dvd_γ₁')

theorem isImg_σ₀ (x : xHTopFunctionFieldC ℚ M H (M * t)) :
    IsImg H d.γ₁ d.γ₁_mem_Gamma0 d.dvd_γ₁ (x : LaurentSeries ℚ) (σ₀ d x) :=
  isImg_σAlgEquiv _ _ _ _ x

theorem σ₀_spec {x : xHTopFunctionFieldC ℚ M H (M * t)} {k : ℤ} (f g : ModularForm (Γt M H t) k)
    (pf pg : PowerSeries ℤ) (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg)
    (hg0 : intSeriesC ℚ pg ≠ 0) (hx : (x : LaurentSeries ℚ) = intSeriesC ℚ pf / intSeriesC ℚ pg) :
    ιC (σ₀ d x : LaurentSeries ℚ) * qC (alForm d.γ₁ d.γ₁_mem_Gamma0 d.dvd_γ₁ g) =
      qC (alForm d.γ₁ d.γ₁_mem_Gamma0 d.dvd_γ₁ f) :=
  (isImg_σ₀ d x).apply_rep (quasiInv_γ₁ d) f g pf pg hf hg hg0 hx

end Inputs
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laurentBaseChange_xHTopFunctionFieldC_coe_eq_qExpand_of_coprime.ALGenT.ALData"

section Expand

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {t : ℕ} [NeZero t] {k : ℤ}

theorem coeffMap_qExpand {R T : Type*} [CommRing R] [CommRing T] (φ : R →+* T)
    (x : LaurentSeries R) : coeffMap φ (qExpand R t x) = qExpand T t (coeffMap φ x) := by
  ext n
  by_cases hk : (t : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd t _ hk, qExpand_coeff_of_not_dvd t _ hk, map_zero]

def expandPS {R : Type*} [CommRing R] (t : ℕ) (P : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun n => if t ∣ n then PowerSeries.coeff (n / t) P else 0

omit [NeZero t] in
theorem coeff_expandPS {R : Type*} [CommRing R] (P : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (expandPS t P) = if t ∣ n then PowerSeries.coeff (n / t) P else 0 := by
  rw [expandPS, PowerSeries.coeff_mk]

theorem ofPowerSeries_expandPS {R : Type*} [CommRing R] (P : PowerSeries R) :
    ofPowerSeries ℤ R (expandPS t P) = qExpand R t (ofPowerSeries ℤ R P) := by
  ext m
  by_cases hdvd : (t : ℤ) ∣ m
  · obtain ⟨j, rfl⟩ := hdvd
    rw [qExpand_coeff_mul, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
    have ht0 : (0 : ℤ) < t := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne t)
    by_cases hj : j < 0
    · rw [if_pos hj, if_pos (mul_neg_of_pos_of_neg ht0 hj)]
    · rw [if_neg hj, if_neg (by push Not at hj ⊢; positivity)]
      simp only [coeff_expandPS]
      have h1 : ((t : ℤ) * j).natAbs = t * j.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      rw [h1, if_pos (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne t))]
  · rw [qExpand_coeff_of_not_dvd t _ hdvd, PowerSeries.coeff_coe]
    split_ifs with hm
    · rfl
    · rw [coeff_expandPS, if_neg]
      rintro ⟨c, hc⟩
      apply hdvd
      refine ⟨c, ?_⟩
      have : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg (le_of_not_gt hm)
      rw [← this, hc]; push_cast; ring

omit [NeZero t] in
theorem expandPS_map (P : PowerSeries ℤ) :
    expandPS t (P.map (Int.castRingHom ℂ)) = (expandPS t P).map (Int.castRingHom ℂ) := by
  ext n
  simp only [coeff_expandPS, PowerSeries.coeff_map]
  split_ifs <;> simp

theorem qExpansion_comp_heckeDiag (f : ModularForm (Γb M H) k) :
    qExpansion 1 (fun τ => f (ModularForm.heckeDiagMatrix t • τ)) = expandPS t (qExpansion 1 f) := by
  ext n
  rw [coeff_expandPS]
  exact ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul f one_mem_strictPeriods_bot (NeZero.ne t) n

theorem qC_levelRaise (f : ModularForm (Γb M H) k) :
    qC (levelRaise (t := t) f) = qExpand ℂ t (qC f) := by
  rw [qC, coe_levelRaise, qExpansion_comp_heckeDiag, ofPowerSeries_expandPS, qC]

theorem isIntegralQExp_levelRaise {f : ModularForm (Γb M H) k} {pf : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) : IsIntegralQExp (levelRaise (t := t) f) (expandPS t pf) := by
  rw [IsIntegralQExp, coe_levelRaise, qExpansion_comp_heckeDiag, ← hf, expandPS_map]

theorem intSeriesC_expandPS (K : Type*) [Field K] (p : PowerSeries ℤ) :
    intSeriesC K (expandPS t p) = qExpand K t (intSeriesC K p) := by
  rw [intSeriesC, intSeriesC, ← ofPowerSeries_expandPS]
  congr 1
  ext n
  simp only [coeff_expandPS, PowerSeries.coeff_map]
  split_ifs <;> simp

end Expand
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laurentBaseChange_xHTopFunctionFieldC_coe_eq_qExpand_of_coprime.ALGenT.ALData"

section Main

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {t : ℕ} [NeZero t] (d : ALData M t)

local notation "L" => AlgebraicClosure ℚ

theorem σ₀_apply_bot {k : ℤ} (f g : ModularForm (Γb M H) k) (pf pg : PowerSeries ℤ)
    (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) (hg0 : intSeriesC ℚ pg ≠ 0)
    (hzt : intSeriesC ℚ pf / intSeriesC ℚ pg ∈ xHTopFunctionFieldC ℚ M H (M * t)) :
    ((σ₀ d ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, hzt⟩ : xHTopFunctionFieldC ℚ M H (M * t)) :
        LaurentSeries ℚ) = qExpand ℚ t (intSeriesC ℚ pf / intSeriesC ℚ pg) := by
  have key := σ₀_spec d (x := ⟨_, hzt⟩) (restrictForm Γt_le_Γb f) (restrictForm Γt_le_Γb g) pf pg
    hf hg hg0 rfl
  rw [alForm_γ₁_restrict, alForm_γ₁_restrict, qC_levelRaise, qC_levelRaise, ← ιC_intSeriesC hf,
    ← ιC_intSeriesC hg, ← coeffMap_qExpand, ← coeffMap_qExpand, ← map_mul] at key
  have key' := ιC_injective key
  have hne : qExpand ℚ t (intSeriesC ℚ pg) ≠ 0 := fun h => hg0 (qExpand_injective t (by rw [h, map_zero]))
  rw [map_div₀, eq_div_iff hne]
  exact key'

variable (w : laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * t)) ≃ₐ[L]
    laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * t)))
  (hw : ∀ y : xHTopFunctionFieldC ℚ M H (M * t),
    ((w ⟨coeffEmb L (y : LaurentSeries ℚ), coeffEmb_mem_laurentBaseChange L y.2⟩ :
      laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * t))) : LaurentSeries L) =
        coeffEmb L ((σ₀ d y : xHTopFunctionFieldC ℚ M H (M * t)) : LaurentSeries ℚ))

omit [NeZero M] [NeZero t] in
theorem bot_le_top :
    xHFunctionFieldBar M H ≤ laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * t)) := by
  rw [xHFunctionFieldBar, laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (xHFunctionFieldC_le_top ℚ M H (M * t) hy)

include hw in

theorem val_comp_w_comp_inclusion :
    ((laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * t))).val.comp
        (w.toAlgHom.comp (IntermediateField.inclusion (bot_le_top (M := M) (H := H) (t := t))))) =
      (qExpandAlgHomC L t).comp (xHFunctionFieldBar M H).val := by
  refine IntermediateField.algHom_ext_of_eq_adjoin (F := L)
    (S := xHFunctionFieldBar M H) (s := ⇑(coeffEmb L) '' (xHFunctionField M H : Set (LaurentSeries ℚ)))
    rfl fun x hx => ?_
  obtain ⟨z, hz, rfl⟩ := hx
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := mem_Sb_of_mem hz
  have hzt : intSeriesC ℚ pf / intSeriesC ℚ pg ∈ xHTopFunctionFieldC ℚ M H (M * t) :=
    xHFunctionFieldC_le_top ℚ M H (M * t) hz
  have hincl : IntermediateField.inclusion (bot_le_top (M := M) (H := H) (t := t))
      ⟨coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg),
        (rfl : xHFunctionFieldBar M H = IntermediateField.adjoin L _).ge
          (IntermediateField.subset_adjoin _ _ ⟨_, hz, rfl⟩)⟩ =
      ⟨coeffEmb L ((⟨_, hzt⟩ : xHTopFunctionFieldC ℚ M H (M * t)) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange L (⟨_, hzt⟩ : xHTopFunctionFieldC ℚ M H (M * t)).2⟩ :=
    Subtype.ext rfl
  change ((w (IntermediateField.inclusion (bot_le_top (M := M) (H := H) (t := t)) _) :
      laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * t))) : LaurentSeries L) =
    qExpand L t (coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg))
  rw [hincl, hw ⟨_, hzt⟩, σ₀_apply_bot d f g pf pg hf hg hg0 hzt]
  exact coeffMap_qExpand _ _

include hw in

theorem w_apply_of_mem (x : laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * t)))
    (hx : (x : LaurentSeries L) ∈ xHFunctionFieldBar M H) :
    ((w x : laurentBaseChange L (xHTopFunctionFieldC ℚ M H (M * t))) : LaurentSeries L) =
      qExpand L t (x : LaurentSeries L) := by
  have hxeq : x = IntermediateField.inclusion (bot_le_top (M := M) (H := H) (t := t)) ⟨x, hx⟩ :=
    Subtype.ext rfl
  have h := DFunLike.congr_fun (val_comp_w_comp_inclusion d w hw) ⟨(x : LaurentSeries L), hx⟩
  simp only [AlgHom.coe_comp, Function.comp_apply, IntermediateField.coe_val,
    qExpandAlgHomC_apply] at h
  rw [hxeq]
  exact h

end Main
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laurentBaseChange_xHTopFunctionFieldC_coe_eq_qExpand_of_coprime.ALGenT.ALData"

end ALGenT
p2m_reactivate "P2MW.S_ModularCurve_exists_algEquiv_laurentBaseChange_xHTopFunctionFieldC_coe_eq_qExpand_of_coprime.ALGenT.ALData P2MW.S_ModularCurve_exists_algEquiv_laurentBaseChange_xHTopFunctionFieldC_coe_eq_qExpand_of_coprime.ALGenT"

open ModularCurve ALGenT in
theorem solution (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (t : ℕ) [NeZero t]
    (htM : Nat.Coprime t M) :
    ∃ w : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * t)) ≃ₐ[AlgebraicClosure ℚ]
        ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * t)),
      ∀ x : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ M H (M * t)),
        (x : LaurentSeries (AlgebraicClosure ℚ)) ∈ ModularCurve.xHFunctionFieldBar M H →
          ((w x : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
              (ModularCurve.xHTopFunctionFieldC ℚ M H (M * t))) :
              LaurentSeries (AlgebraicClosure ℚ)) =
            ModularCurve.qExpand (AlgebraicClosure ℚ) t (x : LaurentSeries (AlgebraicClosure ℚ)) := by
  obtain ⟨d⟩ := nonempty_alData htM
  obtain ⟨w, hw⟩ := ModularCurve.exists_algEquiv_laurentBaseChange_cover (AlgebraicClosure ℚ)
    (xHTopFunctionFieldC ℚ M H (M * t)) (σ₀ d).toRingEquiv
  exact ⟨w, fun x hx => w_apply_of_mem d w hw x hx⟩

end
end S_ModularCurve_exists_algEquiv_laurentBaseChange_xHTopFunctionFieldC_coe_eq_qExpand_of_coprime
end P2MW
export P2MW.S_ModularCurve_exists_algEquiv_laurentBaseChange_xHTopFunctionFieldC_coe_eq_qExpand_of_coprime (solution)
