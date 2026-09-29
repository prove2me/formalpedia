-- Prove2me | solution 1 for ModularCurve.le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/8a0725da-efe3-5d2f-b443-67cb9b7da3b5

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd

set_option linter.unusedSectionVars false

noncomputable section

open scoped MatrixGroups ModularForm Pointwise

namespace LeRelrankSol

open ModularCurve HahnSeries UpperHalfPlane CongruenceSubgroup IntermediateField ModularForm EisensteinSeries Matrix

section LevelOne

def P4 : PowerSeries ℤ :=
  PowerSeries.mk fun m => if m = 0 then 1 else 240 * (ArithmeticFunction.sigma 3 m : ℤ)

def P6 : PowerSeries ℤ :=
  PowerSeries.mk fun m => if m = 0 then 1 else -504 * (ArithmeticFunction.sigma 5 m : ℤ)

theorem isIntegralQExp_E4 : IsIntegralQExp (E₄ : ℍ → ℂ) P4 := by
  rw [isIntegralQExp_iff]
  intro n
  rw [E_qExpansion_coeff (by norm_num) (by decide) n, P4, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 4 = -1 / 30 by decide +kernel]
    push_cast
    ring

theorem isIntegralQExp_E6 : IsIntegralQExp (E₆ : ℍ → ℂ) P6 := by
  rw [isIntegralQExp_iff]
  intro n
  rw [E_qExpansion_coeff (by norm_num) (by decide) n, P6, PowerSeries.coeff_mk]
  split_ifs with h
  · simp
  · rw [show _root_.bernoulli 6 = 1 / 42 by decide +kernel]
    push_cast
    ring

def AF : ModularForm ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrictForm (Subgroup.map_le_range _ ⊤) ((E₄.pow 3).mcast (by norm_num))

def BF : ModularForm ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 12 :=
  restrictForm (Subgroup.map_le_range _ ⊤) ((E₆.pow 2).mcast (by norm_num))

theorem coe_AF : (AF : ℍ → ℂ) = (E₄ : ℍ → ℂ) ^ 3 := by
  rw [AF, coe_restrictForm, coe_mcast, coe_pow]

theorem coe_BF : (BF : ℍ → ℂ) = (E₆ : ℍ → ℂ) ^ 2 := by
  rw [BF, coe_restrictForm, coe_mcast, coe_pow]

theorem isIntegralQExp_AF : IsIntegralQExp (AF : ℍ → ℂ) (P4 ^ 3) := by
  rw [IsIntegralQExp, AF, coe_restrictForm, map_pow, isIntegralQExp_E4]
  rw [ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

theorem isIntegralQExp_BF : IsIntegralQExp (BF : ℍ → ℂ) (P6 ^ 2) := by
  rw [IsIntegralQExp, BF, coe_restrictForm, map_pow, isIntegralQExp_E6]
  rw [ModularForm.qExpansion_mcast, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]

variable (Γ : Subgroup SL(2, ℤ))

def AΓ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 := restrictForm (Subgroup.map_mono le_top) AF

def BΓ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 12 := restrictForm (Subgroup.map_mono le_top) BF

theorem coe_AΓ : (AΓ Γ : ℍ → ℂ) = AF := rfl
theorem coe_BΓ : (BΓ Γ : ℍ → ℂ) = BF := rfl

theorem isIntegralQExp_AΓ : IsIntegralQExp (AΓ Γ : ℍ → ℂ) (P4 ^ 3) := isIntegralQExp_AF
theorem isIntegralQExp_BΓ : IsIntegralQExp (BΓ Γ : ℍ → ℂ) (P6 ^ 2) := isIntegralQExp_BF

theorem constantCoeff_P4 : PowerSeries.constantCoeff P4 = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, P4, PowerSeries.coeff_mk]; simp

theorem constantCoeff_P6 : PowerSeries.constantCoeff P6 = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, P6, PowerSeries.coeff_mk]; simp

theorem coeff_one_P4 : PowerSeries.coeff 1 P4 = 240 := by
  rw [P4, PowerSeries.coeff_mk]; simp [ArithmeticFunction.sigma_one]

theorem coeff_one_P6 : PowerSeries.coeff 1 P6 = -504 := by
  rw [P6, PowerSeries.coeff_mk]; simp [ArithmeticFunction.sigma_one]

def A4Q : PowerSeries ℚ := (P4 ^ 3).map (Int.castRingHom ℚ)
def B6Q : PowerSeries ℚ := (P6 ^ 2).map (Int.castRingHom ℚ)

theorem constantCoeff_A4Q : PowerSeries.constantCoeff A4Q = 1 := by
  rw [A4Q, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_P4, one_pow, map_one]

theorem constantCoeff_B6Q : PowerSeries.constantCoeff B6Q = 1 := by
  rw [B6Q, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_P6, one_pow, map_one]

theorem coeff_one_A4Q : PowerSeries.coeff 1 A4Q = 720 := by
  rw [A4Q, PowerSeries.coeff_map, PowerSeries.coeff_one_pow, coeff_one_P4, constantCoeff_P4]
  norm_num

theorem coeff_one_B6Q : PowerSeries.coeff 1 B6Q = -1008 := by
  rw [B6Q, PowerSeries.coeff_map, PowerSeries.coeff_one_pow, coeff_one_P6, constantCoeff_P6]
  norm_num

theorem isUnit_A4Q : IsUnit A4Q :=
  PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [constantCoeff_A4Q]; exact isUnit_one)

def XQ : PowerSeries ℚ := B6Q * ↑(isUnit_A4Q.unit⁻¹)

theorem XQ_mul_A : XQ * A4Q = B6Q := by
  rw [XQ, mul_assoc, IsUnit.val_inv_mul, mul_one]

theorem coeff_one_XQ : PowerSeries.coeff 1 XQ = -1728 := by
  have h0 : PowerSeries.constantCoeff XQ = 1 := by
    have h := congrArg PowerSeries.constantCoeff XQ_mul_A
    rw [map_mul, constantCoeff_A4Q, mul_one, constantCoeff_B6Q] at h
    exact h
  have h1 := congrArg (PowerSeries.coeff 1) XQ_mul_A
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
    Finset.sum_singleton] at h1
  simp only [zero_add, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, one_mul, coeff_one_A4Q,
    constantCoeff_A4Q, mul_one, coeff_one_B6Q] at h1
  linarith

theorem intSeriesC_ne_zero_of_constantCoeff {K : Type*} [Field K] [CharZero K] {p : PowerSeries ℤ}
    (hp : PowerSeries.constantCoeff p = 1) : intSeriesC K p ≠ 0 := by
  intro h
  have := congrArg (fun z : LaurentSeries K => z.coeff 0) h
  simp only [intSeriesC, HahnSeries.coeff_zero] at this
  rw [PowerSeries.coeff_coe] at this
  simp only [lt_self_iff_false, ↓reduceIte, Int.natAbs_zero, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, hp, map_one, one_ne_zero] at this

theorem intSeriesC_PA_ne_zero (K : Type*) [Field K] [CharZero K] : intSeriesC K (P4 ^ 3) ≠ 0 :=
  intSeriesC_ne_zero_of_constantCoeff (by rw [map_pow, constantCoeff_P4, one_pow])

theorem intSeriesC_PB_ne_zero (K : Type*) [Field K] [CharZero K] : intSeriesC K (P6 ^ 2) ≠ 0 :=
  intSeriesC_ne_zero_of_constantCoeff (by rw [map_pow, constantCoeff_P6, one_pow])

def xq : LaurentSeries ℚ := intSeriesC ℚ (P6 ^ 2) / intSeriesC ℚ (P4 ^ 3)

theorem xq_mem : xq ∈ qExpFunctionFieldC ℚ Γ :=
  div_mem_qExpFunctionFieldC (BΓ Γ) (AΓ Γ) (isIntegralQExp_BΓ Γ) (isIntegralQExp_AΓ Γ)
    (intSeriesC_PA_ne_zero ℚ)

theorem xq_eq : xq = HahnSeries.ofPowerSeries ℤ ℚ XQ := by
  rw [xq, div_eq_iff (intSeriesC_PA_ne_zero ℚ), intSeriesC, intSeriesC, ← map_mul]
  change _ = HahnSeries.ofPowerSeries ℤ ℚ (XQ * A4Q)
  rw [XQ_mul_A]
  rfl

theorem xq_coeff_one : xq.coeff 1 = -1728 := by
  rw [xq_eq, show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, coeff_one_XQ]

end LevelOne

section Groups

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ)

abbrev Gam : Subgroup SL(2, ℤ) := CohCarrier.GammaH M H

abbrev Gam' : Subgroup SL(2, ℤ) := CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)

theorem Gam'_le : Gam' M H ℓ ≤ Gam M H := inf_le_left

theorem T_mem_Gam' : ModularGroup.T ∈ Gam' M H ℓ := by
  refine Subgroup.mem_inf.mpr ⟨translation_mem_GammaH M H, ?_⟩
  rw [Gamma0_mem]
  simp [ModularGroup.T]

theorem one_mem_strictPeriods {Γ : Subgroup SL(2, ℤ)} (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples _

theorem hΓ1 : (1 : ℝ) ∈ ((Gam M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods :=
  one_mem_strictPeriods (translation_mem_GammaH M H)

theorem hΓ'1 : (1 : ℝ) ∈ ((Gam' M H ℓ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods :=
  one_mem_strictPeriods (T_mem_Gam' M H ℓ)

variable {M H ℓ}

def conjMat (ℓ : ℕ) (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![γ 0 0, (ℓ : ℤ) * γ 0 1; γ 1 0 / ℓ, γ 1 1]

theorem det_conjMat (γ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ γ 1 0) : (conjMat ℓ γ).det = 1 := by
  obtain ⟨c, hc⟩ := h
  have hdet := Matrix.SpecialLinearGroup.det_coe γ
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

def conjSL (γ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ γ 1 0) : SL(2, ℤ) := ⟨conjMat ℓ γ, det_conjMat γ h⟩

@[scoped simp] theorem conjSL_apply_00 (γ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ γ 1 0) : conjSL γ h 0 0 = γ 0 0 := rfl
@[scoped simp] theorem conjSL_apply_01 (γ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ γ 1 0) :
    conjSL γ h 0 1 = (ℓ : ℤ) * γ 0 1 := rfl
@[scoped simp] theorem conjSL_apply_10 (γ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ γ 1 0) :
    conjSL γ h 1 0 = γ 1 0 / ℓ := rfl
@[scoped simp] theorem conjSL_apply_11 (γ : SL(2, ℤ)) (h : (ℓ : ℤ) ∣ γ 1 0) : conjSL γ h 1 1 = γ 1 1 := rfl

theorem dvd_of_mem_Gamma0_mul {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (M * ℓ)) : (ℓ : ℤ) ∣ γ 1 0 := by
  rw [Gamma0_mem] at hγ
  have : ((M * ℓ : ℕ) : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  exact (show (ℓ : ℤ) ∣ ((M * ℓ : ℕ) : ℤ) from ⟨M, by push_cast; ring⟩).trans this

theorem conjSL_mem_Gamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 (M * ℓ)) (hℓ : ℓ ≠ 0) :
    conjSL γ (dvd_of_mem_Gamma0_mul hγ) ∈ Gamma0 M := by
  rw [Gamma0_mem]
  have hd : ((M * ℓ : ℕ) : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
  obtain ⟨c, hc⟩ := hd
  have hℓ' : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ
  have : (conjSL γ (dvd_of_mem_Gamma0_mul hγ)) 1 0 = M * c := by
    show γ 1 0 / ℓ = M * c
    rw [hc]; push_cast
    rw [show (M : ℤ) * ℓ * c = ℓ * (M * c) by ring]
    exact Int.mul_ediv_cancel_left _ hℓ'
  rw [this]; push_cast
  simp

theorem conjSL_mem_GammaH {γ : SL(2, ℤ)} (hγH : γ ∈ CohCarrier.GammaH M H)
    (hγ : γ ∈ Gamma0 (M * ℓ)) (hℓ : ℓ ≠ 0) :
    conjSL γ (dvd_of_mem_Gamma0_mul hγ) ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff] at hγH ⊢
  obtain ⟨hγ0, hH⟩ := hγH
  refine ⟨conjSL_mem_Gamma0 hγ hℓ, ?_⟩
  convert hH using 1
  rfl

theorem heckeDiag_mul_mul_inv {γ : SL(2, ℤ)} (h : (ℓ : ℤ) ∣ γ 1 0) (hℓ : ℓ ≠ 0) :
    heckeDiagMatrix ℓ * (γ : GL (Fin 2) ℝ) * (heckeDiagMatrix ℓ)⁻¹ =
      ((conjSL γ h : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  rw [mul_inv_eq_iff_eq_mul]
  ext i j
  obtain ⟨c, hc⟩ := h
  have hℓ' : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ
  have h10 : (conjSL γ ⟨c, hc⟩ : SL(2, ℤ)) 1 0 = c := by
    show γ 1 0 / ℓ = c
    rw [hc]; exact Int.mul_ediv_cancel_left _ hℓ'
  simp only [Matrix.GeneralLinearGroup.coe_mul, val_heckeDiagMatrix hℓ]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h10, hc] <;> ring

theorem inf_le_conj (hℓ : ℓ ≠ 0) :
    ((Gam' M H ℓ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (heckeDiagMatrix ℓ)⁻¹ • ((Gam M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  rintro x ⟨γ, hγ, rfl⟩
  obtain ⟨hγH, hγ0⟩ := Subgroup.mem_inf.mp hγ
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  exact ⟨_, conjSL_mem_GammaH hγH hγ0 hℓ, (heckeDiag_mul_mul_inv (dvd_of_mem_Gamma0_mul hγ0) hℓ).symm⟩

end Groups

section LevelRaise

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ} [NeZero ℓ]

def levelRaise {k : ℤ} (f : ModularForm ((Gam M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) :
    ModularForm ((Gam' M H ℓ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k :=
  ((ℓ : ℂ) ^ (k - 1))⁻¹ •
    restrictForm (inf_le_conj (NeZero.ne ℓ)) (ModularForm.translate f (heckeDiagMatrix ℓ))

theorem levelRaise_apply {k : ℤ} (f : ModularForm ((Gam M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (τ : ℍ) : levelRaise (ℓ := ℓ) f τ = f (heckeDiagMatrix ℓ • τ) := by
  have hℓ : (ℓ : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
  show ((ℓ : ℂ) ^ (k - 1))⁻¹ • ((⇑f ∣[k] heckeDiagMatrix ℓ) τ) = _
  rw [slash_heckeDiagMatrix_apply k (NeZero.ne ℓ), smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (zpow_ne_zero _ hℓ), one_mul]

theorem coe_levelRaise {k : ℤ} (f : ModularForm ((Gam M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) :
    ⇑(levelRaise (ℓ := ℓ) f) = fun τ => f (heckeDiagMatrix ℓ • τ) :=
  funext (levelRaise_apply f)

theorem coeff_qExpansion_levelRaise {k : ℤ}
    (f : ModularForm ((Gam M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ) :
    PowerSeries.coeff n (qExpansion 1 (levelRaise (ℓ := ℓ) f)) =
      if ℓ ∣ n then PowerSeries.coeff (n / ℓ) (qExpansion 1 f) else 0 := by
  rw [coe_levelRaise]
  exact ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul f (hΓ1 M H) (NeZero.ne ℓ) n

theorem ofPowerSeries_qExpansion_levelRaise {k : ℤ}
    (f : ModularForm ((Gam M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k) :
    ofPowerSeries ℤ ℂ (qExpansion 1 (levelRaise (ℓ := ℓ) f)) =
      qExpand ℂ ℓ (ofPowerSeries ℤ ℂ (qExpansion 1 f)) := by
  ext m
  by_cases hdvd : (ℓ : ℤ) ∣ m
  · obtain ⟨j, rfl⟩ := hdvd
    rw [qExpand_coeff_mul, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
    have hℓ0 : (0 : ℤ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
    by_cases hj : j < 0
    · rw [if_pos hj, if_pos (mul_neg_of_pos_of_neg hℓ0 hj)]
    · rw [if_neg hj, if_neg (by push Not at hj ⊢; positivity)]
      rw [coeff_qExpansion_levelRaise]
      have h1 : ((ℓ : ℤ) * j).natAbs = ℓ * j.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      rw [h1, if_pos (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne ℓ))]
  · rw [qExpand_coeff_of_not_dvd ℓ _ hdvd, PowerSeries.coeff_coe]
    split_ifs with hm
    · rfl
    · rw [coeff_qExpansion_levelRaise, if_neg]
      rintro ⟨c, hc⟩
      apply hdvd
      refine ⟨c, ?_⟩
      have : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg (le_of_not_gt hm)
      rw [← this, hc]; push_cast; ring

theorem coeffEmb_intSeriesC {F : ℍ → ℂ} {p : PowerSeries ℤ} (h : IsIntegralQExp F p) :
    coeffEmb ℂ (intSeriesC ℚ p) = ofPowerSeries ℤ ℂ (qExpansion 1 F) := by
  rw [← h]
  ext n
  simp only [coeffEmb, intSeriesC, coeffMap_coeff, PowerSeries.coeff_coe]
  split_ifs
  · exact map_zero _
  · simp [PowerSeries.coeff_map]

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) : coeffMap φ (qExpand R n x) = qExpand S n (coeffMap φ x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

def expandInt (ℓ : ℕ) (p : PowerSeries ℤ) : PowerSeries ℤ :=
  PowerSeries.mk fun n => if ℓ ∣ n then PowerSeries.coeff (n / ℓ) p else 0

omit [NeZero ℓ] in
theorem coeff_expandInt (p : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (expandInt ℓ p) = if ℓ ∣ n then PowerSeries.coeff (n / ℓ) p else 0 := by
  rw [expandInt, PowerSeries.coeff_mk]

theorem isIntegralQExp_levelRaise {k : ℤ}
    {f : ModularForm ((Gam M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k} {pf : PowerSeries ℤ}
    (hf : IsIntegralQExp f pf) : IsIntegralQExp (levelRaise (ℓ := ℓ) f) (expandInt ℓ pf) := by
  rw [isIntegralQExp_iff]
  intro n
  rw [coeff_expandInt, coeff_qExpansion_levelRaise]
  split_ifs with h
  · exact hf.coeff _
  · simp

theorem intSeriesC_expandInt (K : Type*) [Field K] (p : PowerSeries ℤ) :
    intSeriesC K (expandInt ℓ p) = qExpand K ℓ (intSeriesC K p) := by
  ext m
  simp only [intSeriesC]
  by_cases hdvd : (ℓ : ℤ) ∣ m
  · obtain ⟨j, rfl⟩ := hdvd
    rw [qExpand_coeff_mul, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
    have hℓ0 : (0 : ℤ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne ℓ)
    by_cases hj : j < 0
    · rw [if_pos hj, if_pos (mul_neg_of_pos_of_neg hℓ0 hj)]
    · rw [if_neg hj, if_neg (by push Not at hj ⊢; positivity)]
      simp only [PowerSeries.coeff_map, coeff_expandInt]
      have h1 : ((ℓ : ℤ) * j).natAbs = ℓ * j.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      rw [h1, if_pos (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne ℓ))]
  · rw [qExpand_coeff_of_not_dvd ℓ _ hdvd, PowerSeries.coeff_coe]
    split_ifs with hm
    · rfl
    · rw [PowerSeries.coeff_map, coeff_expandInt, if_neg, map_zero]
      rintro ⟨c, hc⟩
      apply hdvd
      refine ⟨c, ?_⟩
      have : (m.natAbs : ℤ) = m := Int.natAbs_of_nonneg (le_of_not_gt hm)
      rw [← this, hc]; push_cast; ring

theorem qExpand_xq_mem : qExpand ℚ ℓ xq ∈ qExpFunctionFieldC ℚ (Gam' M H ℓ) := by
  rw [xq, map_div₀, ← intSeriesC_expandInt, ← intSeriesC_expandInt]
  have h0 : intSeriesC ℚ (expandInt ℓ (P4 ^ 3)) ≠ 0 := by
    rw [intSeriesC_expandInt]
    exact fun h => intSeriesC_PA_ne_zero ℚ (qExpand_injective ℓ (by rw [h, map_zero]))
  exact div_mem_qExpFunctionFieldC (levelRaise (ℓ := ℓ) (BΓ (Gam M H))) (levelRaise (ℓ := ℓ) (AΓ (Gam M H)))
    (isIntegralQExp_levelRaise (isIntegralQExp_BΓ _)) (isIntegralQExp_levelRaise (isIntegralQExp_AΓ _)) h0

end LevelRaise

section Conjugates

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ} [Fact ℓ.Prime]

theorem coprime_M_ℓ (hℓM : ¬ ℓ ∣ M) : M.Coprime ℓ :=
  (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hℓM))

def sVal (hℓM : ¬ ℓ ∣ M) (b : ℕ) : ℕ := (Nat.chineseRemainder (coprime_M_ℓ hℓM) 1 (M * b)).val

theorem sVal_modM (hℓM : ¬ ℓ ∣ M) (b : ℕ) : sVal hℓM b ≡ 1 [MOD M] :=
  (Nat.chineseRemainder (coprime_M_ℓ hℓM) 1 (M * b)).2.1

theorem sVal_modℓ (hℓM : ¬ ℓ ∣ M) (b : ℕ) : sVal hℓM b ≡ M * b [MOD ℓ] :=
  (Nat.chineseRemainder (coprime_M_ℓ hℓM) 1 (M * b)).2.2

theorem gcd_sVal (hℓM : ¬ ℓ ∣ M) (b : ℕ) : Int.gcd (sVal hℓM b : ℤ) (M : ℤ) = 1 := by
  rw [Int.gcd_natCast_natCast, (sVal_modM hℓM b).gcd_eq, Nat.gcd_one_left]

def αC (hℓM : ¬ ℓ ∣ M) (b : ℕ) : ℤ := Int.gcdA (sVal hℓM b : ℤ) M
def βC (hℓM : ¬ ℓ ∣ M) (b : ℕ) : ℤ := Int.gcdB (sVal hℓM b : ℤ) M

theorem bezout (hℓM : ¬ ℓ ∣ M) (b : ℕ) :
    (sVal hℓM b : ℤ) * αC hℓM b + (M : ℤ) * βC hℓM b = 1 := by
  have h := Int.gcd_eq_gcd_ab (sVal hℓM b : ℤ) (M : ℤ)
  rw [gcd_sVal] at h
  exact_mod_cast h.symm

def tC (hℓM : ¬ ℓ ∣ M) (b : ℕ) : ℤ := ((sVal hℓM b : ℤ) - M * b) / ℓ

theorem ℓ_mul_tC (hℓM : ¬ ℓ ∣ M) (b : ℕ) : (ℓ : ℤ) * tC hℓM b = (sVal hℓM b : ℤ) - M * b := by
  have hd : (ℓ : ℤ) ∣ (sVal hℓM b : ℤ) - M * b := by
    have := (sVal_modℓ hℓM b).symm.dvd
    push_cast at this
    exact this
  rw [tC]
  exact Int.mul_ediv_cancel' hd

def gammaB (hℓM : ¬ ℓ ∣ M) (b : ℕ) : SL(2, ℤ) :=
  ⟨!![αC hℓM b, -βC hℓM b; (M : ℤ), (sVal hℓM b : ℤ)], by
    rw [Matrix.det_fin_two_of]
    have := bezout hℓM b
    linear_combination this⟩

def deltaB (hℓM : ¬ ℓ ∣ M) (b : ℕ) : SL(2, ℤ) :=
  ⟨!![(ℓ : ℤ) * αC hℓM b, -βC hℓM b - αC hℓM b * b; (M : ℤ), tC hℓM b], by
    rw [Matrix.det_fin_two_of]
    have h1 := bezout hℓM b
    have h2 := ℓ_mul_tC hℓM b
    linear_combination h1 + (αC hℓM b) * h2⟩

theorem gammaB_mem (hℓM : ¬ ℓ ∣ M) (b : ℕ) : gammaB hℓM b ∈ Gam M H := by
  rw [CohCarrier.mem_GammaH_iff]
  have h0 : gammaB hℓM b ∈ Gamma0 M := by
    rw [Gamma0_mem]
    show (((M : ℤ) : ℤ) : ZMod M) = 0
    simp
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨gammaB hℓM b, h0⟩ = 1 := by
    ext
    simp only [CohCarrier.gamma0Units, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_one, Gamma0Map]
    show (((sVal hℓM b : ℤ)) : ZMod M) = 1
    rw [Int.cast_natCast, ← Nat.cast_one]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (sVal_modM hℓM b)
  rw [this]
  exact one_mem H

theorem heckeDiag_mul_gammaB (hℓM : ¬ ℓ ∣ M) (b : ℕ) :
    heckeDiagMatrix ℓ * ((gammaB hℓM b : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      ((deltaB hℓM b : SL(2, ℤ)) : GL (Fin 2) ℝ) * heckeMatrix ℓ b := by
  have hℓ : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  have h2 : (ℓ : ℝ) * (tC hℓM b : ℝ) = (sVal hℓM b : ℝ) - M * b := by exact_mod_cast ℓ_mul_tC hℓM b
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, val_heckeDiagMatrix hℓ, val_heckeMatrix hℓ]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, gammaB, deltaB]
  · ring
  · linear_combination -h2

theorem heckeDiag_smul_gammaB_smul (hℓM : ¬ ℓ ∣ M) (b : ℕ) (τ : ℍ) :
    heckeDiagMatrix ℓ • ((gammaB hℓM b : SL(2, ℤ)) • τ) =
      (deltaB hℓM b : SL(2, ℤ)) • (heckeMatrix ℓ b • τ) := by
  rw [ModularGroup.sl_moeb, ModularGroup.sl_moeb, ← mul_smul, ← mul_smul, heckeDiag_mul_gammaB]

theorem coe_upperRightHom_smul (x : ℝ) (τ : ℍ) :
    (((Matrix.GeneralLinearGroup.upperRightHom x • τ : ℍ)) : ℂ) = (τ : ℂ) + x := by
  have hdet : 0 < ((Matrix.GeneralLinearGroup.upperRightHom x).det : ℝˣ).val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    simp [Matrix.det_fin_two_of]
  rw [UpperHalfPlane.coe_smul_of_det_pos hdet]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom]

theorem heckeMatrix_smul_heckeDiag_smul (b : ℕ) (τ : ℍ) :
    heckeMatrix ℓ b • (heckeDiagMatrix ℓ • τ) =
      Matrix.GeneralLinearGroup.upperRightHom ((b : ℝ) / ℓ) • τ := by
  have hℓ : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  have hℓ' : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ
  apply UpperHalfPlane.ext
  rw [coe_heckeMatrix_smul hℓ, coe_heckeDiagMatrix_smul hℓ, coe_upperRightHom_smul]
  push_cast
  field_simp

end Conjugates

section Twist

variable (ℓ : ℕ) [Fact ℓ.Prime]

def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / ℓ)

theorem zeta_ne_zero : zeta ℓ ≠ 0 := Complex.exp_ne_zero _

theorem isPrimitiveRoot_zeta : IsPrimitiveRoot (zeta ℓ) ℓ :=
  Complex.isPrimitiveRoot_exp ℓ (Fact.out : ℓ.Prime).ne_zero

def zetaU : ℂˣ := Units.mk0 (zeta ℓ) (zeta_ne_zero ℓ)

@[scoped simp] theorem val_zetaU : (zetaU ℓ : ℂ) = zeta ℓ := rfl

abbrev Ub (b : ℕ) : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.upperRightHom ((b : ℝ) / ℓ)

abbrev SLtop : Subgroup (GL (Fin 2) ℝ) := ((⊤ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem hSL1 : (1 : ℝ) ∈ (SLtop).strictPeriods := one_mem_strictPeriods (Subgroup.mem_top _)

variable {ℓ}

def twistFn {k : ℤ} (F : ModularForm SLtop k) (b : ℕ) : ℍ → ℂ := fun τ => F (Ub ℓ b • τ)

theorem twistFn_eq_translate {k : ℤ} (F : ModularForm SLtop k) (b : ℕ) :
    twistFn (ℓ := ℓ) F b = ⇑(ModularForm.translate F (Ub ℓ b)) := by
  funext τ
  rw [ModularForm.coe_translate, ModularForm.slash_apply, twistFn]
  have hdet : ((Ub ℓ b).det : ℝˣ).val = 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]; simp [Matrix.det_fin_two_of]
  have hσ : UpperHalfPlane.σ (Ub ℓ b) = .refl ℝ ℂ := by
    rw [UpperHalfPlane.σ, if_pos (by rw [hdet]; exact one_pos)]
  have hden : UpperHalfPlane.denom (Ub ℓ b) τ = 1 := by
    simp [UpperHalfPlane.denom]
  rw [hσ, hdet, hden]
  simp

theorem one_mem_strictPeriods_conj (b : ℕ) :
    (1 : ℝ) ∈ (ConjAct.toConjAct (Ub ℓ b)⁻¹ • SLtop).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ← ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]
  have hcomm : Ub ℓ b * Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) * (Ub ℓ b)⁻¹ =
      Matrix.GeneralLinearGroup.upperRightHom (1 : ℝ) := by
    rw [Ub, ← AddChar.map_add_eq_mul, ← AddChar.map_neg_eq_inv, ← AddChar.map_add_eq_mul]
    congr 1; ring
  rw [hcomm]
  exact (Subgroup.mem_strictPeriods_iff).mp (hSL1)

theorem analyticAt_twistFn {k : ℤ} (F : ModularForm SLtop k) (b : ℕ) :
    AnalyticAt ℂ (cuspFunction 1 (twistFn (ℓ := ℓ) F b)) 0 := by
  rw [twistFn_eq_translate]
  exact ModularFormClass.analyticAt_cuspFunction_zero _ one_pos (one_mem_strictPeriods_conj b)

theorem qParam_Ub_smul (b : ℕ) (τ : ℍ) :
    Function.Periodic.qParam 1 ((Ub ℓ b • τ : ℍ) : ℂ) = zeta ℓ ^ b * Function.Periodic.qParam 1 τ := by
  rw [Function.Periodic.qParam, Function.Periodic.qParam, coe_upperRightHom_smul, zeta,
    ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem coeff_qExpansion_twistFn {k : ℤ} (F : ModularForm SLtop k) (b : ℕ) (m : ℕ) :
    (qExpansion 1 (twistFn (ℓ := ℓ) F b)).coeff m = zeta ℓ ^ (b * m) * (qExpansion 1 F).coeff m := by
  haveI : Fact (IsCusp OnePoint.infty SLtop) := ⟨SLtop.isCusp_of_mem_strictPeriods one_pos hSL1⟩
  have hper := SlashInvariantFormClass.periodic_comp_ofComplex F hSL1
  have hhol := ModularFormClass.holo F
  have hbdd : IsBoundedAtImInfty (F : ℍ → ℂ) := ModularFormClass.bdd_at_infty F
  have hF : ∀ τ : ℍ, HasSum (fun n : ℕ => (zeta ℓ ^ (b * n) * (qExpansion 1 F).coeff n) •
      Function.Periodic.qParam 1 τ ^ n) (ModularForm.translate F (Ub ℓ b) τ) := by
    intro τ
    have h := hasSum_qExpansion one_pos hper hhol hbdd (Ub ℓ b • τ)
    have hfun : (fun n : ℕ => (zeta ℓ ^ (b * n) * (qExpansion 1 F).coeff n) •
        Function.Periodic.qParam 1 τ ^ n) =
        fun n : ℕ => (qExpansion 1 F).coeff n • Function.Periodic.qParam 1 ((Ub ℓ b • τ : ℍ) : ℂ) ^ n := by
      funext n
      rw [qParam_Ub_smul, mul_pow, smul_eq_mul, smul_eq_mul, ← pow_mul]
      ring
    rw [hfun]
    have he : ModularForm.translate F (Ub ℓ b) τ = F (Ub ℓ b • τ) := by
      have := congrFun (twistFn_eq_translate (ℓ := ℓ) F b) τ
      exact this.symm
    rw [he]
    exact h
  rw [twistFn_eq_translate]
  exact (ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods_conj b) hF m).symm

theorem ofPowerSeries_qExpansion_twistFn {k : ℤ} (F : ModularForm SLtop k) (b : ℕ) :
    ofPowerSeries ℤ ℂ (qExpansion 1 (twistFn (ℓ := ℓ) F b)) =
      qTwist (zetaU ℓ ^ b) (ofPowerSeries ℤ ℂ (qExpansion 1 F)) := by
  ext n
  rw [qTwist_coeff]
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [ofPowerSeries_apply_coeff, ofPowerSeries_apply_coeff, coeff_qExpansion_twistFn]
    congr 1
    rw [zpow_natCast, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, val_zetaU, ← pow_mul]
  · have h1 : (ofPowerSeries ℤ ℂ (qExpansion 1 (twistFn (ℓ := ℓ) F b))).coeff n = 0 := by
      rw [PowerSeries.coeff_coe, if_pos (lt_of_not_ge hn)]
    have h2 : (ofPowerSeries ℤ ℂ (qExpansion 1 F)).coeff n = 0 := by
      rw [PowerSeries.coeff_coe, if_pos (lt_of_not_ge hn)]
    rw [h1, h2, mul_zero]

def An1 (f : ℍ → ℂ) : Prop := AnalyticAt ℂ (cuspFunction 1 f) 0

theorem cuspFunction_one' : cuspFunction 1 (1 : ℍ → ℂ) = 1 := by
  ext q
  rcases eq_or_ne q 0 with rfl | hq
  · simp [cuspFunction, Function.Periodic.cuspFunction]
    exact Filter.Tendsto.limUnder_eq
      (tendsto_const_nhds (x := (1 : ℂ)))
  · simp [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero 1 _ hq]

theorem An1.one : An1 (1 : ℍ → ℂ) := by
  rw [An1, cuspFunction_one']; exact analyticAt_const

theorem An1.mul {f g : ℍ → ℂ} (hf : An1 f) (hg : An1 g) : An1 (f * g) := by
  rw [An1, cuspFunction_mul hf.continuousAt hg.continuousAt]
  exact AnalyticAt.mul hf hg

theorem An1.pow {f : ℍ → ℂ} (hf : An1 f) (n : ℕ) : An1 (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact An1.one
  | succ n ih => rw [pow_succ]; exact ih.mul hf

theorem qExpansion_pow' {f : ℍ → ℂ} (hf : An1 f) (n : ℕ) :
    qExpansion 1 (f ^ n) = qExpansion 1 f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, qExpansion_one]
  | succ n ih => rw [pow_succ, pow_succ, qExpansion_mul (hf.pow n) hf, ih]

theorem cuspFunction_zero' : cuspFunction 1 (0 : ℍ → ℂ) = 0 := by
  ext q
  rcases eq_or_ne q 0 with rfl | hq
  · simp [cuspFunction, Function.Periodic.cuspFunction]
    exact Filter.Tendsto.limUnder_eq
      (tendsto_const_nhds (x := (0 : ℂ)))
  · simp [cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero 1 _ hq]

theorem An1.zero : An1 (0 : ℍ → ℂ) := by
  rw [An1, cuspFunction_zero']; exact analyticAt_const

theorem An1.add {f g : ℍ → ℂ} (hf : An1 f) (hg : An1 g) : An1 (f + g) := by
  rw [An1, cuspFunction_add hf.continuousAt hg.continuousAt]
  exact AnalyticAt.add hf hg

theorem An1.sum {ι : Type*} (s : Finset ι) {f : ι → ℍ → ℂ} (hf : ∀ i ∈ s, An1 (f i)) :
    An1 (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact An1.zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem qExpansion_sum' {ι : Type*} (s : Finset ι) {f : ι → ℍ → ℂ} (hf : ∀ i ∈ s, An1 (f i)) :
    qExpansion 1 (∑ i ∈ s, f i) = ∑ i ∈ s, qExpansion 1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, qExpansion_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        qExpansion_add (hf a (Finset.mem_insert_self a s))
          (An1.sum s fun i hi => hf i (Finset.mem_insert_of_mem hi)),
        ih fun i hi => hf i (Finset.mem_insert_of_mem hi)]

end Twist

section Core

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {ℓ : ℕ} [Fact ℓ.Prime]

scoped instance instNeZeroOfPrime : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩

abbrev GamGL (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Subgroup (GL (Fin 2) ℝ) :=
  ((Gam M H : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

abbrev Gam'GL (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) : Subgroup (GL (Fin 2) ℝ) :=
  ((Gam' M H ℓ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

def qC (F : ℍ → ℂ) : LaurentSeries ℂ := ofPowerSeries ℤ ℂ (qExpansion 1 F)

def XA : LaurentSeries ℂ := qC AF
def XB : LaurentSeries ℂ := qC BF
def xC : LaurentSeries ℂ := XB / XA

theorem coeffEmb_PA : coeffEmb ℂ (intSeriesC ℚ (P4 ^ 3)) = XA := coeffEmb_intSeriesC isIntegralQExp_AF
theorem coeffEmb_PB : coeffEmb ℂ (intSeriesC ℚ (P6 ^ 2)) = XB := coeffEmb_intSeriesC isIntegralQExp_BF

theorem XA_ne_zero : XA ≠ 0 := by
  rw [← coeffEmb_PA]
  exact (map_ne_zero_iff _ (RingHom.injective _)).mpr (intSeriesC_PA_ne_zero ℚ)

theorem coeffEmb_xq : coeffEmb ℂ xq = xC := by
  rw [xq, map_div₀, coeffEmb_PA, coeffEmb_PB, xC]

theorem xC_coeff_one : xC.coeff 1 = -1728 := by
  rw [← coeffEmb_xq, coeffEmb_coeff, xq_coeff_one]
  simp

variable (M H ℓ) in

def LB : ModularForm (Gam'GL M H ℓ) 12 := levelRaise (ℓ := ℓ) (BΓ (Gam M H))
variable (M H ℓ) in
def LA : ModularForm (Gam'GL M H ℓ) 12 := levelRaise (ℓ := ℓ) (AΓ (Gam M H))

theorem LB_apply (τ : ℍ) : LB M H ℓ τ = BF (heckeDiagMatrix ℓ • τ) := levelRaise_apply _ τ
theorem LA_apply (τ : ℍ) : LA M H ℓ τ = AF (heckeDiagMatrix ℓ • τ) := levelRaise_apply _ τ

theorem qC_LB : qC (LB M H ℓ) = qExpand ℂ ℓ XB := ofPowerSeries_qExpansion_levelRaise _
theorem qC_LA : qC (LA M H ℓ) = qExpand ℂ ℓ XA := ofPowerSeries_qExpansion_levelRaise _

theorem weight_eq (k : ℤ) (i : Fin (ℓ + 1)) :
    k + ((((i : ℕ) : ℤ)) * 12 + ((ℓ - (i : ℕ) : ℕ) : ℤ) * 12) = k + 12 * ℓ := by
  have hi : (i : ℕ) ≤ ℓ := Nat.lt_succ_iff.mp i.is_lt
  push_cast [Nat.cast_sub hi]
  ring

def termF {k : ℤ} (f : Fin (ℓ + 1) → ModularForm (GamGL M H) k) (i : Fin (ℓ + 1)) :
    ModularForm (Gam'GL M H ℓ) (k + 12 * ℓ) :=
  ((restrictForm (Subgroup.map_mono (Gam'_le M H ℓ)) (f i)).mul
    (((LB M H ℓ).pow (i : ℕ)).mul ((LA M H ℓ).pow (ℓ - (i : ℕ))))).mcast (weight_eq k i)

def Phi {k : ℤ} (f : Fin (ℓ + 1) → ModularForm (GamGL M H) k) : ModularForm (Gam'GL M H ℓ) (k + 12 * ℓ) :=
  ∑ i, termF f i

theorem coe_termF {k : ℤ} (f : Fin (ℓ + 1) → ModularForm (GamGL M H) k) (i : Fin (ℓ + 1)) (τ : ℍ) :
    termF f i τ = f i τ * LB M H ℓ τ ^ (i : ℕ) * LA M H ℓ τ ^ (ℓ - (i : ℕ)) := by
  rw [termF, coe_mcast]
  simp only [coe_mul, coe_pow, Pi.mul_apply, Pi.pow_apply, coe_restrictForm]
  ring

theorem coe_finset_sum {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {ι : Type*} (s : Finset ι)
    (F : ι → ModularForm Γ k) (τ : ℍ) : (∑ i ∈ s, F i) τ = ∑ i ∈ s, F i τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.add_apply, ih]

theorem Phi_apply {k : ℤ} (f : Fin (ℓ + 1) → ModularForm (GamGL M H) k) (τ : ℍ) :
    Phi f τ = ∑ i, f i τ * LB M H ℓ τ ^ (i : ℕ) * LA M H ℓ τ ^ (ℓ - (i : ℕ)) := by
  rw [Phi, coe_finset_sum]
  simp only [coe_termF]

theorem qExpansion_finset_sum {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (hΓ : (1 : ℝ) ∈ Γ.strictPeriods)
    {ι : Type*} (s : Finset ι) (F : ι → ModularForm Γ k) :
    qExpansion 1 (⇑(∑ i ∈ s, F i)) = ∑ i ∈ s, qExpansion 1 (F i) := by
  have := map_sum (ModularForm.qExpansionAddHom one_pos hΓ k) F s
  exact this

theorem qC_termF {k : ℤ} (f : Fin (ℓ + 1) → ModularForm (GamGL M H) k) (i : Fin (ℓ + 1)) :
    qC (termF f i) = qC (f i) * qExpand ℂ ℓ XB ^ (i : ℕ) * qExpand ℂ ℓ XA ^ (ℓ - (i : ℕ)) := by
  rw [qC, termF, ModularForm.qExpansion_mcast, ModularForm.qExpansion_mul one_pos (hΓ'1 M H ℓ),
    ModularForm.qExpansion_mul one_pos (hΓ'1 M H ℓ), ModularForm.qExpansion_pow one_pos (hΓ'1 M H ℓ),
    ModularForm.qExpansion_pow one_pos (hΓ'1 M H ℓ), map_mul, map_mul, map_pow, map_pow,
    ← qC_LB (M := M) (H := H), ← qC_LA (M := M) (H := H), mul_assoc]
  rfl

theorem qC_Phi {k : ℤ} (f : Fin (ℓ + 1) → ModularForm (GamGL M H) k) :
    qC (Phi f) = ∑ i, qC (f i) * qExpand ℂ ℓ XB ^ (i : ℕ) * qExpand ℂ ℓ XA ^ (ℓ - (i : ℕ)) := by
  rw [qC, Phi, qExpansion_finset_sum (hΓ'1 M H ℓ), map_sum]
  exact Finset.sum_congr rfl fun i _ => qC_termF f i

variable (hℓM : ¬ ℓ ∣ M)

theorem Phi_eq_zero {k : ℤ} (f : Fin (ℓ + 1) → ModularForm (GamGL M H) k)
    (hrel : ∑ i, qC (f i) * qExpand ℂ ℓ XB ^ (i : ℕ) * qExpand ℂ ℓ XA ^ (ℓ - (i : ℕ)) = 0) :
    Phi f = 0 := by
  have h1 : qC (Phi f) = 0 := by rw [qC_Phi, hrel]
  have h2 : qExpansion 1 (Phi f) = 0 := by
    rw [qC, ← map_zero (ofPowerSeries ℤ ℂ)] at h1
    exact ofPowerSeries_injective h1
  exact (ModularForm.qExpansion_eq_zero_iff one_pos (hΓ'1 M H ℓ) _).mp h2

include hℓM in

theorem rel_at_heckeMatrix {k : ℤ} (f : Fin (ℓ + 1) → ModularForm (GamGL M H) k)
    (hΦ : Phi f = 0) (b : ℕ) (τ : ℍ) :
    ∑ i, f i τ * BF (heckeMatrix ℓ b • τ) ^ (i : ℕ) * AF (heckeMatrix ℓ b • τ) ^ (ℓ - (i : ℕ)) = 0 := by
  have h0 : Phi f ((gammaB hℓM b : SL(2, ℤ)) • τ) = 0 := by rw [hΦ]; rfl
  rw [Phi_apply] at h0
  set d : ℂ := UpperHalfPlane.denom (gammaB hℓM b : SL(2, ℤ)) τ with hd
  set w : ℍ := heckeMatrix ℓ b • τ with hw
  set e : ℂ := UpperHalfPlane.denom (deltaB hℓM b : SL(2, ℤ)) w with he
  have hd0 : d ≠ 0 := UpperHalfPlane.denom_ne_zero _ _
  have he0 : e ≠ 0 := UpperHalfPlane.denom_ne_zero _ _
  have hf : ∀ i, f i ((gammaB hℓM b : SL(2, ℤ)) • τ) = d ^ k * f i τ := fun i =>
    SlashInvariantForm.slash_action_eqn_SL'' (f i) (gammaB_mem hℓM b) τ
  have hB : LB M H ℓ ((gammaB hℓM b : SL(2, ℤ)) • τ) = e ^ (12 : ℤ) * BF w := by
    rw [LB_apply, heckeDiag_smul_gammaB_smul]
    exact SlashInvariantForm.slash_action_eqn_SL'' BF (Subgroup.mem_top _) w
  have hA : LA M H ℓ ((gammaB hℓM b : SL(2, ℤ)) • τ) = e ^ (12 : ℤ) * AF w := by
    rw [LA_apply, heckeDiag_smul_gammaB_smul]
    exact SlashInvariantForm.slash_action_eqn_SL'' AF (Subgroup.mem_top _) w
  simp only [hf, hB, hA] at h0
  have key : ∀ i : Fin (ℓ + 1),
      d ^ k * f i τ * (e ^ (12 : ℤ) * BF w) ^ (i : ℕ) * (e ^ (12 : ℤ) * AF w) ^ (ℓ - (i : ℕ)) =
        (d ^ k * (e ^ (12 : ℤ)) ^ ℓ) * (f i τ * BF w ^ (i : ℕ) * AF w ^ (ℓ - (i : ℕ))) := by
    intro i
    have hi : (i : ℕ) ≤ ℓ := Nat.lt_succ_iff.mp i.is_lt
    have hE : (e ^ (12 : ℤ)) ^ (i : ℕ) * (e ^ (12 : ℤ)) ^ (ℓ - (i : ℕ)) = (e ^ (12 : ℤ)) ^ ℓ := by
      rw [← _root_.pow_add, Nat.add_sub_cancel' hi]
    rw [mul_pow, mul_pow, ← hE]
    ring
  simp only [key, ← Finset.mul_sum] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exfalso
    exact mul_ne_zero (zpow_ne_zero _ hd0) (pow_ne_zero _ (zpow_ne_zero _ he0)) h
  · exact h

include hℓM in

theorem rel_twisted {k : ℤ} (f : Fin (ℓ + 1) → ModularForm (GamGL M H) k)
    (hΦ : Phi f = 0) (b : ℕ) (τ : ℍ) :
    ∑ i, levelRaise (ℓ := ℓ) (f i) τ * twistFn (ℓ := ℓ) BF b τ ^ (i : ℕ) *
      twistFn (ℓ := ℓ) AF b τ ^ (ℓ - (i : ℕ)) = 0 := by
  have := rel_at_heckeMatrix hℓM f hΦ b (heckeDiagMatrix ℓ • τ)
  rw [heckeMatrix_smul_heckeDiag_smul] at this
  simp only [levelRaise_apply]
  exact this

include hℓM in

theorem rel_qTwist {k : ℤ} (f : Fin (ℓ + 1) → ModularForm (GamGL M H) k)
    (hΦ : Phi f = 0) (b : ℕ) :
    ∑ i, qExpand ℂ ℓ (qC (f i)) * qTwist (zetaU ℓ ^ b) XB ^ (i : ℕ) *
      qTwist (zetaU ℓ ^ b) XA ^ (ℓ - (i : ℕ)) = 0 := by

  set ψ : ℍ → ℂ := ∑ i : Fin (ℓ + 1), (⇑(levelRaise (ℓ := ℓ) (f i)) * twistFn (ℓ := ℓ) BF b ^ (i : ℕ) *
    twistFn (ℓ := ℓ) AF b ^ (ℓ - (i : ℕ))) with hψ
  have hψ0 : ψ = 0 := by
    funext τ
    simp only [hψ, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, Pi.zero_apply]
    exact rel_twisted hℓM f hΦ b τ
  have hLR : ∀ i, An1 (⇑(levelRaise (ℓ := ℓ) (f i))) := fun i =>
    ModularFormClass.analyticAt_cuspFunction_zero _ one_pos (hΓ'1 M H ℓ)
  have hTB : An1 (twistFn (ℓ := ℓ) BF b) := analyticAt_twistFn BF b
  have hTA : An1 (twistFn (ℓ := ℓ) AF b) := analyticAt_twistFn AF b
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin (ℓ + 1))),
      An1 (⇑(levelRaise (ℓ := ℓ) (f i)) * twistFn (ℓ := ℓ) BF b ^ (i : ℕ) *
        twistFn (ℓ := ℓ) AF b ^ (ℓ - (i : ℕ))) := fun i _ =>
    ((hLR i).mul (hTB.pow _)).mul (hTA.pow _)
  have hq : qExpansion 1 ψ = ∑ i : Fin (ℓ + 1), qExpansion 1 (levelRaise (ℓ := ℓ) (f i)) *
      qExpansion 1 (twistFn (ℓ := ℓ) BF b) ^ (i : ℕ) * qExpansion 1 (twistFn (ℓ := ℓ) AF b) ^ (ℓ - (i : ℕ)) := by
    rw [hψ, qExpansion_sum' _ hterm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [qExpansion_mul ((hLR i).mul (hTB.pow _)) (hTA.pow _), qExpansion_mul (hLR i) (hTB.pow _),
      qExpansion_pow' hTB, qExpansion_pow' hTA]
  rw [hψ0, qExpansion_zero] at hq
  have h2 := congrArg (ofPowerSeries ℤ ℂ) hq
  rw [map_zero, map_sum] at h2
  refine Eq.trans ?_ h2.symm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, map_pow, map_pow, ofPowerSeries_qExpansion_levelRaise,
    ofPowerSeries_qExpansion_twistFn, ofPowerSeries_qExpansion_twistFn]
  rfl

theorem rel_qExpand {k : ℤ} (f : Fin (ℓ + 1) → ModularForm (GamGL M H) k)
    (hrel : ∑ i, qC (f i) * qExpand ℂ ℓ XB ^ (i : ℕ) * qExpand ℂ ℓ XA ^ (ℓ - (i : ℕ)) = 0) :
    ∑ i, qExpand ℂ ℓ (qC (f i)) * qExpand ℂ ℓ (qExpand ℂ ℓ XB) ^ (i : ℕ) *
      qExpand ℂ ℓ (qExpand ℂ ℓ XA) ^ (ℓ - (i : ℕ)) = 0 := by
  have := congrArg (qExpand ℂ ℓ) hrel
  simpa only [map_sum, map_mul, map_pow, map_zero] using this

theorem qTwist_ne_zero {u : ℂˣ} {x : LaurentSeries ℂ} (hx : x ≠ 0) : qTwist u x ≠ 0 := by
  intro h
  apply hx
  ext k
  have := congrArg (fun z : LaurentSeries ℂ => z.coeff k) h
  simp only [qTwist_coeff, HahnSeries.coeff_zero] at this
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 (Units.ne_zero _)
  · rw [h1, HahnSeries.coeff_zero]

theorem isRoot_of_rel {R : Type*} [Field R] {n : ℕ} (a : Fin (n + 1) → R) {u v : R} (hv : v ≠ 0)
    (h : ∑ i, a i * u ^ (i : ℕ) * v ^ (n - (i : ℕ)) = 0) :
    (∑ i : Fin (n + 1), Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)).IsRoot (u / v) := by
  rw [Polynomial.IsRoot, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have key : (∑ i : Fin (n + 1), a i * (u / v) ^ (i : ℕ)) * v ^ n =
      ∑ i : Fin (n + 1), a i * u ^ (i : ℕ) * v ^ (n - (i : ℕ)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.is_lt
    have hv' : v ^ n = v ^ (i : ℕ) * v ^ (n - (i : ℕ)) := by
      rw [← _root_.pow_add, Nat.add_sub_cancel' hi]
    rw [hv', div_pow]
    field_simp
  rw [h] at key
  rcases mul_eq_zero.mp key with h1 | h1
  · exact h1
  · exact absurd h1 (pow_ne_zero _ hv)

theorem coeff_sum_C_mul_X_pow {R : Type*} [Semiring R] {n : ℕ} (a : Fin (n + 1) → R) (i : Fin (n + 1)) :
    (∑ j : Fin (n + 1), Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)).coeff (i : ℕ) = a i := by
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
  · intro j _ hji
    rw [if_neg]
    exact fun h => hji (Fin.ext h.symm)
  · intro h; exact absurd (Finset.mem_univ i) h

theorem natDegree_sum_le {R : Type*} [Semiring R] {n : ℕ} (a : Fin (n + 1) → R) :
    (∑ j : Fin (n + 1), Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)).natDegree ≤ n := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp j.is_lt)

theorem not_dvd_one : ¬ ((ℓ : ℤ) ∣ 1) := by
  intro h
  have : ℓ ∣ 1 := Int.natCast_dvd_natCast.mp (by simpa using h)
  exact (Fact.out : ℓ.Prime).one_lt.ne' (Nat.dvd_one.mp this)

include hℓM in

theorem core {k : ℤ} (f : Fin (ℓ + 1) → ModularForm (GamGL M H) k)
    (hrel : ∑ i, qC (f i) * qExpand ℂ ℓ XB ^ (i : ℕ) * qExpand ℂ ℓ XA ^ (ℓ - (i : ℕ)) = 0) :
    ∀ i, f i = 0 := by
  classical
  have hΦ := Phi_eq_zero f hrel

  set a : Fin (ℓ + 1) → LaurentSeries ℂ := fun i => qExpand ℂ ℓ (qC (f i)) with ha
  set Q : Polynomial (LaurentSeries ℂ) := ∑ i : Fin (ℓ + 1), Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)
    with hQ

  set r : ℕ → LaurentSeries ℂ := fun b => qTwist (zetaU ℓ ^ b) xC with hr
  set rinf : LaurentSeries ℂ := qExpand ℂ ℓ (qExpand ℂ ℓ xC) with hrinf
  have hroot_r : ∀ b, Q.IsRoot (r b) := by
    intro b
    have h := rel_qTwist hℓM f hΦ b
    have hv : qTwist (zetaU ℓ ^ b) XA ≠ 0 := qTwist_ne_zero XA_ne_zero
    have := isRoot_of_rel a hv h
    rwa [← map_div₀] at this
  have hroot_inf : Q.IsRoot rinf := by
    have h := rel_qExpand f hrel
    have hv : qExpand ℂ ℓ (qExpand ℂ ℓ XA) ≠ 0 := fun h0 =>
      XA_ne_zero (qExpand_injective ℓ (qExpand_injective ℓ (by rw [h0, map_zero, map_zero])))
    have := isRoot_of_rel a hv h
    rwa [← map_div₀, ← map_div₀] at this

  have hcoef_r : ∀ b, (r b).coeff 1 = zeta ℓ ^ b * (-1728) := by
    intro b
    rw [hr]
    simp only [qTwist_coeff, zpow_one, Units.val_pow_eq_pow_val, val_zetaU, xC_coeff_one]
  have hcoef_inf : rinf.coeff 1 = 0 := qExpand_coeff_of_not_dvd ℓ _ not_dvd_one
  have hz : ∀ b, zeta ℓ ^ b * (-1728) ≠ 0 := fun b =>
    mul_ne_zero (pow_ne_zero _ (zeta_ne_zero ℓ)) (by norm_num)

  set Z : Finset (LaurentSeries ℂ) := insert rinf ((Finset.range ℓ).image r) with hZ
  have hinj : Set.InjOn r (Finset.range ℓ : Set ℕ) := by
    intro b hb b' hb' hbb
    have h1 := congrArg (fun z : LaurentSeries ℂ => z.coeff 1) hbb
    simp only [hcoef_r] at h1
    have h2 : zeta ℓ ^ b = zeta ℓ ^ b' := mul_right_cancel₀ (by norm_num : (-1728 : ℂ) ≠ 0) h1
    exact (isPrimitiveRoot_zeta ℓ).pow_inj (Finset.mem_range.mp hb) (Finset.mem_range.mp hb') h2
  have hnot : rinf ∉ (Finset.range ℓ).image r := by
    intro hmem
    obtain ⟨b, -, hb⟩ := Finset.mem_image.mp hmem
    have := congrArg (fun z : LaurentSeries ℂ => z.coeff 1) hb
    simp only [hcoef_r, hcoef_inf] at this
    exact hz b this
  have hcard : Z.card = ℓ + 1 := by
    rw [hZ, Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn hinj, Finset.card_range]

  have hQ0 : Q = 0 := by
    by_contra hQ0
    have hsub : Z.val ⊆ Q.roots := by
      intro z hz'
      rw [Polynomial.mem_roots hQ0]
      have hz'' : z ∈ Z := hz'
      rw [hZ, Finset.mem_insert, Finset.mem_image] at hz''
      rcases hz'' with rfl | ⟨b, -, rfl⟩
      · exact hroot_inf
      · exact hroot_r b
    have h1 := Polynomial.card_le_degree_of_subset_roots hsub
    have h2 : Q.natDegree ≤ ℓ := natDegree_sum_le a
    rw [hcard] at h1
    omega

  intro i
  have hai : qExpand ℂ ℓ (qC (f i)) = 0 := by
    have := coeff_sum_C_mul_X_pow a i
    rw [← hQ, hQ0, Polynomial.coeff_zero] at this
    exact this.symm
  have hq : qC (f i) = 0 := qExpand_injective ℓ (by rw [map_zero, hai])
  have hq' : qExpansion 1 (f i) = 0 := by
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
    rw [map_zero]
    exact hq
  exact (ModularForm.qExpansion_eq_zero_iff one_pos (hΓ1 M H) _).mp hq'

end Core

section Ratio

variable {M : ℕ} {H : Subgroup (ZMod M)ˣ}

theorem intSeriesC_add' {K : Type*} [Field K] (p p' : PowerSeries ℤ) :
    intSeriesC K (p + p') = intSeriesC K p + intSeriesC K p' := by
  simp [intSeriesC]

theorem intSeriesC_neg' {K : Type*} [Field K] (p : PowerSeries ℤ) :
    intSeriesC K (-p) = -intSeriesC K p := by
  simp [intSeriesC]

variable (M H)

abbrev S : Set (LaurentSeries ℚ) := intFormRatiosC ℚ (CohCarrier.GammaH M H)

variable {M H}

theorem isIntegralQExp_mul {k₁ k₂ : ℤ} {f : ModularForm (GamGL M H) k₁} {g : ModularForm (GamGL M H) k₂}
    {pf pg : PowerSeries ℤ} (hf : IsIntegralQExp f pf) (hg : IsIntegralQExp g pg) :
    IsIntegralQExp (f.mul g) (pf * pg) := by
  rw [IsIntegralQExp, map_mul, hf, hg, ModularForm.coe_mul]
  exact (ModularForm.qExpansion_mul_coe one_pos (hΓ1 M H) f g).symm

theorem mul_mem_S {a b : LaurentSeries ℚ} (ha : a ∈ S M H) (hb : b ∈ S M H) : a * b ∈ S M H := by
  obtain ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, hg₁0, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, rfl⟩ := hb
  refine ⟨k₁ + k₂, f₁.mul f₂, g₁.mul g₂, pf₁ * pf₂, pg₁ * pg₂, isIntegralQExp_mul hf₁ hf₂,
    isIntegralQExp_mul hg₁ hg₂, ?_, ?_⟩
  · rw [intSeriesC_mul]; exact mul_ne_zero hg₁0 hg₂0
  · rw [intSeriesC_mul, intSeriesC_mul, div_mul_div_comm]

theorem add_mem_S {a b : LaurentSeries ℚ} (ha : a ∈ S M H) (hb : b ∈ S M H) : a + b ∈ S M H := by
  obtain ⟨k₁, f₁, g₁, pf₁, pg₁, hf₁, hg₁, hg₁0, rfl⟩ := ha
  obtain ⟨k₂, f₂, g₂, pf₂, pg₂, hf₂, hg₂, hg₂0, rfl⟩ := hb
  refine ⟨k₁ + k₂, f₁.mul g₂ + (g₁.mul f₂), g₁.mul g₂, pf₁ * pg₂ + pg₁ * pf₂, pg₁ * pg₂, ?_,
    isIntegralQExp_mul hg₁ hg₂, ?_, ?_⟩
  · rw [IsIntegralQExp, map_add, map_mul, map_mul, hf₁, hf₂, hg₁, hg₂, ModularForm.coe_add,
      ModularForm.qExpansion_add one_pos (hΓ1 M H), ModularForm.coe_mul, ModularForm.coe_mul,
      ModularForm.qExpansion_mul_coe one_pos (hΓ1 M H),
      ModularForm.qExpansion_mul_coe one_pos (hΓ1 M H)]
  · rw [intSeriesC_mul]; exact mul_ne_zero hg₁0 hg₂0
  · rw [intSeriesC_add', intSeriesC_mul, intSeriesC_mul, intSeriesC_mul, div_add_div _ _ hg₁0 hg₂0]

theorem neg_mem_S {a : LaurentSeries ℚ} (ha : a ∈ S M H) : -a ∈ S M H := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := ha
  refine ⟨k, -f, g, -pf, pg, ?_, hg, hg0, ?_⟩
  · rw [IsIntegralQExp, map_neg, hf, ModularForm.coe_neg]
    exact (ModularForm.qExpansion_neg one_pos (hΓ1 M H) f).symm
  · rw [intSeriesC_neg', neg_div]

theorem inv_mem_S {a : LaurentSeries ℚ} (ha : a ∈ S M H) : a⁻¹ ∈ S M H := by
  obtain ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩ := ha
  by_cases hf0 : intSeriesC ℚ pf = 0
  · rw [hf0, zero_div, _root_.inv_zero, ← zero_div (intSeriesC ℚ pg), ← hf0]
    exact ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
  · refine ⟨k, g, f, pg, pf, hg, hf, hf0, ?_⟩
    rw [inv_div]

theorem coe_const_eq_smul_one (c : ℂ) :
    ((ModularForm.const c : ModularForm (GamGL M H) 0) : ℍ → ℂ) =
      c • ((1 : ModularForm (GamGL M H) 0) : ℍ → ℂ) := by
  funext z
  rw [Pi.smul_apply, ModularForm.const_apply, ModularForm.one_coe_eq_one, Pi.one_apply, smul_eq_mul,
    mul_one]

theorem isIntegralQExp_const (n : ℤ) :
    IsIntegralQExp ((ModularForm.const (n : ℂ) : ModularForm (GamGL M H) 0) : ℍ → ℂ) (PowerSeries.C n) := by
  rw [IsIntegralQExp, PowerSeries.map_C, coe_const_eq_smul_one,
    ModularForm.qExpansion_smul one_pos (hΓ1 M H), ModularForm.qExpansion_one,
    PowerSeries.smul_eq_C_mul, mul_one, eq_intCast]

theorem algebraMap_mem_S (c : ℚ) : algebraMap ℚ (LaurentSeries ℚ) c ∈ S M H := by
  have hden : ((c.den : ℤ) : ℚ) ≠ 0 := by exact_mod_cast c.den_nz
  refine ⟨0, ModularForm.const (c.num : ℂ), ModularForm.const (c.den : ℂ),
    PowerSeries.C (c.num : ℤ), PowerSeries.C (c.den : ℤ), isIntegralQExp_const _, ?_, ?_, ?_⟩
  · have := isIntegralQExp_const (M := M) (H := H) (c.den : ℤ)
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

variable (M H) in

def SField : IntermediateField ℚ (LaurentSeries ℚ) where
  carrier := S M H
  mul_mem' ha hb := mul_mem_S ha hb
  one_mem' := by simpa using algebraMap_mem_S (M := M) (H := H) 1
  add_mem' ha hb := add_mem_S ha hb
  zero_mem' := by simpa using algebraMap_mem_S (M := M) (H := H) 0
  algebraMap_mem' c := algebraMap_mem_S c
  inv_mem' a ha := inv_mem_S ha

theorem mem_S_of_mem {y : LaurentSeries ℚ} (hy : y ∈ qExpFunctionFieldC ℚ (Gam M H)) : y ∈ S M H := by
  have hle : qExpFunctionFieldC ℚ (Gam M H) ≤ SField M H :=
    IntermediateField.adjoin_le_iff.mpr (fun _ h => h)
  exact hle hy

theorem common_denominator (n : ℕ) (c : Fin n → LaurentSeries ℚ) (hc : ∀ i, c i ∈ S M H) :
    ∃ (k : ℤ) (g : ModularForm (GamGL M H) k) (pg : PowerSeries ℤ) (f : Fin n → ModularForm (GamGL M H) k)
      (pf : Fin n → PowerSeries ℤ), IsIntegralQExp g pg ∧ intSeriesC ℚ pg ≠ 0 ∧
        ∀ i, IsIntegralQExp (f i) (pf i) ∧ c i * intSeriesC ℚ pg = intSeriesC ℚ (pf i) := by
  induction n with
  | zero =>
      refine ⟨0, 1, 1, Fin.elim0, Fin.elim0, ?_, by simp, fun i => Fin.elim0 i⟩
      show IsIntegralQExp (⇑(1 : ModularForm (GamGL M H) 0)) 1
      rw [ModularForm.one_coe_eq_one]; exact isIntegralQExp_one
  | succ n ih =>
      obtain ⟨k, g, pg, f, pf, hg, hg0, hf⟩ := ih (Fin.tail c) (fun i => hc i.succ)
      obtain ⟨k₀, f₀, g₀, pf₀, pg₀, hf₀, hg₀, hg₀0, hc0⟩ := hc 0
      refine ⟨k₀ + k, g₀.mul g, pg₀ * pg, Fin.cons (f₀.mul g) (fun i => g₀.mul (f i)),
        Fin.cons (pf₀ * pg) (fun i => pg₀ * pf i), isIntegralQExp_mul hg₀ hg, ?_, ?_⟩
      · rw [intSeriesC_mul]; exact mul_ne_zero hg₀0 hg0
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero]
          refine ⟨isIntegralQExp_mul hf₀ hg, ?_⟩
          rw [hc0, intSeriesC_mul, intSeriesC_mul]
          field_simp
        · simp only [Fin.cons_succ]
          refine ⟨isIntegralQExp_mul hg₀ (hf j).1, ?_⟩
          have h2 : c j.succ * intSeriesC ℚ pg = intSeriesC ℚ (pf j) := (hf j).2
          rw [intSeriesC_mul, intSeriesC_mul, ← h2]
          ring

end Ratio

section Final

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)

theorem rel_of_rat_rel {n : ℕ} {k : ℤ} (f : Fin (n + 1) → ModularForm (GamGL M H) k)
    (pf : Fin (n + 1) → PowerSeries ℤ) (hf : ∀ i, IsIntegralQExp (f i) (pf i))
    (h : ∑ i, intSeriesC ℚ (pf i) * qExpand ℚ ℓ (intSeriesC ℚ (P6 ^ 2)) ^ (i : ℕ) *
      qExpand ℚ ℓ (intSeriesC ℚ (P4 ^ 3)) ^ (n - (i : ℕ)) = 0) :
    ∑ i, qC (f i) * qExpand ℂ ℓ XB ^ (i : ℕ) * qExpand ℂ ℓ XA ^ (n - (i : ℕ)) = 0 := by
  have := congrArg (coeffEmb ℂ) h
  rw [map_zero, map_sum] at this
  refine Eq.trans ?_ this
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, map_pow, map_pow, coeffEmb, coeffMap_qExpand, coeffMap_qExpand]
  change _ = coeffEmb ℂ _ * qExpand ℂ ℓ (coeffEmb ℂ _) ^ _ * qExpand ℂ ℓ (coeffEmb ℂ _) ^ _
  rw [coeffEmb_intSeriesC (hf i), coeffEmb_PA, coeffEmb_PB]
  rfl

include hℓM in

theorem linearIndependent_pow_y :
    LinearIndependent (qExpFunctionFieldC ℚ (Gam M H))
      (fun i : Fin (ℓ + 1) => (⟨qExpand ℚ ℓ xq ^ (i : ℕ), pow_mem qExpand_xq_mem _⟩ :
        extendScalars (F := qExpFunctionFieldC ℚ (Gam M H))
          (E := qExpFunctionFieldC ℚ (Gam' M H ℓ)) (qExpFunctionFieldC_mono ℚ (Gam'_le M H ℓ)))) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i₀

  have hrelQ : ∑ i, ((g i : qExpFunctionFieldC ℚ (Gam M H)) : LaurentSeries ℚ) *
      qExpand ℚ ℓ xq ^ (i : ℕ) = 0 := by
    have := congrArg (fun z : extendScalars (F := qExpFunctionFieldC ℚ (Gam M H))
      (E := qExpFunctionFieldC ℚ (Gam' M H ℓ)) (qExpFunctionFieldC_mono ℚ (Gam'_le M H ℓ)) =>
        ((z : qExpFunctionFieldC ℚ (Gam' M H ℓ)) : LaurentSeries ℚ)) hg
    simp at this
    exact this

  obtain ⟨k, gF, pg, f, pf, hgF, hg0, hf⟩ :=
    common_denominator (M := M) (H := H) (ℓ + 1) (fun i => ((g i : qExpFunctionFieldC ℚ (Gam M H)) :
      LaurentSeries ℚ)) (fun i => mem_S_of_mem (g i).2)

  have hrel1 : ∑ i, intSeriesC ℚ (pf i) * qExpand ℚ ℓ xq ^ (i : ℕ) = 0 := by
    have := congrArg (· * intSeriesC ℚ pg) hrelQ
    simp only [zero_mul, Finset.sum_mul] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← (hf i).2]; ring

  have hYA : qExpand ℚ ℓ (intSeriesC ℚ (P4 ^ 3)) ≠ 0 := fun h0 =>
    intSeriesC_PA_ne_zero ℚ (qExpand_injective ℓ (by rw [h0, map_zero]))
  have hrel2 : ∑ i, intSeriesC ℚ (pf i) * qExpand ℚ ℓ (intSeriesC ℚ (P6 ^ 2)) ^ (i : ℕ) *
      qExpand ℚ ℓ (intSeriesC ℚ (P4 ^ 3)) ^ (ℓ - (i : ℕ)) = 0 := by
    have key : (∑ i : Fin (ℓ + 1), intSeriesC ℚ (pf i) * qExpand ℚ ℓ xq ^ (i : ℕ)) *
        qExpand ℚ ℓ (intSeriesC ℚ (P4 ^ 3)) ^ ℓ =
        ∑ i : Fin (ℓ + 1), intSeriesC ℚ (pf i) * qExpand ℚ ℓ (intSeriesC ℚ (P6 ^ 2)) ^ (i : ℕ) *
          qExpand ℚ ℓ (intSeriesC ℚ (P4 ^ 3)) ^ (ℓ - (i : ℕ)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi : (i : ℕ) ≤ ℓ := Nat.lt_succ_iff.mp i.is_lt
      have hv' : qExpand ℚ ℓ (intSeriesC ℚ (P4 ^ 3)) ^ ℓ =
          qExpand ℚ ℓ (intSeriesC ℚ (P4 ^ 3)) ^ (i : ℕ) * qExpand ℚ ℓ (intSeriesC ℚ (P4 ^ 3)) ^ (ℓ - (i : ℕ)) := by
        rw [← _root_.pow_add, Nat.add_sub_cancel' hi]
      rw [xq, map_div₀, hv', div_pow]
      field_simp
    rw [hrel1, zero_mul] at key
    exact key.symm

  have hrelC := rel_of_rat_rel M H f pf (fun i => (hf i).1) hrel2
  have hfi := core hℓM f hrelC i₀

  have h1 : intSeriesC ℚ (pf i₀) = 0 := by
    have h2 : coeffEmb ℂ (intSeriesC ℚ (pf i₀)) = 0 := by
      rw [coeffEmb_intSeriesC (hf i₀).1, hfi, ModularForm.coe_zero, qExpansion_zero, map_zero]
    exact (map_eq_zero_iff _ (RingHom.injective _)).mp h2
  have h3 : ((g i₀ : qExpFunctionFieldC ℚ (Gam M H)) : LaurentSeries ℚ) = 0 := by
    have := (hf i₀).2
    rw [h1] at this
    exact (mul_eq_zero.mp this).resolve_right hg0
  exact_mod_cast h3

end Final

end LeRelrankSol
p2m_reactivate "P2MW.S_ModularCurve_le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd.LeRelrankSol"

theorem solution (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M) :
    ((ℓ + 1 : ℕ) : Cardinal) ≤
      IntermediateField.relrank (ModularCurve.xHFunctionField M H)
        (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)) := by
  have hle : ModularCurve.xHFunctionField M H ≤ ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ) :=
    ModularCurve.xHFunctionFieldC_le_top ℚ M H (M * ℓ)
  rw [IntermediateField.relrank_eq_rank_of_le hle]
  have h := (LeRelrankSol.linearIndependent_pow_y M H hℓM).cardinal_le_rank
  rw [Cardinal.mk_fin] at h
  exact h

end
p2m_reactivate "P2MW.S_ModularCurve_le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd.LeRelrankSol"

end S_ModularCurve_le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_le_relrank_xHFunctionField_xHTopFunctionFieldC_of_not_dvd (solution)
