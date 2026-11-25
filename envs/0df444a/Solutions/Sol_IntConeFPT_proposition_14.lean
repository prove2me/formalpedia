-- Prove2me | solution 1 for IntConeFPT.proposition_14
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ohnesorgefelix
-- created : 2026-11-25T11:53:32.440384+00:00
-- url     : https://prove2.me/submissions/f4b12307-11a9-4ebe-9265-92d8824e9bf1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_IntConeFPT_counted_grid
import Theorems.Thm_IntConeFPT_counted_threshold_search
import Theorems.Thm_IntConeFPT_threshold_bisection_machine
import Theorems.Thm_IntConeFPT_section_3_6_nstar_bound
open IntConeFPT OnlineCRS.Combine
namespace IntConeFPT.BudgetOptimize
lemma one_le_tau_logb {τ : ℕ} (hτ : 1 ≤ τ) :
    (1 : ℝ) ≤ (τ : ℝ) * Real.logb 2 ((τ : ℝ) + 1) := by
  have hτR : (1 : ℝ) ≤ (τ : ℝ) := by exact_mod_cast hτ
  have hlog : (1 : ℝ) ≤ Real.logb 2 ((τ : ℝ) + 1) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by linarith)]
    linarith [Real.rpow_one (2 : ℝ)]
  nlinarith

lemma nat_le_two_rpow (n : ℕ) : (n : ℝ) ≤ (2 : ℝ) ^ (n : ℝ) := by
  rw [Real.rpow_natCast]
  exact_mod_cast Nat.le_of_lt Nat.lt_two_pow_self

lemma fptBound_mono_L {C τ d L₁ L₂ : ℕ} (hL : L₁ ≤ L₂) :
    fptBound C τ d L₁ ≤ fptBound C τ d L₂ := by
  unfold fptBound
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hL) C

lemma fptBound_nonneg (C τ d L : ℕ) : 0 ≤ fptBound C τ d L := by
  unfold fptBound
  positivity

lemma exp_factor_bound {C_p14 C_drv k₁ C d : ℕ} {α : ℝ}
    (hd1 : 1 ≤ d) (hα1 : 1 ≤ α) (hC : C_p14 + C_drv + k₁ + 4 ≤ C) :
    ((2 : ℝ) ^ (α * (2 : ℝ) ^ ((C_p14 : ℝ) * d))) ^ C_drv * (2 : ℝ) ^ (k₁ * d) ≤
      (2 : ℝ) ^ (α * (2 : ℝ) ^ ((C : ℝ) * d)) := by
  have hα0 : 0 ≤ α := le_trans zero_le_one hα1
  have hdR : (1 : ℝ) ≤ (d : ℝ) := Nat.one_le_cast.mpr hd1
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := le_trans zero_le_one hdR
  have hF_pow : ((2 : ℝ) ^ (α * (2 : ℝ) ^ ((C_p14 : ℝ) * d))) ^ C_drv =
      (2 : ℝ) ^ ((C_drv : ℝ) * (α * (2 : ℝ) ^ ((C_p14 : ℝ) * d))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have h2_pow : ((2 : ℝ) ^ (k₁ * d)) = (2 : ℝ) ^ (((k₁ * d : ℕ) : ℝ)) :=
    (Real.rpow_natCast 2 (k₁ * d)).symm
  rw [hF_pow, h2_pow, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hd_le_2d : (d : ℝ) ≤ (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d) := by
    calc (d : ℝ) ≤ (2 : ℝ) ^ (d : ℝ) := nat_le_two_rpow d
      _ ≤ (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d) := by
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          calc (d : ℝ) = 1 * (d : ℝ) := (one_mul _).symm
            _ ≤ ((C_p14 : ℝ) + 1) * (d : ℝ) :=
                mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) C_p14]) hd0
  have h2d_mono : (2 : ℝ) ^ ((C_p14 : ℝ) * d) ≤ (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    exact mul_le_mul_of_nonneg_right (by linarith) hd0
  have hKd : ((k₁ * d : ℕ) : ℝ) ≤ α * ((k₁ : ℝ) * (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d)) := by
    calc ((k₁ * d : ℕ) : ℝ) = 1 * ((k₁ : ℝ) * (d : ℝ)) := by push_cast; ring
      _ ≤ α * ((k₁ : ℝ) * (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d)) :=
          mul_le_mul hα1 (mul_le_mul_of_nonneg_left hd_le_2d (Nat.cast_nonneg _))
            (by positivity) hα0
  have hCd : (C_drv : ℝ) * (α * (2 : ℝ) ^ ((C_p14 : ℝ) * d)) ≤
      α * ((C_drv : ℝ) * (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d)) := by
    calc (C_drv : ℝ) * (α * (2 : ℝ) ^ ((C_p14 : ℝ) * d))
      _ = ((C_drv : ℝ) * α) * (2 : ℝ) ^ ((C_p14 : ℝ) * d) := by ring
      _ ≤ ((C_drv : ℝ) * α) * (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d) :=
          mul_le_mul_of_nonneg_left h2d_mono (mul_nonneg (Nat.cast_nonneg _) hα0)
      _ = α * ((C_drv : ℝ) * (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d)) := by ring
  have hCoef : (C_drv : ℝ) + (k₁ : ℝ) ≤ (2 : ℝ) ^ ((C_drv + k₁ + 1 : ℕ) : ℝ) := by
    have h := nat_le_two_rpow (C_drv + k₁ + 1)
    have hcast : ((C_drv + k₁ + 1 : ℕ) : ℝ) = (C_drv : ℝ) + (k₁ : ℝ) + 1 := by push_cast; ring
    linarith
  have hExpC : (2 : ℝ) ^ ((C_drv + k₁ + 1 : ℕ) : ℝ) * (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d) ≤
      (2 : ℝ) ^ ((C : ℝ) * d) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hC_geR : ((C_p14 + C_drv + k₁ + 4 : ℕ) : ℝ) ≤ (C : ℝ) := Nat.cast_le.mpr hC
    have hcast1 : ((C_drv + k₁ + 1 : ℕ) : ℝ) = (C_drv : ℝ) + (k₁ : ℝ) + 1 := by push_cast; ring
    have hcast2 : ((C_p14 + C_drv + k₁ + 4 : ℕ) : ℝ) =
        (C_p14 : ℝ) + (C_drv : ℝ) + (k₁ : ℝ) + 4 := by push_cast; ring
    rw [hcast1]
    rw [hcast2] at hC_geR
    have h1d : ((C_drv : ℝ) + (k₁ : ℝ) + 1) ≤ ((C_drv : ℝ) + (k₁ : ℝ) + 1) * (d : ℝ) :=
      le_mul_of_one_le_right (by positivity) hdR
    calc ((C_drv : ℝ) + (k₁ : ℝ) + 1) + ((C_p14 : ℝ) + 1) * (d : ℝ)
      _ ≤ ((C_drv : ℝ) + (k₁ : ℝ) + 1) * (d : ℝ) + ((C_p14 : ℝ) + 1) * (d : ℝ) := by linarith [h1d]
      _ = ((C_p14 : ℝ) + (C_drv : ℝ) + (k₁ : ℝ) + 2) * (d : ℝ) := by ring
      _ ≤ (C : ℝ) * (d : ℝ) := mul_le_mul_of_nonneg_right (by linarith) hd0
  calc (C_drv : ℝ) * (α * (2 : ℝ) ^ ((C_p14 : ℝ) * d)) + ((k₁ * d : ℕ) : ℝ)
    _ ≤ α * ((C_drv : ℝ) * (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d)) +
          α * ((k₁ : ℝ) * (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d)) := add_le_add hCd hKd
    _ = α * (((C_drv : ℝ) + (k₁ : ℝ)) * (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d)) := by ring
    _ ≤ α * ((2 : ℝ) ^ ((C_drv + k₁ + 1 : ℕ) : ℝ) * (2 : ℝ) ^ ((C_p14 + 1 : ℝ) * d)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hCoef (by positivity)) hα0
    _ ≤ α * (2 : ℝ) ^ ((C : ℝ) * d) :=
        mul_le_mul_of_nonneg_left hExpC hα0

lemma fptBound_absorb (C_box C_p14 C_drv : ℕ) :
    ∃ C : ℕ, ∀ {τ d L LM LN L₀ LHom : ℕ},
      1 ≤ d → 1 ≤ τ → 1 ≤ L → τ ≤ L →
      LM ≤ L ^ C_box →
      LN ≤ 64 * (τ * 2 ^ d) ^ 3 * (L + LM) ^ 2 →
      L₀ = L + LN + 1 →
      LHom ≤ L₀ →
      (((L + LM + LN +
          (L : ℝ) ^ C_box + fptBound C_p14 τ d L₀ + fptBound C_p14 τ d LHom + 2 : ℝ)) ^ C_drv) ≤
        fptBound C τ d L := by
  set E₁ : ℕ := 2 * C_box + 5
  set E₂ : ℕ := E₁ * (C_p14 + 1)
  set K₁ : ℕ := (12 * C_p14 + 15) * (C_drv + 1)
  set C : ℕ := max (E₂ * C_drv) (C_p14 + C_drv + K₁ + 4)
  refine ⟨C, fun {τ d L LM LN L₀ LHom} hd1 hτ1 hL1 hτL hMlen hNlen hL₀_eq hLHom_le => ?_⟩
  have hE₁_ge1 : 1 ≤ E₁ := by omega
  have hE₂_ge1 : 1 ≤ E₂ := Nat.mul_pos hE₁_ge1 (Nat.succ_pos _)
  have hE₂_ge_box : C_box ≤ E₂ := by
    calc C_box ≤ E₁ := by omega
      _ = E₁ * 1 := (Nat.mul_one E₁).symm
      _ ≤ E₁ * (C_p14 + 1) := Nat.mul_le_mul_left E₁ (Nat.succ_pos _)
  have hE₂_ge_E₁ : E₁ ≤ E₂ := by
    calc E₁ = E₁ * 1 := (Nat.mul_one E₁).symm
      _ ≤ E₁ * (C_p14 + 1) := Nat.mul_le_mul_left E₁ (Nat.succ_pos _)
  have hE₂_ge_mul : E₁ * C_p14 ≤ E₂ :=
    Nat.mul_le_mul_left E₁ (Nat.le_succ C_p14)
  have hLN_bound : LN ≤ 2 ^ (3 * d + 8) * L ^ E₁ := by
    have hL_pow1 : L ≤ L ^ (C_box + 1) := by
      simpa using Nat.pow_le_pow_right hL1 (Nat.le_add_left 1 C_box)
    have hM_pow : LM ≤ L ^ (C_box + 1) :=
      le_trans hMlen (Nat.pow_le_pow_right hL1 (Nat.le_succ C_box))
    have hsum_sq : (L + LM) ^ 2 ≤ 4 * L ^ (2 * C_box + 2) := by
      calc (L + LM) ^ 2
        _ ≤ (2 * L ^ (C_box + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = 4 * L ^ (2 * C_box + 2) := by ring
    have hs3 : (τ * 2 ^ d) ^ 3 ≤ L ^ 3 * 2 ^ (3 * d) := by
      calc (τ * 2 ^ d) ^ 3 = τ ^ 3 * 2 ^ (3 * d) := by ring
        _ ≤ L ^ 3 * 2 ^ (3 * d) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hτL 3)
    calc LN
      _ ≤ 64 * (τ * 2 ^ d) ^ 3 * (L + LM) ^ 2 := hNlen
      _ ≤ 64 * (L ^ 3 * 2 ^ (3 * d)) * (4 * L ^ (2 * C_box + 2)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 64 hs3) hsum_sq
      _ = 2 ^ (3 * d + 8) * L ^ E₁ := by
          have h64 : (64 : ℕ) * 4 = 2 ^ 8 := by decide
          calc 64 * (L ^ 3 * 2 ^ (3 * d)) * (4 * L ^ (2 * C_box + 2))
            _ = (2 ^ (3 * d) * (64 * 4)) * (L ^ 3 * L ^ (2 * C_box + 2)) := by ring
            _ = 2 ^ (3 * d + 8) * L ^ E₁ := by
                rw [h64, ← pow_add, ← pow_add]
                congr 2
                omega
  have hL₀_len : L₀ ≤ 2 ^ (3 * d + 9) * L ^ E₁ := by
    have hLE1 : L + 1 ≤ 2 * L ^ E₁ := by
      have : 1 ≤ L ^ E₁ := Nat.one_le_pow E₁ L hL1
      have : L ≤ L ^ E₁ := by simpa using Nat.pow_le_pow_right hL1 hE₁_ge1
      omega
    have h2pos : 2 ≤ 2 ^ (3 * d + 8) :=
      le_trans (by decide) (Nat.pow_le_pow_right (by omega) (by omega) : 2 ^ 1 ≤ 2 ^ (3 * d + 8))
    have hp9 : 2 ^ (3 * d + 9) = 2 * 2 ^ (3 * d + 8) := by
      rw [show 3 * d + 9 = (3 * d + 8) + 1 by omega, pow_succ, mul_comm]
    rw [hL₀_eq, hp9]
    nlinarith
  set α : ℝ := (τ : ℝ) * Real.logb 2 ((τ : ℝ) + 1)
  have hα1 : 1 ≤ α := one_le_tau_logb hτ1
  have hα0 : 0 ≤ α := by linarith
  set F₀ : ℝ := (2 : ℝ) ^ (α * (2 : ℝ) ^ ((C_p14 : ℝ) * d))
  have hF₀1 : 1 ≤ F₀ := Real.one_le_rpow (by norm_num) (by positivity)
  have hF₀0 : 0 ≤ F₀ := by linarith
  have hT₀_bound : fptBound C_p14 τ d L₀ ≤
      F₀ * (2 : ℝ) ^ ((3 * d + 9) * C_p14) * (L : ℝ) ^ (E₁ * C_p14) := by
    calc fptBound C_p14 τ d L₀
      _ ≤ fptBound C_p14 τ d (2 ^ (3 * d + 9) * L ^ E₁) := fptBound_mono_L hL₀_len
      _ = F₀ * (2 : ℝ) ^ ((3 * d + 9) * C_p14) * (L : ℝ) ^ (E₁ * C_p14) := by
          unfold fptBound
          have hpow : ((2 ^ (3 * d + 9) * L ^ E₁ : ℕ) : ℝ) ^ C_p14 =
              (2 : ℝ) ^ ((3 * d + 9) * C_p14) * (L : ℝ) ^ (E₁ * C_p14) := by
            push_cast
            rw [mul_pow, ← pow_mul, ← pow_mul]
          rw [hpow]
          ring
  have hThom_bound : fptBound C_p14 τ d LHom ≤
      F₀ * (2 : ℝ) ^ ((3 * d + 9) * C_p14) * (L : ℝ) ^ (E₁ * C_p14) :=
    le_trans (fptBound_mono_L hLHom_le) hT₀_bound
  have hLR1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  have hLE2_ge : ∀ e ≤ E₂, (L : ℝ) ^ e ≤ (L : ℝ) ^ E₂ :=
    fun e he => pow_le_pow_right₀ hLR1 he
  set P₂ : ℕ := (12 * C_p14 + 12) * d
  have hP₂_ge1 : (3 * d + 9) * C_p14 ≤ P₂ := by
    have hCd : C_p14 ≤ C_p14 * d := Nat.le_mul_of_pos_right C_p14 hd1
    calc (3 * d + 9) * C_p14 = 3 * (C_p14 * d) + 9 * C_p14 := by ring
      _ ≤ 3 * (C_p14 * d) + 9 * (C_p14 * d) := Nat.add_le_add_left (Nat.mul_le_mul_left 9 hCd) _
      _ = (12 * C_p14) * d := by ring
      _ ≤ (12 * C_p14 + 12) * d := Nat.mul_le_mul_right d (Nat.le_add_right _ 12)
  have hP₂_ge2 : 3 * d + 8 ≤ P₂ := by
    calc 3 * d + 8 ≤ 12 * d := by omega
      _ ≤ (12 * C_p14 + 12) * d := Nat.mul_le_mul_right d (by omega)
  set B_unit : ℝ := F₀ * (2 : ℝ) ^ P₂ * (L : ℝ) ^ E₂
  have hUnit_ge : (1 : ℝ) ≤ F₀ * (2 : ℝ) ^ P₂ :=
    one_le_mul_of_one_le_of_one_le hF₀1 (one_le_pow₀ (by norm_num))
  have ht1 : (L : ℝ) ≤ B_unit := by
    calc (L : ℝ) = 1 * (L : ℝ) ^ 1 := by ring
      _ ≤ (F₀ * (2 : ℝ) ^ P₂) * (L : ℝ) ^ E₂ :=
          mul_le_mul hUnit_ge (hLE2_ge 1 hE₂_ge1) (by positivity) (by positivity)
      _ = B_unit := by ring
  have ht2 : (LM : ℝ) ≤ B_unit := by
    have h1 : (LM : ℝ) ≤ (L : ℝ) ^ C_box := by exact_mod_cast hMlen
    calc (LM : ℝ) ≤ 1 * (L : ℝ) ^ C_box := by linarith
      _ ≤ (F₀ * (2 : ℝ) ^ P₂) * (L : ℝ) ^ E₂ :=
          mul_le_mul hUnit_ge (hLE2_ge C_box hE₂_ge_box) (by positivity) (by positivity)
      _ = B_unit := by ring
  have ht3 : (LN : ℝ) ≤ B_unit := by
    have h1 : (LN : ℝ) ≤ (2 : ℝ) ^ (3 * d + 8) * (L : ℝ) ^ E₁ := by exact_mod_cast hLN_bound
    have h2 : (2 : ℝ) ^ (3 * d + 8) ≤ F₀ * (2 : ℝ) ^ P₂ := by
      calc (2 : ℝ) ^ (3 * d + 8) = 1 * (2 : ℝ) ^ (3 * d + 8) := by ring
        _ ≤ F₀ * (2 : ℝ) ^ P₂ :=
            mul_le_mul hF₀1 (pow_le_pow_right₀ (by norm_num) hP₂_ge2) (by positivity) hF₀0
    exact le_trans h1 (mul_le_mul h2 (hLE2_ge E₁ hE₂_ge_E₁) (by positivity) (by positivity))
  have ht4 : (L : ℝ) ^ C_box ≤ B_unit := by
    calc (L : ℝ) ^ C_box = 1 * (L : ℝ) ^ C_box := by ring
      _ ≤ (F₀ * (2 : ℝ) ^ P₂) * (L : ℝ) ^ E₂ :=
          mul_le_mul hUnit_ge (hLE2_ge C_box hE₂_ge_box) (by positivity) (by positivity)
      _ = B_unit := by ring
  have ht5 : fptBound C_p14 τ d L₀ ≤ B_unit := by
    refine le_trans hT₀_bound ?_
    refine mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hP₂_ge1) hF₀0)
      (hLE2_ge (E₁ * C_p14) hE₂_ge_mul) (by positivity) (by positivity)
  have ht6 : fptBound C_p14 τ d LHom ≤ B_unit :=
    le_trans (fptBound_mono_L hLHom_le) ht5
  have ht7 : (2 : ℝ) ≤ 2 * B_unit := by
    have : (1 : ℝ) ≤ B_unit :=
      one_le_mul_of_one_le_of_one_le hUnit_ge (one_le_pow₀ hLR1)
    linarith
  have hBase : ((L : ℝ) + (LM : ℝ) + (LN : ℝ) +
      (L : ℝ) ^ C_box + fptBound C_p14 τ d L₀ + fptBound C_p14 τ d LHom + 2) ≤ 8 * B_unit := by
    linarith
  have h8B : 8 * B_unit ≤ F₀ * (2 : ℝ) ^ ((12 * C_p14 + 15) * d) * (L : ℝ) ^ E₂ := by
    have h3d : P₂ + 3 ≤ (12 * C_p14 + 15) * d := by
      calc P₂ + 3 = (12 * C_p14 + 12) * d + 3 := rfl
        _ ≤ (12 * C_p14 + 12) * d + 3 * d := Nat.add_le_add_left (by omega) _
        _ = (12 * C_p14 + 15) * d := by ring
    calc 8 * B_unit = F₀ * ((2 : ℝ) ^ P₂ * (2 : ℝ) ^ 3) * (L : ℝ) ^ E₂ := by
          change 8 * (F₀ * (2 : ℝ) ^ P₂ * (L : ℝ) ^ E₂) = _
          ring
      _ = F₀ * (2 : ℝ) ^ (P₂ + 3) * (L : ℝ) ^ E₂ := by rw [← pow_add]
      _ ≤ F₀ * (2 : ℝ) ^ ((12 * C_p14 + 15) * d) * (L : ℝ) ^ E₂ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) h3d) hF₀0)
            (by positivity)
  have hPow : ((L : ℝ) + (LM : ℝ) + (LN : ℝ) +
      (L : ℝ) ^ C_box + fptBound C_p14 τ d L₀ + fptBound C_p14 τ d LHom + 2) ^ C_drv ≤
      F₀ ^ C_drv * (2 : ℝ) ^ (K₁ * d) * (L : ℝ) ^ (E₂ * C_drv) := by
    have hK₁_ge : ((12 * C_p14 + 15) * d) * C_drv ≤ K₁ * d := by
      calc ((12 * C_p14 + 15) * d) * C_drv
        _ = ((12 * C_p14 + 15) * C_drv) * d := by ring
        _ ≤ ((12 * C_p14 + 15) * (C_drv + 1)) * d :=
            Nat.mul_le_mul_right d (Nat.mul_le_mul_left _ (Nat.le_succ C_drv))
    have hLHS0 : 0 ≤ ((L : ℝ) + (LM : ℝ) + (LN : ℝ) +
        (L : ℝ) ^ C_box + fptBound C_p14 τ d L₀ + fptBound C_p14 τ d LHom + 2) :=
      add_nonneg
        (add_nonneg
          (add_nonneg
            (add_nonneg
              (add_nonneg (add_nonneg (by positivity) (by positivity)) (by positivity))
              (by positivity))
            (fptBound_nonneg C_p14 τ d L₀))
          (fptBound_nonneg C_p14 τ d LHom))
        (by positivity)
    calc _ ≤ (F₀ * (2 : ℝ) ^ ((12 * C_p14 + 15) * d) * (L : ℝ) ^ E₂) ^ C_drv :=
          pow_le_pow_left₀ hLHS0 (le_trans hBase h8B) C_drv
      _ = F₀ ^ C_drv * (2 : ℝ) ^ (((12 * C_p14 + 15) * d) * C_drv) * (L : ℝ) ^ (E₂ * C_drv) := by
          rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
      _ ≤ F₀ ^ C_drv * (2 : ℝ) ^ (K₁ * d) * (L : ℝ) ^ (E₂ * C_drv) := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hK₁_ge) (by positivity))
            (by positivity)
  have hC_ge_left : E₂ * C_drv ≤ C := le_max_left _ _
  have hC_ge_right : C_p14 + C_drv + K₁ + 4 ≤ C := le_max_right _ _
  have hExpFactor : F₀ ^ C_drv * (2 : ℝ) ^ (K₁ * d) ≤
      (2 : ℝ) ^ (α * (2 : ℝ) ^ ((C : ℝ) * d)) :=
    exp_factor_bound hd1 hα1 hC_ge_right
  have hLPow : (L : ℝ) ^ (E₂ * C_drv) ≤ (L : ℝ) ^ C :=
    pow_le_pow_right₀ hLR1 hC_ge_left
  refine le_trans hPow ?_
  unfold fptBound
  exact mul_le_mul hExpFactor hLPow (by positivity) (by positivity)


private abbrev L (I : Instance) (N : ℕ) := (encInstance I ++ encNat N ++ [3]).length
private abbrev Q (I : Instance) := ∏ t, ∏ j, (I.coeff t j).den
private abbrev B (I : Instance) (N : ℕ) := 2^((L I N)^2+4*L I N)
private def yes (I : Instance) (N k : ℕ) := ∃ μ, I.FeasibleN N μ ∧ (Q I:ℝ)*I.cost μ ≤ (k:ℝ)-B I N
private def answer (I : Instance) (N k : ℕ) (o : Output I) : Prop := match o with
  | .unbounded => False
  | .infeasible => ¬ yes I N k
  | .optimal y v c => CertOK I c ∧ I.FeasibleN N (certMult I c) ∧
      I.totalAgg (certMult I c) = ((fun i => (y i:ℝ)), fun i => (v i:ℝ)) ∧
      (Q I:ℝ)*I.cost (certMult I c) ≤ (k:ℝ)-B I N

private lemma tag {I N k o} (h : answer I N k o) : encOutput o ≠ [0] ↔ yes I N k := by
  cases o with
  | unbounded => exact h.elim
  | infeasible => simpa [encOutput] using (show ¬ yes I N k from h)
  | optimal y v c => exact ⟨fun _ => ⟨_,h.2.1,h.2.2.2⟩,fun _ => by simp [encOutput]⟩

private lemma index {I : Instance} {N : ℕ} (hI : I.Valid) {μ : Mult I} (hf : I.FeasibleN N μ) :
    ∃ j ≤ 2*B I N, (Q I:ℝ)*I.cost μ = (j:ℝ)-B I N := by
  obtain ⟨_,_,grid⟩ := counted_grid I hI N
  obtain ⟨z,hz,hb⟩ := grid μ hf
  change z.natAbs ≤ B I N at hb
  have hzz : |z| ≤ (B I N:ℤ) := by simpa only [Int.natCast_natAbs] using Int.ofNat_le.mpr hb
  have hzlo := (abs_le.mp hzz).1
  have hzhi := (abs_le.mp hzz).2
  let j := (z+(B I N:ℤ)).toNat
  have hj : (j:ℤ) = z+(B I N:ℤ) := Int.toNat_of_nonneg (by omega)
  exact ⟨j,by omega,hz.trans (by exact_mod_cast (by omega : z=(j:ℤ)-(B I N:ℤ)))⟩

end IntConeFPT.BudgetOptimize
open IntConeFPT.BudgetOptimize

set_option maxHeartbeats 1200000 in
theorem solution :
    ∃ C : ℕ, ∃ M : Machine, ∀ I : Instance, I.Valid → ∀ Nmax : ℕ,
      let inp := encInstance I ++ encNat Nmax ++ [3]
      ∃ o : Output I, o.CorrectN Nmax ∧
        RunsWithin M inp (encOutput o) (fptBound C I.τ I.d inp.length) := by
  classical
  obtain ⟨e,A,hA⟩ := counted_threshold_search
  obtain ⟨d,W,hW⟩ := threshold_bisection_machine A
  obtain ⟨C,hC⟩ := fptBound_absorb 0 e d
  refine ⟨C,W,?_⟩
  intro I hI N inp
  let U := 2 * B I N
  let T := fptBound e I.τ I.d inp.length
  have ht (k : ℕ) (hk : k ≤ U) : ∃ o, answer I N k o ∧ RunsWithin A (inp ++ encNat k ++ [3]) (encOutput o) T := hA I hI N k hk
  choose o ho using fun k : Fin (U+1) => ht k (by omega)
  let out := fun k => if h : k ≤ U then o ⟨k,by omega⟩ else Output.infeasible (I:=I)
  have go (k : ℕ) (hk : k ≤ U) : answer I N k (out k) ∧
      RunsWithin A (inp ++ encNat k ++ [3]) (encOutput (out k)) T := by simpa [out,hk] using ho ⟨k,by omega⟩
  obtain ⟨k,hk,hn,hy,run⟩ := hW inp (fun k => encOutput (out k)) T (fun k hk => (go k hk).2) (by
    intro i j hij hj h
    apply (tag (go j hj).1).mpr
    obtain ⟨μ,hμ,hc⟩ := (tag (go i (hij.trans hj)).1).mp h
    exact ⟨μ,hμ,hc.trans (sub_le_sub_right (Nat.cast_le.mpr hij) _)⟩)
  have htag := (go k hk).1
  have hcorr : (out k).CorrectN N := by
    cases he : out k with
    | unbounded => rw [he] at htag; exact htag.elim
    | infeasible =>
      intro ⟨μ,hμ⟩
      obtain ⟨j,hj,hval⟩ := index hI hμ
      exact (tag (go j hj).1).mpr ⟨μ,hμ,hval.le⟩ (hn (by simp [he,encOutput]) j hj)
    | optimal y v cert =>
      rw [he] at htag
      obtain ⟨hc,hf,ha,hcost⟩ := htag
      refine ⟨hc,hf,ha,fun μ hμ => ?_⟩
      obtain ⟨j,hj,hval⟩ := index hI hμ
      have hkj : k ≤ j := by
        by_contra! h
        exact (tag (go j hj).1).mpr ⟨μ,hμ,hval.le⟩ (hy (by simp [he,encOutput]) j h)
      apply le_of_mul_le_mul_left (a:=(Q I:ℝ)) _ (Nat.cast_pos.mpr (counted_grid I hI N).1)
      rw [hval]; exact hcost.trans (sub_le_sub_right (Nat.cast_le.mpr hkj) _)
  refine ⟨out k,hcorr,?_⟩
  obtain ⟨m,hm,hr⟩ := run
  refine ⟨m,hm.trans ?_,hr⟩
  have hlen : (encInstance I).length ≤ inp.length := by simp [inp] <;> omega
  have hnstar := section_3_6_nstar_bound I hI 1 le_rfl
  obtain ⟨_,_,_,_,_,_,hL,_,_,hτ,_⟩ := hnstar
  have hbound := hC (L:=inp.length) (LM:=0) (LN:=0) (L₀:=inp.length+1) (LHom:=inp.length)
    hI.one_le_d hI.one_le_τ (hL.trans hlen) (hτ.trans hlen) (Nat.zero_le _) (Nat.zero_le _) (by simp) (by omega)
  apply le_trans _ hbound
  apply pow_le_pow_left₀ (add_nonneg (add_nonneg (Nat.cast_nonneg _) (fptBound_nonneg ..)) (by norm_num))
  simp only [Nat.cast_zero,add_zero,pow_zero,T]
  linarith [fptBound_nonneg e I.τ I.d (inp.length+1)]
