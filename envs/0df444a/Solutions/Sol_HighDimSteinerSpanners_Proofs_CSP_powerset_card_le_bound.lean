-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.powerset_card_le_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:07.506441+00:00
-- url     : https://prove2.me/submissions/8ffd504d-62c2-4354-a0b4-c1bb4d1bded9

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_Definitions
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_CalibrationBounds

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution {α : Type*} (R_set : Finset α)
    (C₁ A b : ℕ) (hC₁ : 3 ≤ C₁) (hA : A ≤ 21) (hcard : R_set.card ≤ A * C₁ ^ 2 * b) :
    ((R_set.powerset.filter (fun G => G.card ≤ b)).card : ℝ) ≤
      ((b + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (((2 * Nat.clog 2 C₁ + 6) * b : ℕ) : ℝ) := by
  classical
  let M : ℕ := 21 * C₁ ^ 2 * b
  have hR_le_M : R_set.card ≤ M := by
    have hAC : A * C₁ ^ 2 ≤ 21 * C₁ ^ 2 := Nat.mul_le_mul_right _ hA
    exact le_trans hcard (Nat.mul_le_mul_right b hAC)
  have h2b_le_M : 2 * b ≤ M := by
    dsimp [M]
    have hC2 : 9 ≤ C₁ ^ 2 := by nlinarith
    nlinarith
  have hchoose_mono : ∀ (N0 t0 b0 : ℕ), 2 * b0 ≤ N0 → t0 ≤ b0 → N0.choose t0 ≤ N0.choose b0 := by
    intro N0 t0 b0 h2b htb
    have hstep : ∀ k : ℕ, 2 * (k + 1) ≤ N0 → N0.choose k ≤ N0.choose (k + 1) := by
      intro k hk
      have hid := (Nat.choose_succ_right_eq N0 k).symm
      have hkle : k + 1 ≤ N0 - k := by omega
      have hmul : N0.choose k * (k + 1) ≤ N0.choose (k + 1) * (k + 1) := by
        calc
          N0.choose k * (k + 1) ≤ N0.choose k * (N0 - k) := Nat.mul_le_mul_left _ hkle
          _ = N0.choose (k + 1) * (k + 1) := hid
      exact Nat.le_of_mul_le_mul_right hmul (by omega)
    have hm : ∀ x : ℕ, t0 ≤ x → 2 * x ≤ N0 → N0.choose t0 ≤ N0.choose x :=
      Nat.le_induction (fun _ => le_refl _) (fun k _ ih hk1 =>
        le_trans (ih (by omega)) (hstep k hk1))
    exact hm b0 htb h2b
  have hMb_le : (M.choose b : ℝ) ≤ (2 : ℝ) ^ (((2 * Nat.clog 2 C₁ + 6) * b : ℕ) : ℝ) := by
    have h1 : (M.choose b : ℝ) ≤ (M : ℝ) ^ b / (b.factorial : ℝ) := Nat.choose_le_pow_div b M
    have hM_cast : (M : ℝ) = (21 * (C₁ : ℝ) ^ 2) * (b : ℝ) := by dsimp [M]; push_cast; ring
    have h2 : (M : ℝ) ^ b / (b.factorial : ℝ) =
        (21 * (C₁ : ℝ) ^ 2) ^ b * ((b : ℝ) ^ b / (b.factorial : ℝ)) := by
      rw [hM_cast, mul_pow, mul_div_assoc]
    have hexp3 : (b : ℝ) ^ b / (b.factorial : ℝ) ≤ (3 : ℝ) ^ b := by
      have he : Real.exp (b : ℝ) ≤ (3 : ℝ) ^ b := by
        have heb : Real.exp (b : ℝ) = (Real.exp 1) ^ b := by simp
        have he3 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
        rw [heb]
        exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) he3 b
      exact le_trans (Real.pow_div_factorial_le_exp (b : ℝ) (Nat.cast_nonneg b) b) he
    have hC_pow : C₁ ≤ 2 ^ Nat.clog 2 C₁ := Nat.le_pow_clog (by decide : 1 < 2) C₁
    have hC_r : (C₁ : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 C₁ := by exact_mod_cast hC_pow
    have hbase : 63 * (C₁ : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * Nat.clog 2 C₁ + 6) := by
      calc
        63 * (C₁ : ℝ) ^ 2 ≤ 64 * ((2 : ℝ) ^ Nat.clog 2 C₁) ^ 2 := by
          have hsq : (C₁ : ℝ) ^ 2 ≤ ((2 : ℝ) ^ Nat.clog 2 C₁) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg C₁) hC_r 2
          nlinarith [show (0 : ℝ) ≤ ((2 : ℝ) ^ Nat.clog 2 C₁) ^ 2 by positivity]
        _ = (2 : ℝ) ^ (2 * Nat.clog 2 C₁ + 6) := by
          rw [show (64 : ℝ) = (2 : ℝ) ^ 6 by norm_num, ← pow_mul, ← pow_add]
          congr 1; omega
    have h12 : (M.choose b : ℝ) ≤ (21 * (C₁ : ℝ) ^ 2) ^ b * (3 : ℝ) ^ b := by
      calc
        (M.choose b : ℝ) ≤ (M : ℝ) ^ b / (b.factorial : ℝ) := h1
        _ = (21 * (C₁ : ℝ) ^ 2) ^ b * ((b : ℝ) ^ b / (b.factorial : ℝ)) := h2
        _ ≤ (21 * (C₁ : ℝ) ^ 2) ^ b * (3 : ℝ) ^ b :=
            mul_le_mul_of_nonneg_left hexp3 (by positivity)
    calc
      (M.choose b : ℝ) ≤ (21 * (C₁ : ℝ) ^ 2) ^ b * (3 : ℝ) ^ b := h12
      _ = (63 * (C₁ : ℝ) ^ 2) ^ b := by rw [← mul_pow]; congr 1; ring
      _ ≤ ((2 : ℝ) ^ (2 * Nat.clog 2 C₁ + 6)) ^ b := pow_le_pow_left₀ (by positivity) hbase b
      _ = (2 : ℝ) ^ (((2 * Nat.clog 2 C₁ + 6) * b : ℕ) : ℝ) := by
        rw [← pow_mul, ← Real.rpow_natCast]
  have hsub : R_set.powerset.filter (fun G => G.card ≤ b) ⊆
      (Finset.range (b + 1)).biUnion (fun t => R_set.powersetCard t) := by
    intro G hG
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion,
      Finset.mem_range, Finset.mem_powersetCard] at hG ⊢
    exact ⟨G.card, Nat.lt_succ_of_le hG.2, hG.1, rfl⟩
  have hcard_nat : (R_set.powerset.filter (fun G => G.card ≤ b)).card ≤ (b + 1) * M.choose b := by
    calc
      (R_set.powerset.filter (fun G => G.card ≤ b)).card
        ≤ ((Finset.range (b + 1)).biUnion (fun t => R_set.powersetCard t)).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ t ∈ Finset.range (b + 1), (R_set.powersetCard t).card := Finset.card_biUnion_le
      _ ≤ ∑ _t ∈ Finset.range (b + 1), M.choose b := by
          refine Finset.sum_le_sum (fun t ht => ?_)
          rw [Finset.card_powersetCard]
          exact le_trans (Nat.choose_le_choose t hR_le_M)
            (hchoose_mono M t b h2b_le_M (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)))
      _ = (b + 1) * M.choose b := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  calc
    ((R_set.powerset.filter (fun G => G.card ≤ b)).card : ℝ)
      ≤ ((b + 1 : ℕ) : ℝ) * (M.choose b : ℝ) := by exact_mod_cast hcard_nat
    _ ≤ ((b + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (((2 * Nat.clog 2 C₁ + 6) * b : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hMb_le (Nat.cast_nonneg _)
end HighDimSteinerSpanners.Proofs.CSP
