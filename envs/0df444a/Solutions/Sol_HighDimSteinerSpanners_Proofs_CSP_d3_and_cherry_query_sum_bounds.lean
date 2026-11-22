-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.CSP.d3_and_cherry_query_sum_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:52:44.133784+00:00
-- url     : https://prove2.me/submissions/76430977-88be-4126-9b5c-8868cbd0d0ee

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.GCongr
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_WitnessMoments
public import Definitions.Def_LeanPool_SteinerSpanners_CSP_CherryMoments
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_freshHomQueryCardinality
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_threeWayFiberCardinality
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_cherryFiberCardinality
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_CSP_lam0_ge_1000_C1

section
@[expose] public section
open scoped ENNReal
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners.Proofs.CSP
noncomputable section Helpers
open Classical in
private lemma cherryMoments_h_edge_split :
    ∀ (C₁ r_star t : ℕ),
      t ≤ (2 : ℕ) ^ cspL C₁ * r_star →
        cspPEdge C₁ r_star ^ (t * ((2 : ℕ) ^ cspL C₁ * r_star - (1 : ℕ)) - t.choose (2 : ℕ)) =
          cspPEdge C₁ r_star ^ (t * ((2 : ℕ) ^ cspL C₁ * r_star - (1 : ℕ))) *
            (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * (↑(t.choose (2 : ℕ)) : ℝ)) := by
  classical
  intro C₁ r_star t ht
  have h2c : 2 * t.choose 2 = t * (t - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Even.two_dvd (Nat.even_mul_pred_self t))
  have hc_le : t.choose 2 ≤ t * (2 ^ cspL C₁ * r_star - 1) := by
    have hsub : t - 1 ≤ 2 ^ cspL C₁ * r_star - 1 := Nat.sub_le_sub_right ht 1
    have hm : t * (t - 1) ≤ t * (2 ^ cspL C₁ * r_star - 1) := Nat.mul_le_mul_left t hsub
    omega
  have hcancel : (cspPEdge C₁ r_star) ^ (t.choose 2) *
      (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * (t.choose 2 : ℝ)) = 1 := by
    dsimp only [cspPEdge]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have hexp0 : - cspSigmaEdge C₁ r_star * (t.choose 2 : ℝ) +
        cspSigmaEdge C₁ r_star * (t.choose 2 : ℝ) = 0 := by ring
    rw [hexp0, Real.rpow_zero]
  calc
    (cspPEdge C₁ r_star) ^ (t * (2 ^ cspL C₁ * r_star - 1) - t.choose 2)
      = (cspPEdge C₁ r_star) ^ (t * (2 ^ cspL C₁ * r_star - 1) - t.choose 2) *
          ((cspPEdge C₁ r_star) ^ (t.choose 2) *
            (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * (t.choose 2 : ℝ))) := by
        rw [hcancel, mul_one]
    _ = ((cspPEdge C₁ r_star) ^ (t * (2 ^ cspL C₁ * r_star - 1) - t.choose 2) *
          (cspPEdge C₁ r_star) ^ (t.choose 2)) *
          (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * (t.choose 2 : ℝ)) := by ring
    _ = (cspPEdge C₁ r_star) ^ (t * (2 ^ cspL C₁ * r_star - 1)) *
          (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * (t.choose 2 : ℝ)) := by
        rw [← pow_add, Nat.sub_add_cancel hc_le]
open Classical in
private lemma cherryMoments_h_large_d3 :
    ∀ (C₁ : ℕ),
      (3 : ℕ) ≤ C₁ →
        ∀ (r_star : ℕ),
          (1000 : ℕ) * C₁ < r_star →
            (0 : ℝ) < cspSigmaEdge C₁ r_star →
              (0 : ℝ) < cspPEdge C₁ r_star →
                (4 : ℝ) * (2 : ℝ) ^ cspL C₁ * (↑(cspQ C₁ - (1 : ℕ)) : ℝ) *
                      cspPEdge C₁ r_star ^ ((2 : ℕ) ^ cspL C₁ * r_star - (1 : ℕ)) =
                    (2 : ℝ) ^ (-(↑(cspGamma0 C₁) : ℝ)) →
                  cspSigmaEdge C₁ r_star * (↑r_star : ℝ) / (2 : ℝ) ≤ (10001 / 10000 : ℝ) *
                      (↑(cspBeta0 C₁) : ℝ) →
                    (∀ (s : ℕ),
                        (↑(((2 : ℕ) ^ cspL C₁ * r_star).choose s) : ℝ) * (↑(cspQ C₁ - (1 : ℕ)) :
                            ℝ) ^ s *
                            cspPEdge C₁ r_star ^ (s * ((2 : ℕ) ^ cspL C₁ * r_star - (1 : ℕ))) ≤
                          (2 : ℝ) ^ ((2 : ℝ) * (↑r_star : ℝ) - (↑(cspGamma0 C₁) : ℝ) * (↑s : ℝ))) →
                      (1000 : ℕ) * C₁ ≤ cspLam0 C₁ →
                        (3000 : ℕ) ≤ cspLam0 C₁ →
                          (↑(cspBeta0 C₁) : ℝ) = (6 : ℝ) * (↑(cspLam0 C₁) : ℝ) →
                            C₁ * r_star ≤ (2 : ℕ) ^ cspL C₁ * r_star →
                              (∀ t ≤ (2 : ℕ) ^ cspL C₁ * r_star,
                                  cspPEdge C₁ r_star ^ (t * ((2 : ℕ) ^ cspL C₁ * r_star - (1 :
                                      ℕ)) - t.choose (2 : ℕ)) =
                                    cspPEdge C₁ r_star ^ (t * ((2 : ℕ) ^ cspL C₁ * r_star - (1 :
                                        ℕ))) *
                                      (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * (↑(t.choose (2 : ℕ)) :
                                          ℝ))) →
                                ∀ (d₃ w : ℕ),
                                  d₃ + w ≤ C₁ * r_star →
                                    r_star < cspInvEta0 C₁ * d₃ →
                                      (↑((C₁ * r_star + (1 : ℕ)) ^ (2 : ℕ)) : ℝ) *
                                          ((↑((2 : ℕ) ^ ((2 : ℕ) * (C₁ * r_star))) : ℝ) *
                                              (↑(cspQ C₁ - (1 : ℕ)) : ℝ) ^ d₃ *
                                              ((↑(((2 : ℕ) ^ cspL C₁ * r_star).choose w) : ℝ) *
                                                (↑(cspQ C₁ - (1 : ℕ)) : ℝ) ^ w) *
                                            cspPEdge C₁ r_star ^
                                              ((d₃ + w) * ((2 : ℕ) ^ cspL C₁ * r_star - (1 : ℕ)) -
                                                (d₃ + w).choose (2 : ℕ))) ≤
                                        (2 : ℝ) ^
                                          (-((12 : ℝ) * (↑(C₁ ^ (2 : ℕ)) : ℝ)) * (↑(cspLam0 C₁)
                                              : ℝ) * (↑r_star : ℝ)) := by
  classical
  intro C₁ hC₁ r_star hr hσ_pos hp_edge_pos h_cal hσ_up h_binom_edge hlam_1000C1 hlam_ge
      hbeta_eq hCr_le_N h_edge_split d₃ w hdw hr_d3
  have ht_le_N : d₃ + w ≤ 2 ^ cspL C₁ * r_star := le_trans hdw hCr_le_N
  have hL_d3 : 20 * C₁ ^ 2 * cspLam0 C₁ * r_star ≤ cspL C₁ * d₃ := by
    have h1 : r_star ≤ cspInvEta0 C₁ * d₃ := le_of_lt hr_d3
    have h2 := Nat.mul_le_mul_left (20 * C₁ ^ 2 * cspLam0 C₁) h1
    have h3 : (20 * C₁ ^ 2 * cspLam0 C₁) * (cspInvEta0 C₁ * d₃) =
        (20 * C₁ ^ 2 * cspInvEta0 C₁ * cspLam0 C₁) * d₃ := by ring
    have h4 : 20 * C₁ ^ 2 * cspInvEta0 C₁ * cspLam0 C₁ ≤ cspL C₁ := by
      dsimp only [cspL]; omega
    have h5 := Nat.mul_le_mul_right d₃ h4
    have h6 : (20 * C₁ ^ 2 * cspLam0 C₁) * r_star = 20 * C₁ ^ 2 * cspLam0 C₁ * r_star := by ring
    rw [h6, h3] at h2
    exact le_trans h2 h5
  have hsplit := h_edge_split (d₃ + w) ht_le_N
  have hpow_dw : (cspPEdge C₁ r_star) ^ ((d₃ + w) * (2 ^ cspL C₁ * r_star - 1)) =
      (cspPEdge C₁ r_star) ^ (d₃ * (2 ^ cspL C₁ * r_star - 1)) *
        (cspPEdge C₁ r_star) ^ (w * (2 ^ cspL C₁ * r_star - 1)) := by
    rw [add_mul, pow_add]
  rw [hsplit, hpow_dw]
  let u_cal : ℝ := ((cspQ C₁ - 1 : ℕ) : ℝ) * (cspPEdge C₁ r_star) ^ (2 ^ cspL C₁ * r_star - 1)
  have hu_nn : 0 ≤ u_cal := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (le_of_lt hp_edge_pos) _)
  have hF1 : (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (4 * (r_star : ℝ)) := by
    have hCr1 : C₁ * r_star + 1 ≤ r_star * r_star := by
      have hC1_lt : C₁ + 1 ≤ r_star := by omega
      calc
        C₁ * r_star + 1 ≤ C₁ * r_star + r_star := by omega
        _ = (C₁ + 1) * r_star := by ring
        _ ≤ r_star * r_star := Nat.mul_le_mul_right r_star hC1_lt
    have hr_pow : r_star ≤ 2 ^ r_star := Nat.le_of_lt Nat.lt_two_pow_self
    have hrr_pow : r_star * r_star ≤ 2 ^ (2 * r_star) := by
      calc
        r_star * r_star ≤ 2 ^ r_star * 2 ^ r_star := Nat.mul_le_mul hr_pow hr_pow
        _ = 2 ^ (r_star + r_star) := (pow_add 2 r_star r_star).symm
        _ = 2 ^ (2 * r_star) := by rw [two_mul]
    have hsq_nat : (C₁ * r_star + 1) ^ 2 ≤ 2 ^ (4 * r_star) := by
      have h1 : (C₁ * r_star + 1) ^ 2 ≤ (2 ^ (2 * r_star)) ^ 2 :=
        Nat.pow_le_pow_left (le_trans hCr1 hrr_pow) 2
      have h2 : (2 ^ (2 * r_star)) ^ 2 = 2 ^ (4 * r_star) := by
        rw [← pow_mul]
        congr 1
        omega
      rwa [h2] at h1
    have hcast : (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) ≤ ((2 ^ (4 * r_star) : ℕ) : ℝ) := by
      exact_mod_cast hsq_nat
    have hrpow : ((2 ^ (4 * r_star) : ℕ) : ℝ) = (2 : ℝ) ^ (4 * (r_star : ℝ)) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
      push_cast
      rfl
    linarith only [hcast, hrpow]
  have hF2 : ((2 ^ (2 * (C₁ * r_star)) : ℕ) : ℝ) = (2 : ℝ) ^ (2 * (C₁ : ℝ) * (r_star : ℝ)) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hF3 : u_cal ^ d₃ ≤ (2 : ℝ) ^ (- (cspL C₁ : ℝ) * (d₃ : ℝ)) := by
    have h2L_u : (2 : ℝ) ^ (cspL C₁ : ℝ) * u_cal ≤ 1 := by
      rw [Real.rpow_natCast]
      have hcal' : 4 * ((2 : ℝ) ^ cspL C₁ * u_cal) = (2 : ℝ) ^ (-(cspGamma0 C₁ : ℝ)) := by
        have heq : 4 * ((2 : ℝ) ^ cspL C₁ * u_cal) =
            (4 : ℝ) * (2 : ℝ) ^ cspL C₁ * ((cspQ C₁ - 1 : ℕ) : ℝ) *
              (cspPEdge C₁ r_star) ^ (2 ^ cspL C₁ * r_star - 1) := by
          dsimp only [u_cal]
          ring
        rw [heq, h_cal]
      have hgam_le1 : (2 : ℝ) ^ (-(cspGamma0 C₁ : ℝ)) ≤ 1 := by
        rw [show (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) by norm_num]
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hg_nn : 0 ≤ (cspGamma0 C₁ : ℝ) := Nat.cast_nonneg _
        linarith only [hg_nn]
      have hnn : 0 ≤ (2 : ℝ) ^ cspL C₁ * u_cal :=
        mul_nonneg (pow_nonneg (by norm_num) _) hu_nn
      linarith only [hcal', hgam_le1, hnn]
    have hu_le : u_cal ≤ (2 : ℝ) ^ (- (cspL C₁ : ℝ)) := by
      have hprod1 : (2 : ℝ) ^ (- (cspL C₁ : ℝ)) * (2 : ℝ) ^ (cspL C₁ : ℝ) = 1 := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), neg_add_cancel, Real.rpow_zero]
      calc
        u_cal = ((2 : ℝ) ^ (- (cspL C₁ : ℝ)) * (2 : ℝ) ^ (cspL C₁ : ℝ)) * u_cal := by
          rw [hprod1, one_mul]
        _ = (2 : ℝ) ^ (- (cspL C₁ : ℝ)) * ((2 : ℝ) ^ (cspL C₁ : ℝ) * u_cal) := by ring
        _ ≤ (2 : ℝ) ^ (- (cspL C₁ : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left h2L_u (Real.rpow_nonneg (by norm_num) _)
        _ = (2 : ℝ) ^ (- (cspL C₁ : ℝ)) := mul_one _
    calc
      u_cal ^ d₃ ≤ ((2 : ℝ) ^ (- (cspL C₁ : ℝ))) ^ d₃ := pow_le_pow_left₀ hu_nn hu_le d₃
      _ = (2 : ℝ) ^ (- (cspL C₁ : ℝ) * (d₃ : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hF4 : ((2 ^ cspL C₁ * r_star).choose w : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ w *
      (cspPEdge C₁ r_star) ^ (w * (2 ^ cspL C₁ * r_star - 1)) ≤
      (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
    refine le_trans (h_binom_edge w) (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    have hgw_nn : 0 ≤ (cspGamma0 C₁ : ℝ) * (w : ℝ) :=
      mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    linarith only [hgw_nn]
  have hF6 : (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * ((d₃ + w).choose 2 : ℝ)) ≤
      (2 : ℝ) ^ ((60006 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have h2c : 2 * (d₃ + w).choose 2 ≤ (C₁ ^ 2) * (r_star * r_star) := by
      have heq : 2 * (d₃ + w).choose 2 = (d₃ + w) * (d₃ + w - 1) := by
        rw [Nat.choose_two_right]
        exact Nat.mul_div_cancel' (Even.two_dvd (Nat.even_mul_pred_self (d₃ + w)))
      have hle1 : (d₃ + w) * (d₃ + w - 1) ≤ (d₃ + w) * (d₃ + w) :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ 1)
      have hle2 : (d₃ + w) * (d₃ + w) ≤ (C₁ * r_star) * (C₁ * r_star) :=
        Nat.mul_le_mul hdw hdw
      have hle3 : (C₁ * r_star) * (C₁ * r_star) = (C₁ ^ 2) * (r_star * r_star) := by ring
      rw [heq]
      exact le_trans hle1 (hle3 ▸ hle2)
    have h2c_real : 2 * ((d₃ + w).choose 2 : ℝ) ≤
        ((C₁ ^ 2 : ℕ) : ℝ) * ((r_star : ℝ) * (r_star : ℝ)) := by
      have hc : ((2 * (d₃ + w).choose 2 : ℕ) : ℝ) ≤
          (((C₁ ^ 2) * (r_star * r_star) : ℕ) : ℝ) := by exact_mod_cast h2c
      push_cast at hc ⊢
      linarith only [hc]
    have h1 : cspSigmaEdge C₁ r_star * ((d₃ + w).choose 2 : ℝ) ≤
        (cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2) * (((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ)) := by
      have hm := mul_le_mul_of_nonneg_left h2c_real (le_of_lt hσ_pos)
      have eq1 : cspSigmaEdge C₁ r_star * (((C₁ ^ 2 : ℕ) : ℝ) * ((r_star : ℝ) * (r_star : ℝ))) =
        2 * ((cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2) * (((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ)))
            := by ring
      have eq2 : cspSigmaEdge C₁ r_star * (2 * ((d₃ + w).choose 2 : ℝ)) =
        2 * (cspSigmaEdge C₁ r_star * ((d₃ + w).choose 2 : ℝ)) := by ring
      linarith only [hm, eq1, eq2]
    have h2 : (cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2) * (((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ)) ≤
        ((10001 / 10000 : ℝ) * (6 * (cspLam0 C₁ : ℝ))) * (((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith only [hσ_up, hbeta_eq])
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    have eq3 : ((10001 / 10000 : ℝ) * (6 * (cspLam0 C₁ : ℝ))) *
        (((C₁ ^ 2 : ℕ) : ℝ) * (r_star : ℝ)) =
        (60006 / 10000 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) := by ring
    linarith only [h1, h2, eq3]
  have hrearr :
      (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) *
        (((2 ^ (2 * (C₁ * r_star)) : ℕ) : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ d₃ *
          (((2 ^ cspL C₁ * r_star).choose w : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ w) *
          ((cspPEdge C₁ r_star) ^ (d₃ * (2 ^ cspL C₁ * r_star - 1)) *
            (cspPEdge C₁ r_star) ^ (w * (2 ^ cspL C₁ * r_star - 1)) *
            (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * ((d₃ + w).choose 2 : ℝ)))) =
      (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) *
        ((2 ^ (2 * (C₁ * r_star)) : ℕ) : ℝ) *
        (u_cal ^ d₃) *
        (((2 ^ cspL C₁ * r_star).choose w : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ w *
          (cspPEdge C₁ r_star) ^ (w * (2 ^ cspL C₁ * r_star - 1))) *
        (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * ((d₃ + w).choose 2 : ℝ)) := by
    dsimp only [u_cal]
    rw [mul_pow, ← pow_mul]
    ring
  rw [hrearr, hF2]
  have hnn_2r : ∀ e : ℝ, (0 : ℝ) ≤ (2 : ℝ) ^ e := fun _ => Real.rpow_nonneg (by norm_num) _
  have hnn_F4 : 0 ≤ ((2 ^ cspL C₁ * r_star).choose w : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ w *
      (cspPEdge C₁ r_star) ^ (w * (2 ^ cspL C₁ * r_star - 1)) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
      (pow_nonneg (le_of_lt hp_edge_pos) _)
  have hm12 : (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) * (2 : ℝ) ^ (2 * (C₁ : ℝ) * (r_star : ℝ)) ≤
      (2 : ℝ) ^ (4 * (r_star : ℝ)) * (2 : ℝ) ^ (2 * (C₁ : ℝ) * (r_star : ℝ)) :=
    mul_le_mul_of_nonneg_right hF1 (hnn_2r _)
  have hm123 := mul_le_mul hm12 hF3 (pow_nonneg hu_nn _) (mul_nonneg (hnn_2r _) (hnn_2r _))
  have hm1234 := mul_le_mul hm123 hF4 hnn_F4 (mul_nonneg (mul_nonneg (hnn_2r _) (hnn_2r _))
      (hnn_2r _))
  have hm12346 := mul_le_mul hm1234 hF6 (hnn_2r _)
    (mul_nonneg (mul_nonneg (mul_nonneg (hnn_2r _) (hnn_2r _)) (hnn_2r _)) (hnn_2r _))
  refine le_trans hm12346 ?_
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hLd3_real : 20 * ((C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) ≤
      (cspL C₁ : ℝ) * (d₃ : ℝ) := by
    have hc : ((20 * C₁ ^ 2 * cspLam0 C₁ * r_star : ℕ) : ℝ) ≤ ((cspL C₁ * d₃ : ℕ) : ℝ) := by
      exact_mod_cast hL_d3
    push_cast at hc ⊢
    linarith only [hc]
  have hlam_2C : 100 * (2 * C₁ + 6) ≤ cspLam0 C₁ := by omega
  have hlam_2C_real : (6 + 2 * (C₁ : ℝ)) * (r_star : ℝ) ≤
      (1 / 100 : ℝ) * ((C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) := by
    have hc : (100 * (2 * (C₁ : ℝ) + 6)) ≤ (cspLam0 C₁ : ℝ) := by
      exact_mod_cast hlam_2C
    have hC2_ge1 : (1 : ℝ) ≤ ((C₁ ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ C₁ ^ 2 by nlinarith only [hC₁])
    have hlam_nn : (0 : ℝ) ≤ (cspLam0 C₁ : ℝ) := Nat.cast_nonneg _
    have hc2 : 100 * (2 * (C₁ : ℝ) + 6) ≤ ((C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) := by
      nlinarith only [hc, hC2_ge1, hlam_nn]
    have hr_nn : (0 : ℝ) ≤ (r_star : ℝ) := Nat.cast_nonneg _
    nlinarith only [hc2, hr_nn]
  have hnn_C2 : 0 ≤ ((C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hcast12 : (12 * (C₁ ^ 2 : ℕ) : ℝ) = 12 * ((C₁ ^ 2 : ℕ) : ℝ) := by push_cast; ring
  rw [hcast12]
  linarith only [hLd3_real, hlam_2C_real, hnn_C2]
open Classical in
private lemma cherryMoments_h_small_s :
    ∀ (C₁ : ℕ),
      (3 : ℕ) ≤ C₁ →
        ∀ (r_star : ℕ),
          (1000 : ℕ) * C₁ < r_star →
            (0 : ℝ) < cspSigmaEdge C₁ r_star →
              (0 : ℝ) < cspPEdge C₁ r_star →
                cspSigmaEdge C₁ r_star * (↑r_star : ℝ) / (2 : ℝ) ≤ (10001 / 10000 : ℝ) *
                    (↑(cspBeta0 C₁) : ℝ) →
                  (∀ (s : ℕ),
                      (↑(((2 : ℕ) ^ cspL C₁ * r_star).choose s) : ℝ) * (↑(cspQ C₁ - (1 : ℕ)) :
                          ℝ) ^ s *
                          cspPEdge C₁ r_star ^ (s * ((2 : ℕ) ^ cspL C₁ * r_star - (1 : ℕ))) ≤
                        (2 : ℝ) ^ ((2 : ℝ) * (↑r_star : ℝ) - (↑(cspGamma0 C₁) : ℝ) * (↑s : ℝ))) →
                    (0 : ℝ) < cspPKeep C₁ r_star →
                      cspPKeep C₁ r_star ≤ (2 : ℝ) ^ (-(747 / 1000 : ℝ) * (↑(cspLam0 C₁) : ℝ) *
                          (↑r_star : ℝ)) →
                        (3000 : ℕ) ≤ cspLam0 C₁ →
                          (↑(cspBeta0 C₁) : ℝ) = (6 : ℝ) * (↑(cspLam0 C₁) : ℝ) →
                            (↑(cspGamma0 C₁) : ℝ) = (5 : ℝ) * (↑(cspLam0 C₁) : ℝ) →
                              r_star ≤ (2 : ℕ) ^ cspL C₁ * r_star →
                                (∀ t ≤ (2 : ℕ) ^ cspL C₁ * r_star,
                                    cspPEdge C₁ r_star ^ (t * ((2 : ℕ) ^ cspL C₁ * r_star - (1 :
                                        ℕ)) - t.choose (2 : ℕ)) =
                                      cspPEdge C₁ r_star ^ (t * ((2 : ℕ) ^ cspL C₁ * r_star - (1
                                          : ℕ))) *
                                        (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * (↑(t.choose (2 : ℕ))
                                            : ℝ))) →
                                  ∀ (s : ℕ),
                                    (80 : ℕ) * s ≤ (61 : ℕ) * r_star →
                                      (↑(r_star + (1 : ℕ)) : ℝ) *
                                          ((↑(r_star + (1 : ℕ)) : ℝ) *
                                                (2 : ℝ) ^ ((1 / 100 : ℝ) * (↑(cspLam0 C₁) : ℝ) *
                                                    (↑r_star : ℝ)) *
                                              ((↑(((2 : ℕ) ^ cspL C₁ * r_star).choose s) : ℝ) *
                                                (↑(cspQ C₁ - (1 : ℕ)) : ℝ) ^ s) *
                                            (cspPKeep C₁ r_star *
                                              cspPEdge C₁ r_star ^
                                                (s * ((2 : ℕ) ^ cspL C₁ * r_star - (1 : ℕ)) -
                                                    s.choose (2 : ℕ)))) ≤
                                        (2 : ℝ) ^ (-(72 / 100 : ℝ) * (↑(cspLam0 C₁) : ℝ) *
                                            (↑r_star : ℝ)) := by
  classical
  intro C₁ hC₁ r_star hr hσ_pos hp_edge_pos hσ_up h_binom_edge hp_keep_pos hp_keep_up hlam_ge
      hbeta_eq hgamma_eq hr_le_N h_edge_split s hs
  have hs_le_r : s ≤ r_star := by omega
  have hs_le_N : s ≤ 2 ^ cspL C₁ * r_star := le_trans hs_le_r hr_le_N
  rw [h_edge_split s hs_le_N]
  have hG1 : ((r_star + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (r_star : ℝ) := by
    have hnat : r_star + 1 ≤ 2 ^ r_star := Nat.lt_two_pow_self
    have hc : ((r_star + 1 : ℕ) : ℝ) ≤ ((2 ^ r_star : ℕ) : ℝ) := by exact_mod_cast hnat
    have hrp : ((2 ^ r_star : ℕ) : ℝ) = (2 : ℝ) ^ (r_star : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
    linarith only [hc, hrp]
  have hG_s : (((2 ^ cspL C₁ * r_star).choose s : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ s *
      (cspPEdge C₁ r_star) ^ (s * (2 ^ cspL C₁ * r_star - 1))) *
      (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ)) ≤
      (2 : ℝ) ^ (2 * (r_star : ℝ)) := by
    have hsc : cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ) ≤
        (cspGamma0 C₁ : ℝ) * (s : ℝ) := by
      have h160 : 160 * s.choose 2 ≤ 61 * r_star * s := by
        have h2c : 2 * s.choose 2 = s * (s - 1) := by
          rw [Nat.choose_two_right]
          exact Nat.mul_div_cancel' (Even.two_dvd (Nat.even_mul_pred_self s))
        have h1 : 2 * s.choose 2 ≤ s * s := by
          rw [h2c]
          exact Nat.mul_le_mul_left s (Nat.sub_le s 1)
        have h2 : 80 * (2 * s.choose 2) ≤ (80 * s) * s := by
          have hm := Nat.mul_le_mul_left 80 h1
          rwa [← Nat.mul_assoc 80 s s] at hm
        have h3 : (80 * s) * s ≤ (61 * r_star) * s := Nat.mul_le_mul_right s hs
        omega
      have h160_r : 160 * (s.choose 2 : ℝ) ≤ 61 * (r_star : ℝ) * (s : ℝ) := by
        exact_mod_cast h160
      have h1 : cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ) ≤
          (61 / 80 : ℝ) * ((cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2) * (s : ℝ)) := by
        have hm := mul_le_mul_of_nonneg_left h160_r (le_of_lt hσ_pos)
        linarith [hm,
          show cspSigmaEdge C₁ r_star * (61 * (r_star : ℝ) * (s : ℝ)) =
            160 * ((61 / 80 : ℝ) *
              ((cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2) * (s : ℝ))) by ring,
          show cspSigmaEdge C₁ r_star * (160 * (s.choose 2 : ℝ)) =
            160 * (cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ)) by ring]
      have h2 : (cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2) * (s : ℝ) ≤
          ((10001 / 10000 : ℝ) * (6 * (cspLam0 C₁ : ℝ))) * (s : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith only [hσ_up, hbeta_eq]) (Nat.cast_nonneg _)
      have hls_nn : 0 ≤ (cspLam0 C₁ : ℝ) * (s : ℝ) := by positivity
      rw [hgamma_eq]
      linarith [h1, h2, hls_nn]
    calc
      (((2 ^ cspL C₁ * r_star).choose s : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ s *
          (cspPEdge C₁ r_star) ^ (s * (2 ^ cspL C₁ * r_star - 1))) *
          (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ))
        ≤ (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ)) *
            (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (h_binom_edge s) (by positivity)
      _ = (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ) +
            cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ)) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (2 : ℝ) ^ (2 * (r_star : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hsc])
  have hrearr :
      ((r_star + 1 : ℕ) : ℝ) *
        ((((r_star + 1 : ℕ) : ℝ) *
          (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
          (((2 ^ cspL C₁ * r_star).choose s : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ s)) *
          (cspPKeep C₁ r_star *
            ((cspPEdge C₁ r_star) ^ (s * (2 ^ cspL C₁ * r_star - 1)) *
              (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ))))) =
      ((r_star + 1 : ℕ) : ℝ) *
        ((r_star + 1 : ℕ) : ℝ) *
        (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
        ((((2 ^ cspL C₁ * r_star).choose s : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ s *
          (cspPEdge C₁ r_star) ^ (s * (2 ^ cspL C₁ * r_star - 1))) *
          (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ))) *
        cspPKeep C₁ r_star := by ring
  rw [hrearr]
  have hnn_2r : ∀ e : ℝ, (0 : ℝ) ≤ (2 : ℝ) ^ e := fun _ => Real.rpow_nonneg (by norm_num) _
  have hnn_Gs : 0 ≤ (((2 ^ cspL C₁ * r_star).choose s : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ s *
      (cspPEdge C₁ r_star) ^ (s * (2 ^ cspL C₁ * r_star - 1))) *
      (2 : ℝ) ^ (cspSigmaEdge C₁ r_star * (s.choose 2 : ℝ)) :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
        (pow_nonneg (le_of_lt hp_edge_pos) _)) (hnn_2r _)
  have hm11 := mul_le_mul hG1 hG1 (Nat.cast_nonneg _) (hnn_2r _)
  have hm112 := mul_le_mul_of_nonneg_right hm11
    (hnn_2r ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)))
  have hm1123 := mul_le_mul hm112 hG_s hnn_Gs (by positivity)
  have hm11234 := mul_le_mul hm1123 hp_keep_up (le_of_lt hp_keep_pos) (by positivity)
  refine le_trans hm11234 ?_
  repeat rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hlam_r : (3000 : ℝ) ≤ (cspLam0 C₁ : ℝ) := by exact_mod_cast hlam_ge
  have hr_nn : (0 : ℝ) ≤ (r_star : ℝ) := Nat.cast_nonneg _
  nlinarith only [hlam_r, hr_nn]
open Classical in
private lemma cherryMoments_h_d3_sum :
    ∀ (C₁ : ℕ),
      (3 : ℕ) ≤ C₁ →
        ∀ (r_star : ℕ),
          (0 : ℝ) < cspPEdge C₁ r_star →
            cspPEdge C₁ r_star < (1 : ℝ) →
              (∀ (d₃ w : ℕ),
                  d₃ + w ≤ C₁ * r_star →
                    r_star < cspInvEta0 C₁ * d₃ →
                      (↑((C₁ * r_star + (1 : ℕ)) ^ (2 : ℕ)) : ℝ) *
                          ((↑((2 : ℕ) ^ ((2 : ℕ) * (C₁ * r_star))) : ℝ) * (↑(cspQ C₁ - (1 : ℕ))
                              : ℝ) ^ d₃ *
                              ((↑(((2 : ℕ) ^ cspL C₁ * r_star).choose w) : ℝ) * (↑(cspQ C₁ - (1
                                  : ℕ)) : ℝ) ^ w) *
                            cspPEdge C₁ r_star ^
                              ((d₃ + w) * ((2 : ℕ) ^ cspL C₁ * r_star - (1 : ℕ)) - (d₃ +
                                  w).choose (2 : ℕ))) ≤
                        (2 : ℝ) ^ (-((12 : ℝ) * (↑(C₁ ^ (2 : ℕ)) : ℝ)) * (↑(cspLam0 C₁) : ℝ) *
                            (↑r_star : ℝ))) →
                ∀ (x u : Fin ((2 : ℕ) ^ cspL C₁ * r_star) → Fin (cspQ C₁)),
                    dHam x u ≤ C₁ * r_star →
                      ∑ z : Fin ((2 : ℕ) ^ cspL C₁ * r_star) → Fin (cspQ C₁) with
                          dHam x z ≤ C₁ * r_star ∧
                            r_star < cspInvEta0 C₁ * (threeWayDisagree x u z).card,
                          cspPEdge C₁ r_star ^ (homQueries z \ (homQueries x ∪ homQueries u)).card ≤
                        (2 : ℝ) ^ (-((12 : ℝ) * (↑(C₁ ^ (2 : ℕ)) : ℝ)) * (↑(cspLam0 C₁) : ℝ) *
                            (↑r_star : ℝ)) := by
  classical
  intro C₁ hC₁ r_star hp_edge_pos hp_edge_lt1 h_s3a x u hd_xu
  let Z_bad := Finset.univ.filter (fun z : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁) =>
    dHam x z ≤ C₁ * r_star ∧
    r_star < cspInvEta0 C₁ * (threeWayDisagree x u z).card)
  let γ := fun z : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁) =>
    ((threeWayDisagree x u z).card, (disagreeSet x z \ disagreeSet x u).card)
  let B_idx := Finset.range (C₁ * r_star + 1) ×ˢ Finset.range (C₁ * r_star + 1)
  let f_z := fun z : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁) =>
    (cspPEdge C₁ r_star) ^ ((homQueries z \ (homQueries x ∪ homQueries u)).card)
  let RHS_a : ℝ := (2 : ℝ) ^ (- (12 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))
  have hd3w_le : ∀ z : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁),
      (threeWayDisagree x u z).card + (disagreeSet x z \ disagreeSet x u).card ≤ dHam x z := by
    intro z
    have hdisj : Disjoint (threeWayDisagree x u z) (disagreeSet x z \ disagreeSet x u) := by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      simp only [threeWayDisagree, disagreeSet, Finset.mem_sdiff, Finset.mem_filter,
        Finset.mem_univ,
          true_and] at hv1 hv2
      exact hv2.2 hv1.1
    have hsub : threeWayDisagree x u z ∪ (disagreeSet x z \ disagreeSet x u) ⊆ disagreeSet x z := by
      intro v hv
      rcases Finset.mem_union.mp hv with hv1 | hv2
      · simp only [threeWayDisagree, disagreeSet, Finset.mem_filter, Finset.mem_univ,
          true_and] at hv1 ⊢
        exact hv1.2.1
      · exact (Finset.mem_sdiff.mp hv2).1
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card hsub
  have hmaps : ∀ z ∈ Z_bad, γ z ∈ B_idx := by
    intro z hz
    simp only [Z_bad, Finset.mem_filter, Finset.mem_univ, true_and] at hz
    have hsum := le_trans (hd3w_le z) hz.1
    simp only [γ, B_idx, Finset.mem_product, Finset.mem_range]
    omega
  have hf_bound : ∀ z : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁),
      f_z z ≤
        (cspPEdge C₁ r_star) ^
          (((threeWayDisagree x u z).card + (disagreeSet x z \ disagreeSet x u).card) *
            (2 ^ cspL C₁ * r_star - 1) -
           ((threeWayDisagree x u z).card +
             (disagreeSet x z \ disagreeSet x u).card).choose 2) := by
    intro z
    let T := threeWayDisagree x u z ∪ (disagreeSet x z \ disagreeSet x u)
    have hdisj : Disjoint (threeWayDisagree x u z) (disagreeSet x z \ disagreeSet x u) := by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      simp only [threeWayDisagree, disagreeSet, Finset.mem_sdiff, Finset.mem_filter,
        Finset.mem_univ,
          true_and] at hv1 hv2
      exact hv2.2 hv1.1
    have hT_card : T.card =
        (threeWayDisagree x u z).card + (disagreeSet x z \ disagreeSet x u).card :=
      Finset.card_union_of_disjoint hdisj
    have hT_fresh : ∀ v ∈ T, ∀ y ∈ ({x, u} : Finset _), z v ≠ y v := by
      intro v hv y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases Finset.mem_union.mp hv with hv1 | hv2
      · simp only [threeWayDisagree, Finset.mem_filter, Finset.mem_univ, true_and] at hv1
        rcases hy with rfl | rfl
        · exact hv1.2.1.symm
        · exact hv1.2.2.symm
      · simp only [disagreeSet, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
          not_not] at hv2
        rcases hy with rfl | rfl
        · exact hv2.1.symm
        · rw [← hv2.2]; exact hv2.1.symm
    have hbi : ({x, u} : Finset _).biUnion homQueries = homQueries x ∪ homQueries u := by
      ext q_e
      simp
    have hq_le := freshHomQueryCardinality z ({x, u} : Finset _) T hT_fresh
    rw [hT_card, hbi] at hq_le
    exact pow_le_pow_of_le_one (le_of_lt hp_edge_pos) (le_of_lt hp_edge_lt1) hq_le
  rw [← Finset.sum_fiberwise_of_maps_to hmaps f_z]
  have hfib_le : ∀ dw ∈ B_idx,
      (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) * (∑ z ∈ Z_bad with γ z = dw, f_z z) ≤ RHS_a := by
    rintro ⟨d₃, w⟩ _
    let Fib := Z_bad.filter (fun z => γ z = (d₃, w))
    change (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) * (∑ z ∈ Fib, f_z z) ≤ RHS_a
    by_cases hne : Fib.Nonempty
    · obtain ⟨z₀, hz₀⟩ := hne
      simp only [Fib, Z_bad, γ, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hz₀
      have hdw_le : d₃ + w ≤ C₁ * r_star := by
        have hs := le_trans (hd3w_le z₀) hz₀.1.1
        omega
      have hr_d3 : r_star < cspInvEta0 C₁ * d₃ := by
        rw [← hz₀.2.1]; exact hz₀.1.2
      let W_dw : ℝ :=
        (cspPEdge C₁ r_star) ^ ((d₃ + w) * (2 ^ cspL C₁ * r_star - 1) - (d₃ + w).choose 2)
      have hsum_W : ∑ z ∈ Fib, f_z z ≤ (Fib.card : ℝ) * W_dw := by
        calc
          ∑ z ∈ Fib, f_z z ≤ ∑ _z ∈ Fib, W_dw := by
            refine Finset.sum_le_sum (fun z hz => ?_)
            simp only [Fib, γ, Finset.mem_filter, Prod.mk.injEq] at hz
            simpa only [W_dw, hz.2.1, hz.2.2] using hf_bound z
          _ = (Fib.card : ℝ) * W_dw := by rw [Finset.sum_const, nsmul_eq_mul]
      have hcard_le : Fib.card ≤
          2 ^ (2 * (C₁ * r_star)) * (cspQ C₁ - 1) ^ d₃ *
            ((2 ^ cspL C₁ * r_star).choose w * (cspQ C₁ - 1) ^ w) := by
        have hsub : Fib ⊆ Finset.univ.filter (fun z =>
            (threeWayDisagree x u z).card = d₃ ∧ (disagreeSet x z \ disagreeSet x u).card = w) := by
          intro z hz
          simp only [Fib, γ, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hz ⊢
          exact hz.2
        have hc1 := le_trans (Finset.card_le_card hsub) (threeWayFiberCardinality x u d₃ w)
        have hpow : 2 ^ (2 * dHam x u) ≤ 2 ^ (2 * (C₁ * r_star)) :=
          Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left 2 hd_xu)
        calc
          Fib.card ≤ 2 ^ (2 * dHam x u) * (cspQ C₁ - 1) ^ d₃ *
              ((2 ^ cspL C₁ * r_star).choose w * (cspQ C₁ - 1) ^ w) := hc1
          _ ≤ 2 ^ (2 * (C₁ * r_star)) * (cspQ C₁ - 1) ^ d₃ *
              ((2 ^ cspL C₁ * r_star).choose w * (cspQ C₁ - 1) ^ w) := by gcongr
      have hcard_real : (Fib.card : ℝ) ≤
          ((2 ^ (2 * (C₁ * r_star)) : ℕ) : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ d₃ *
            (((2 ^ cspL C₁ * r_star).choose w : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ w) := by
        exact_mod_cast hcard_le
      have hW_nn : 0 ≤ W_dw := pow_nonneg (le_of_lt hp_edge_pos) _
      calc
        (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) * (∑ z ∈ Fib, f_z z)
          ≤ (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) * ((Fib.card : ℝ) * W_dw) :=
            mul_le_mul_of_nonneg_left hsum_W (Nat.cast_nonneg _)
        _ ≤ (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) *
              ((((2 ^ (2 * (C₁ * r_star)) : ℕ) : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ d₃ *
                (((2 ^ cspL C₁ * r_star).choose w : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ w)) * W_dw) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard_real hW_nn)
                (Nat.cast_nonneg _)
        _ ≤ RHS_a := h_s3a d₃ w hdw_le hr_d3
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty, mul_zero]
      exact Real.rpow_nonneg (by norm_num) _
  have hB_card : B_idx.card = (C₁ * r_star + 1) ^ 2 := by
    simp [B_idx, Finset.card_product, sq]
  have hB_pos : (0 : ℝ) < (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) := by positivity
  apply le_of_mul_le_mul_left _ hB_pos
  calc
    (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) * ∑ dw ∈ B_idx, ∑ z ∈ Z_bad with γ z = dw, f_z z
      = ∑ dw ∈ B_idx, (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) * (∑ z ∈ Z_bad with γ z = dw, f_z z) :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ _dw ∈ B_idx, RHS_a := Finset.sum_le_sum hfib_le
    _ = (((C₁ * r_star + 1) ^ 2 : ℕ) : ℝ) * RHS_a := by
        rw [Finset.sum_const, hB_card, nsmul_eq_mul]
open Classical in
private lemma cherryMoments_hy_eval :
    ∀ (C₁ r_star : ℕ) (x w₀ : Fin ((2 : ℕ) ^ cspL C₁ * r_star) → Fin (cspQ C₁)),
      dHam x w₀ ≤ C₁ * r_star →
          ∀ (m : ℕ) (y_prev : Fin m → Fin ((2 : ℕ) ^ cspL C₁ * r_star) → Fin (cspQ C₁)),
            (∀ (t : Fin m), y_prev t ∈ cspPoolCh C₁ r_star x w₀) →
              let P_rem : Finset (Fin ((2 : ℕ) ^ cspL C₁ * r_star) → Fin (cspQ C₁)) :=
                cspPoolCh C₁ r_star x w₀ \ Finset.image y_prev Finset.univ;
              let S_old : Finset (Fin ((2 : ℕ) ^ cspL C₁ * r_star) → Fin (cspQ C₁)) :=
                {x, w₀} ∪ Finset.image y_prev Finset.univ;
              let R_old : Finset (Fin ((2 : ℕ) ^ cspL C₁ * r_star) × Fin (cspQ C₁)) :=
                Finset.image (fun (v : Fin ((2 : ℕ) ^ cspL C₁ * r_star)) => (v, w₀ v))
                    (disagreeSet x w₀) ∪
                  Finset.univ.biUnion fun (t : Fin m) =>
                    Finset.image (fun (v : Fin ((2 : ℕ) ^ cspL C₁ * r_star)) => (v, y_prev t v))
                        (disagreeSet x (y_prev t));
              let F_fresh :
                (Fin ((2 : ℕ) ^ cspL C₁ * r_star) → Fin (cspQ C₁)) → Finset (Fin ((2 : ℕ) ^ cspL
                    C₁ * r_star)) :=
                fun (y : Fin ((2 : ℕ) ^ cspL C₁ * r_star) → Fin (cspQ C₁)) => {v ∈ disagreeSet x
                    y | (v, y v) ∉ R_old};
              let g_y : (Fin ((2 : ℕ) ^ cspL C₁ * r_star) → Fin (cspQ C₁)) → ℝ :=
                fun (y : Fin ((2 : ℕ) ^ cspL C₁ * r_star) → Fin (cspQ C₁)) =>
                ∏ i ∈ (Finset.image Sum.inr {y} ∪ Finset.image Sum.inl (homQueries y)) \ cspUCh
                    x w₀ m y_prev,
                  cspPIota C₁ r_star i;
                  ∀ y ∈ P_rem,
                    g_y y = cspPKeep C₁ r_star * cspPEdge C₁ r_star ^ (homQueries y \
                        S_old.biUnion homQueries).card ∧
                      (80 : ℕ) * (F_fresh y).card ≤ (61 : ℕ) * r_star ∧ (F_fresh y).card <
                          r_star + (1 : ℕ) := by
  classical
  intro C₁ r_star x w₀ hd_xw₀ m y_prev hpool P_rem S_old R_old F_fresh g_y y hy
  rcases Finset.mem_sdiff.mp hy with ⟨hy_pool, hy_not_img⟩
  simp only [cspPoolCh, Finset.mem_filter, Finset.mem_univ, true_and] at hy_pool
  rcases hy_pool with ⟨hy_ne_x, hy_ne_w0, hd_xy, hov_xy, hd3_xy⟩
  have hset_eq :
      (({y} : Finset (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))).image Sum.inr ∪
          (homQueries y).image Sum.inl) \ cspUCh x w₀ m y_prev =
      {Sum.inr y} ∪ (homQueries y \ S_old.biUnion homQueries).image Sum.inl := by
    ext i
    rcases i with q_e | z_v
    · simp only [cspUCh, S_old, Finset.mem_sdiff, Finset.mem_union, Finset.mem_image,
        Finset.mem_singleton, Finset.mem_insert, Finset.mem_univ, true_and,
        Finset.mem_biUnion, Sum.inl.injEq, reduceCtorEq]
      constructor
      · rintro ⟨(⟨_, _, h⟩ | ⟨t, ht, rfl⟩), hnot⟩
        · nomatch h
        · refine Or.inr ⟨t, ⟨ht, ?_⟩, rfl⟩
          rintro ⟨z, (rfl | rfl) | ⟨idx, rfl⟩, htz⟩
          · exact hnot (Or.inr ⟨t, Or.inl (Or.inl htz), rfl⟩)
          · exact hnot (Or.inr ⟨t, Or.inl (Or.inr htz), rfl⟩)
          · exact hnot (Or.inr ⟨t, Or.inr ⟨idx, htz⟩, rfl⟩)
      · rintro (h | ⟨t, ⟨ht, hnot⟩, rfl⟩)
        · nomatch h
        · refine ⟨Or.inr ⟨t, ht, rfl⟩, ?_⟩
          rintro ((⟨_, _, h⟩ | ⟨_, h⟩) | ⟨t', (htx | htw) | ⟨idx, hti⟩, rfl⟩)
          · nomatch h
          · nomatch h
          · exact hnot ⟨x, Or.inl (Or.inl rfl), htx⟩
          · exact hnot ⟨w₀, Or.inl (Or.inr rfl), htw⟩
          · exact hnot ⟨y_prev idx, Or.inr ⟨idx, rfl⟩, hti⟩
    · simp only [cspUCh, S_old, Finset.mem_sdiff, Finset.mem_union, Finset.mem_image,
        Finset.mem_singleton, Finset.mem_insert, Finset.mem_univ, true_and,
        Finset.mem_biUnion, Sum.inr.injEq, reduceCtorEq]
      constructor
      · rintro ⟨(⟨z, rfl, rfl⟩ | ⟨_, _, h⟩), _⟩
        · exact Or.inl rfl
        · nomatch h
      · rintro (rfl | ⟨_, _, h⟩)
        · refine ⟨Or.inl ⟨z_v, rfl, rfl⟩, ?_⟩
          rintro ((⟨z, rfl | rfl, rfl⟩ | ⟨idx, rfl⟩) | ⟨_, _, h⟩)
          · exact hy_ne_x rfl
          · exact hy_ne_w0 rfl
          · exact hy_not_img (Finset.mem_image.mpr ⟨idx, Finset.mem_univ idx, rfl⟩)
          · nomatch h
        · nomatch h
  have hg_eq : g_y y = cspPKeep C₁ r_star *
      (cspPEdge C₁ r_star) ^ ((homQueries y \ S_old.biUnion homQueries).card) := by
    dsimp only [g_y]
    rw [hset_eq, Finset.prod_union]
    · rw [Finset.prod_singleton, Finset.prod_image (fun _ _ _ _ h => Sum.inl.inj h)]
      simp [cspPIota]
    · rw [Finset.disjoint_left]
      intro i hi1 hi2
      rw [Finset.mem_singleton] at hi1
      subst hi1
      rcases Finset.mem_image.mp hi2 with ⟨_, _, h⟩
      cases h
  let B_w0 := (disagreeSet x w₀ ∩ disagreeSet x y) \ threeWayDisagree x w₀ y
  have hdisj_FB : Disjoint (F_fresh y) B_w0 := by
    rw [Finset.disjoint_left]
    intro v hvF hvB
    simp only [F_fresh, Finset.mem_filter] at hvF
    simp only [B_w0, threeWayDisagree, disagreeSet, Finset.mem_sdiff, Finset.mem_inter,
      Finset.mem_filter, Finset.mem_univ, true_and] at hvB
    have hyw : w₀ v = y v := by
      by_contra hne
      exact hvB.2 ⟨hvB.1.1, hvB.1.2, hne⟩
    apply hvF.2
    rw [← hyw]
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,
      Finset.mem_filter.mpr ⟨Finset.mem_univ v, hvB.1.1⟩, rfl⟩)
  have hFB_sub : F_fresh y ∪ B_w0 ⊆ disagreeSet x y := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvF | hvB
    · exact (Finset.mem_filter.mp hvF).1
    · exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp hvB).1).2
  have hFB_card : (F_fresh y).card + B_w0.card ≤ r_star := by
    rw [← Finset.card_union_of_disjoint hdisj_FB]
    exact le_trans (Finset.card_le_card hFB_sub) (le_of_eq hd_xy)
  have hinter_le : (disagreeSet x w₀ ∩ disagreeSet x y).card ≤
      B_w0.card + (threeWayDisagree x w₀ y).card
      := by
    have hcov : disagreeSet x w₀ ∩ disagreeSet x y ⊆ B_w0 ∪ threeWayDisagree x w₀ y := by
      intro v hv
      by_cases hd3 : v ∈ threeWayDisagree x w₀ y
      · exact Finset.mem_union_right _ hd3
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hv, hd3⟩)
    exact le_trans (Finset.card_le_card hcov) (Finset.card_union_le _ _)
  have hd3_80 : 80 * (threeWayDisagree x w₀ y).card ≤ r_star := by
    simpa [cspInvEta0] using hd3_xy
  refine ⟨hg_eq, by omega, by omega⟩
open Classical in
private lemma cherryMoments_h_s3 :
    ∀ (C₁ : ℕ),
      (3 : ℕ) ≤ C₁ →
        ∀ (r_star : ℕ),
          (1000 : ℕ) * C₁ < r_star →
            (0 : ℝ) < cspSigmaEdge C₁ r_star →
              (0 : ℝ) < cspPEdge C₁ r_star →
                (4 : ℝ) * (2 : ℝ) ^ cspL C₁ * (↑(cspQ C₁ - (1 : ℕ)) : ℝ) *
                      cspPEdge C₁ r_star ^ ((2 : ℕ) ^ cspL C₁ * r_star - (1 : ℕ)) =
                    (2 : ℝ) ^ (-(↑(cspGamma0 C₁) : ℝ)) →
                  cspSigmaEdge C₁ r_star * (↑r_star : ℝ) / (2 : ℝ) ≤ (10001 / 10000 : ℝ) *
                      (↑(cspBeta0 C₁) : ℝ) →
                    (∀ (s : ℕ),
                        (↑(((2 : ℕ) ^ cspL C₁ * r_star).choose s) : ℝ) * (↑(cspQ C₁ - (1 : ℕ)) :
                            ℝ) ^ s *
                            cspPEdge C₁ r_star ^ (s * ((2 : ℕ) ^ cspL C₁ * r_star - (1 : ℕ))) ≤
                          (2 : ℝ) ^ ((2 : ℝ) * (↑r_star : ℝ) - (↑(cspGamma0 C₁) : ℝ) * (↑s : ℝ))) →
                      (0 : ℝ) < cspPKeep C₁ r_star →
                        cspPKeep C₁ r_star ≤ (2 : ℝ) ^ (-(747 / 1000 : ℝ) * (↑(cspLam0 C₁) : ℝ)
                            * (↑r_star : ℝ)) →
                          (∀ (d₃ w : ℕ),
                              d₃ + w ≤ C₁ * r_star →
                                r_star < cspInvEta0 C₁ * d₃ →
                                  (↑((C₁ * r_star + (1 : ℕ)) ^ (2 : ℕ)) : ℝ) *
                                      ((↑((2 : ℕ) ^ ((2 : ℕ) * (C₁ * r_star))) : ℝ) * (↑(cspQ C₁
                                          - (1 : ℕ)) : ℝ) ^ d₃ *
                                          ((↑(((2 : ℕ) ^ cspL C₁ * r_star).choose w) : ℝ) *
                                            (↑(cspQ C₁ - (1 : ℕ)) : ℝ) ^ w) *
                                        cspPEdge C₁ r_star ^
                                          ((d₃ + w) * ((2 : ℕ) ^ cspL C₁ * r_star - (1 : ℕ)) -
                                              (d₃ + w).choose (2 : ℕ))) ≤
                                    (2 : ℝ) ^ (-((12 : ℝ) * (↑(C₁ ^ (2 : ℕ)) : ℝ)) * (↑(cspLam0
                                        C₁) : ℝ) * (↑r_star : ℝ))) ∧
                            ∀ (s : ℕ),
                              (80 : ℕ) * s ≤ (61 : ℕ) * r_star →
                                (↑(r_star + (1 : ℕ)) : ℝ) *
                                    ((↑(r_star + (1 : ℕ)) : ℝ) *
                                          (2 : ℝ) ^ ((1 / 100 : ℝ) * (↑(cspLam0 C₁) : ℝ) *
                                              (↑r_star : ℝ)) *
                                        ((↑(((2 : ℕ) ^ cspL C₁ * r_star).choose s) : ℝ) *
                                            (↑(cspQ C₁ - (1 : ℕ)) : ℝ) ^ s) *
                                      (cspPKeep C₁ r_star *
                                        cspPEdge C₁ r_star ^
                                          (s * ((2 : ℕ) ^ cspL C₁ * r_star - (1 : ℕ)) - s.choose
                                              (2 : ℕ)))) ≤
                                  (2 : ℝ) ^ (-(72 / 100 : ℝ) * (↑(cspLam0 C₁) : ℝ) * (↑r_star :
                                      ℝ)) := by
  classical
  intro C₁ hC₁ r_star hr hσ_pos hp_edge_pos h_cal hσ_up h_binom_edge hp_keep_pos hp_keep_up
  have hlam_1000C1 : 1000 * C₁ ≤ cspLam0 C₁ := (lam0_ge_1000_C1 C₁ hC₁).2.1
  have hlam_ge : 3000 ≤ cspLam0 C₁ := by omega
  have hbeta_eq : (cspBeta0 C₁ : ℝ) = 6 * (cspLam0 C₁ : ℝ) := by
    unfold cspBeta0; push_cast; ring
  have hgamma_eq : (cspGamma0 C₁ : ℝ) = 5 * (cspLam0 C₁ : ℝ) := by
    unfold cspGamma0; push_cast; ring
  have hC₁_le_L : C₁ ≤ cspL C₁ := by
    have hc2 : 1 ≤ C₁ ^ 2 := Nat.one_le_pow 2 C₁ (by omega)
    unfold cspL cspInvEta0
    nlinarith only [hc2, hlam_1000C1]
  have hC₁_le_2L : C₁ ≤ 2 ^ cspL C₁ :=
    le_trans hC₁_le_L (Nat.le_of_lt Nat.lt_two_pow_self)
  have hCr_le_N : C₁ * r_star ≤ 2 ^ cspL C₁ * r_star :=
    Nat.mul_le_mul_right r_star hC₁_le_2L
  have hr_le_Cr : r_star ≤ C₁ * r_star := by
    simpa using Nat.mul_le_mul_right r_star (show 1 ≤ C₁ by omega)
  have hr_le_N : r_star ≤ 2 ^ cspL C₁ * r_star := le_trans hr_le_Cr hCr_le_N
  have h_edge_split :=
    @cherryMoments_h_edge_split C₁ r_star
  have h_large_d3 :=
    @cherryMoments_h_large_d3 C₁ hC₁ r_star hr hσ_pos hp_edge_pos h_cal hσ_up h_binom_edge
        hlam_1000C1 hlam_ge hbeta_eq hCr_le_N h_edge_split
  have h_small_s :=
    @cherryMoments_h_small_s C₁ hC₁ r_star hr hσ_pos hp_edge_pos hσ_up h_binom_edge
        hp_keep_pos hp_keep_up hlam_ge hbeta_eq hgamma_eq hr_le_N h_edge_split
  exact ⟨h_large_d3, h_small_s⟩
end Helpers
end HighDimSteinerSpanners.Proofs.CSP
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.CSP
noncomputable section
namespace HighDimSteinerSpanners.Proofs.CSP
theorem _root_.solution (C₁ : ℕ) (hC₁ : 3 ≤ C₁) (r_star : ℕ) (hr : 1000 * C₁ <
    r_star)
    (hσ_pos : 0 < cspSigmaEdge C₁ r_star)
    (hp_edge_pos : 0 < cspPEdge C₁ r_star)
    (hp_edge_lt1 : cspPEdge C₁ r_star < 1)
    (h_cal : (4 : ℝ) * (2 : ℝ) ^ cspL C₁ * ((cspQ C₁ - 1 : ℕ) : ℝ) *
      (cspPEdge C₁ r_star) ^ (2 ^ cspL C₁ * r_star - 1) = (2 : ℝ) ^ (-(cspGamma0 C₁ : ℝ)))
    (hσ_up : cspSigmaEdge C₁ r_star * (r_star : ℝ) / 2 ≤
      (10001 / 10000 : ℝ) * (cspBeta0 C₁ : ℝ))
    (h_binom_edge : ∀ s : ℕ,
      ((2 ^ cspL C₁ * r_star).choose s : ℝ) * ((cspQ C₁ - 1 : ℕ) : ℝ) ^ s *
        (cspPEdge C₁ r_star) ^ (s * (2 ^ cspL C₁ * r_star - 1)) ≤
        (2 : ℝ) ^ (2 * (r_star : ℝ) - (cspGamma0 C₁ : ℝ) * (s : ℝ)))
    (hp_keep_pos : 0 < cspPKeep C₁ r_star)
    (hp_keep_up : cspPKeep C₁ r_star ≤
      (2 : ℝ) ^ (- (747 / 1000 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) :
    (∀ x u : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁), dHam x u ≤ C₁ * r_star →
      ∑ z ∈ Finset.univ.filter (fun z : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁) =>
          dHam x z ≤ C₁ * r_star ∧
          r_star < cspInvEta0 C₁ * (threeWayDisagree x u z).card),
        (cspPEdge C₁ r_star) ^ ((homQueries z \ (homQueries x ∪ homQueries u)).card) ≤
        (2 : ℝ) ^ (- (12 * (C₁ ^ 2 : ℕ) : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) ∧
    (∀ x w₀ : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁), dHam x w₀ ≤ C₁ * r_star →
      ∀ m < cspKCh C₁, ∀ y_prev : Fin m → (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)),
        (∀ t : Fin m, y_prev t ∈ cspPoolCh C₁ r_star x w₀) →
        ∑ y ∈ cspPoolCh C₁ r_star x w₀ \ Finset.univ.image y_prev,
          (∏ i ∈ (({y} : Finset (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))).image Sum.inr ∪
              (homQueries y).image Sum.inl) \ cspUCh x w₀ m y_prev,
            cspPIota C₁ r_star i) ≤
          (2 : ℝ) ^ (- (72 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))) :=
by
  classical
  have h_s3 :=
    @cherryMoments_h_s3 C₁ hC₁ r_star hr hσ_pos hp_edge_pos h_cal hσ_up h_binom_edge hp_keep_pos
        hp_keep_up
  obtain ⟨h_s3a, h_s3b⟩ := h_s3
  clear hr hσ_pos h_cal hσ_up h_binom_edge hp_keep_up
  have h_d3_sum :=
    @cherryMoments_h_d3_sum C₁ hC₁ r_star hp_edge_pos hp_edge_lt1 h_s3a
  constructor
  · exact h_d3_sum
  · intro x w₀ hd_xw₀ m hm y_prev hpool
    let P_rem := cspPoolCh C₁ r_star x w₀ \ Finset.univ.image y_prev
    let S_old : Finset (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁)) :=
      ({x, w₀} : Finset _) ∪ Finset.univ.image y_prev
    let R_old : Finset (Fin (2 ^ cspL C₁ * r_star) × Fin (cspQ C₁)) :=
      (disagreeSet x w₀).image (fun v => (v, w₀ v)) ∪
        Finset.univ.biUnion (fun t : Fin m =>
          (disagreeSet x (y_prev t)).image (fun v => (v, y_prev t v)))
    let F_fresh := fun y : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁) =>
      (disagreeSet x y).filter (fun v => (v, y v) ∉ R_old)
    let g_y := fun y : Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁) =>
      ∏ i ∈ (({y} : Finset (Fin (2 ^ cspL C₁ * r_star) → Fin (cspQ C₁))).image Sum.inr ∪
          (homQueries y).image Sum.inl) \ cspUCh x w₀ m y_prev,
        cspPIota C₁ r_star i
    let RHS_b : ℝ := (2 : ℝ) ^ (- (72 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ))
    have hR_card : R_old.card ≤ (C₁ + cspKCh C₁) * r_star := by
      have hc1 : ((disagreeSet x w₀).image (fun v => (v, w₀ v))).card ≤ C₁ * r_star :=
        le_trans Finset.card_image_le hd_xw₀
      have hc2 : (Finset.univ.biUnion (fun t : Fin m =>
          (disagreeSet x (y_prev t)).image (fun v => (v, y_prev t v)))).card ≤ cspKCh C₁ * r_star
              := by
        calc
          (Finset.univ.biUnion (fun t : Fin m =>
              (disagreeSet x (y_prev t)).image (fun v => (v, y_prev t v)))).card
            ≤ ∑ t : Fin m, ((disagreeSet x (y_prev t)).image (fun v => (v, y_prev t v))).card :=
              Finset.card_biUnion_le
          _ ≤ ∑ _t : Fin m, r_star := by
              refine Finset.sum_le_sum (fun t _ => ?_)
              have ht := hpool t
              simp only [cspPoolCh, Finset.mem_filter, Finset.mem_univ, true_and] at ht
              exact le_trans Finset.card_image_le (le_of_eq ht.2.2.1)
          _ = m * r_star := by simp
          _ ≤ cspKCh C₁ * r_star := Nat.mul_le_mul_right r_star (le_of_lt hm)
      calc
        R_old.card ≤ ((disagreeSet x w₀).image (fun v => (v, w₀ v))).card +
            (Finset.univ.biUnion (fun t : Fin m =>
              (disagreeSet x (y_prev t)).image (fun v => (v, y_prev t v)))).card :=
          Finset.card_union_le _ _
        _ ≤ C₁ * r_star + cspKCh C₁ * r_star := Nat.add_le_add hc1 hc2
        _ = (C₁ + cspKCh C₁) * r_star := (add_mul C₁ (cspKCh C₁) r_star).symm
    have hR_card21 : R_old.card ≤ 21 * C₁ ^ 2 * r_star := by
      have hc21 : C₁ + cspKCh C₁ ≤ 21 * C₁ ^ 2 := by
        unfold cspKCh
        nlinarith only [hC₁]
      exact le_trans hR_card (Nat.mul_le_mul_right r_star hc21)
    have hy_eval : ∀ y ∈ P_rem,
        g_y y = cspPKeep C₁ r_star *
          (cspPEdge C₁ r_star) ^ (homQueries y \ S_old.biUnion homQueries).card ∧
        80 * (F_fresh y).card ≤ 61 * r_star ∧ (F_fresh y).card < r_star + 1 :=
      @cherryMoments_hy_eval C₁ r_star x w₀ hd_xw₀ m y_prev hpool
    have hg_bound : ∀ y ∈ P_rem,
        g_y y ≤ cspPKeep C₁ r_star *
          (cspPEdge C₁ r_star) ^
            ((F_fresh y).card * (2 ^ cspL C₁ * r_star - 1) - (F_fresh y).card.choose 2) := by
      intro y hy
      rw [(hy_eval y hy).1]
      have hfresh : ∀ v ∈ F_fresh y, ∀ z ∈ S_old, y v ≠ z v := by
        intro v hv z hz
        simp only [F_fresh, disagreeSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        simp only [S_old, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          Finset.mem_image, Finset.mem_univ, true_and] at hz
        rcases hz with (rfl | rfl) | ⟨t, rfl⟩
        · exact hv.1.symm
        · intro heq
          apply hv.2
          rw [heq]
          exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,
            Finset.mem_filter.mpr ⟨Finset.mem_univ v, by rw [← heq]; exact hv.1⟩, rfl⟩)
        · intro heq
          apply hv.2
          rw [heq]
          refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ t, ?_⟩)
          exact Finset.mem_image.mpr ⟨v,
            Finset.mem_filter.mpr ⟨Finset.mem_univ v, by rw [← heq]; exact hv.1⟩, rfl⟩
      have hq_le := freshHomQueryCardinality y S_old (F_fresh y) hfresh
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one (le_of_lt hp_edge_pos) (le_of_lt hp_edge_lt1) hq_le)
        (le_of_lt hp_keep_pos)
    have hmaps : ∀ y ∈ P_rem, (F_fresh y).card ∈ Finset.range (r_star + 1) := by
      intro y hy
      exact Finset.mem_range.mpr (hy_eval y hy).2.2
    rw [← Finset.sum_fiberwise_of_maps_to hmaps g_y]
    have hfib_le : ∀ s ∈ Finset.range (r_star + 1),
        ((r_star + 1 : ℕ) : ℝ) * (∑ y ∈ P_rem with (F_fresh y).card = s, g_y y) ≤ RHS_b := by
      intro s _
      let Fib := P_rem.filter (fun y => (F_fresh y).card = s)
      change ((r_star + 1 : ℕ) : ℝ) * (∑ y ∈ Fib, g_y y) ≤ RHS_b
      by_cases hne : Fib.Nonempty
      · obtain ⟨y₀, hy₀⟩ := hne
        rcases Finset.mem_filter.mp hy₀ with ⟨hy₀_rem, rfl⟩
        have hs_61 : 80 * (F_fresh y₀).card ≤ 61 * r_star := (hy_eval y₀ hy₀_rem).2.1
        let W_s : ℝ := cspPKeep C₁ r_star *
          (cspPEdge C₁ r_star) ^ ((F_fresh y₀).card * (2 ^ cspL C₁ * r_star - 1) -
            (F_fresh y₀).card.choose 2)
        have hsum_W : ∑ y ∈ Fib, g_y y ≤ (Fib.card : ℝ) * W_s := by
          calc
            ∑ y ∈ Fib, g_y y ≤ ∑ _y ∈ Fib, W_s := by
              refine Finset.sum_le_sum (fun y hy => ?_)
              rcases Finset.mem_filter.mp hy with ⟨hy_rem, hy_eq⟩
              simpa only [W_s, ← hy_eq] using hg_bound y hy_rem
            _ = (Fib.card : ℝ) * W_s := by rw [Finset.sum_const, nsmul_eq_mul]
        have hsub : Fib ⊆ Finset.univ.filter (fun y =>
            (F_fresh y).card = (F_fresh y₀).card ∧ dHam x y ≤ r_star) := by
          intro y hy
          rcases Finset.mem_filter.mp hy with ⟨hy_rem, hy_eq⟩
          have hy_pool := (Finset.mem_sdiff.mp hy_rem).1
          simp only [cspPoolCh, Finset.mem_filter, Finset.mem_univ, true_and] at hy_pool
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy_eq, le_of_eq hy_pool.2.2.1⟩
        have hcard_le1 : (Fib.card : ℝ) ≤
            ((Finset.univ.filter (fun y =>
              (F_fresh y).card = (F_fresh y₀).card ∧ dHam x y ≤ r_star)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        have hcard_real : (Fib.card : ℝ) ≤
            ((r_star + 1 : ℕ) : ℝ) *
              (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
              (((2 ^ cspL C₁ * r_star).choose (F_fresh y₀).card : ℝ) *
                ((cspQ C₁ - 1 : ℕ) : ℝ) ^ (F_fresh y₀).card) :=
          le_trans hcard_le1 (cherryFiberCardinality C₁ r_star hC₁ x R_old hR_card21 (F_fresh
              y₀).card)
        have hW_nn : 0 ≤ W_s :=
          mul_nonneg (le_of_lt hp_keep_pos) (pow_nonneg (le_of_lt hp_edge_pos) _)
        calc
          ((r_star + 1 : ℕ) : ℝ) * (∑ y ∈ Fib, g_y y)
            ≤ ((r_star + 1 : ℕ) : ℝ) * ((Fib.card : ℝ) * W_s) :=
              mul_le_mul_of_nonneg_left hsum_W (Nat.cast_nonneg _)
          _ ≤ ((r_star + 1 : ℕ) : ℝ) *
                ((((r_star + 1 : ℕ) : ℝ) *
                  (2 : ℝ) ^ ((1 / 100 : ℝ) * (cspLam0 C₁ : ℝ) * (r_star : ℝ)) *
                  (((2 ^ cspL C₁ * r_star).choose (F_fresh y₀).card : ℝ) *
                    ((cspQ C₁ - 1 : ℕ) : ℝ) ^ (F_fresh y₀).card)) * W_s) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard_real hW_nn)
                  (Nat.cast_nonneg _)
          _ ≤ RHS_b := h_s3b (F_fresh y₀).card hs_61
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty, mul_zero]
        exact Real.rpow_nonneg (by norm_num) _
    have hr1_pos : (0 : ℝ) < ((r_star + 1 : ℕ) : ℝ) := by positivity
    apply le_of_mul_le_mul_left _ hr1_pos
    calc
      ((r_star + 1 : ℕ) : ℝ) * ∑ s ∈ Finset.range (r_star + 1), ∑ y ∈ P_rem with (F_fresh
          y).card = s, g_y y
        = ∑ s ∈ Finset.range (r_star + 1), ((r_star + 1 : ℕ) : ℝ) * (∑ y ∈ P_rem with (F_fresh
            y).card = s, g_y y) :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ _s ∈ Finset.range (r_star + 1), RHS_b := Finset.sum_le_sum hfib_le
      _ = ((r_star + 1 : ℕ) : ℝ) * RHS_b := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
end HighDimSteinerSpanners.Proofs.CSP
