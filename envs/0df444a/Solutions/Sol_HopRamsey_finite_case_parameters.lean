-- Prove2me | solution 1 for HopRamsey.finite_case_parameters
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T00:36:18.430165+00:00
-- url     : https://prove2.me/submissions/190ae5c5-af2a-49eb-bb84-bfc0c2aedf24

import Mathlib
import Definitions.Def_HopRamsey_Fig2Params
import Definitions.Def_HopRamsey_polylogBound

namespace HopRamsey.FZ

open HopRamsey

namespace P2

variable (P : Fig2Params)

lemma logN1_gt_one (hN : 2 ≤ P.N) : 1 < Real.logb 2 ((P.N : ℝ) + 1) := by
  rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity)]
  have : (2 : ℝ) ≤ P.N := by exact_mod_cast hN
  simp; linarith

lemma L_pos (hN : 2 ≤ P.N) : 1 ≤ P.L := by
  unfold Fig2Params.L
  rw [Nat.one_le_iff_ne_zero, ne_eq, Nat.ceil_eq_zero, not_le]
  exact Real.logb_pos (by norm_num) (logN1_gt_one P hN)

lemma L_le (hN : 2 ≤ P.N) : (P.L : ℝ) < Real.logb 2 (Real.logb 2 ((P.N : ℝ) + 1)) + 1 := by
  unfold Fig2Params.L
  exact Nat.ceil_lt_add_one (Real.logb_pos (by norm_num) (logN1_gt_one P hN)).le

lemma L_ge : Real.logb 2 (Real.logb 2 ((P.N : ℝ) + 1)) ≤ P.L := by
  unfold Fig2Params.L; exact Nat.le_ceil _

lemma two_pow_L_ge (hN : 2 ≤ P.N) : Real.logb 2 ((P.N : ℝ) + 1) ≤ 2 ^ P.L := by
  have h1 := L_ge P
  have hx := logN1_gt_one P hN
  calc Real.logb 2 ((P.N : ℝ) + 1) = (2 : ℝ) ^ (Real.logb 2 (Real.logb 2 ((P.N : ℝ) + 1))) := by
        rw [Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]
    _ ≤ (2 : ℝ) ^ (P.L : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    _ = 2 ^ P.L := by norm_cast

lemma two_pow_Lsub1_lt (hN : 2 ≤ P.N) : (2 : ℝ) ^ (P.L - 1) < Real.logb 2 ((P.N : ℝ) + 1) := by
  have h1 := L_le P hN
  have hL := L_pos P hN
  have hx := logN1_gt_one P hN
  have : ((P.L - 1 : ℕ) : ℝ) < Real.logb 2 (Real.logb 2 ((P.N : ℝ) + 1)) := by
    push_cast [hL]; linarith
  calc (2 : ℝ) ^ (P.L - 1) = (2 : ℝ) ^ (((P.L - 1 : ℕ)) : ℝ) := by norm_cast
    _ < (2 : ℝ) ^ (Real.logb 2 (Real.logb 2 ((P.N : ℝ) + 1))) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) this
    _ = _ := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)

lemma mu_cast (ℓ : ℕ) : ((P.mu ℓ : ℕ) : ℝ) = (2 : ℝ) ^ (2 ^ (P.L - ℓ)) := by
  unfold Fig2Params.mu; push_cast; ring

lemma mu_ge_two (ℓ : ℕ) (hℓ : ℓ ≤ P.L) : (2 : ℝ) ≤ P.mu ℓ := by
  rw [mu_cast]
  calc (2 : ℝ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (2 ^ (P.L - ℓ)) := pow_le_pow_right₀ (by norm_num) (Nat.one_le_two_pow)

lemma mu_pos (ℓ : ℕ) : (0 : ℝ) < P.mu ℓ := by rw [mu_cast]; positivity

lemma mu_L : P.mu P.L = 2 := by unfold Fig2Params.mu; simp

lemma mu_sq (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) : (P.mu (ℓ - 1) : ℝ) = (P.mu ℓ : ℝ) ^ 2 := by
  rw [mu_cast, mu_cast, ← pow_mul]
  congr 1
  have : P.L - (ℓ - 1) = (P.L - ℓ) + 1 := by omega
  rw [this, pow_succ]

lemma mu_zero_gt (hN : 2 ≤ P.N) : (P.N : ℝ) < P.mu 0 := by
  rw [mu_cast]
  have h := two_pow_L_ge P hN
  have hx := logN1_gt_one P hN
  calc (P.N : ℝ) < P.N + 1 := by linarith
    _ = (2 : ℝ) ^ (Real.logb 2 ((P.N : ℝ) + 1)) := by
        rw [Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
    _ ≤ (2 : ℝ) ^ ((2 ^ (P.L - 0) : ℕ) : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        push_cast; simpa using h
    _ = _ := by norm_cast

lemma mu_le_of_one_le (hN : 2 ≤ P.N) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : (P.mu ℓ : ℝ) < P.N + 1 := by
  rw [mu_cast]
  have h := two_pow_Lsub1_lt P hN
  calc (2 : ℝ) ^ (2 ^ (P.L - ℓ)) ≤ (2 : ℝ) ^ (2 ^ (P.L - 1)) := by
        apply pow_le_pow_right₀ (by norm_num)
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = (2 : ℝ) ^ (((2 ^ (P.L - 1) : ℕ)) : ℝ) := by norm_cast
    _ < (2 : ℝ) ^ (Real.logb 2 ((P.N : ℝ) + 1)) := by
        apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
        push_cast; exact h
    _ = _ := Real.rpow_logb (by norm_num) (by norm_num) (by positivity)

lemma delta_pos (hN : 2 ≤ P.N) : 0 < P.delta := by
  unfold Fig2Params.delta; have := logN1_gt_one P hN; positivity

lemma delta_lt_one (hN : 2 ≤ P.N) : P.delta < 1 := by
  unfold Fig2Params.delta
  have := logN1_gt_one P hN
  rw [inv_lt_one₀ (by positivity)]
  nlinarith

lemma delta_eq (hN : 2 ≤ P.N) :
    Real.log (1 / P.delta) = 2 * Real.log (Real.logb 2 ((P.N : ℝ) + 1)) := by
  unfold Fig2Params.delta
  rw [one_div, inv_inv, Real.log_pow]; push_cast; ring

/-- `L·δ ≤ 1`. -/
lemma L_delta_le (hN : 2 ≤ P.N) : (P.L : ℝ) * P.delta ≤ 1 := by
  set x := Real.logb 2 ((P.N : ℝ) + 1) with hx
  have hx1 : 1 < x := logN1_gt_one P hN
  have hL := L_le P hN
  have hlog : Real.logb 2 x ≤ 2 * (x - 1) := by
    rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
    have h1 := Real.log_le_sub_one_of_pos (by linarith : 0 < x)
    have h2 : (1:ℝ)/2 ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    nlinarith
  have hd : P.delta = (x ^ 2)⁻¹ := rfl
  rw [hd, ← div_eq_mul_inv, div_le_one (by positivity)]
  nlinarith

lemma k_ge (hN : 2 ≤ P.N) (hε : 0 < P.ε) (hε1 : P.ε < 1) (hΦ : 2 ≤ P.Φ) :
    4 * (Real.log P.N + Real.log (2 / P.delta)) ≤ (P.k : ℝ) := by
  have hδ0 := delta_pos P hN
  have hδ1 := delta_lt_one P hN
  have hlogΦ : 1 ≤ Real.logb 2 P.Φ := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; simpa using hΦ
  have hl2 : 0 ≤ Real.log (2 / P.delta) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
  have hlN : 0 ≤ Real.log P.N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ P.N))
  have hpow : 1 ≤ (1 + 2 * P.delta) ^ (Real.logb 2 P.Φ) :=
    Real.one_le_rpow (by linarith) (by linarith)
  unfold Fig2Params.k
  refine le_trans ?_ (Nat.le_ceil _)
  set B := Real.log P.N + Real.log (2 / P.delta) * Real.logb 2 P.Φ
  have hB : Real.log P.N + Real.log (2 / P.delta) ≤ B := by
    simp only [B]; nlinarith
  have hB0 : 0 ≤ B := by linarith
  have h4 : 4 ≤ 4 / P.ε := by rw [le_div_iff₀ hε]; linarith
  calc 4 * (Real.log P.N + Real.log (2 / P.delta)) ≤ 4 * B := by linarith
    _ ≤ (4 / P.ε) * B := by nlinarith
    _ ≤ (4 / P.ε) * (1 + 2 * P.delta) ^ (Real.logb 2 P.Φ) * B := by
        have : 0 ≤ 4 / P.ε := by positivity
        have := mul_le_mul_of_nonneg_left hpow (mul_nonneg this hB0)
        nlinarith


section Std

set_option linter.unusedSectionVars false
variable (hN : 2 ≤ P.N) (hε : 0 < P.ε) (hε1 : P.ε < 1) (hΦ : 2 ≤ P.Φ)
include hN hε hε1 hΦ

lemma log2_delta_nonneg : 0 ≤ Real.log (2 / P.delta) :=
  Real.log_nonneg (by rw [le_div_iff₀ (delta_pos P hN)]; linarith [delta_lt_one P hN])

lemma k_pos : 0 < P.k := by
  have h := k_ge P hN hε hε1 hΦ
  have hl2 := log2_delta_nonneg P hN hε hε1 hΦ
  have hlN : 0 < Real.log P.N := Real.log_pos (by exact_mod_cast (by omega : 1 < P.N))
  have : (0 : ℝ) < P.k := by linarith
  exact_mod_cast this

lemma log_mu_arg_pos (ℓ : ℕ) (hℓ : ℓ ≤ P.L) : 0 < Real.log (2 * (P.mu ℓ : ℝ) / P.delta) := by
  apply Real.log_pos
  have := mu_ge_two P ℓ hℓ
  have hd := delta_pos P hN
  have hd1 := delta_lt_one P hN
  rw [lt_div_iff₀ hd]; nlinarith

lemma p_pos (ℓ : ℕ) (hℓ : ℓ ≤ P.L) : 0 < P.p ℓ := by
  unfold Fig2Params.p
  have := log_mu_arg_pos P hN hε hε1 hΦ ℓ hℓ
  have : (0 : ℝ) < P.k := by exact_mod_cast k_pos P hN hε hε1 hΦ
  positivity

lemma pk_eq (ℓ : ℕ) : P.p ℓ * P.k = 2 * Real.log (2 * (P.mu ℓ : ℝ) / P.delta) := by
  have : (P.k : ℝ) ≠ 0 := by exact_mod_cast (k_pos P hN hε hε1 hΦ).ne'
  unfold Fig2Params.p; field_simp

lemma p_le_one (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) : P.p ℓ ≤ 1 := by
  have hk : (0 : ℝ) < P.k := by exact_mod_cast k_pos P hN hε hε1 hΦ
  have hpk := pk_eq P hN hε hε1 hΦ ℓ
  have hkge := k_ge P hN hε hε1 hΦ
  have hd := delta_pos P hN
  have hd1 := delta_lt_one P hN
  have hmu := mu_le_of_one_le P hN ℓ h1
  have hmu2 := mu_ge_two P ℓ hℓ
  have hNr : (2 : ℝ) ≤ P.N := by exact_mod_cast hN
  -- 2 ln(2μ/δ) ≤ 2 ln 2 + 2 ln (N+1) + 2 ln (1/δ) ≤ 4 ln N + 4 ln (2/δ) ≤ k
  have e1 : Real.log (2 * (P.mu ℓ : ℝ) / P.delta) =
      Real.log 2 + Real.log (P.mu ℓ) + Real.log (1 / P.delta) := by
    rw [mul_div_assoc, Real.log_mul (by norm_num) (by positivity),
      div_eq_mul_one_div (P.mu ℓ : ℝ), Real.log_mul (by positivity) (by positivity)]; ring
  have e2 : Real.log (2 / P.delta) = Real.log 2 + Real.log (1 / P.delta) := by
    rw [div_eq_mul_one_div 2, Real.log_mul (by norm_num) (by positivity)]
  have e3 : Real.log (P.mu ℓ) ≤ Real.log ((P.N : ℝ) + 1) :=
    Real.log_le_log (by positivity) hmu.le
  have e4 : Real.log ((P.N : ℝ) + 1) ≤ 2 * Real.log P.N := by
    rw [← Real.log_rpow (by positivity)]
    apply Real.log_le_log (by positivity)
    norm_num; nlinarith
  have e5 : 0 ≤ Real.log (1 / P.delta) := Real.log_nonneg (by rw [le_div_iff₀ hd]; linarith)
  have e6 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [← mul_le_mul_iff_of_pos_right hk, one_mul, hpk]
  linarith

/-- `θ_ℓ = (1-p_ℓ)^k ≤ (δ/(2μ_ℓ))^2`. -/
lemma theta_le (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) :
    (1 - P.p ℓ) ^ P.k ≤ (P.delta / (2 * P.mu ℓ)) ^ 2 := by
  have hp0 := p_pos P hN hε hε1 hΦ ℓ hℓ
  have hp1 := p_le_one P hN hε hε1 hΦ ℓ h1 hℓ
  have hpk := pk_eq P hN hε hε1 hΦ ℓ
  have hd := delta_pos P hN
  have hmu := mu_pos P ℓ
  calc (1 - P.p ℓ) ^ P.k ≤ (Real.exp (-P.p ℓ)) ^ P.k := by
        apply pow_le_pow_left₀ (by linarith)
        have := Real.add_one_le_exp (-P.p ℓ); linarith
    _ = Real.exp (-(P.p ℓ * P.k)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ = (P.delta / (2 * P.mu ℓ)) ^ 2 := by
        rw [hpk, show -(2 * Real.log (2 * (P.mu ℓ : ℝ) / P.delta)) =
          Real.log (((2 * (P.mu ℓ : ℝ) / P.delta))⁻¹) * 2 by rw [Real.log_inv]; ring]
        rw [Real.exp_mul, Real.exp_log (by positivity)]
        rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
        rw [inv_div]

/-- The truncation correction factor `ψ_ℓ = 1/(1-(1-p_ℓ)^k)`. -/
noncomputable def psi (ℓ : ℕ) : ℝ := 1 / (1 - (1 - P.p ℓ) ^ P.k)

lemma theta_small (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) : (1 - P.p ℓ) ^ P.k ≤ 1 / 16 := by
  have h := theta_le P hN hε hε1 hΦ ℓ h1 hℓ
  have hd := delta_pos P hN
  have hd1 := delta_lt_one P hN
  have hmu := mu_ge_two P ℓ hℓ
  refine le_trans h ?_
  rw [div_pow, div_le_iff₀ (by positivity)]
  nlinarith

lemma psi_ge_one (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) : 1 ≤ psi P ℓ := by
  have h := theta_small P hN hε hε1 hΦ ℓ h1 hℓ
  have hp0 := p_pos P hN hε hε1 hΦ ℓ hℓ
  have hp1 := p_le_one P hN hε hε1 hΦ ℓ h1 hℓ
  have : 0 ≤ (1 - P.p ℓ) ^ P.k := pow_nonneg (by linarith) _
  unfold psi; rw [one_le_div (by linarith)]; linarith

lemma psi_mul (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) : psi P ℓ * (1 - (1 - P.p ℓ) ^ P.k) = 1 := by
  have h := theta_small P hN hε hε1 hΦ ℓ h1 hℓ
  unfold psi; rw [one_div, inv_mul_cancel₀]; linarith

lemma psi_pow_le (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) :
    psi P ℓ ^ (P.mu (ℓ - 1)) ≤ Real.exp (P.delta ^ 2 / 2) := by
  have hθ := theta_le P hN hε hε1 hΦ ℓ h1 hℓ
  have hs := theta_small P hN hε hε1 hΦ ℓ h1 hℓ
  have hp0 := p_pos P hN hε hε1 hΦ ℓ hℓ
  have hp1 := p_le_one P hN hε hε1 hΦ ℓ h1 hℓ
  set θ := (1 - P.p ℓ) ^ P.k with hθdef
  have hθ0 : 0 ≤ θ := pow_nonneg (by linarith) _
  have hpsi : psi P ℓ ≤ 1 + 2 * θ := by
    unfold psi; rw [div_le_iff₀ (by linarith)]; nlinarith
  have hmu := mu_sq P ℓ h1 hℓ
  have hmu2 := mu_ge_two P ℓ hℓ
  calc psi P ℓ ^ (P.mu (ℓ - 1)) ≤ (1 + 2 * θ) ^ (P.mu (ℓ - 1)) :=
        pow_le_pow_left₀ (by linarith [psi_ge_one P hN hε hε1 hΦ ℓ h1 hℓ]) hpsi _
    _ ≤ (Real.exp (2 * θ)) ^ (P.mu (ℓ - 1)) := by
        apply pow_le_pow_left₀ (by linarith)
        have := Real.add_one_le_exp (2 * θ); linarith
    _ = Real.exp (2 * θ * (P.mu (ℓ - 1) : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (P.delta ^ 2 / 2) := by
        apply Real.exp_le_exp.mpr
        rw [hmu]
        have : θ * (P.mu ℓ : ℝ) ^ 2 ≤ P.delta ^ 2 / 4 := by
          calc θ * (P.mu ℓ : ℝ) ^ 2 ≤ (P.delta / (2 * P.mu ℓ)) ^ 2 * (P.mu ℓ : ℝ) ^ 2 :=
                mul_le_mul_of_nonneg_right hθ (by positivity)
            _ = P.delta ^ 2 / 4 := by field_simp; ring
        nlinarith

/-- The product of truncation factors over the phases is at most `1 + 2δ`. -/
lemma prod_psi_le :
    ∏ j ∈ Finset.Icc 1 P.L, psi P j ^ (P.mu (j - 1)) ≤ 1 + 2 * P.delta := by
  have hd := delta_pos P hN
  have hd1 := delta_lt_one P hN
  have hLd := L_delta_le P hN
  calc ∏ j ∈ Finset.Icc 1 P.L, psi P j ^ (P.mu (j - 1))
      ≤ ∏ _j ∈ Finset.Icc 1 P.L, Real.exp (P.delta ^ 2 / 2) := by
        apply Finset.prod_le_prod
        · intro j hj; rw [Finset.mem_Icc] at hj
          exact pow_nonneg (by linarith [psi_ge_one P hN hε hε1 hΦ j hj.1 hj.2]) _
        · intro j hj; rw [Finset.mem_Icc] at hj
          exact psi_pow_le P hN hε hε1 hΦ j hj.1 hj.2
    _ = Real.exp (P.L * (P.delta ^ 2 / 2)) := by
        rw [Finset.prod_const, Nat.card_Icc, ← Real.exp_nat_mul]; simp
    _ ≤ Real.exp (P.delta / 2) := by
        apply Real.exp_le_exp.mpr
        have : (P.L : ℝ) * P.delta ^ 2 ≤ P.delta := by nlinarith
        linarith
    _ ≤ 1 + 2 * P.delta := by
        have := Real.exp_bound_div_one_sub_of_interval' (x := P.delta / 2) (by linarith) (by linarith)
        refine le_trans this.le ?_
        rw [div_le_iff₀ (by linarith)]; nlinarith

end Std


section Radius

lemma radius_closed (L : ℕ) (Δ : ℝ) (ℓ : ℕ) (hℓ : ℓ ≤ L) :
    radius L Δ ℓ = Δ * (2 ^ (ℓ + 1) - 1) / 2 ^ (L + 4) + ℓ * (Δ / (8 * L)) := by
  induction ℓ with
  | zero => simp [radius]; ring
  | succ j ih =>
    rw [radius, ih (by omega)]
    have : (2 : ℝ) ^ (L - (j + 1) + 4) = 2 ^ (L + 4) / 2 ^ (j + 1) := by
      rw [eq_div_iff (by positivity), ← pow_add]; congr 1; omega
    rw [this]; push_cast; field_simp; ring

lemma radius_nonneg (L : ℕ) {Δ : ℝ} (hΔ : 0 ≤ Δ) (ℓ : ℕ) : 0 ≤ radius L Δ ℓ := by
  induction ℓ with
  | zero => simp [radius]; positivity
  | succ j ih => rw [radius]; positivity

lemma radius_mono (L : ℕ) {Δ : ℝ} (hΔ : 0 ≤ Δ) {a b : ℕ} (hab : a ≤ b) :
    radius L Δ a ≤ radius L Δ b := by
  induction b with
  | zero => rw [Nat.le_zero.mp hab]
  | succ j ih =>
    rcases Nat.of_le_succ hab with h | h
    · rw [radius]; have := ih h; have : 0 ≤ Δ / 2 ^ (L - (j + 1) + 4) := by positivity
      have : 0 ≤ Δ / (8 * L) := by positivity
      linarith
    · rw [h]

lemma radius_L_le (L : ℕ) (hL : 1 ≤ L) {Δ : ℝ} (hΔ : 0 ≤ Δ) : radius L Δ L ≤ Δ / 4 := by
  rw [radius_closed L Δ L le_rfl]
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
  have : (L : ℝ) * (Δ / (8 * L)) = Δ / 8 := by field_simp
  rw [this]
  have h2 : Δ * (2 ^ (L + 1) - 1) / 2 ^ (L + 4) ≤ Δ / 8 := by
    rw [div_le_iff₀ (by positivity), pow_add, pow_add]
    have : (0:ℝ) < 2 ^ L := by positivity
    nlinarith
  linarith

lemma radius_succ_sub (L : ℕ) (Δ : ℝ) (j : ℕ) :
    radius L Δ (j + 1) - radius L Δ j = Δ / 2 ^ (L - (j + 1) + 4) + Δ / (8 * L) := by
  rw [radius]; ring

end Radius

section Std2

set_option linter.unusedSectionVars false
variable (hN : 2 ≤ P.N) (hε : 0 < P.ε) (hε1 : P.ε < 1) (hΦ : 2 ≤ P.Φ)
include hN hε hε1 hΦ

lemma k_ne_zero_real : (P.k : ℝ) ≠ 0 := by exact_mod_cast (k_pos P hN hε hε1 hΦ).ne'

lemma r_add_kq (Δ : ℝ) (ℓ : ℕ) (h1 : 1 ≤ ℓ) : P.r Δ (ℓ - 1) + P.k * P.q Δ ℓ = P.r Δ ℓ := by
  have := k_ne_zero_real P hN hε hε1 hΦ
  unfold Fig2Params.q; field_simp; ring

lemma q_ge (Δ : ℝ) (hΔ : 0 ≤ Δ) (ℓ : ℕ) (h1 : 1 ≤ ℓ) :
    Δ / (8 * P.L * P.k) ≤ P.q Δ ℓ := by
  have hk : (0:ℝ) < P.k := by exact_mod_cast k_pos P hN hε hε1 hΦ
  unfold Fig2Params.q Fig2Params.r
  obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [radius_succ_sub]
  rw [← div_div]
  apply div_le_div_of_nonneg_right _ hk.le
  have : 0 ≤ Δ / 2 ^ (P.L - (j + 1) + 4) := by positivity
  linarith


lemma logb_mu (ℓ : ℕ) : Real.logb 2 (P.mu ℓ : ℝ) = 2 ^ (P.L - ℓ) := by
  rw [mu_cast, Real.logb_pow]; simp

lemma log_mu_eq (ℓ : ℕ) : Real.log (P.mu ℓ : ℝ) = 2 ^ (P.L - ℓ) * Real.log 2 := by
  rw [mu_cast, Real.log_pow]; push_cast; ring

lemma log_inv_delta_le : Real.log (1 / P.delta) ≤ 2 * P.L * Real.log 2 := by
  rw [delta_eq P hN]
  have h := two_pow_L_ge P hN
  have hx := logN1_gt_one P hN
  have : Real.log (Real.logb 2 ((P.N : ℝ) + 1)) ≤ Real.log ((2:ℝ) ^ P.L) :=
    Real.log_le_log (by linarith) h
  rw [Real.log_pow] at this
  linarith

lemma log_arg_split (ℓ : ℕ) : Real.log (2 * (P.mu ℓ : ℝ) / P.delta) =
    Real.log (2 / P.delta) + Real.log (P.mu ℓ) := by
  have hd := delta_pos P hN
  have := mu_pos P ℓ
  rw [mul_comm, mul_div_assoc, Real.log_mul (by positivity) (by positivity)]; ring

/-- The pair inequality `p_ℓ·Δ ≤ 2^7·L·log₂ µ_ℓ·q_ℓ` (from inequality (#)). -/
lemma pair_ineq (Δ : ℝ) (hΔ : 0 ≤ Δ) (ℓ : ℕ) (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ P.L) :
    P.p ℓ * Δ ≤ 2 ^ 7 * P.L * Real.logb 2 (P.mu ℓ : ℝ) * P.q Δ ℓ := by
  have hk : (0:ℝ) < P.k := by exact_mod_cast k_pos P hN hε hε1 hΦ
  have hL : (1:ℝ) ≤ P.L := by exact_mod_cast L_pos P hN
  have hd := delta_pos P hN
  have hd1 := delta_lt_one P hN
  have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hinv := log_inv_delta_le P hN hε hε1 hΦ
  have e2 : Real.log (2 / P.delta) = Real.log 2 + Real.log (1 / P.delta) := by
    rw [div_eq_mul_one_div 2, Real.log_mul (by norm_num) (by positivity)]
  have hsplit := log_arg_split P hN hε hε1 hΦ ℓ
  have hmu := log_mu_eq P hN hε hε1 hΦ ℓ
  rw [logb_mu P hN hε hε1 hΦ]
  obtain ⟨j, rfl⟩ : ∃ j, ℓ = j + 1 := ⟨ℓ - 1, by omega⟩
  unfold Fig2Params.p Fig2Params.q Fig2Params.r
  simp only [Nat.add_sub_cancel]
  rw [radius_succ_sub]
  set J := P.L - (j + 1) with hJ
  have hpow : (2:ℝ) ^ (J + 4) = 2 ^ J * 16 := by rw [pow_add]; norm_num
  rw [hpow]
  have h2J : (1:ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
  -- reduce to ln(2μ/δ) ≤ 4L + 8·2^J
  have key : Real.log (2 * (P.mu (j + 1) : ℝ) / P.delta) ≤ 4 * P.L + 8 * 2 ^ J := by
    rw [hsplit, e2, hmu]
    nlinarith
  have hLpos : (0:ℝ) < P.L := by linarith
  have hlog0 : 0 ≤ Real.log (2 * (P.mu (j + 1) : ℝ) / P.delta) :=
    (log_mu_arg_pos P hN hε hε1 hΦ (j+1) hℓ).le
  rw [show 2 / (P.k : ℝ) * Real.log (2 * (P.mu (j + 1) : ℝ) / P.delta) * Δ =
      (2 * Real.log (2 * (P.mu (j + 1) : ℝ) / P.delta) * Δ) / P.k by ring]
  rw [mul_div_assoc', div_le_div_iff_of_pos_right hk]
  have e : 2 ^ 7 * (P.L : ℝ) * 2 ^ J * (Δ / (2 ^ J * 16) + Δ / (8 * P.L)) =
      Δ * (8 * P.L + 16 * 2 ^ J) := by field_simp; ring
  rw [e]
  nlinarith

end Std2

end P2

end HopRamsey.FZ


namespace HopRamsey.FZ

open HopRamsey

theorem finite_case_parameters' (c : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ P : Fig2Params, 2 ≤ P.N → 0 < P.ε → P.ε < 1 → 2 ≤ P.Φ →
      P.Φ ≤ (P.N : ℝ) ^ c →
      (2 * P.k * (P.L + 1) : ℝ) ≤ C * polylogBound K P.N / P.ε ∧
      ((P.k : ℝ) * 8 * P.L) ≤ C * polylogBound K P.N / P.ε ∧
      P.g P.N P.Φ ≤ C * polylogBound K P.N := by
  set C1 : ℝ := 4 * Real.exp (2 * c) * (1 + 2 * c) + 1 with hC1
  have hC1pos : 1 ≤ C1 := by
    have : 0 ≤ 4 * Real.exp (2 * c) * (1 + 2 * c) := by positivity
    linarith
  refine ⟨8 * C1 + 2 ^ 8 * Real.exp (2 * c), by positivity, 2, ?_⟩
  intro P hN hε hε1 hΦ hΦc
  set ℓ := Real.logb 2 ((P.N : ℝ) + 1) with hℓ
  set lam2 := 1 + Real.logb 2 (1 + ℓ) with hlam2
  have hℓ1 : 1 < ℓ := P2.logN1_gt_one P hN
  have hlam1 : 1 ≤ lam2 := by
    have : 0 ≤ Real.logb 2 (1 + ℓ) := Real.logb_nonneg (by norm_num) (by linarith)
    linarith
  have hΛ : polylogBound 2 P.N = ℓ * lam2 ^ 2 := rfl
  rw [hΛ]
  have hNr : (2:ℝ) ≤ P.N := by exact_mod_cast hN
  have hd0 := P2.delta_pos P hN
  have hdef : P.delta = (ℓ ^ 2)⁻¹ := rfl
  have hln2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hln2p : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- (p1)
  have hlogN : Real.logb 2 P.N ≤ ℓ :=
    Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
  have hlogΦ : Real.logb 2 P.Φ ≤ c * ℓ := by
    have : Real.logb 2 P.Φ ≤ Real.logb 2 ((P.N : ℝ) ^ c) :=
      Real.logb_le_logb_of_le (by norm_num) (by linarith) hΦc
    rw [Real.logb_pow] at this
    have hc0 : (0:ℝ) ≤ c := by positivity
    nlinarith
  have hlogΦ1 : 1 ≤ Real.logb 2 P.Φ := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]; simpa using hΦ
  -- (p3)
  have hpow : (1 + 2 * P.delta) ^ (Real.logb 2 P.Φ) ≤ Real.exp (2 * c) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    apply Real.exp_le_exp.mpr
    have h1 : Real.log (1 + 2 * P.delta) ≤ 2 * P.delta := by
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + 2 * P.delta); linarith
    have h2 : P.delta * Real.logb 2 P.Φ ≤ c := by
      rw [hdef]
      rw [inv_mul_le_iff₀ (by positivity)]
      have hc0 : (0:ℝ) ≤ c := by positivity
      nlinarith
    have h0 : 0 ≤ Real.logb 2 P.Φ := by linarith
    nlinarith
  have hpow1 : 1 ≤ (1 + 2 * P.delta) ^ (Real.logb 2 P.Φ) :=
    Real.one_le_rpow (by linarith) (by linarith)
  -- (p4) (p5)
  have hlnN : Real.log P.N ≤ ℓ := by
    have : Real.log P.N = Real.logb 2 P.N * Real.log 2 := by
      rw [Real.logb, div_mul_cancel₀ _ hln2p.ne']
    have h0 : 0 ≤ Real.logb 2 P.N := Real.logb_nonneg (by norm_num) (by linarith)
    nlinarith
  have hln2d : Real.log (2 / P.delta) ≤ 2 * lam2 := by
    have e : Real.log (2 / P.delta) = Real.log 2 + 2 * Real.log ℓ := by
      rw [hdef, div_inv_eq_mul, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast; ring
    have h1 : Real.log ℓ ≤ Real.logb 2 (1 + ℓ) := by
      have a1 : Real.log ℓ ≤ Real.log (1 + ℓ) := Real.log_le_log (by linarith) (by linarith)
      have a2 : Real.log (1 + ℓ) = Real.logb 2 (1 + ℓ) * Real.log 2 := by
        rw [Real.logb, div_mul_cancel₀ _ hln2p.ne']
      have a3 : 0 ≤ Real.logb 2 (1 + ℓ) := Real.logb_nonneg (by norm_num) (by linarith)
      nlinarith
    rw [e]; linarith
  have hln2d0 : 0 ≤ Real.log (2 / P.delta) := P2.log2_delta_nonneg P hN hε hε1 hΦ
  have hlnN0 : 0 ≤ Real.log P.N := Real.log_nonneg (by linarith)
  -- (p6) (p7)
  have hA : (1 + 2 * P.delta) ^ (Real.logb 2 P.Φ) *
      (Real.log P.N + Real.log (2 / P.delta) * Real.logb 2 P.Φ) ≤
      Real.exp (2 * c) * (1 + 2 * c) * (ℓ * lam2) := by
    have hB : Real.log P.N + Real.log (2 / P.delta) * Real.logb 2 P.Φ ≤ (1 + 2 * c) * (ℓ * lam2) := by
      have : Real.log (2 / P.delta) * Real.logb 2 P.Φ ≤ 2 * lam2 * (c * ℓ) :=
        mul_le_mul hln2d hlogΦ (by linarith) (by linarith)
      nlinarith
    have hB0 : 0 ≤ Real.log P.N + Real.log (2 / P.delta) * Real.logb 2 P.Φ := by
      have : 0 ≤ Real.log (2 / P.delta) * Real.logb 2 P.Φ := mul_nonneg hln2d0 (by linarith)
      linarith
    calc _ ≤ Real.exp (2 * c) * (Real.log P.N + Real.log (2 / P.delta) * Real.logb 2 P.Φ) :=
          mul_le_mul_of_nonneg_right hpow hB0
      _ ≤ Real.exp (2 * c) * ((1 + 2 * c) * (ℓ * lam2)) :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ = _ := by ring
  have hlam : 1 ≤ ℓ * lam2 / P.ε := by
    rw [le_div_iff₀ hε]; nlinarith
  have hk : (P.k : ℝ) ≤ C1 * (ℓ * lam2 / P.ε) := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ (4 / P.ε) * (1 + 2 * P.delta) ^ (Real.logb 2 P.Φ) *
        (Real.log P.N + Real.log (2 / P.delta) * Real.logb 2 P.Φ) by
      have : 0 ≤ Real.log (2 / P.delta) * Real.logb 2 P.Φ := mul_nonneg hln2d0 (by linarith)
      positivity)
    have : (P.k : ℝ) < (4 / P.ε) * ((1 + 2 * P.delta) ^ (Real.logb 2 P.Φ) *
        (Real.log P.N + Real.log (2 / P.delta) * Real.logb 2 P.Φ)) + 1 := by
      unfold Fig2Params.k; rw [← mul_assoc]; exact hc
    have h4 : (4 / P.ε) * ((1 + 2 * P.delta) ^ (Real.logb 2 P.Φ) *
        (Real.log P.N + Real.log (2 / P.delta) * Real.logb 2 P.Φ)) ≤
        4 * Real.exp (2 * c) * (1 + 2 * c) * (ℓ * lam2 / P.ε) := by
      rw [show 4 * Real.exp (2 * c) * (1 + 2 * c) * (ℓ * lam2 / P.ε) =
        (4 / P.ε) * (Real.exp (2 * c) * (1 + 2 * c) * (ℓ * lam2)) by ring]
      exact mul_le_mul_of_nonneg_left hA (by positivity)
    have e : C1 * (ℓ * lam2 / P.ε) = 4 * Real.exp (2 * c) * (1 + 2 * c) * (ℓ * lam2 / P.ε) +
        ℓ * lam2 / P.ε := by rw [hC1]; ring
    linarith
  -- (p8)
  have hL : (P.L : ℝ) ≤ lam2 := by
    have h1 := P2.L_le P hN
    have h2 : Real.logb 2 ℓ ≤ Real.logb 2 (1 + ℓ) :=
      Real.logb_le_logb_of_le (b := 2) (by norm_num) (by linarith : (0:ℝ) < ℓ)
        (by linarith : ℓ ≤ 1 + ℓ)
    linarith
  have hL0 : (0:ℝ) ≤ P.L := by positivity
  have hk0 : (0:ℝ) ≤ P.k := by positivity
  have hX : 0 ≤ ℓ * lam2 / P.ε := by positivity
  have hE : 0 < Real.exp (2 * c) := Real.exp_pos _
  have hY2 : 0 ≤ ℓ * lam2 ^ 2 := mul_nonneg (by linarith) (pow_nonneg (by linarith) 2)
  have hlam0 : 0 ≤ lam2 := by linarith
  have hC0 : 0 ≤ C1 := by linarith
  have hCC : 8 * C1 ≤ 8 * C1 + 2 ^ 8 * Real.exp (2 * c) := by linarith
  have hk2 : (P.k : ℝ) * lam2 ≤ C1 * (ℓ * lam2 ^ 2) / P.ε := by
    have := mul_le_mul_of_nonneg_right hk hlam0
    rw [show C1 * (ℓ * lam2 ^ 2) / P.ε = C1 * (ℓ * lam2 / P.ε) * lam2 by ring]
    exact this
  have hkL : (P.k : ℝ) * P.L ≤ (P.k : ℝ) * lam2 := mul_le_mul_of_nonneg_left hL hk0
  have hkL1 : (P.k : ℝ) * (P.L + 1) ≤ 2 * ((P.k : ℝ) * lam2) := by
    have h1 : (P.k : ℝ) ≤ P.k * lam2 := le_mul_of_one_le_right hk0 hlam1
    have e : (P.k : ℝ) * (P.L + 1) = P.k * P.L + P.k := by ring
    linarith
  have hmain : 8 * (C1 * (ℓ * lam2 ^ 2) / P.ε) ≤
      (8 * C1 + 2 ^ 8 * Real.exp (2 * c)) * (ℓ * lam2 ^ 2) / P.ε := by
    rw [show 8 * (C1 * (ℓ * lam2 ^ 2) / P.ε) = 8 * C1 * (ℓ * lam2 ^ 2) / P.ε by ring]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hY2) hε.le
  refine ⟨?_, ?_, ?_⟩
  · have : (2 * P.k * (P.L + 1) : ℝ) = 2 * ((P.k : ℝ) * (P.L + 1)) := by ring
    rw [this]
    have h0 : 0 ≤ C1 * (ℓ * lam2 ^ 2) / P.ε := div_nonneg (mul_nonneg hC0 hY2) hε.le
    linarith
  · have : ((P.k : ℝ) * 8 * P.L) = 8 * ((P.k : ℝ) * P.L) := by ring
    rw [this]
    linarith
  · unfold Fig2Params.g
    have hlN0 : 0 ≤ Real.logb 2 P.N := Real.logb_nonneg (by norm_num) (by linarith)
    have hLl : (P.L : ℝ) * Real.logb 2 P.N ≤ lam2 * ℓ := mul_le_mul hL hlogN hlN0 hlam0
    have hLl0 : 0 ≤ (P.L : ℝ) * Real.logb 2 P.N := mul_nonneg hL0 hlN0
    have h1 : 2 ^ 8 * (P.L : ℝ) * Real.logb 2 P.N * (1 + 2 * P.delta) ^ (Real.logb 2 P.Φ) ≤
        2 ^ 8 * (lam2 * ℓ) * Real.exp (2 * c) := by
      rw [mul_assoc (2 ^ 8 : ℝ)]
      apply mul_le_mul _ hpow (by linarith) (by positivity)
      exact mul_le_mul_of_nonneg_left hLl (by norm_num)
    have h2 : lam2 * ℓ ≤ ℓ * lam2 ^ 2 := by
      have : lam2 ≤ lam2 ^ 2 := by rw [sq]; exact le_mul_of_one_le_right hlam0 hlam1
      have := mul_le_mul_of_nonneg_left this (by linarith : (0:ℝ) ≤ ℓ)
      linarith
    have h3 : 2 ^ 8 * (lam2 * ℓ) * Real.exp (2 * c) ≤ 2 ^ 8 * Real.exp (2 * c) * (ℓ * lam2 ^ 2) := by
      have := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 2 ^ 8 * Real.exp (2 * c))
      linarith
    have h4 : 2 ^ 8 * Real.exp (2 * c) * (ℓ * lam2 ^ 2) ≤
        (8 * C1 + 2 ^ 8 * Real.exp (2 * c)) * (ℓ * lam2 ^ 2) := by
      apply mul_le_mul_of_nonneg_right _ hY2; linarith
    linarith

end HopRamsey.FZ


open scoped ENNReal
open HopRamsey

theorem solution (c : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ P : Fig2Params, 2 ≤ P.N → 0 < P.ε → P.ε < 1 → 2 ≤ P.Φ →
      P.Φ ≤ (P.N : ℝ) ^ c →
      (2 * P.k * (P.L + 1) : ℝ) ≤ C * polylogBound K P.N / P.ε ∧
      ((P.k : ℝ) * 8 * P.L) ≤ C * polylogBound K P.N / P.ε ∧
      P.g P.N P.Φ ≤ C * polylogBound K P.N := by
  exact HopRamsey.FZ.finite_case_parameters' c
