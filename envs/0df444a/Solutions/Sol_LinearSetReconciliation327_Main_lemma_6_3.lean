-- Prove2me | solution 1 for LinearSetReconciliation327.Main.lemma_6_3
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-16T13:14:08.638201+00:00
-- url     : https://prove2.me/submissions/b79333a3-2601-47dd-a08a-c40be3697111

/-
# Lemma 6.3: Top-layer child capacities

This file proves the *Top-layer child capacities* lemma of §6.2 of
Liu--Xu--Yang--Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*
(`lem:top-initial-budget`, PDF p.30 / printed p.29), for the top layer of §3.2.

The proof follows the paper's argument in the paper's order:

1. **The capacities are sufficient** (first half of the paper's proof).
   Lemma 6.1 (*across words*) gives `E U_{a,k} ≤ q_a`, Lemma 6.2 (*within a word*) gives
   `E V_{a,k} ≤ q_a p_k`; the capacities of (28) add the margin `Δ = η(d+1)` to these expectations.
   Lemma 4.8 (*concentration*) then bounds each violation probability by
   `exp (-(2Δ²/(5d)))`, and `d > (C')³ λ_* log⁶ n / η²` makes this `≤ 2^{-λ_*}`.
2. **The `X`-budget** (`eq:top-initial-budget`, first line): with `b = η(d+1) + 1`,
   `Σ_{a,k} X_{a,k} ≤ w Σ_a q_a + ℓ b ≤ dw + ℓ b`, and `ℓ b = O(C'd/log n)`.
3. **The `h_N(Y)`-budget** (second line): monotonicity and subadditivity of `h_d` (Lemma 4.4) reduce
   the sum to `Σ_{a,k} h_d(q_a p_k) + ℓ h_d(b)`; the first term is expanded termwise and bounded
   with the entropy bounds of Lemma 6.1 and Lemma 6.2, giving `d[log e + H(q/d) + H(p)] = O(d)`;
   the tail term is `ℓ h_d(b) = O(C'd/log n)`.
4. **The mixed budget**: the paper's last display `Σ (X_{a,k} + α h_d(Y_{a,k}))`.

No statement is weakened: `K` and `C₀` are explicit (`C₀ = 10`, `K = 1000(α+2)`).
-/
import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_TopLevel
import Theorems.Thm_LinearSetReconciliation327_Main_lemma_4_4
import Theorems.Thm_LinearSetReconciliation327_Main_lemma_4_8
import Theorems.Thm_LinearSetReconciliation327_Main_lemma_6_1
import Theorems.Thm_LinearSetReconciliation327_Main_lemma_6_2

set_option autoImplicit false

open scoped ENNReal
open Finset

noncomputable section

namespace LinearSetReconciliation327.Main

set_option maxHeartbeats 4000000

/-! ## §0. Elementary estimates

The paper's unmarked `log` is base two (`lg`).  Here we collect the small facts about `lg`, `exp`,
`h_N`, `prU` and the uniform expectation used by the budget computation. -/

lemma lg_log_two_pos : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]

lemma lg_two : lg 2 = 1 := Real.logb_self_eq_one (by norm_num)

lemma lg_exp_one : lg (Real.exp 1) = 1 / Real.log 2 := by
  rw [show lg (Real.exp 1) = Real.log (Real.exp 1) / Real.log 2 from rfl, Real.log_exp]

lemma one_le_lg_exp : (1 : ℝ) ≤ lg (Real.exp 1) := by
  rw [lg_exp_one, le_div_iff₀ lg_log_two_pos]
  linarith [Real.log_two_lt_d9]

lemma lg_exp_one_le_two : lg (Real.exp 1) ≤ 2 := by
  rw [lg_exp_one, div_le_iff₀ lg_log_two_pos]
  linarith [Real.log_two_gt_d9]

lemma lg_mono {x y : ℝ} (hx : 0 < x) (h : x ≤ y) : lg x ≤ lg y :=
  Real.logb_le_logb_of_le (by norm_num) hx h

lemma lg_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) : lg (x * y) = lg x + lg y :=
  Real.logb_mul hx hy

lemma lg_div {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) : lg (x / y) = lg x - lg y :=
  Real.logb_div hx hy

lemma lg_inv' {x : ℝ} : lg x⁻¹ = - lg x := Real.logb_inv 2 x

lemma lg_pow' (x : ℝ) (n : ℕ) : lg (x ^ n) = n * lg x := Real.logb_pow 2 x n

lemma lg_one : lg 1 = 0 := Real.logb_one

lemma lg_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ lg x := by
  have h := lg_mono zero_lt_one hx
  rwa [lg_one] at h

/-- `log₂ x ≤ 2x` for `x ≥ 1` (crude, but enough to bound `log log n` by `log n`). -/
lemma lg_le_two_mul {x : ℝ} (hx : 1 ≤ x) : lg x ≤ 2 * x := by
  have hx0 : 0 < x := by linarith
  have hlog : Real.log x ≤ x := by
    have := Real.log_le_sub_one_of_pos hx0
    linarith
  have h2 : lg x = Real.log x / Real.log 2 := rfl
  rw [h2, div_le_iff₀ lg_log_two_pos]
  have h3 : (1 : ℝ) ≤ 2 * Real.log 2 := by linarith [Real.log_two_gt_d9]
  nlinarith [hlog, hx0.le, h3]

/-- `2^{-λ} = exp (-(λ log 2))`, the form in which the `2^{-λ_*}` tails are compared. -/
lemma two_pow_inv_eq_exp (n : ℕ) : ((2 : ℝ) ^ n)⁻¹ = Real.exp (-(n * Real.log 2)) := by
  have h1 : (2 : ℝ) ^ n = Real.exp (n * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [h1, ← Real.exp_neg]

lemma prU_nonneg {α : Type} [Fintype α] (Q : α → Prop) : 0 ≤ prU Q := by
  unfold prU
  positivity

lemma prU_mono {α : Type} [Fintype α] [Nonempty α] {Q R : α → Prop} (h : ∀ a, Q a → R a) :
    prU Q ≤ prU R := by
  have hc : (0 : ℝ) < (Fintype.card α : ℝ) := by
    have := Fintype.card_pos (α := α)
    exact_mod_cast this
  unfold prU
  rw [div_le_div_iff_of_pos_right hc]
  exact_mod_cast Finset.card_le_card (fun a ha => by
    simp only [mem_filter, mem_univ, true_and] at ha ⊢
    exact h a ha)

lemma hN_zero (N : ℕ) : hN N 0 = 0 := by unfold hN; simp

lemma hN_eq_log {N : ℕ} (hN0 : (N : ℝ) ≠ 0) {z : ℝ} (hz : 0 < z) :
    hN N z = z * lg (Real.exp 1 * N) - z * lg z := by
  have heN : Real.exp 1 * (N : ℝ) ≠ 0 := mul_ne_zero (Real.exp_ne_zero 1) hN0
  rw [hN, if_neg (ne_of_gt hz), lg_div heN (ne_of_gt hz)]
  ring

lemma hN_nonneg {N : ℕ} {z : ℝ} (hz : 0 ≤ z) (hzN : z ≤ (N : ℝ)) : 0 ≤ hN N z := by
  rcases eq_or_lt_of_le hz with h | h
  · rw [← h, hN_zero]
  · rw [hN, if_neg (ne_of_gt h)]
    have h1 : (1 : ℝ) ≤ Real.exp 1 * N / z := by
      rw [le_div_iff₀ h]
      have h2 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      nlinarith
    exact mul_nonneg h.le (lg_nonneg h1)

lemma hN_self {N : ℕ} (hN0 : (N : ℝ) ≠ 0) : hN N N = lg (Real.exp 1) * N := by
  have hNpos : (0 : ℝ) < N := by positivity
  rw [hN_eq_log hN0 hNpos, lg_mul (Real.exp_ne_zero 1) hN0]
  ring

/-- Monotonicity of `h_N` on `[0,N]`, used for the paper's "monotonicity of `h_d`" in
`eq:top-ideal-entropy`. -/
lemma hN_mono {N : ℕ} {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z) (hzN : z ≤ (N : ℝ)) :
    hN N y ≤ hN N z := by
  rcases eq_or_lt_of_le hyz with h | hlt
  · rw [h]
  have hz : 0 < z := lt_of_le_of_lt hy hlt
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le hz hzN
  have hN0 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  rcases eq_or_lt_of_le hy with hy0 | hypos
  · rw [← hy0, hN_zero]
    exact hN_nonneg hz.le hzN
  have hloge : lg (Real.exp 1) = 1 / Real.log 2 := lg_exp_one
  have hkey : z * lg z - y * lg y ≤ (z - y) * lg (Real.exp 1 * N) := by
    have hsplit : z * lg z - y * lg y = (z - y) * lg z + y * (lg z - lg y) := by ring
    rw [hsplit]
    have hzy : y ≠ 0 := ne_of_gt hypos
    have h1 : lg z - lg y = lg (z / y) := by
      rw [lg_div (ne_of_gt hz) hzy]
    rw [h1]
    have h2 : lg (z / y) ≤ (z / y - 1) * lg (Real.exp 1) := by
      have ht : 0 < z / y := div_pos hz hypos
      have hlog : Real.log (z / y) ≤ z / y - 1 := Real.log_le_sub_one_of_pos ht
      have hlhs : lg (z / y) = Real.log (z / y) / Real.log 2 := rfl
      rw [hlhs, hloge, div_le_iff₀ lg_log_two_pos]
      have h4 : (z / y - 1) * (1 / Real.log 2) * Real.log 2 = z / y - 1 := by
        field_simp
      linarith
    have h3 : y * lg (z / y) ≤ (z - y) * lg (Real.exp 1) := by
      calc y * lg (z / y) ≤ y * ((z / y - 1) * lg (Real.exp 1)) :=
            mul_le_mul_of_nonneg_left h2 hypos.le
        _ = (z - y) * lg (Real.exp 1) := by field_simp
    have h4 : lg z + lg (Real.exp 1) ≤ lg (Real.exp 1 * N) := by
      rw [lg_mul (Real.exp_ne_zero 1) hN0]
      linarith [lg_mono hz hzN]
    have h5 : (z - y) * (lg z + lg (Real.exp 1)) ≤ (z - y) * lg (Real.exp 1 * N) :=
      mul_le_mul_of_nonneg_left h4 (by linarith)
    nlinarith [h3, h5]
  rw [hN_eq_log hN0 hypos, hN_eq_log hN0 hz]
  linarith [hkey]

/-- The termwise form of `h_N` used in `eq:top-ideal-entropy`:
`h_d(q p) ≤ q p (log e + log(d/q) + log(1/p))`. -/
lemma hN_mul_le {N : ℕ} (hN0 : (N : ℝ) ≠ 0) {q p : ℝ} (hq : 0 ≤ q) (hp : 0 < p) :
    hN N (q * p) ≤ q * p * (lg (Real.exp 1) + lg ((N : ℝ) / q) + lg (1 / p)) := by
  rcases eq_or_lt_of_le hq with hq0 | hqpos
  · rw [← hq0, zero_mul, hN_zero, zero_mul]
  have hqp : 0 < q * p := mul_pos hqpos hp
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hpne : p ≠ 0 := ne_of_gt hp
  have heN : Real.exp 1 * (N : ℝ) ≠ 0 := mul_ne_zero (Real.exp_ne_zero 1) hN0
  have hqpe : q * p ≠ 0 := ne_of_gt hqp
  rw [hN_eq_log hN0 hqp]
  have e1 : lg (Real.exp 1 * N) = lg (Real.exp 1) + lg (N : ℝ) :=
    lg_mul (Real.exp_ne_zero 1) hN0
  have e2 : lg (q * p) = lg q + lg p := lg_mul hqne hpne
  have e3 : lg ((N : ℝ) / q) = lg (N : ℝ) - lg q := lg_div hN0 hqne
  have e4 : lg (1 / p) = - lg p := by
    rw [one_div, lg_inv']
  have hmain : q * p * lg (Real.exp 1 * (N : ℝ)) - q * p * lg (q * p)
      = q * p * (lg (Real.exp 1) + lg ((N : ℝ) / q) + lg (1 / p)) := by
    rw [e1, e2, e3, e4]
    ring
  rw [hmain]

/-! ## §1. Consequences of the row-column regime

The regime `d < n/2` and `(C')³ λ_* log⁶ n / η² < d` is the only quantitative input to the budget
estimates.  It forces `n > 4`, `log₂ n ≥ 2`, `η = log^{-A} n ≤ 2^{-10}`, `d ≥ 2^26` and
`log₂ n ^ 26 ≤ d`. -/


/-- C' ≥ 10 gives 1 ≤ C' as a real. -/
lemma one_le_C'_R (P : TopParams) (hC : 10 ≤ P.C') : (1 : ℝ) ≤ (P.C' : ℝ) := by
  have h : 1 ≤ P.C' := by omega
  exact_mod_cast h


section Regime

variable (P : TopParams) (hA : 10 ≤ P.A) (hC : 10 ≤ P.C') (hargs : P.Args)
  (hreg : P.RowColumnRegime)

include hA hC hargs hreg

lemma args_d_two : 2 ≤ P.d := by obtain ⟨h, -, -⟩ := hargs; exact h

lemma args_d_le_n : P.d ≤ P.n := by obtain ⟨-, h, -⟩ := hargs; exact h

lemma args_lam : 1 ≤ P.lam := by obtain ⟨-, -, h⟩ := hargs; exact h

lemma args_d_pos : 0 < P.d := by
  have := args_d_two P hA hC hargs hreg; omega

lemma regime_lt : (P.d : ℝ) < (P.n : ℝ) / 2 := by obtain ⟨h, -⟩ := hreg; exact h

lemma regime_big :
    (P.C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 / P.eta ^ 2 < (P.d : ℝ) := by
  obtain ⟨-, h⟩ := hreg; exact h

lemma n_gt_four : 4 < P.n := by
  have hd2 : (2 : ℝ) ≤ (P.d : ℝ) := by exact_mod_cast (args_d_two P hA hC hargs hreg)
  have h := regime_lt P hA hC hargs hreg
  have h4 : (4 : ℝ) < (P.n : ℝ) := by linarith
  exact_mod_cast h4

lemma lg_four : lg 4 = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, lg_pow', lg_two]
  norm_num

lemma two_le_lgn : 2 ≤ P.lgn := by
  have h4 : (4 : ℝ) ≤ (P.n : ℝ) := by
    have := n_gt_four P hA hC hargs hreg
    exact_mod_cast le_of_lt this
  have h := lg_mono (by norm_num : (0 : ℝ) < 4) h4
  rwa [lg_four P hA hC hargs hreg] at h

lemma lgn_pos : 0 < P.lgn := lt_of_lt_of_le (by norm_num) (two_le_lgn P hA hC hargs hreg)

lemma eta_pos : 0 < P.eta := by
  rw [TopParams.eta]
  exact inv_pos.mpr (pow_pos (lgn_pos P hA hC hargs hreg) P.A)

lemma eta_le_inv1024 : P.eta ≤ 1 / 1024 := by
  rw [TopParams.eta]
  have hL := lgn_pos P hA hC hargs hreg
  have hL2 := two_le_lgn P hA hC hargs hreg
  have hLA : (2 : ℝ) ^ 10 ≤ P.lgn ^ P.A :=
    calc (2 : ℝ) ^ 10 ≤ P.lgn ^ 10 := pow_le_pow_left₀ (by norm_num) hL2 10
      _ ≤ P.lgn ^ P.A := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ P.lgn) hA
  have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2 ^ 10) hLA
  rw [show (2 : ℝ) ^ 10 = 1024 by norm_num] at h
  simpa [one_div] using h

lemma eta_sq_eq : P.eta ^ 2 = (P.lgn ^ (2 * P.A))⁻¹ := by
  rw [TopParams.eta, inv_pow, ← pow_mul, show P.A * 2 = 2 * P.A by ring]

lemma one_le_lamStar : (1 : ℝ) ≤ (P.lamStar : ℝ) := by
  have h : 1 ≤ P.lamStar := by
    rw [TopParams.lamStar]
    have := args_lam P hA hC hargs hreg
    omega
  exact_mod_cast h

/-- The regime gives `(C')³ λ_* log⁶ n < d η²`. -/
lemma regime_key :
    (P.C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 < (P.d : ℝ) * P.eta ^ 2 := by
  have hη : (0 : ℝ) < P.eta ^ 2 := pow_pos (eta_pos P hA hC hargs hreg) 2
  have h := (div_lt_iff₀ hη).mp (regime_big P hA hC hargs hreg)
  linarith

/-- `log₂ n ^ 26 ≤ d`: the quantitative form of `d > (C')³ λ_* log^{6+2A} n`. -/
lemma lgn_pow_26_le_d : P.lgn ^ 26 ≤ (P.d : ℝ) := by
  have hL := lgn_pos P hA hC hargs hreg
  have hL1 : (1 : ℝ) ≤ P.lgn := by linarith [two_le_lgn P hA hC hargs hreg]
  have hC1 : (1 : ℝ) ≤ (P.C' : ℝ) ^ 3 := by
    have h : (1 : ℝ) ≤ (P.C' : ℝ) := one_le_C'_R P hC
    calc (1 : ℝ) = 1 ^ 3 := by norm_num
      _ ≤ (P.C' : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) h 3
  have hlam1 := one_le_lamStar P hA hC hargs hreg
  have hL2A : (0 : ℝ) < P.lgn ^ (2 * P.A) := pow_pos hL _
  have hkey := regime_key P hA hC hargs hreg
  have hkey2 :
      (P.C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 * P.lgn ^ (2 * P.A) < (P.d : ℝ) := by
    have h := mul_lt_mul_of_pos_right hkey hL2A
    rw [eta_sq_eq P hA hC hargs hreg] at h
    have hx : (P.lgn ^ (2 * P.A)) * (P.lgn ^ (2 * P.A))⁻¹ = 1 :=
      mul_inv_cancel₀ (ne_of_gt hL2A)
    nlinarith [h, hx]
  have hle : P.lgn ^ 26 ≤
      (P.C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 * P.lgn ^ (2 * P.A) := by
    have h6 : P.lgn ^ 26 ≤ P.lgn ^ 6 * P.lgn ^ (2 * P.A) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hL1 (by omega)
    have h1 : P.lgn ^ 6 * P.lgn ^ (2 * P.A) ≤
        (P.C' : ℝ) ^ 3 * (P.lamStar : ℝ) * (P.lgn ^ 6 * P.lgn ^ (2 * P.A)) := by
      have h0 : (0 : ℝ) ≤ P.lgn ^ 6 * P.lgn ^ (2 * P.A) := by positivity
      have h1' : (1 : ℝ) ≤ (P.C' : ℝ) ^ 3 * (P.lamStar : ℝ) := by nlinarith
      nlinarith
    calc P.lgn ^ 26 ≤ P.lgn ^ 6 * P.lgn ^ (2 * P.A) := h6
      _ ≤ (P.C' : ℝ) ^ 3 * (P.lamStar : ℝ) * (P.lgn ^ 6 * P.lgn ^ (2 * P.A)) := h1
      _ = (P.C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 * P.lgn ^ (2 * P.A) := by ring
  linarith

lemma hundred_le_d : (100 : ℝ) ≤ (P.d : ℝ) := by
  have h := lgn_pow_26_le_d P hA hC hargs hreg
  have hL2 := two_le_lgn P hA hC hargs hreg
  have h2 : (2 : ℝ) ^ 26 ≤ P.lgn ^ 26 := pow_le_pow_left₀ (by norm_num) hL2 26
  have h3 : (2 : ℝ) ^ 26 = 67108864 := by norm_num
  linarith

lemma one_le_lgn : (1 : ℝ) ≤ P.lgn := by linarith [two_le_lgn P hA hC hargs hreg]

lemma lgn_pow_le_d {k : ℕ} (hk : k ≤ 26) : P.lgn ^ k ≤ (P.d : ℝ) := by
  have h := lgn_pow_26_le_d P hA hC hargs hreg
  have h1 := one_le_lgn P hA hC hargs hreg
  calc P.lgn ^ k ≤ P.lgn ^ 26 := pow_le_pow_right₀ h1 hk
    _ ≤ (P.d : ℝ) := h

/-- `N ≤ n`, hence `w ≤ log₂ n + 2`. -/
lemma N_le_n : P.N ≤ P.n := by
  rw [TopParams.N]
  refine Nat.ceil_le.mpr ?_
  have hd : (0 : ℝ) < P.d := by exact_mod_cast args_d_pos P hA hC hargs hreg
  have hd1 : (1 : ℝ) ≤ P.d := by
    have h : 1 ≤ P.d := by have := args_d_two P hA hC hargs hreg; omega
    exact_mod_cast h
  rw [div_le_iff₀ hd]
  nlinarith [Nat.cast_nonneg (α := ℝ) P.n]

lemma w_le : (P.w : ℝ) ≤ P.lgn + 2 := by
  rw [TopParams.w]
  have h1 : ((⌈lg ((P.N : ℝ) + 1)⌉₊ : ℕ) : ℝ) < lg ((P.N : ℝ) + 1) + 1 :=
    Nat.ceil_lt_add_one (lg_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) P.N] :
      (1 : ℝ) ≤ (P.N : ℝ) + 1))
  have hNn : (P.N : ℝ) ≤ (P.n : ℝ) := by exact_mod_cast N_le_n P hA hC hargs hreg
  have hpos : (0 : ℝ) < (P.N : ℝ) + 1 := by positivity
  have hmono : lg ((P.N : ℝ) + 1) ≤ lg ((P.n : ℝ) + 1) := lg_mono hpos (by linarith)
  have hn : (P.n : ℝ) + 1 ≤ 2 * (P.n : ℝ) := by
    have h1 : (1 : ℝ) ≤ (P.n : ℝ) := by
      have h2 : 1 ≤ P.n := by have := n_gt_four P hA hC hargs hreg; omega
      exact_mod_cast h2
    linarith
  have h2 : lg ((P.n : ℝ) + 1) ≤ P.lgn + 1 := by
    calc lg ((P.n : ℝ) + 1) ≤ lg (2 * (P.n : ℝ)) := lg_mono (by positivity) hn
      _ = lg 2 + P.lgn := lg_mul (by norm_num) (by
            have h2 : (0 : ℕ) < P.n := by
              have h4 := n_gt_four P hA hC hargs hreg
              omega
            have h : (0 : ℝ) < (P.n : ℝ) := by exact_mod_cast h2
            exact ne_of_gt h)
      _ = P.lgn + 1 := by rw [lg_two]; ring
  linarith

lemma B_le : (P.B : ℝ) ≤ 20 * (P.C' : ℝ) * P.lgn := by
  rw [TopParams.B]
  have hmin : (min P.N ⌈(P.C' : ℝ) * lg (P.lgn + 2)⌉₊ : ℕ) ≤
      ⌈(P.C' : ℝ) * lg (P.lgn + 2)⌉₊ := min_le_right _ _
  have hcast : ((min P.N ⌈(P.C' : ℝ) * lg (P.lgn + 2)⌉₊ : ℕ) : ℝ) ≤
      ((⌈(P.C' : ℝ) * lg (P.lgn + 2)⌉₊ : ℕ) : ℝ) := by exact_mod_cast hmin
  have hnonneg : (0 : ℝ) ≤ (P.C' : ℝ) * lg (P.lgn + 2) := by
    have h2 : (0 : ℝ) ≤ lg (P.lgn + 2) := by
      apply lg_nonneg
      linarith [one_le_lgn P hA hC hargs hreg]
    positivity
  have h1 : ((⌈(P.C' : ℝ) * lg (P.lgn + 2)⌉₊ : ℕ) : ℝ) <
      (P.C' : ℝ) * lg (P.lgn + 2) + 1 := Nat.ceil_lt_add_one hnonneg
  have h2 : lg (P.lgn + 2) ≤ 2 * (P.lgn + 2) := by
    apply lg_le_two_mul
    linarith [one_le_lgn P hA hC hargs hreg]
  have hL := one_le_lgn P hA hC hargs hreg
  have hC' : (1 : ℝ) ≤ (P.C' : ℝ) := by exact_mod_cast (by omega : 1 ≤ P.C')
  have hCpos : (0 : ℝ) ≤ (P.C' : ℝ) := by linarith
  have h4 : (P.C' : ℝ) * lg (P.lgn + 2) ≤ (P.C' : ℝ) * (2 * (P.lgn + 2)) :=
    mul_le_mul_of_nonneg_left h2 hCpos
  have hL2 : (2 : ℝ) ≤ P.lgn := two_le_lgn P hA hC hargs hreg
  have h5 : (P.C' : ℝ) * (2 * (P.lgn + 2)) ≤ (P.C' : ℝ) * (4 * P.lgn) :=
    mul_le_mul_of_nonneg_left (by linarith) hCpos
  have h3 : (P.C' : ℝ) * lg (P.lgn + 2) + 1 ≤ 20 * (P.C' : ℝ) * P.lgn := by
    nlinarith [h4, h5, hC', hL, hL2, hCpos]
  linarith

/-- `b = η(d+1)+1 ≤ d/10`. -/
lemma b_le_tenth : P.eta * ((P.d : ℝ) + 1) + 1 ≤ (P.d : ℝ) / 10 := by
  have hη := eta_le_inv1024 P hA hC hargs hreg
  have hη0 := eta_pos P hA hC hargs hreg
  have hd := hundred_le_d P hA hC hargs hreg
  have h1 : P.eta * P.d ≤ (1 / 1024) * P.d := mul_le_mul_of_nonneg_right hη (by linarith)
  have h2 : P.eta * 1 ≤ (1 / 1024) * 1 := by simpa using hη
  nlinarith

/-- `1 ≤ η d`: the regime gives `d η² > 64000` and `η ≤ 1/1024`. -/
lemma eta_d_ge : 1 ≤ P.eta * (P.d : ℝ) := by
  have hη0 := eta_pos P hA hC hargs hreg
  have hη := eta_le_inv1024 P hA hC hargs hreg
  have hC10 : (10 : ℝ) ≤ (P.C' : ℝ) := by exact_mod_cast hC
  have hL2 : (2 : ℝ) ≤ P.lgn := two_le_lgn P hA hC hargs hreg
  have hlam1 := one_le_lamStar P hA hC hargs hreg
  have hkey := regime_key P hA hC hargs hreg
  have hC3 : (1000 : ℝ) ≤ (P.C' : ℝ) ^ 3 := by
    have h : (10 : ℝ) ^ 3 ≤ (P.C' : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hC10 3
    norm_num at h
    linarith
  have hL6 : (64 : ℝ) ≤ P.lgn ^ 6 := by
    have h : (2 : ℝ) ^ 6 ≤ P.lgn ^ 6 := pow_le_pow_left₀ (by norm_num) hL2 6
    norm_num at h
    linarith
  have hCL : (64000 : ℝ) ≤ (P.C' : ℝ) ^ 3 * P.lgn ^ 6 := by nlinarith [hC3, hL6]
  have hstep1 : (64000 : ℝ) * (P.lamStar : ℝ) ≤
      (P.C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 := by nlinarith [hCL, hlam1]
  have hstep2 : (64000 : ℝ) * (P.lamStar : ℝ) < (P.d : ℝ) * P.eta ^ 2 :=
    lt_of_le_of_lt hstep1 hkey
  have hbig : (64000 : ℝ) ≤ (P.d : ℝ) * P.eta ^ 2 := by nlinarith [hstep2, hlam1]
  have h3 : 64000 * (1 / P.eta) ≤ (P.d : ℝ) * P.eta ^ 2 * (1 / P.eta) :=
    mul_le_mul_of_nonneg_right hbig (by positivity)
  have h4 : (P.d : ℝ) * P.eta ^ 2 * (1 / P.eta) = (P.d : ℝ) * P.eta := by
    field_simp
  have h6 : (1 : ℝ) ≤ 64000 / P.eta := by
    rw [le_div_iff₀ hη0]
    nlinarith [hη]
  have h7 : 64000 / P.eta = 64000 * (1 / P.eta) := by ring
  linarith [h3, h4, h6, h7]

/-- `b = η(d+1)+1 = O(η d)`, in the explicit form `b ≤ 3 η d`. -/
lemma b_le_three_eta : P.eta * ((P.d : ℝ) + 1) + 1 ≤ 3 * P.eta * (P.d : ℝ) := by
  have hη0 := eta_pos P hA hC hargs hreg
  have hη1 : P.eta ≤ 1 := by linarith [eta_le_inv1024 P hA hC hargs hreg]
  have hd1 := eta_d_ge P hA hC hargs hreg
  nlinarith

lemma one_le_b : (1 : ℝ) ≤ P.eta * ((P.d : ℝ) + 1) + 1 := by
  have h := eta_pos P hA hC hargs hreg
  have := Nat.cast_nonneg (α := ℝ) P.d
  nlinarith

/-- `ℓ = B w ≤ 40 C' log² n`. -/

lemma ell_le : (P.ell : ℝ) ≤ 40 * (P.C' : ℝ) * P.lgn ^ 2 := by
  have hB := B_le P hA hC hargs hreg
  have hw := w_le P hA hC hargs hreg
  have hL := one_le_lgn P hA hC hargs hreg
  have hCpos : (0 : ℝ) ≤ (P.C' : ℝ) := by
    have : (1 : ℝ) ≤ (P.C' : ℝ) := by exact_mod_cast (by omega : 1 ≤ P.C')
    linarith
  have hell : (P.ell : ℝ) = (P.B : ℝ) * (P.w : ℝ) := by
    rw [TopParams.ell]; push_cast; ring
  rw [hell]
  have hB0 : (0 : ℝ) ≤ (P.B : ℝ) := by positivity
  have hw0 : (0 : ℝ) ≤ (P.w : ℝ) := by positivity
  have hstep : (P.B : ℝ) * (P.w : ℝ) ≤ (20 * (P.C' : ℝ) * P.lgn) * (P.lgn + 2) :=
    mul_le_mul hB hw hw0 (by positivity)
  have hstep' : (40 : ℝ) * (P.C' : ℝ) * P.lgn ^ 2 = 40 * (P.C' : ℝ) * P.lgn ^ 2 := rfl
  have hstep2 : (20 * (P.C' : ℝ) * P.lgn) * (P.lgn + 2) ≤ 40 * (P.C' : ℝ) * P.lgn ^ 2 := by
    have hL2 : (2 : ℝ) ≤ P.lgn := two_le_lgn P hA hC hargs hreg
    have hp : P.lgn + 2 ≤ 2 * P.lgn := by linarith
    have hq : (0 : ℝ) ≤ 20 * (P.C' : ℝ) * P.lgn := by nlinarith
    have h2 : (20 * (P.C' : ℝ) * P.lgn) * (P.lgn + 2) ≤
        (20 * (P.C' : ℝ) * P.lgn) * (2 * P.lgn) := mul_le_mul_of_nonneg_left hp hq
    have h3 : (20 * (P.C' : ℝ) * P.lgn) * (2 * P.lgn) = 40 * (P.C' : ℝ) * P.lgn ^ 2 := by ring
    linarith [h2, h3]
  linarith

end Regime

/-! ## §2. The four parts of Lemma 6.3

We follow the paper `lem:top-initial-budget`, in the paper's order.

* §2.1: the candidate support lies in its row (the hypothesis of Lemma 4.8);
* §2.2: an elementary estimate `exp(-(2Δ²/(5d))) ≤ 2^{-λ_*}` from the row-column regime;
* §2.3: the two per-column capacity-failure tails — Lemma 6.1 (*across words*) and Lemma 6.2
  (*within a word*) give `E U_{a,k} ≤ q_a`, `E V_{a,k} ≤ q_a p_k`; the capacities of (28) add the
  margin `η(d+1)`, and Lemma 4.8 (*concentration*) does the rest;
* §2.4: the `X`-budget (first line of `eq:top-initial-budget`);
* §2.5: the `h_N(Y)`-budget (second line), via `h_d`-monotonicity and subadditivity (Lemma 4.4) and
  the entropy bounds of Lemmas 6.1 and 6.2;
* §2.6: the mixed budget (the paper's last display).

The entropy-from-the-mean step (paper Lemma 4.5) is not imported separately: it is already packaged in
the third conjunct of the platform’s Lemma 6.1, which is what we use here. Lemma 6.2 is still *Open* on
the platform, so this file is a reduction through it: replace that import by its proof and everything
below is unconditional.
-/

/-- A uniform probability is at most one. -/
lemma prU_le_one {α : Type} [Fintype α] [Nonempty α] (Q : α → Prop) : prU Q ≤ 1 := by
  classical
  unfold prU
  have hc : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [div_le_one hc]
  have h := Finset.card_filter_le (s := (univ : Finset α)) (p := Q)
  have h2 : ((univ.filter Q).card : ℝ) ≤ ((univ : Finset α).card : ℝ) := by exact_mod_cast h
  simpa using h2

/-- `q_a ≥ 0`. -/
lemma q_nonneg (P : TopParams) (a : ℕ) : 0 ≤ P.q a := by
  unfold TopParams.q
  exact Finset.sum_nonneg fun j _ => prU_nonneg _

/-- `q_a ≤ d`: there are only `d` rows. -/
lemma q_le_d (P : TopParams) (a : ℕ) : P.q a ≤ (P.d : ℝ) := by
  unfold TopParams.q
  haveI : Nonempty (Equiv.Perm (Fin P.n)) := ⟨Equiv.refl _⟩
  calc ∑ j ∈ range P.d, prU (fun π : Equiv.Perm (Fin P.n) => a ≤ P.refLoad π j)
      ≤ ∑ j ∈ range P.d, (1 : ℝ) := Finset.sum_le_sum fun j _ => prU_le_one _
    _ = (P.d : ℝ) := by simp

/-- `q_a = 0` for `a > n`: a row of `[n]` holds at most `n` nonzeros. -/
lemma q_eq_zero_of_gt (P : TopParams) {a : ℕ} (ha : P.n < a) : P.q a = 0 := by
  haveI : Nonempty (Equiv.Perm (Fin P.n)) := ⟨Equiv.refl _⟩
  unfold TopParams.q
  refine Finset.sum_eq_zero fun j _ => ?_
  have h0 : ∀ π : Equiv.Perm (Fin P.n), ¬ (a ≤ P.refLoad π j) := by
    intro π hπ
    have hle : P.refLoad π j ≤ P.n := by
      unfold TopParams.refLoad rowImage
      calc ((univ.filter (fun i : Fin P.n => i.val ∈ range P.d ∧ (π i).val % P.d = j)).image
            (fun i => (π i).val / P.d)).card
          ≤ (univ.filter (fun i : Fin P.n => i.val ∈ range P.d ∧ (π i).val % P.d = j)).card :=
            Finset.card_image_le
        _ ≤ (univ : Finset (Fin P.n)).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
        _ = P.n := by simp
    omega
  have hbot : prU (fun _ : Equiv.Perm (Fin P.n) => False) = 0 := by
    unfold prU
    simp
  have hmono : prU (fun π : Equiv.Perm (Fin P.n) => a ≤ P.refLoad π j)
      ≤ prU (fun _ : Equiv.Perm (Fin P.n) => False) := by
    refine prU_mono fun π h => ?_
    exact absurd h (h0 π)
  have hnn : 0 ≤ prU (fun π : Equiv.Perm (Fin P.n) => a ≤ P.refLoad π j) := prU_nonneg _
  linarith

/-- Lemma 6.1 (second item) in finite form: `∑_{a=1}^{n} q_a ≤ d`. -/
lemma sum_q_le (P : TopParams) (hargs : P.Args) (F : Type) [Field F] [Fintype F]
    [Algebra (ZMod 2) F] (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F)
    (hι : P.IsAddress ι) (x : Finset ℕ) (hx : x ⊆ range P.n) (hxd : x.card ≤ P.d) :
    ∑ a ∈ range P.n, P.q (a + 1) ≤ (P.d : ℝ) := by
  have htsum : (∑' a : ℕ, ENNReal.ofReal (P.q (a + 1))) = (P.d : ℝ≥0∞) :=
    (lemma_6_1 P hargs F b ι hι x hx hxd).2.1
  have hzero : ∀ a ∉ range P.n, ENNReal.ofReal (P.q (a + 1)) = 0 := by
    intro a ha
    rw [Finset.mem_range, not_lt] at ha
    rw [q_eq_zero_of_gt P (by omega), ENNReal.ofReal_zero]
  rw [tsum_eq_sum hzero] at htsum
  have hcast : ENNReal.ofReal (∑ a ∈ range P.n, P.q (a + 1)) = ENNReal.ofReal ((P.d : ℝ)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => q_nonneg P (a + 1)), htsum,
      ENNReal.ofReal_natCast]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity : (0 : ℝ) ≤ (P.d : ℝ))).mp (le_of_eq hcast)

/-- `B ≤ n`. -/
lemma B_le_n (P : TopParams) (hA : 10 ≤ P.A) (hC : 10 ≤ P.C') (hargs : P.Args)
    (hreg : P.RowColumnRegime) : P.B ≤ P.n := by
  have h1 : P.B ≤ P.N := by rw [TopParams.B]; exact min_le_left _ _
  have h2 : P.N ≤ P.n := N_le_n P hA hC hargs hreg
  omega

/-- `∑_{a=1}^{B} q_a ≤ d`. -/
lemma sum_q_le_B (P : TopParams) (hA : 10 ≤ P.A) (hC : 10 ≤ P.C') (hargs : P.Args)
    (hreg : P.RowColumnRegime) (F : Type) [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (hι : P.IsAddress ι)
    (x : Finset ℕ) (hx : x ⊆ range P.n) (hxd : x.card ≤ P.d) :
    ∑ a ∈ range P.B, P.q (a + 1) ≤ (P.d : ℝ) := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
    (sum_q_le P hargs F b ι hι x hx hxd)
  · intro i hi
    rw [Finset.mem_range] at hi ⊢
    have h := B_le_n P hA hC hargs hreg
    omega
  · intro i _ _
    exact q_nonneg P (i + 1)

/-- `x log(1/x) ≥ 0` for a sub-probability `x`. -/
lemma entropy_term_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ x * lg (1 / x) := by
  rcases eq_or_lt_of_le hx0 with h | h
  · rw [← h]
    simp [lg]
  · have h1 : (1 : ℝ) ≤ 1 / x := by
      rw [le_div_iff₀ h]
      linarith
    exact mul_nonneg h.le (lg_nonneg h1)

/-- `q_a log(d/q_a) ≥ 0`. -/
lemma q_entropy_term_nonneg (P : TopParams) (a : ℕ) :
    0 ≤ P.q (a + 1) * lg ((P.d : ℝ) / P.q (a + 1)) := by
  have hq0 := q_nonneg P (a + 1)
  have hqd : P.q (a + 1) ≤ (P.d : ℝ) := q_le_d P (a + 1)
  rcases eq_or_lt_of_le hq0 with h | h
  · rw [← h]
    simp [lg]
  · refine mul_nonneg h.le (lg_nonneg ?_)
    rw [le_div_iff₀ h]
    linarith

/-- Lemma 6.1 (third item) in finite form, written in the `q log(d/q)` shape of
`eq:top-ideal-entropy`. -/
lemma sum_q_entropy_le (P : TopParams) (hargs : P.Args) (F : Type) [Field F] [Fintype F]
    [Algebra (ZMod 2) F] (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F)
    (hι : P.IsAddress ι) (x : Finset ℕ) (hx : x ⊆ range P.n) (hxd : x.card ≤ P.d) :
    ∑ a ∈ range P.n, P.q (a + 1) * lg ((P.d : ℝ) / P.q (a + 1)) ≤
      (P.d : ℝ) * lg (2 * Real.exp 1) := by
  have hdpos : (0 : ℝ) < (P.d : ℝ) := by
    exact_mod_cast (by have := hargs.1; omega : 0 < P.d)
  have hdne : ((P.d : ℝ)) ≠ 0 := ne_of_gt hdpos
  have hle1 : 0 ≤ lg (2 * Real.exp 1) := by
    apply lg_nonneg
    have h := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have h6 := (lemma_6_1 P hargs F b ι hι x hx hxd).2.2
  have hzero : ∀ a ∉ range P.n,
      ENNReal.ofReal ((P.q (a + 1) / (P.d : ℝ)) * lg (1 / (P.q (a + 1) / (P.d : ℝ)))) = 0 := by
    intro a ha
    rw [Finset.mem_range, not_lt] at ha
    rw [q_eq_zero_of_gt P (by omega)]
    simp [lg]
  have h6e : (∑ a ∈ range P.n, ENNReal.ofReal
      ((P.q (a + 1) / (P.d : ℝ)) * lg (1 / (P.q (a + 1) / (P.d : ℝ))))) ≤
      ENNReal.ofReal (lg (2 * Real.exp 1)) := by
    have h := h6
    simp only [entropy] at h
    rwa [tsum_eq_sum hzero] at h
  have hterm : ∀ a ∈ range P.n, ENNReal.ofReal
      ((P.q (a + 1) / (P.d : ℝ)) * lg (1 / (P.q (a + 1) / (P.d : ℝ))))
      = ENNReal.ofReal ((P.q (a + 1) * lg ((P.d : ℝ) / P.q (a + 1))) / (P.d : ℝ)) := by
    intro a _
    congr 1
    by_cases hq : P.q (a + 1) = 0
    · rw [hq]
      simp [lg]
    · have hqpos : 0 < P.q (a + 1) := lt_of_le_of_ne (q_nonneg P (a + 1)) (Ne.symm hq)
      have e : 1 / (P.q (a + 1) / (P.d : ℝ)) = (P.d : ℝ) / P.q (a + 1) := by
        field_simp
      rw [e]
      field_simp
  have hnn : ∀ a ∈ range P.n, 0 ≤ (P.q (a + 1) * lg ((P.d : ℝ) / P.q (a + 1))) / (P.d : ℝ) :=
    fun a _ => div_nonneg (q_entropy_term_nonneg P a) hdpos.le
  have hsum_eq : (∑ a ∈ range P.n, ENNReal.ofReal
        ((P.q (a + 1) * lg ((P.d : ℝ) / P.q (a + 1))) / (P.d : ℝ)))
      = ENNReal.ofReal ((∑ a ∈ range P.n, P.q (a + 1) * lg ((P.d : ℝ) / P.q (a + 1))) /
          (P.d : ℝ)) := by
    rw [← ENNReal.ofReal_sum_of_nonneg hnn, Finset.sum_div]
  have h6f : ENNReal.ofReal ((∑ a ∈ range P.n,
        P.q (a + 1) * lg ((P.d : ℝ) / P.q (a + 1))) / (P.d : ℝ)) ≤
      ENNReal.ofReal (lg (2 * Real.exp 1)) := by
    rw [← hsum_eq, ← Finset.sum_congr rfl hterm]
    exact h6e
  have hreal : (∑ a ∈ range P.n, P.q (a + 1) * lg ((P.d : ℝ) / P.q (a + 1))) / (P.d : ℝ) ≤
      lg (2 * Real.exp 1) :=
    (ENNReal.ofReal_le_ofReal_iff hle1).mp h6f
  rw [div_le_iff₀ hdpos] at hreal
  calc ∑ a ∈ range P.n, P.q (a + 1) * lg ((P.d : ℝ) / P.q (a + 1))
      ≤ lg (2 * Real.exp 1) * (P.d : ℝ) := hreal
    _ = (P.d : ℝ) * lg (2 * Real.exp 1) := by ring

/-- The same bound cut down to `a ≤ B`. -/
lemma sum_q_entropy_le_B (P : TopParams) (hA : 10 ≤ P.A) (hC : 10 ≤ P.C') (hargs : P.Args)
    (hreg : P.RowColumnRegime) (F : Type) [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (hι : P.IsAddress ι)
    (x : Finset ℕ) (hx : x ⊆ range P.n) (hxd : x.card ≤ P.d) :
    ∑ a ∈ range P.B, P.q (a + 1) * lg ((P.d : ℝ) / P.q (a + 1)) ≤
      (P.d : ℝ) * lg (2 * Real.exp 1) := by
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
    (sum_q_entropy_le P hargs F b ι hι x hx hxd)
  · intro i hi
    rw [Finset.mem_range] at hi ⊢
    have h := B_le_n P hA hC hargs hreg
    omega
  · intro i _ _
    exact q_entropy_term_nonneg P i

/-- `1 ≤ N`. -/
lemma one_le_N (P : TopParams) (hargs : P.Args) : 1 ≤ P.N := by
  rw [TopParams.N]
  have hd : (0 : ℝ) < (P.d : ℝ) := by
    exact_mod_cast (by have := hargs.1; omega : 0 < P.d)
  have h1 : (1 : ℝ) ≤ (P.n : ℝ) / (P.d : ℝ) := by
    rw [le_div_iff₀ hd]
    have h2 : (P.d : ℝ) ≤ (P.n : ℝ) := by exact_mod_cast hargs.2.1
    linarith
  have h2 : (P.n : ℝ) / (P.d : ℝ) ≤ ((⌈(P.n : ℝ) / (P.d : ℝ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h3 : (1 : ℝ) ≤ ((⌈(P.n : ℝ) / (P.d : ℝ)⌉₊ : ℕ) : ℝ) := le_trans h1 h2
  exact_mod_cast h3

/-- `1 ≤ w`. -/
lemma one_le_w (P : TopParams) (hargs : P.Args) : 1 ≤ P.w := by
  rw [TopParams.w]
  have hN := one_le_N P hargs
  have hN1 : (2 : ℝ) ≤ (P.N : ℝ) + 1 := by
    have h : (1 : ℝ) ≤ (P.N : ℝ) := by exact_mod_cast hN
    linarith
  have h1 : (1 : ℝ) ≤ lg ((P.N : ℝ) + 1) := by
    have h := lg_mono (by norm_num : (0 : ℝ) < 2) hN1
    rwa [lg_two] at h
  have h2 : lg ((P.N : ℝ) + 1) ≤ ((⌈lg ((P.N : ℝ) + 1)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h3 : (1 : ℝ) ≤ ((⌈lg ((P.N : ℝ) + 1)⌉₊ : ℕ) : ℝ) := le_trans h1 h2
  exact_mod_cast h3

/-- `p_k > 0` for `k < w`. -/
lemma p_pos (P : TopParams) (hargs : P.Args) {k : ℕ} (hk : k < P.w) : 0 < P.p k := by
  have hw := one_le_w P hargs
  unfold TopParams.p
  refine div_pos (pow_pos (by norm_num) _) ?_
  have h : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ P.w := pow_le_pow_right₀ (by norm_num) hw
  nlinarith

/-- `p_k ≤ 1` for `k < w`. -/
lemma p_le_one (P : TopParams) (hargs : P.Args) {k : ℕ} (hk : k < P.w) : P.p k ≤ 1 := by
  have hw := one_le_w P hargs
  have hpos : (0 : ℝ) < (2 : ℝ) ^ P.w - 1 := by
    have h : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ P.w := pow_le_pow_right₀ (by norm_num) hw
    nlinarith
  unfold TopParams.p
  rw [div_le_one hpos]
  have h2 : (2 : ℝ) ^ (P.w - (k + 1)) ≤ (2 : ℝ) ^ (P.w - 1) := by
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have h4 : (2 : ℝ) ^ P.w = 2 * (2 : ℝ) ^ (P.w - 1) := by
    have h5 := pow_succ (2 : ℝ) (P.w - 1)
    rw [show P.w - 1 + 1 = P.w by omega] at h5
    linarith
  have h6 : (1 : ℝ) ≤ (2 : ℝ) ^ (P.w - 1) := by
    have h7 : (2 : ℝ) ^ 0 ≤ (2 : ℝ) ^ (P.w - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    simpa using h7
  linarith

/-- Lemma 6.2: `∑_k p_k = 1`. -/
lemma sum_p_eq_one (P : TopParams) (hargs : P.Args) (F : Type) [Field F] [Fintype F]
    [Algebra (ZMod 2) F] (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F)
    (hι : P.IsAddress ι) (x : Finset ℕ) (hx : x ⊆ range P.n) (hxd : x.card ≤ P.d) :
    ∑ k ∈ range P.w, P.p k = 1 :=
  (lemma_6_2 P hargs F b ι hι x hx hxd).2.1

/-- Lemma 6.2: `H(p) ≤ 2`. -/
lemma sum_p_entropy_le (P : TopParams) (hargs : P.Args) (F : Type) [Field F] [Fintype F]
    [Algebra (ZMod 2) F] (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F)
    (hι : P.IsAddress ι) (x : Finset ℕ) (hx : x ⊆ range P.n) (hxd : x.card ≤ P.d) :
    ∑ k ∈ range P.w, P.p k * lg (1 / P.p k) ≤ 2 := by
  have h3 := (lemma_6_2 P hargs F b ι hι x hx hxd).2.2.1
  have he : entropyFin (fun k : Fin P.w => P.p k.val) =
      ∑ k ∈ range P.w, P.p k * lg (1 / P.p k) := by
    simp only [entropyFin]
    exact Fin.sum_univ_eq_sum_range (fun k => P.p k * lg (1 / P.p k)) P.w
  rw [he] at h3
  exact h3

/-- `η log^k n ≤ 1/log n` for `k + 1 ≤ A`. -/
lemma eta_mul_lgn_pow_le (P : TopParams) (hA : 10 ≤ P.A) (hC : 10 ≤ P.C') (hargs : P.Args)
    (hreg : P.RowColumnRegime) {k : ℕ} (hk : k + 1 ≤ P.A) :
    P.eta * P.lgn ^ k ≤ 1 / P.lgn := by
  have hL0 := lgn_pos P hA hC hargs hreg
  have hL1 := one_le_lgn P hA hC hargs hreg
  have hstep : P.lgn ^ (k + 1) ≤ P.lgn ^ P.A := pow_le_pow_right₀ hL1 hk
  have hinv : (P.lgn ^ P.A)⁻¹ ≤ (P.lgn ^ (k + 1))⁻¹ := by
    rw [inv_le_inv₀ (pow_pos hL0 P.A) (pow_pos hL0 (k + 1))]
    exact hstep
  have h1 : P.eta * P.lgn ^ k = P.lgn ^ k * (P.lgn ^ P.A)⁻¹ := by
    rw [TopParams.eta]; ring
  rw [h1]
  calc P.lgn ^ k * (P.lgn ^ P.A)⁻¹ ≤ P.lgn ^ k * (P.lgn ^ (k + 1))⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 1 / P.lgn := by
        rw [pow_succ]
        field_simp

/-! ### §2.1 The candidate support lies in its row (hypothesis of Lemma 4.8) -/

/-- Every candidate support is a subset of the row. -/
lemma cand_subset (P : TopParams) (F : Type) [Field F] [Algebra (ZMod 2) F]
    (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (j : ℕ) (α : Fin P.B → Fˣ)
    (z : List (ZMod 2)) (i : ℕ) {C : Finset ℕ} (hC : P.cand b ι j α z i = some C) :
    C ⊆ range (rowLen P.n P.d j) := by
  classical
  simp only [TopParams.cand] at hC
  have h2 : C ∈ ((range (rowLen P.n P.d j)).powerset.filter fun S =>
      S.card ≤ i ∧ ∀ a : Fin P.B, a.val < i →
        TopParams.power ι (2 * a.val + 1) S = ((α a)⁻¹ : Fˣ) * TopParams.wordOf P b z a.val) :=
    Finset.mem_toList.mp (List.mem_of_mem_head? hC)
  exact Finset.mem_powerset.mp (Finset.mem_filter.mp h2).1

/-- A candidate has at most `n` elements. -/
lemma cand_card_le (P : TopParams) (F : Type) [Field F] [Algebra (ZMod 2) F]
    (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (j : ℕ) (α : Fin P.B → Fˣ)
    (z : List (ZMod 2)) (i : ℕ) {C : Finset ℕ} (hC : P.cand b ι j α z i = some C) :
    C.card ≤ P.n := by
  have hsub := cand_subset P F b ι j α z i hC
  have h1 : C.card ≤ (range (rowLen P.n P.d j)).card := Finset.card_le_card hsub
  rw [Finset.card_range] at h1
  have h2 : rowLen P.n P.d j ≤ P.n := by
    unfold rowLen
    calc ((range P.n).filter fun p => p % P.d = j).card ≤ (range P.n).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ = P.n := Finset.card_range P.n
  omega

/-- The row estimate of the exact execution has at most `n` elements, so Lemma 4.8 applies with
`K = n` (only the `Z`-part of Lemma 4.8 uses `K`, and we do not need that part). -/
lemma exactRowEst_card_le (P : TopParams) (F : Type) [Field F] [Fintype F]
    [Algebra (ZMod 2) F] (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F)
    (x J : Finset ℕ) :
    ∀ (lr : (P.scheme b ι).LocalSeed) (j : Fin (P.scheme b ι).m),
      ((P.scheme b ι).exactRowEst lr x J j).card ≤ P.n := by
  intro lr j
  have hfin : (P.scheme b ι).exactRowEst lr x J j
      = (P.cand b ι j.val (lr.2 j) ((P.scheme b ι).truePrefix j (lr.2 j)
          ((P.scheme b ι).rowOf lr x j) P.ell) P.B).getD ∅ := rfl
  rw [hfin]
  cases hc : P.cand b ι j.val (lr.2 j) ((P.scheme b ι).truePrefix j (lr.2 j)
      ((P.scheme b ι).rowOf lr x j) P.ell) P.B with
  | none => simp only [hc, Option.getD_none, Finset.card_empty]; exact Nat.zero_le _
  | some C =>
      simp only [hc, Option.getD_some]
      exact cand_card_le P F b ι j.val (lr.2 j) _ P.B hc

/-- `U_s ≤ m = d`: `U_s` counts rows. -/
lemma U_le_m (P : TopParams) (F : Type) [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (x J : Finset ℕ)
    (s : Fin (P.scheme b ι).ℓ) (lr : (P.scheme b ι).LocalSeed) :
    (P.scheme b ι).U lr x J s ≤ P.d := by
  have h := Finset.card_le_card (Finset.filter_subset
    (fun j : Fin (P.scheme b ι).m => (P.scheme b ι).exactPred lr x J s j = none) Finset.univ)
  have h2 : (Finset.univ : Finset (Fin (P.scheme b ι).m)).card = P.d := by
    show (Finset.univ : Finset (Fin P.d)).card = P.d
    simp
  unfold RowScheme.U
  omega

/-- `V_s ≤ m = d`. -/
lemma V_le_m (P : TopParams) (F : Type) [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (x J : Finset ℕ)
    (s : Fin (P.scheme b ι).ℓ) (lr : (P.scheme b ι).LocalSeed) :
    (P.scheme b ι).V lr x J s ≤ P.d := by
  have h := Finset.card_le_card (Finset.filter_subset
    (fun j : Fin (P.scheme b ι).m => ∃ b', (P.scheme b ι).exactPred lr x J s j = some b' ∧
      b' ≠ (P.scheme b ι).code j (lr.2 j) ((P.scheme b ι).rowOf lr x j) s) Finset.univ)
  have h2 : (Finset.univ : Finset (Fin (P.scheme b ι).m)).card = P.d := by
    show (Finset.univ : Finset (Fin P.d)).card = P.d
    simp
  unfold RowScheme.V
  omega

/-! ### §2.2 The concentration estimate `2^{-λ_*}` -/

/-- With `Δ = η(d+1)` and the row-column regime, `exp(-(2Δ²/(5d))) ≤ 2^{-λ_*}`: this is the last
step of the paper's "capacities are sufficient" argument. -/
lemma exp_bound_lamStar (P : TopParams) (hA : 10 ≤ P.A) (hC : 10 ≤ P.C') (hargs : P.Args)
    (hreg : P.RowColumnRegime) {Δ : ℝ} (hΔ : Δ = P.eta * ((P.d : ℝ) + 1)) :
    Real.exp (-(2 * Δ ^ 2 / (5 * (P.d : ℝ)))) ≤ ((2 : ℝ) ^ P.lamStar)⁻¹ := by
  rw [two_pow_inv_eq_exp]
  apply Real.exp_le_exp.mpr
  have hd2 : (2 : ℝ) ≤ (P.d : ℝ) := by exact_mod_cast hargs.1
  have hd0 : (0 : ℝ) < (P.d : ℝ) := by linarith
  have hC10 : (10 : ℝ) ≤ (P.C' : ℝ) := by exact_mod_cast hC
  have hL2 : (2 : ℝ) ≤ P.lgn := two_le_lgn P hA hC hargs hreg
  have hη0 : 0 < P.eta := eta_pos P hA hC hargs hreg
  have hη2 : (0 : ℝ) ≤ P.eta ^ 2 := by positivity
  have hlam1 : (1 : ℝ) ≤ (P.lamStar : ℝ) := one_le_lamStar P hA hC hargs hreg
  have hregk := regime_key P hA hC hargs hreg
  have hC3 : (1000 : ℝ) ≤ (P.C' : ℝ) ^ 3 := by
    have h : (10 : ℝ) ^ 3 ≤ (P.C' : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hC10 3
    norm_num at h
    linarith
  have hL6 : (64 : ℝ) ≤ P.lgn ^ 6 := by
    have h : (2 : ℝ) ^ 6 ≤ P.lgn ^ 6 := pow_le_pow_left₀ (by norm_num) hL2 6
    norm_num at h
    linarith
  have hCL : (64000 : ℝ) ≤ (P.C' : ℝ) ^ 3 * P.lgn ^ 6 := by nlinarith [hC3, hL6]
  have hstep1 : (64000 : ℝ) * (P.lamStar : ℝ) ≤
      (P.C' : ℝ) ^ 3 * (P.lamStar : ℝ) * P.lgn ^ 6 := by nlinarith [hCL, hlam1]
  have hstep2 : (64000 : ℝ) * (P.lamStar : ℝ) < (P.d : ℝ) * P.eta ^ 2 :=
    lt_of_le_of_lt hstep1 hregk
  have hbig : (64000 : ℝ) * (P.d : ℝ) * (P.lamStar : ℝ) < (P.d : ℝ) ^ 2 * P.eta ^ 2 := by
    nlinarith [hstep2, hd0]
  have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have h5 : 5 * ((P.d : ℝ) * (P.lamStar : ℝ) * Real.log 2) ≤
      5 * ((P.d : ℝ) * (P.lamStar : ℝ)) := by
    have h1 : (P.d : ℝ) * (P.lamStar : ℝ) * Real.log 2 ≤ (P.d : ℝ) * (P.lamStar : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hlog2 (by positivity)
    linarith
  have h6 : 5 * ((P.d : ℝ) * (P.lamStar : ℝ)) ≤ 2 * ((P.d : ℝ) ^ 2 * P.eta ^ 2) := by
    nlinarith [hbig]
  have hsq : (P.d : ℝ) ^ 2 ≤ ((P.d : ℝ) + 1) ^ 2 := by nlinarith
  have h7 : 2 * ((P.d : ℝ) ^ 2 * P.eta ^ 2) ≤ 2 * (P.eta * ((P.d : ℝ) + 1)) ^ 2 := by
    nlinarith [hsq, hη2, hd0]
  have hpos : (0 : ℝ) < 5 * (P.d : ℝ) := by positivity
  have hkey : (P.lamStar : ℝ) * Real.log 2 ≤
      2 * (P.eta * ((P.d : ℝ) + 1)) ^ 2 / (5 * (P.d : ℝ)) := by
    rw [le_div_iff₀ hpos]
    nlinarith [h5, h6, h7]
  rw [hΔ]
  linarith [hkey]

/-! ### §2.3 The two capacity-failure tails -/

/-- **Lemma 6.3, part 1 (X).** The event `U_{a,k} > X_{a,k}` has probability at most `2^{-λ_*}`:
Lemma 6.1 gives `E U_{a,k} ≤ q_a`, the capacity `X_{a,k} = min{d, ⌈q_a + η(d+1)⌉}` adds the margin
`η(d+1)`, and Lemma 4.8 concentrates `U` with `Δ = η(d+1)`. -/
lemma tail_X (P : TopParams) (hA : 10 ≤ P.A) (hC : 10 ≤ P.C') (hargs : P.Args)
    (hreg : P.RowColumnRegime) (F : Type) [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (hι : P.IsAddress ι)
    (x : Finset ℕ) (hx : x ⊆ range P.n) (hxd : x.card ≤ P.d) (s : Fin P.ell) :
    prU (fun lr : (P.scheme b ι).LocalSeed =>
        P.capX (P.wordIdx s).val < (P.scheme b ι).U lr x ∅ s) ≤
      ((2 : ℝ) ^ P.lamStar)⁻¹ := by
  have hne : Nonempty (P.scheme b ι).LocalSeed :=
    ⟨(Equiv.refl _, fun _ => Classical.arbitrary _)⟩
  haveI := hne
  have hΔpos : 0 < P.eta * ((P.d : ℝ) + 1) := by
    have h1 := eta_pos P hA hC hargs hreg
    have h2 : (0 : ℝ) ≤ (P.d : ℝ) := by positivity
    nlinarith
  have hm1 : 1 ≤ (P.scheme b ι).m := by
    simp only [TopParams.scheme]
    have h := hargs.1
    omega
  have hD : (P.scheme b ι).m ≤ P.d := by simp [TopParams.scheme]
  have hDJ : (∅ ∪ x).card ≤ P.d := by simpa using hxd
  have hK : 1 ≤ P.n := by
    have h1 := hargs.1
    have h2 := hargs.2.1
    omega
  have h48 := (lemma_4_8 (P.scheme b ι) x ∅ hx (Finset.empty_subset _) hm1 P.d hD hDJ P.n hK
    (exactRowEst_card_le P F b ι x ∅) (P.eta * ((P.d : ℝ) + 1)) hΔpos).1 s
  refine le_trans (prU_mono ?_) (le_trans h48 ?_)
  · intro lr hlt
    have hU := U_le_m P F b ι x ∅ s lr
    have hexp := (lemma_6_1 P hargs F b ι hι x hx hxd).1 s
    have hcap : P.capX (P.wordIdx s).val
        = min P.d ⌈P.q ((P.wordIdx s).val + 1) + P.eta * ((P.d : ℝ) + 1)⌉₊ := rfl
    have hkey : P.q ((P.wordIdx s).val + 1) + P.eta * ((P.d : ℝ) + 1) <
        ((P.scheme b ι).U lr x ∅ s : ℝ) := by
      rcases le_total ⌈P.q ((P.wordIdx s).val + 1) + P.eta * ((P.d : ℝ) + 1)⌉₊ P.d with h | h
      · rw [hcap, min_eq_right h] at hlt
        have h1 : P.q ((P.wordIdx s).val + 1) + P.eta * ((P.d : ℝ) + 1)
            ≤ (⌈P.q ((P.wordIdx s).val + 1) + P.eta * ((P.d : ℝ) + 1)⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : (⌈P.q ((P.wordIdx s).val + 1) + P.eta * ((P.d : ℝ) + 1)⌉₊ : ℝ)
            < ((P.scheme b ι).U lr x ∅ s : ℝ) := by exact_mod_cast hlt
        linarith
      · rw [hcap, min_eq_left h] at hlt
        omega
    linarith
  · exact exp_bound_lamStar P hA hC hargs hreg rfl

/-- **Lemma 6.3, part 1 (Y).** The event `V_{a,k} > Y_{a,k}` has probability at most `2^{-λ_*}`:
Lemma 6.2 gives `E V_{a,k} ≤ q_a p_k`, and the same concentration argument applies. -/
lemma tail_Y (P : TopParams) (hA : 10 ≤ P.A) (hC : 10 ≤ P.C') (hargs : P.Args)
    (hreg : P.RowColumnRegime) (F : Type) [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (hι : P.IsAddress ι)
    (x : Finset ℕ) (hx : x ⊆ range P.n) (hxd : x.card ≤ P.d) (s : Fin P.ell) :
    prU (fun lr : (P.scheme b ι).LocalSeed =>
        P.capY (P.wordIdx s).val (P.bitIdx s).val < (P.scheme b ι).V lr x ∅ s) ≤
      ((2 : ℝ) ^ P.lamStar)⁻¹ := by
  have hne : Nonempty (P.scheme b ι).LocalSeed :=
    ⟨(Equiv.refl _, fun _ => Classical.arbitrary _)⟩
  haveI := hne
  have hΔpos : 0 < P.eta * ((P.d : ℝ) + 1) := by
    have h1 := eta_pos P hA hC hargs hreg
    have h2 : (0 : ℝ) ≤ (P.d : ℝ) := by positivity
    nlinarith
  have hm1 : 1 ≤ (P.scheme b ι).m := by
    simp only [TopParams.scheme]
    have h := hargs.1
    omega
  have hD : (P.scheme b ι).m ≤ P.d := by simp [TopParams.scheme]
  have hDJ : (∅ ∪ x).card ≤ P.d := by simpa using hxd
  have hK : 1 ≤ P.n := by
    have h1 := hargs.1
    have h2 := hargs.2.1
    omega
  have h48 := (lemma_4_8 (P.scheme b ι) x ∅ hx (Finset.empty_subset _) hm1 P.d hD hDJ P.n hK
    (exactRowEst_card_le P F b ι x ∅) (P.eta * ((P.d : ℝ) + 1)) hΔpos).2.1 s
  refine le_trans (prU_mono ?_) (le_trans h48 ?_)
  · intro lr hlt
    have hV := (lemma_6_2 P hargs F b ι hι x hx hxd).2.2.2 s
    have hVm := V_le_m P F b ι x ∅ s lr
    have hcap : P.capY (P.wordIdx s).val (P.bitIdx s).val
        = min P.d ⌈P.q ((P.wordIdx s).val + 1) * P.p (P.bitIdx s).val +
            P.eta * ((P.d : ℝ) + 1)⌉₊ := rfl
    have hkey : P.q ((P.wordIdx s).val + 1) * P.p (P.bitIdx s).val +
        P.eta * ((P.d : ℝ) + 1) < ((P.scheme b ι).V lr x ∅ s : ℝ) := by
      rcases le_total (⌈P.q ((P.wordIdx s).val + 1) * P.p (P.bitIdx s).val +
          P.eta * ((P.d : ℝ) + 1)⌉₊) P.d with h | h
      · rw [hcap, min_eq_right h] at hlt
        have h1 : P.q ((P.wordIdx s).val + 1) * P.p (P.bitIdx s).val +
            P.eta * ((P.d : ℝ) + 1)
            ≤ (⌈P.q ((P.wordIdx s).val + 1) * P.p (P.bitIdx s).val +
                P.eta * ((P.d : ℝ) + 1)⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : (⌈P.q ((P.wordIdx s).val + 1) * P.p (P.bitIdx s).val +
            P.eta * ((P.d : ℝ) + 1)⌉₊ : ℝ) < ((P.scheme b ι).V lr x ∅ s : ℝ) := by
          exact_mod_cast hlt
        linarith
      · rw [hcap, min_eq_left h] at hlt
        omega
    linarith
  · exact exp_bound_lamStar P hA hC hargs hreg rfl

/-! ### §2.4 The `X`-budget (`eq:top-initial-budget`, first line) -/

/-- **Lemma 6.3, part 2.** `∑_{a,k} X_{a,k} ≤ d w + O(C' d / log n)`, with explicit constant
`100`: the paper's `∑_{a,k} X_{a,k} ≤ w ∑_a q_a + ℓ b ≤ dw + ℓ b`. -/
lemma budget_X (P : TopParams) (hA : 10 ≤ P.A) (hC : 10 ≤ P.C') (hargs : P.Args)
    (hreg : P.RowColumnRegime) (F : Type) [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (hι : P.IsAddress ι)
    (x : Finset ℕ) (hx : x ⊆ range P.n) (hxd : x.card ≤ P.d) :
    (∑ a ∈ range P.B, ∑ _k ∈ range P.w, (P.capX a : ℝ)) ≤
      (P.d : ℝ) * P.w + 250 * ((P.C' : ℝ) * (P.d : ℝ) / P.lgn) := by
  have hL0 := lgn_pos P hA hC hargs hreg
  have hdpos : (0 : ℝ) < (P.d : ℝ) := by
    exact_mod_cast (by have := hargs.1; omega : 0 < P.d)
  have hw0 : (0 : ℝ) ≤ (P.w : ℝ) := Nat.cast_nonneg _
  have hXp : (0 : ℝ) ≤ (P.C' : ℝ) * (P.d : ℝ) / P.lgn :=
    div_nonneg (by positivity) (le_of_lt hL0)
  have hcap : ∀ a, (P.capX a : ℝ) ≤ P.q (a + 1) + (P.eta * ((P.d : ℝ) + 1) + 1) := by
    intro a
    have h1 : (P.capX a : ℝ) ≤ ((⌈P.q (a + 1) + P.eta * ((P.d : ℝ) + 1)⌉₊ : ℕ) : ℝ) := by
      have h0 : P.capX a ≤ ⌈P.q (a + 1) + P.eta * ((P.d : ℝ) + 1)⌉₊ :=
        min_le_right P.d ⌈P.q (a + 1) + P.eta * ((P.d : ℝ) + 1)⌉₊
      exact_mod_cast h0
    have hb0 : (0 : ℝ) ≤ P.q (a + 1) + P.eta * ((P.d : ℝ) + 1) := by
      have hq := q_nonneg P (a + 1)
      have hη := eta_pos P hA hC hargs hreg
      have h2 : (0 : ℝ) ≤ (P.d : ℝ) := by positivity
      nlinarith
    have h2 := Nat.ceil_lt_add_one hb0
    linarith
  have hinner : ∀ a : ℕ, (∑ _k ∈ range P.w, (P.capX a : ℝ)) = (P.w : ℝ) * (P.capX a : ℝ) := by
    intro a
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
  have hstep : (∑ a ∈ range P.B, ∑ _k ∈ range P.w, (P.capX a : ℝ))
      = (P.w : ℝ) * ∑ a ∈ range P.B, (P.capX a : ℝ) := by
    simp only [hinner]
    rw [Finset.mul_sum]
  have hmass : ∑ a ∈ range P.B, P.q (a + 1) ≤ (P.d : ℝ) :=
    sum_q_le_B P hA hC hargs hreg F b ι hι x hx hxd
  have hsum : ∑ a ∈ range P.B, (P.capX a : ℝ) ≤
      (P.d : ℝ) + (P.B : ℝ) * (P.eta * ((P.d : ℝ) + 1) + 1) := by
    have h1 : ∑ a ∈ range P.B, (P.capX a : ℝ)
        ≤ ∑ a ∈ range P.B, (P.q (a + 1) + (P.eta * ((P.d : ℝ) + 1) + 1)) :=
      Finset.sum_le_sum fun a _ => hcap a
    have h2 : ∑ a ∈ range P.B, (P.q (a + 1) + (P.eta * ((P.d : ℝ) + 1) + 1))
        = (∑ a ∈ range P.B, P.q (a + 1)) + (P.B : ℝ) * (P.eta * ((P.d : ℝ) + 1) + 1) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_range]
    linarith
  have hell : (P.ell : ℝ) ≤ 40 * (P.C' : ℝ) * P.lgn ^ 2 := ell_le P hA hC hargs hreg
  have hm3 : P.eta * ((P.d : ℝ) + 1) + 1 ≤ 3 * P.eta * (P.d : ℝ) :=
    b_le_three_eta P hA hC hargs hreg
  have hm0 : (0 : ℝ) ≤ P.eta * ((P.d : ℝ) + 1) + 1 := by
    linarith [one_le_b P hA hC hargs hreg]
  have hEL : (P.ell : ℝ) * (P.eta * ((P.d : ℝ) + 1) + 1)
      ≤ (40 * (P.C' : ℝ) * P.lgn ^ 2) * (3 * P.eta * (P.d : ℝ)) :=
    mul_le_mul hell hm3 hm0 (by positivity)
  have heta : P.eta * P.lgn ^ 2 ≤ 1 / P.lgn :=
    eta_mul_lgn_pow_le P hA hC hargs hreg (k := 2) (by omega)
  have hEL2 : (40 * (P.C' : ℝ) * P.lgn ^ 2) * (3 * P.eta * (P.d : ℝ)) ≤
      250 * ((P.C' : ℝ) * (P.d : ℝ) / P.lgn) := by
    have h1 : (40 * (P.C' : ℝ) * P.lgn ^ 2) * (3 * P.eta * (P.d : ℝ))
        = 120 * (P.C' : ℝ) * (P.d : ℝ) * (P.eta * P.lgn ^ 2) := by ring
    rw [h1]
    have h2 : 120 * (P.C' : ℝ) * (P.d : ℝ) * (P.eta * P.lgn ^ 2)
        ≤ 120 * (P.C' : ℝ) * (P.d : ℝ) * (1 / P.lgn) :=
      mul_le_mul_of_nonneg_left heta (by positivity)
    have h3 : 120 * (P.C' : ℝ) * (P.d : ℝ) * (1 / P.lgn)
        = 120 * ((P.C' : ℝ) * (P.d : ℝ) / P.lgn) := by ring
    linarith [h2, h3]
  have hmain : (P.w : ℝ) * ∑ a ∈ range P.B, (P.capX a : ℝ) ≤
      (P.w : ℝ) * ((P.d : ℝ) + (P.B : ℝ) * (P.eta * ((P.d : ℝ) + 1) + 1)) :=
    mul_le_mul_of_nonneg_left hsum hw0
  have hexpand : (P.w : ℝ) * ((P.d : ℝ) + (P.B : ℝ) * (P.eta * ((P.d : ℝ) + 1) + 1))
      = (P.d : ℝ) * P.w + (P.ell : ℝ) * (P.eta * ((P.d : ℝ) + 1) + 1) := by
    have h1 : (P.ell : ℝ) = (P.B : ℝ) * (P.w : ℝ) := by
      rw [TopParams.ell]; push_cast; ring
    rw [h1]; ring
  rw [hstep]
  linarith [hmain, hexpand, hEL, hEL2, hXp]

/-! ### §2.5 The `h_N(Y)`-budget (`eq:top-initial-budget`, second line) -/

/-- `∑_{a,k} q_a p_k ≤ d`: `∑_k p_k = 1` and `∑_a q_a ≤ d`. -/
lemma sum_qp_le (P : TopParams) (hA : 10 ≤ P.A) (hC : 10 ≤ P.C') (hargs : P.Args)
    (hreg : P.RowColumnRegime) (F : Type) [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (hι : P.IsAddress ι)
    (x : Finset ℕ) (hx : x ⊆ range P.n) (hxd : x.card ≤ P.d) :
    ∑ a ∈ range P.B, ∑ k ∈ range P.w, P.q (a + 1) * P.p k ≤ (P.d : ℝ) := by
  have h1 : ∑ a ∈ range P.B, ∑ k ∈ range P.w, P.q (a + 1) * P.p k
      = (∑ a ∈ range P.B, P.q (a + 1)) * (∑ k ∈ range P.w, P.p k) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
  rw [h1, sum_p_eq_one P hargs F b ι hι x hx hxd, mul_one]
  exact sum_q_le_B P hA hC hargs hreg F b ι hι x hx hxd

/-- `∑_{k ∈ s} (if p k then c else 0) = (∑_{k ∈ s} (if p k then 1 else 0)) * c`. -/
lemma sum_ite_mul_const (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] (c : ℝ) :
    ∑ k ∈ s, (if p k then c else 0) = (∑ k ∈ s, (if p k then (1 : ℝ) else 0)) * c := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by by_cases h : p k <;> simp [h]

/-- The pointwise reduction of `eq:top-ideal-entropy`: `h_d(Y_{a,k})` is at most the ideal term
`h_d(q_a p_k)` plus the margin `h_d(b)`, plus a full `h_d(d) = log e · d` in the single place where
the ideal value overflows `d`. -/
lemma hN_capY_le (P : TopParams) (hA : 10 ≤ P.A) (hC : 10 ≤ P.C') (hargs : P.Args)
    (hreg : P.RowColumnRegime) (a k : ℕ) (hk : k < P.w) (m : ℝ)
    (hm : m = P.eta * ((P.d : ℝ) + 1) + 1) :
    hN P.d (P.capY a k : ℝ) ≤ hN P.d (P.q (a + 1) * P.p k) + hN P.d m +
      (if P.q (a + 1) * P.p k + m ≤ (P.d : ℝ) then 0 else lg (Real.exp 1) * (P.d : ℝ)) := by
  have hdpos : (0 : ℝ) < (P.d : ℝ) := by
    exact_mod_cast (by have := hargs.1; omega : 0 < P.d)
  have hdne : ((P.d : ℝ)) ≠ 0 := ne_of_gt hdpos
  have hmpos : 0 < m := by
    rw [hm]
    have h1 := eta_pos P hA hC hargs hreg
    have h2 : (0 : ℝ) ≤ (P.d : ℝ) := by positivity
    nlinarith
  have hmd : m ≤ (P.d : ℝ) := by
    rw [hm]
    have h := b_le_tenth P hA hC hargs hreg
    linarith
  have hz0 : (0 : ℝ) ≤ P.q (a + 1) * P.p k :=
    mul_nonneg (q_nonneg P (a + 1)) (p_pos P hargs hk).le
  have hzle : P.q (a + 1) * P.p k ≤ (P.d : ℝ) := by
    have h1 : P.q (a + 1) ≤ (P.d : ℝ) := q_le_d P (a + 1)
    have h2 : P.p k ≤ 1 := p_le_one P hargs hk
    calc P.q (a + 1) * P.p k ≤ (P.d : ℝ) * 1 :=
          mul_le_mul h1 h2 (p_pos P hargs hk).le hdpos.le
      _ = (P.d : ℝ) := by ring
  have hcap : (P.capY a k : ℝ) ≤ P.q (a + 1) * P.p k + m := by
    have h1 : (P.capY a k : ℝ) ≤
        ((⌈P.q (a + 1) * P.p k + P.eta * ((P.d : ℝ) + 1)⌉₊ : ℕ) : ℝ) := by
      have h0 : P.capY a k ≤ ⌈P.q (a + 1) * P.p k + P.eta * ((P.d : ℝ) + 1)⌉₊ :=
        min_le_right P.d ⌈P.q (a + 1) * P.p k + P.eta * ((P.d : ℝ) + 1)⌉₊
      exact_mod_cast h0
    have hb0 : (0 : ℝ) ≤ P.q (a + 1) * P.p k + P.eta * ((P.d : ℝ) + 1) := by
      have hη := eta_pos P hA hC hargs hreg
      have h2 : (0 : ℝ) ≤ (P.d : ℝ) := by positivity
      nlinarith
    have h2 := Nat.ceil_lt_add_one hb0
    rw [hm]
    linarith
  have hcapd : (P.capY a k : ℝ) ≤ (P.d : ℝ) := by
    have h0 : P.capY a k ≤ P.d := min_le_left _ _
    exact_mod_cast h0
  by_cases hcase : P.q (a + 1) * P.p k + m ≤ (P.d : ℝ)
  · rw [if_pos hcase]
    have hsub : hN P.d (P.q (a + 1) * P.p k + m) ≤
        hN P.d (P.q (a + 1) * P.p k) + hN P.d m :=
      (lemma_4_4 P.d).2 _ _ hz0 hmpos.le hcase
    have hmono : hN P.d (P.capY a k : ℝ) ≤ hN P.d (P.q (a + 1) * P.p k + m) :=
      hN_mono (Nat.cast_nonneg _) hcap hcase
    linarith
  · rw [if_neg hcase]
    have hle : hN P.d (P.capY a k : ℝ) ≤ lg (Real.exp 1) * (P.d : ℝ) := by
      have h1 : hN P.d ((P.capY a k : ℕ) : ℝ) ≤ hN P.d ((P.d : ℕ) : ℝ) :=
        hN_mono (Nat.cast_nonneg _) hcapd (le_refl _)
      have h2 : hN P.d ((P.d : ℕ) : ℝ) = lg (Real.exp 1) * (P.d : ℝ) := hN_self hdne
      linarith
    have hz : (0 : ℝ) ≤ hN P.d (P.q (a + 1) * P.p k) := hN_nonneg hz0 hzle
    have hzm : (0 : ℝ) ≤ hN P.d m := hN_nonneg hmpos.le hmd
    linarith

/-- `∑_{a,k} h_d(q_a p_k) ≤ d (log e + log 2e + 2)`: the termwise entropy expansion of
`eq:top-ideal-entropy`, using Lemmas 6.1 and 6.2. -/
lemma budget_hN_ideal (P : TopParams) (hA : 10 ≤ P.A) (hC : 10 ≤ P.C') (hargs : P.Args)
    (hreg : P.RowColumnRegime) (F : Type) [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (hι : P.IsAddress ι)
    (x : Finset ℕ) (hx : x ⊆ range P.n) (hxd : x.card ≤ P.d) :
    ∑ a ∈ range P.B, ∑ k ∈ range P.w, hN P.d (P.q (a + 1) * P.p k) ≤
      (P.d : ℝ) * (lg (Real.exp 1) + lg (2 * Real.exp 1) + 2) := by
  have hdpos : (0 : ℝ) < (P.d : ℝ) := by
    exact_mod_cast (by have := hargs.1; omega : 0 < P.d)
  have hdne : ((P.d : ℝ)) ≠ 0 := ne_of_gt hdpos
  have hstep1 : ∑ a ∈ range P.B, ∑ k ∈ range P.w, hN P.d (P.q (a + 1) * P.p k) ≤
      ∑ a ∈ range P.B, ∑ k ∈ range P.w, (P.q (a + 1) * (P.p k * lg (Real.exp 1))
        + (P.q (a + 1) * lg ((P.d : ℝ) / P.q (a + 1))) * P.p k
        + P.q (a + 1) * (P.p k * lg (1 / P.p k))) := by
    refine Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun k hk => ?_
    have h1 := hN_mul_le (N := P.d) hdne (q_nonneg P (a + 1))
      (p_pos P hargs (Finset.mem_range.mp hk))
    have h2 : P.q (a + 1) * P.p k * (lg (Real.exp 1) + lg ((P.d : ℝ) / P.q (a + 1)) +
        lg (1 / P.p k)) = P.q (a + 1) * (P.p k * lg (Real.exp 1)) +
        (P.q (a + 1) * lg ((P.d : ℝ) / P.q (a + 1))) * P.p k +
        P.q (a + 1) * (P.p k * lg (1 / P.p k)) := by ring
    linarith
  have hsplit : (∑ a ∈ range P.B, ∑ k ∈ range P.w, (P.q (a + 1) * (P.p k * lg (Real.exp 1))
        + (P.q (a + 1) * lg ((P.d : ℝ) / P.q (a + 1))) * P.p k
        + P.q (a + 1) * (P.p k * lg (1 / P.p k))))
      = (∑ a ∈ range P.B, ∑ k ∈ range P.w, P.q (a + 1) * (P.p k * lg (Real.exp 1)))
        + (∑ a ∈ range P.B, ∑ k ∈ range P.w,
            (P.q (a + 1) * lg ((P.d : ℝ) / P.q (a + 1))) * P.p k)
        + (∑ a ∈ range P.B, ∑ k ∈ range P.w, P.q (a + 1) * (P.p k * lg (1 / P.p k))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    try ring
  have hA1 : (∑ a ∈ range P.B, ∑ k ∈ range P.w, P.q (a + 1) * (P.p k * lg (Real.exp 1)))
      = (∑ a ∈ range P.B, P.q (a + 1)) * (∑ k ∈ range P.w, P.p k * lg (Real.exp 1)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
  have hA2 : (∑ a ∈ range P.B, ∑ k ∈ range P.w,
        (P.q (a + 1) * lg ((P.d : ℝ) / P.q (a + 1))) * P.p k)
      = (∑ a ∈ range P.B, P.q (a + 1) * lg ((P.d : ℝ) / P.q (a + 1))) *
          (∑ k ∈ range P.w, P.p k) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
  have hA3 : (∑ a ∈ range P.B, ∑ k ∈ range P.w, P.q (a + 1) * (P.p k * lg (1 / P.p k)))
      = (∑ a ∈ range P.B, P.q (a + 1)) * (∑ k ∈ range P.w, P.p k * lg (1 / P.p k)) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
  have hsp : ∑ k ∈ range P.w, P.p k = 1 := sum_p_eq_one P hargs F b ι hι x hx hxd
  have hsq : ∑ a ∈ range P.B, P.q (a + 1) ≤ (P.d : ℝ) :=
    sum_q_le_B P hA hC hargs hreg F b ι hι x hx hxd
  have hse : ∑ a ∈ range P.B, P.q (a + 1) * lg ((P.d : ℝ) / P.q (a + 1)) ≤
      (P.d : ℝ) * lg (2 * Real.exp 1) :=
    sum_q_entropy_le_B P hA hC hargs hreg F b ι hι x hx hxd
  have hpe : ∑ k ∈ range P.w, P.p k * lg (1 / P.p k) ≤ 2 :=
    sum_p_entropy_le P hargs F b ι hι x hx hxd
  have hpe0 : (0 : ℝ) ≤ ∑ k ∈ range P.w, P.p k * lg (1 / P.p k) := by
    refine Finset.sum_nonneg fun k hk => ?_
    have hk' : k < P.w := Finset.mem_range.mp hk
    exact entropy_term_nonneg (p_pos P hargs hk').le (p_le_one P hargs hk')
  have hlg1 : (0 : ℝ) ≤ lg (Real.exp 1) := by linarith [one_le_lg_exp]
  have hb1 : (∑ a ∈ range P.B, P.q (a + 1)) * (∑ k ∈ range P.w, P.p k * lg (Real.exp 1))
      ≤ (P.d : ℝ) * lg (Real.exp 1) := by
    have hsp' : ∑ k ∈ range P.w, P.p k * lg (Real.exp 1) = lg (Real.exp 1) := by
      rw [← Finset.sum_mul, hsp, one_mul]
    rw [hsp']
    calc (∑ a ∈ range P.B, P.q (a + 1)) * lg (Real.exp 1) ≤ (P.d : ℝ) * lg (Real.exp 1) :=
          mul_le_mul_of_nonneg_right hsq hlg1
      _ = (P.d : ℝ) * lg (Real.exp 1) := by ring
  have hb2 : (∑ a ∈ range P.B, P.q (a + 1) * lg ((P.d : ℝ) / P.q (a + 1))) *
        (∑ k ∈ range P.w, P.p k) ≤ (P.d : ℝ) * lg (2 * Real.exp 1) := by
    rw [hsp, mul_one]
    exact hse
  have hb3 : (∑ a ∈ range P.B, P.q (a + 1)) * (∑ k ∈ range P.w, P.p k * lg (1 / P.p k))
      ≤ (P.d : ℝ) * 2 := by
    have h2 := mul_le_mul hsq hpe hpe0 hdpos.le
    linarith
  refine le_trans hstep1 ?_
  rw [hsplit]
  linarith [hA1, hA2, hA3, hb1, hb2, hb3]

/-- `ℓ h_d(b) ≤ 180 A C' d / log n`: the paper's `ℓ b log(ed/b) = O(C' A η d log³n)` step. -/
lemma budget_hN_margin (P : TopParams) (hA : 10 ≤ P.A) (hC : 10 ≤ P.C') (hargs : P.Args)
    (hreg : P.RowColumnRegime) :
    (P.ell : ℝ) * hN P.d (P.eta * ((P.d : ℝ) + 1) + 1) ≤
      360 * (P.A : ℝ) * ((P.C' : ℝ) * (P.d : ℝ) / P.lgn) := by
  have hL0 := lgn_pos P hA hC hargs hreg
  have hL1 := one_le_lgn P hA hC hargs hreg
  have hA10 : (10 : ℝ) ≤ (P.A : ℝ) := by exact_mod_cast hA
  have hdpos : (0 : ℝ) < (P.d : ℝ) := by
    exact_mod_cast (by have := hargs.1; omega : 0 < P.d)
  have hm_ge : P.eta * (P.d : ℝ) ≤ P.eta * ((P.d : ℝ) + 1) + 1 := by
    have h1 := eta_pos P hA hC hargs hreg
    have h2 : (0 : ℝ) ≤ (P.d : ℝ) := by positivity
    nlinarith
  have hm_gt : 0 < P.eta * ((P.d : ℝ) + 1) + 1 := by
    linarith [one_le_b P hA hC hargs hreg]
  have hmd : P.eta * ((P.d : ℝ) + 1) + 1 ≤ (P.d : ℝ) := by
    have h := b_le_tenth P hA hC hargs hreg
    linarith
  have hm3 : P.eta * ((P.d : ℝ) + 1) + 1 ≤ 3 * P.eta * (P.d : ℝ) :=
    b_le_three_eta P hA hC hargs hreg
  have hratio : (P.d : ℝ) / (P.eta * ((P.d : ℝ) + 1) + 1) ≤ 1 / P.eta := by
    rw [div_le_iff₀ hm_gt]
    have hηne : P.eta ≠ 0 := ne_of_gt (eta_pos P hA hC hargs hreg)
    have h2 : (1 / P.eta) * (P.eta * (P.d : ℝ)) = (P.d : ℝ) := by
      rw [← mul_assoc, one_div, inv_mul_cancel₀ hηne, one_mul]
    nlinarith [hm_ge, h2]
  have harg : Real.exp 1 * (P.d : ℝ) / (P.eta * ((P.d : ℝ) + 1) + 1) ≤
      Real.exp 1 * (1 / P.eta) := by
    have heq : Real.exp 1 * (P.d : ℝ) / (P.eta * ((P.d : ℝ) + 1) + 1)
        = Real.exp 1 * ((P.d : ℝ) / (P.eta * ((P.d : ℝ) + 1) + 1)) := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hratio (le_of_lt (Real.exp_pos 1))
  have hargpos : (0 : ℝ) < Real.exp 1 * (P.d : ℝ) / (P.eta * ((P.d : ℝ) + 1) + 1) := by
    have h1 : (0 : ℝ) < Real.exp 1 * (P.d : ℝ) := by positivity
    exact div_pos h1 hm_gt
  have hval : lg (Real.exp 1 * (1 / P.eta)) = lg (Real.exp 1) + (P.A : ℝ) * lg P.lgn := by
    have heta : (1 : ℝ) / P.eta = P.lgn ^ P.A := by
      rw [TopParams.eta]
      field_simp
    rw [heta, lg_mul (Real.exp_ne_zero 1) (ne_of_gt (pow_pos hL0 P.A)), lg_pow']
  have hmono := lg_mono hargpos harg
  rw [hval] at hmono
  have hlog : lg (Real.exp 1 * (P.d : ℝ) / (P.eta * ((P.d : ℝ) + 1) + 1)) ≤
      3 * (P.A : ℝ) * P.lgn := by
    have h1 : lg (Real.exp 1) ≤ 2 := lg_exp_one_le_two
    have h2 : (P.A : ℝ) * lg P.lgn ≤ (P.A : ℝ) * (2 * P.lgn) :=
      mul_le_mul_of_nonneg_left (lg_le_two_mul hL1) (by positivity)
    have h3 : (2 : ℝ) ≤ (P.A : ℝ) * P.lgn := by nlinarith [hA10, hL1]
    linarith [hmono, h1, h2, h3]
  have hNm : hN P.d (P.eta * ((P.d : ℝ) + 1) + 1) ≤
      (P.eta * ((P.d : ℝ) + 1) + 1) * (3 * (P.A : ℝ) * P.lgn) := by
    rw [hN, if_neg (ne_of_gt hm_gt)]
    exact mul_le_mul_of_nonneg_left hlog hm_gt.le
  have hell : (P.ell : ℝ) ≤ 40 * (P.C' : ℝ) * P.lgn ^ 2 := ell_le P hA hC hargs hreg
  have hN0 : (0 : ℝ) ≤ hN P.d (P.eta * ((P.d : ℝ) + 1) + 1) :=
    hN_nonneg hm_gt.le hmd
  have hcomb : (P.ell : ℝ) * hN P.d (P.eta * ((P.d : ℝ) + 1) + 1) ≤
      (40 * (P.C' : ℝ) * P.lgn ^ 2) *
        ((3 * P.eta * (P.d : ℝ)) * (3 * (P.A : ℝ) * P.lgn)) := by
    have h2 : (0 : ℝ) ≤ 40 * (P.C' : ℝ) * P.lgn ^ 2 := by positivity
    have h3 : hN P.d (P.eta * ((P.d : ℝ) + 1) + 1) ≤
        (3 * P.eta * (P.d : ℝ)) * (3 * (P.A : ℝ) * P.lgn) := by
      refine le_trans hNm ?_
      exact mul_le_mul_of_nonneg_right hm3 (by positivity)
    exact mul_le_mul hell h3 hN0 h2
  have heta2 : P.eta * P.lgn ^ 3 ≤ 1 / P.lgn :=
    eta_mul_lgn_pow_le P hA hC hargs hreg (k := 3) (by omega)
  have hfin : (40 * (P.C' : ℝ) * P.lgn ^ 2) *
        ((3 * P.eta * (P.d : ℝ)) * (3 * (P.A : ℝ) * P.lgn))
      ≤ 360 * (P.A : ℝ) * ((P.C' : ℝ) * (P.d : ℝ) / P.lgn) := by
    have h1 : (40 * (P.C' : ℝ) * P.lgn ^ 2) *
        ((3 * P.eta * (P.d : ℝ)) * (3 * (P.A : ℝ) * P.lgn))
        = 360 * (P.A : ℝ) * (P.C' : ℝ) * (P.d : ℝ) * (P.eta * P.lgn ^ 3) := by ring
    rw [h1]
    have h2 : 360 * (P.A : ℝ) * (P.C' : ℝ) * (P.d : ℝ) * (P.eta * P.lgn ^ 3)
        ≤ 360 * (P.A : ℝ) * (P.C' : ℝ) * (P.d : ℝ) * (1 / P.lgn) :=
      mul_le_mul_of_nonneg_left heta2 (by positivity)
    have h3 : 360 * (P.A : ℝ) * (P.C' : ℝ) * (P.d : ℝ) * (1 / P.lgn)
        = 360 * (P.A : ℝ) * ((P.C' : ℝ) * (P.d : ℝ) / P.lgn) := by ring
    linarith [h2, h3]
  linarith [hcomb, hfin]

/-- **Lemma 6.3, part 3.** `∑_{a,k} h_d(Y_{a,k}) ≤ K d + K C' d / log n` with `K = 300(A+1)`. -/
lemma budget_Y (P : TopParams) (hA : 10 ≤ P.A) (hC : 10 ≤ P.C') (hargs : P.Args)
    (hreg : P.RowColumnRegime) (F : Type) [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (hι : P.IsAddress ι)
    (x : Finset ℕ) (hx : x ⊆ range P.n) (hxd : x.card ≤ P.d) :
    (∑ a ∈ range P.B, ∑ k ∈ range P.w, hN P.d (P.capY a k)) ≤
      500 * ((P.A : ℝ) + 1) * (P.d : ℝ) +
        500 * ((P.A : ℝ) + 1) * ((P.C' : ℝ) * (P.d : ℝ) / P.lgn) := by
  have hdpos : (0 : ℝ) < (P.d : ℝ) := by
    exact_mod_cast (by have := hargs.1; omega : 0 < P.d)
  set m0 : ℝ := P.eta * ((P.d : ℝ) + 1) + 1 with hm0
  -- the paper's pointwise step, with the overflow written as `if … then 0 else log e · d`
  have hstep1 : ∑ a ∈ range P.B, ∑ k ∈ range P.w, hN P.d (P.capY a k) ≤
      ∑ a ∈ range P.B, ∑ k ∈ range P.w, (hN P.d (P.q (a + 1) * P.p k) + hN P.d m0 +
        (if P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ) then 0 else lg (Real.exp 1) * (P.d : ℝ))) := by
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun k hk => ?_
    exact hN_capY_le P hA hC hargs hreg a k (Finset.mem_range.mp hk) m0 hm0
  have hsplit : (∑ a ∈ range P.B, ∑ k ∈ range P.w, (hN P.d (P.q (a + 1) * P.p k) +
        hN P.d m0 +
        (if P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ) then 0 else lg (Real.exp 1) * (P.d : ℝ))))
      = (∑ a ∈ range P.B, ∑ k ∈ range P.w, hN P.d (P.q (a + 1) * P.p k))
        + (∑ a ∈ range P.B, ∑ _k ∈ range P.w, hN P.d m0)
        + (∑ a ∈ range P.B, ∑ k ∈ range P.w,
            (if P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ) then 0
              else lg (Real.exp 1) * (P.d : ℝ))) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    try ring
  have hell_eq : (∑ a ∈ range P.B, ∑ _k ∈ range P.w, hN P.d m0)
      = (P.ell : ℝ) * hN P.d m0 := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range, Finset.sum_const, nsmul_eq_mul,
      Finset.card_range, TopParams.ell]
    push_cast
    ring
  -- at most two columns overflow, each contributing `log e · d`
  have hover : (∑ a ∈ range P.B, ∑ k ∈ range P.w,
      (if P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ) then 0 else lg (Real.exp 1) * (P.d : ℝ)))
      ≤ 2 * (lg (Real.exp 1) * (P.d : ℝ)) := by
    have hfac : ∀ a, (∑ k ∈ range P.w,
          (if P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ) then 0 else lg (Real.exp 1) * (P.d : ℝ)))
        = (∑ k ∈ range P.w,
            (if P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ) then (0 : ℝ) else 1)) *
            (lg (Real.exp 1) * (P.d : ℝ)) := by
      intro a
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by
        by_cases h : P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ) <;> simp [h]
    have h1 : (∑ a ∈ range P.B, ∑ k ∈ range P.w,
          (if P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ) then 0 else lg (Real.exp 1) * (P.d : ℝ)))
        = (∑ a ∈ range P.B, ∑ k ∈ range P.w,
            (if P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ) then (0 : ℝ) else 1)) *
            (lg (Real.exp 1) * (P.d : ℝ)) := by
      simp only [hfac]
      rw [Finset.sum_mul]
    have hK2 : (∑ a ∈ range P.B, ∑ k ∈ range P.w,
        (if P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ) then (0 : ℝ) else 1)) ≤ 2 := by
      have hfac1 : ∀ a, (∑ k ∈ range P.w,
            (if P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ) then (0 : ℝ) else 1)) *
            ((P.d : ℝ) - m0)
          = ∑ k ∈ range P.w,
              (if P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ) then (0 : ℝ) else ((P.d : ℝ) - m0)) := by
        intro a
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by
          by_cases h : P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ) <;> simp [h]
      have h1 : (∑ a ∈ range P.B, ∑ k ∈ range P.w,
            (if P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ) then (0 : ℝ) else 1)) * ((P.d : ℝ) - m0)
          = ∑ a ∈ range P.B, ∑ k ∈ range P.w,
              (if P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ) then (0 : ℝ) else ((P.d : ℝ) - m0)) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => hfac1 a
      have hpoint : ∀ a ∈ range P.B, ∀ k ∈ range P.w,
          (if P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ) then (0 : ℝ) else ((P.d : ℝ) - m0))
            ≤ (if P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ) then (0 : ℝ)
                else P.q (a + 1) * P.p k) := by
        intro a _ k _
        by_cases h : P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ)
        · rw [if_pos h, if_pos h]
        · rw [if_neg h, if_neg h]
          have hlt : (P.d : ℝ) < P.q (a + 1) * P.p k + m0 := lt_of_not_ge h
          linarith
      have h2 : (∑ a ∈ range P.B, ∑ k ∈ range P.w,
            (if P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ) then (0 : ℝ) else ((P.d : ℝ) - m0)))
          ≤ ∑ a ∈ range P.B, ∑ k ∈ range P.w,
              (if P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ) then (0 : ℝ)
                else P.q (a + 1) * P.p k) :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun k hk => hpoint a ha k hk
      have h3 : (∑ a ∈ range P.B, ∑ k ∈ range P.w,
            (if P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ) then (0 : ℝ)
              else P.q (a + 1) * P.p k))
          ≤ ∑ a ∈ range P.B, ∑ k ∈ range P.w, P.q (a + 1) * P.p k := by
        refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun k hk => ?_
        by_cases h : P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ)
        · rw [if_pos h]
          exact mul_nonneg (q_nonneg P (a + 1)) (p_pos P hargs (Finset.mem_range.mp hk)).le
        · rw [if_neg h]
      have h4 : (∑ a ∈ range P.B, ∑ k ∈ range P.w,
            (if P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ) then (0 : ℝ) else 1)) * ((P.d : ℝ) - m0)
          ≤ (P.d : ℝ) := by
        rw [h1]
        exact le_trans h2 (le_trans h3 (sum_qp_le P hA hC hargs hreg F b ι hι x hx hxd))
      have hK0 : (0 : ℝ) ≤ ∑ a ∈ range P.B, ∑ k ∈ range P.w,
          (if P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ) then (0 : ℝ) else 1) :=
        Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun k _ => by
          by_cases h : P.q (a + 1) * P.p k + m0 ≤ (P.d : ℝ) <;> simp [h]
      have hdm : (P.d : ℝ) / 2 ≤ (P.d : ℝ) - m0 := by
        have hb : m0 ≤ (P.d : ℝ) / 10 := by
          rw [hm0]
          exact b_le_tenth P hA hC hargs hreg
        linarith
      nlinarith [h4, hdm, hdpos, hK0]
    rw [h1]
    have hc : (0 : ℝ) ≤ lg (Real.exp 1) * (P.d : ℝ) := by
      have h := one_le_lg_exp
      have h2 : (0 : ℝ) ≤ (P.d : ℝ) := Nat.cast_nonneg _
      nlinarith
    nlinarith [hK2, hc]
  have hideal := budget_hN_ideal P hA hC hargs hreg F b ι hι x hx hxd
  have hmargin : (P.ell : ℝ) * hN P.d m0 ≤
      360 * (P.A : ℝ) * ((P.C' : ℝ) * (P.d : ℝ) / P.lgn) := by
    rw [hm0]
    exact budget_hN_margin P hA hC hargs hreg
  have hloge1 : lg (Real.exp 1) ≤ 2 := lg_exp_one_le_two
  have hloge2 : lg (2 * Real.exp 1) ≤ 3 := by
    rw [lg_mul (by norm_num : (2 : ℝ) ≠ 0) (Real.exp_ne_zero 1), lg_two]
    linarith [lg_exp_one_le_two]
  have hAp : (10 : ℝ) ≤ (P.A : ℝ) := by exact_mod_cast hA
  have hXp : (0 : ℝ) ≤ (P.C' : ℝ) * (P.d : ℝ) / P.lgn :=
    div_nonneg (by positivity) (le_of_lt (lgn_pos P hA hC hargs hreg))
  refine le_trans hstep1 ?_
  rw [hsplit]
  nlinarith [hideal, hmargin, hell_eq, hover, hloge1, hloge2, hAp, hdpos, hXp]

/-! ### §2.6 The mixed budget -/

/-- **Lemma 6.3, part 4.** `∑_{a,k} (X_{a,k} + α h_d(Y_{a,k})) ≤ dw + Kd + K C'd/log n`: the
paper's last display, obtained by adding the `X`-budget to `α` times the `h_N(Y)`-budget. -/
lemma budget_mixed (P : TopParams) (hA : 10 ≤ P.A) (hC : 10 ≤ P.C') (hargs : P.Args)
    (hreg : P.RowColumnRegime) (F : Type) [Field F] [Fintype F] [Algebra (ZMod 2) F]
    (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F) (hι : P.IsAddress ι)
    (x : Finset ℕ) (hx : x ⊆ range P.n) (hxd : x.card ≤ P.d) (α : ℝ) (hα : 0 ≤ α) :
    (∑ a ∈ range P.B, ∑ k ∈ range P.w, ((P.capX a : ℝ) + α * hN P.d (P.capY a k))) ≤
      (P.d : ℝ) * P.w + 1000 * ((P.A : ℝ) + 2) * (α + 2) * (P.d : ℝ) +
        1000 * ((P.A : ℝ) + 2) * (α + 2) * ((P.C' : ℝ) * (P.d : ℝ) / P.lgn) := by
  have hsplit : (∑ a ∈ range P.B, ∑ k ∈ range P.w, ((P.capX a : ℝ) + α * hN P.d (P.capY a k)))
      = (∑ a ∈ range P.B, ∑ k ∈ range P.w, (P.capX a : ℝ))
        + α * (∑ a ∈ range P.B, ∑ k ∈ range P.w, hN P.d (P.capY a k)) := by
    have h1 : ∀ a ∈ range P.B, (∑ k ∈ range P.w, ((P.capX a : ℝ) + α * hN P.d (P.capY a k)))
        = (∑ k ∈ range P.w, (P.capX a : ℝ)) + α * (∑ k ∈ range P.w, hN P.d (P.capY a k)) := by
      intro a _
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsplit]
  have hX := budget_X P hA hC hargs hreg F b ι hι x hx hxd
  have hY := budget_Y P hA hC hargs hreg F b ι hι x hx hxd
  have hdpos : (0 : ℝ) < (P.d : ℝ) := by
    exact_mod_cast (by have := hargs.1; omega : 0 < P.d)
  have hXp : (0 : ℝ) ≤ (P.C' : ℝ) * (P.d : ℝ) / P.lgn :=
    div_nonneg (by positivity) (le_of_lt (lgn_pos P hA hC hargs hreg))
  have hw0 : (0 : ℝ) ≤ (P.d : ℝ) * P.w := by positivity
  have hAp : (10 : ℝ) ≤ (P.A : ℝ) := by exact_mod_cast hA
  have hK1 : (250 : ℝ) ≤ 1000 * ((P.A : ℝ) + 2) * (α + 2) := by nlinarith
  have hK2 : 500 * ((P.A : ℝ) + 1) ≤ 1000 * ((P.A : ℝ) + 2) * (α + 2) := by nlinarith
  have hK3 : α * (500 * ((P.A : ℝ) + 1)) ≤ 1000 * ((P.A : ℝ) + 2) * (α + 2) := by nlinarith
  have hY' := mul_le_mul_of_nonneg_left hY hα
  nlinarith [hX, hY', hK1, hK2, hK3, hXp, hdpos, hw0]

/-! ### §2.7 Lemma 6.3 and the submission wrapper -/

/-- **Lemma 6.3 (Top-layer child capacities)**, for a fixed parameter tuple `P`. This is the
four-part statement of `lem:top-initial-budget` with the hidden constant `K = 1000(A+2)(α+2)`. -/
lemma lemma_6_3_core (P : TopParams) (hA : 10 ≤ P.A) (hC : 10 ≤ P.C') (α : ℝ) (hα : 0 ≤ α)
    (hargs : P.Args) (hreg : P.RowColumnRegime) :
    ∀ (F : Type) [Field F] [Fintype F] [Algebra (ZMod 2) F]
      (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F), P.IsAddress ι →
    (∀ x : Finset ℕ, x ⊆ range P.n → x.card ≤ P.d →
      let sch := P.scheme b ι
      ∀ s : Fin P.ell,
        prU (fun lr : sch.LocalSeed => P.capX (P.wordIdx s).val < sch.U lr x ∅ s) ≤
          ((2 : ℝ) ^ P.lamStar)⁻¹ ∧
        prU (fun lr : sch.LocalSeed =>
            P.capY (P.wordIdx s).val (P.bitIdx s).val < sch.V lr x ∅ s) ≤
          ((2 : ℝ) ^ P.lamStar)⁻¹) ∧
    (∑ a ∈ range P.B, ∑ _k ∈ range P.w, (P.capX a : ℝ) ≤
      (P.d : ℝ) * P.w + 1000 * ((P.A : ℝ) + 2) * (α + 2) * ((P.C' : ℝ) * P.d / P.lgn)) ∧
    (∑ a ∈ range P.B, ∑ k ∈ range P.w, hN P.d (P.capY a k) ≤
      1000 * ((P.A : ℝ) + 2) * (α + 2) * (P.d : ℝ) +
        1000 * ((P.A : ℝ) + 2) * (α + 2) * ((P.C' : ℝ) * P.d / P.lgn)) ∧
    (∑ a ∈ range P.B, ∑ k ∈ range P.w, ((P.capX a : ℝ) + α * hN P.d (P.capY a k)) ≤
      (P.d : ℝ) * P.w + 1000 * ((P.A : ℝ) + 2) * (α + 2) * (P.d : ℝ) +
        1000 * ((P.A : ℝ) + 2) * (α + 2) * ((P.C' : ℝ) * P.d / P.lgn)) := by
  intro F _ _ _ b ι hι
  have hXp : (0 : ℝ) ≤ (P.C' : ℝ) * (P.d : ℝ) / P.lgn :=
    div_nonneg (by positivity) (le_of_lt (lgn_pos P hA hC hargs hreg))
  have hdpos : (0 : ℝ) < (P.d : ℝ) := by
    exact_mod_cast (by have := hargs.1; omega : 0 < P.d)
  have hAp : (10 : ℝ) ≤ (P.A : ℝ) := by exact_mod_cast hA
  have hK1 : (250 : ℝ) ≤ 1000 * ((P.A : ℝ) + 2) * (α + 2) := by nlinarith
  have hK2 : 500 * ((P.A : ℝ) + 1) ≤ 1000 * ((P.A : ℝ) + 2) * (α + 2) := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hxd
    exact fun s => ⟨tail_X P hA hC hargs hreg F b ι hι x hx hxd s,
      tail_Y P hA hC hargs hreg F b ι hι x hx hxd s⟩
  · refine le_trans (budget_X P hA hC hargs hreg F b ι hι ∅ (Finset.empty_subset _)
      (by simp)) ?_
    nlinarith [hK1, hXp]
  · refine le_trans (budget_Y P hA hC hargs hreg F b ι hι ∅ (Finset.empty_subset _)
      (by simp)) ?_
    nlinarith [hK2, hXp, hdpos]
  · exact budget_mixed P hA hC hargs hreg F b ι hι ∅ (Finset.empty_subset _) (by simp) α hα

/-- **Lemma 6.3 (Top-layer child capacities)**, PDF p.30 (printed p.29). `A` and `α` are the fixed
constants of §5; the hidden constant `K` precedes `C'`, which is sufficiently large. -/
theorem lemma_6_3 (A : ℕ) (hA : 10 ≤ A) (α : ℝ) (hα : 0 ≤ α) :
    ∃ K : ℝ, 0 < K ∧ ∃ C₀ : ℕ, ∀ C' ≥ C₀, ∀ (n d lam : ℕ),
      let P : TopParams := ⟨A, C', n, d, lam⟩
      P.Args → P.RowColumnRegime →
      ∀ (F : Type) [Field F] [Fintype F] [Algebra (ZMod 2) F]
        (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F), P.IsAddress ι →
      (∀ x : Finset ℕ, x ⊆ range P.n → x.card ≤ P.d →
        let sch := P.scheme b ι
        ∀ s : Fin P.ell,
          prU (fun lr : sch.LocalSeed => P.capX (P.wordIdx s).val < sch.U lr x ∅ s) ≤
            ((2 : ℝ) ^ P.lamStar)⁻¹ ∧
          prU (fun lr : sch.LocalSeed =>
              P.capY (P.wordIdx s).val (P.bitIdx s).val < sch.V lr x ∅ s) ≤
            ((2 : ℝ) ^ P.lamStar)⁻¹) ∧
      (∑ a ∈ range P.B, ∑ _k ∈ range P.w, (P.capX a : ℝ) ≤
        (d : ℝ) * P.w + K * ((C' : ℝ) * d / P.lgn)) ∧
      (∑ a ∈ range P.B, ∑ k ∈ range P.w, hN d (P.capY a k) ≤
        K * d + K * ((C' : ℝ) * d / P.lgn)) ∧
      (∑ a ∈ range P.B, ∑ k ∈ range P.w, ((P.capX a : ℝ) + α * hN d (P.capY a k)) ≤
        (d : ℝ) * P.w + K * d + K * ((C' : ℝ) * d / P.lgn)) := by
  refine ⟨1000 * ((A : ℝ) + 2) * (α + 2), ?_, 10, ?_⟩
  · have h1 : (0 : ℝ) < (A : ℝ) + 2 := by positivity
    have h2 : (0 : ℝ) < α + 2 := by linarith
    positivity
  · intro C' hC' n d lam
    exact lemma_6_3_core ⟨A, C', n, d, lam⟩ hA hC' α hα

end LinearSetReconciliation327.Main

open LinearSetReconciliation327.Main in
/-- Lemma 6.3 (Top-layer child capacities) — submission wrapper matching the target statement. -/
theorem solution (A : ℕ) (hA : 10 ≤ A) (α : ℝ) (hα : 0 ≤ α) :
    ∃ K : ℝ, 0 < K ∧ ∃ C₀ : ℕ, ∀ C' ≥ C₀, ∀ (n d lam : ℕ),
      let P : TopParams := ⟨A, C', n, d, lam⟩
      P.Args → P.RowColumnRegime →
      ∀ (F : Type) [Field F] [Fintype F] [Algebra (ZMod 2) F]
        (b : Module.Basis (Fin P.w) (ZMod 2) F) (ι : ℕ → F), P.IsAddress ι →
      (∀ x : Finset ℕ, x ⊆ range P.n → x.card ≤ P.d →
        let sch := P.scheme b ι
        ∀ s : Fin P.ell,
          prU (fun lr : sch.LocalSeed => P.capX (P.wordIdx s).val < sch.U lr x ∅ s) ≤
            ((2 : ℝ) ^ P.lamStar)⁻¹ ∧
          prU (fun lr : sch.LocalSeed =>
              P.capY (P.wordIdx s).val (P.bitIdx s).val < sch.V lr x ∅ s) ≤
            ((2 : ℝ) ^ P.lamStar)⁻¹) ∧
      (∑ a ∈ range P.B, ∑ _k ∈ range P.w, (P.capX a : ℝ) ≤
        (d : ℝ) * P.w + K * ((C' : ℝ) * d / P.lgn)) ∧
      (∑ a ∈ range P.B, ∑ k ∈ range P.w, hN d (P.capY a k) ≤
        K * d + K * ((C' : ℝ) * d / P.lgn)) ∧
      (∑ a ∈ range P.B, ∑ k ∈ range P.w, ((P.capX a : ℝ) + α * hN d (P.capY a k)) ≤
        (d : ℝ) * P.w + K * d + K * ((C' : ℝ) * d / P.lgn)) :=
  lemma_6_3 A hA α hα

