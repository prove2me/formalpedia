-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds_choiceScalar
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T07:55:13.208289+00:00
-- url     : https://prove2.me/submissions/6e06255b-9f5a-4175-b825-08c507b023e0

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionWeights
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_logTail_product_coefficient_control
import Theorems.Thm_OAI_PiExponent_MatrixArithmetic_approximation_center_exp_control
import Mathlib.Data.Nat.Choose.Bounds

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

private theorem binomial_product_bound {m : ℕ} (a beta b : Fin m → ℕ) :
    (∏ i, (a i).choose (beta i) * (a i - beta i).choose (b i)) ≤
      4 ^ (∑ i, a i) := by
  calc
    _ ≤ ∏ i, 4 ^ a i := by
      apply Finset.prod_le_prod (fun i _ => Nat.zero_le _)
      intro i _
      calc
        _ ≤ 2 ^ a i * 2 ^ (a i - beta i) :=
          Nat.mul_le_mul (Nat.choose_le_two_pow _ _) (Nat.choose_le_two_pow _ _)
        _ ≤ 2 ^ a i * 2 ^ a i :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
        _ = 4 ^ a i := by rw [← mul_pow]; norm_num
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

set_option maxHeartbeats 4000000 in
private theorem raw_scalar_bound {m : ℕ}
    (eps : Fin m → ℂ) (T a beta : Fin m → ℕ)
    (b : ∀ i, Fin (a i - beta i + 1)) (k : ℕ) (w : Fin m → ℝ)
    (C nu H ws v F : ℝ) (hC : 0 ≤ C) (hnu : 0 ≤ nu)
    (hws : 0 < ws) (hv : 0 < v) (hF : 0 < F)
    (hw : ∀ i, ws ≤ w i) (ha : ∑ i, w i * (a i : ℝ) ≤ H)
    (hk : (k : ℝ) ≤ H / v) (hT : ∀ i, 1 ≤ T i)
    (hTw : ∀ i, F * w i ≤ v * (T i : ℝ))
    (heps : ∀ i, ‖eps i‖ ≤ Real.exp (C - nu * w i)) :
    ‖((∏ i, (a i).choose (beta i) * (a i - beta i).choose (b i) : ℕ) : ℂ) *
      (∏ i, eps i ^ (a i - beta i - b i)) *
      PowerSeries.coeff k
        (∏ i, ((PowerSeries.trunc (T i) (PowerSeries.log ℂ) : PowerSeries ℂ) -
          PowerSeries.log ℂ) ^ (b i : ℕ))‖ ≤
    Real.exp (-nu * ((∑ i, w i * (a i : ℝ)) - (∑ i, w i * (beta i : ℝ))) +
      H * (nu / F + Real.log 2 / v + (Real.log 4 + C) / ws)) := by
  classical
  let z : ℂ := PowerSeries.coeff k
    (∏ i, ((PowerSeries.trunc (T i) (PowerSeries.log ℂ) : PowerSeries ℂ) -
      PowerSeries.log ℂ) ^ (b i : ℕ))
  have ht := logTail_product_coefficient_control T (fun i => (b i : ℕ)) k hT
  change ‖((∏ i, (a i).choose (beta i) * (a i - beta i).choose (b i) : ℕ) : ℂ) *
    (∏ i, eps i ^ (a i - beta i - b i)) * z‖ ≤ _
  by_cases hz : z = 0
  · simp [hz, Real.exp_nonneg]
  have hs : ∑ i, T i * (b i : ℕ) ≤ k := ht.2 hz
  have hbudget : (∑ i, w i * (b i : ℝ)) ≤ H / F := by
    apply (le_div_iff₀ hF).2
    calc
      (∑ i, w i * (b i : ℝ)) * F = ∑ i, (b i : ℝ) * (F * w i) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ i, (b i : ℝ) * (v * (T i : ℝ)) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hTw i) (by positivity))
      _ = v * ((∑ i, T i * (b i : ℕ) : ℕ) : ℝ) := by
        simp only [Nat.cast_sum, Nat.cast_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ v * (k : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hs) hv.le
      _ ≤ H := by nlinarith [(le_div_iff₀ hv).mp hk]
  have hsize : ((∑ i, a i : ℕ) : ℝ) ≤ H / ws := by
    apply (le_div_iff₀ hws).2
    calc
      ((∑ i, a i : ℕ) : ℝ) * ws = ∑ i, ws * (a i : ℝ) := by
        simp only [Nat.cast_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ ∑ i, w i * (a i : ℝ) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hw i) (Nat.cast_nonneg _))
      _ ≤ H := ha
  have hcount : ((∑ i, (a i - beta i - b i) : ℕ) : ℝ) ≤ ((∑ i, a i : ℕ) : ℝ) := by
    exact_mod_cast Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
      (Nat.sub_le (a i - beta i) (b i)).trans (Nat.sub_le (a i) (beta i)))
  have hid :
      (∑ i, ((a i - beta i - b i : ℕ) : ℝ) * (C - nu * w i)) =
      C * ((∑ i, (a i - beta i - b i) : ℕ) : ℝ) -
        nu * (∑ i, w i * ((a i - beta i : ℕ) : ℝ)) +
        nu * (∑ i, w i * (b i : ℝ)) := by
    simp only [Nat.cast_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_sub (Nat.le_of_lt_succ (b i).isLt)]
    ring
  have hdiff :
      (∑ i, w i * (a i : ℝ)) - (∑ i, w i * (beta i : ℝ)) ≤
        ∑ i, w i * ((a i - beta i : ℕ) : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [← mul_sub]
    apply mul_le_mul_of_nonneg_left _ (hws.le.trans (hw i))
    by_cases hi : beta i ≤ a i
    · rw [Nat.cast_sub hi]
    · have hi' : a i ≤ beta i := by omega
      rw [Nat.sub_eq_zero_of_le hi', Nat.cast_zero]
      exact sub_nonpos.mpr (by exact_mod_cast hi')
  have hep : (∏ i, ‖eps i‖ ^ (a i - beta i - b i)) ≤
      Real.exp (∑ i, ((a i - beta i - b i : ℕ) : ℝ) * (C - nu * w i)) := by
    rw [Real.exp_sum]
    apply Finset.prod_le_prod (fun i _ => by positivity)
    intro i _
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (heps i) _
  have hbin :
      ‖((∏ i, (a i).choose (beta i) * (a i - beta i).choose (b i) : ℕ) : ℂ)‖ ≤
        (4 : ℝ) ^ (∑ i, a i) := by
    rw [Complex.norm_natCast]
    exact_mod_cast binomial_product_bound a beta (fun i => (b i : ℕ))
  have hbasic :
      ‖((∏ i, (a i).choose (beta i) * (a i - beta i).choose (b i) : ℕ) : ℂ) *
        (∏ i, eps i ^ (a i - beta i - b i)) * z‖ ≤
      Real.exp (((∑ i, a i : ℕ) : ℝ) * Real.log 4 +
        (∑ i, ((a i - beta i - b i : ℕ) : ℝ) * (C - nu * w i)) +
        (k : ℝ) * Real.log 2) := by
    calc
      _ = ‖((∏ i, (a i).choose (beta i) * (a i - beta i).choose (b i) : ℕ) : ℂ)‖ *
          (∏ i, ‖eps i‖ ^ (a i - beta i - b i)) * ‖z‖ := by
        simp only [norm_mul, norm_prod, norm_pow]
      _ ≤ (4 : ℝ) ^ (∑ i, a i) *
          Real.exp (∑ i, ((a i - beta i - b i : ℕ) : ℝ) * (C - nu * w i)) * (2 : ℝ) ^ k :=
        mul_le_mul
          (mul_le_mul hbin hep (by positivity) (by positivity)) ht.1
          (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
          Real.exp_log (by norm_num : (0 : ℝ) < 4),
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  apply hbasic.trans
  apply Real.exp_le_exp.mpr
  rw [hid]
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  calc
    _ ≤ (Real.log 4 + C) * ((∑ i, a i : ℕ) : ℝ) -
        nu * (∑ i, w i * ((a i - beta i : ℕ) : ℝ)) + nu * (H / F) +
        (H / v) * Real.log 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hcount hC,
        mul_le_mul_of_nonneg_left hbudget hnu,
        mul_le_mul_of_nonneg_right hk hlog2]
    _ ≤ (Real.log 4 + C) * (H / ws) -
        nu * (∑ i, w i * ((a i - beta i : ℕ) : ℝ)) + nu * (H / F) +
        (H / v) * Real.log 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hsize (add_nonneg hlog4 hC)]
    _ = -nu * (∑ i, w i * ((a i - beta i : ℕ) : ℝ)) +
        H * (nu / F + Real.log 2 / v + (Real.log 4 + C) / ws) := by ring
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hdiff hnu]

private theorem mapped_simplex_weight_le {m : ℕ} (w : Fin m → ℝ) (H : ℝ)
    (a : Fin m →₀ ℕ)
    (ha : a ∈ (realWeightedSimplex w H).map
      Finsupp.equivFunOnFinite.symm.toEmbedding) :
    ∑ i, w i * (a i : ℝ) ≤ H := by
  obtain ⟨a', ha', heq⟩ := Finset.mem_map.mp ha
  have hs : ∑ i, w i * (a' i : ℝ) ≤ H := (Finset.mem_filter.mp ha').2
  rw [← heq]
  exact hs

private theorem strict_simplex_zero_bound {m : ℕ} (v theta : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (a : Fin (m + 1) → ℕ)
    (hv : 0 < v) (htheta : 0 < theta) (hw : ∀ i, 0 ≤ w i)
    (ha : a ∈ strictWeightedSimplex (InterpolationMatrix.rowWeights v theta w) H) :
    (a 0 : ℝ) ≤ H / v := by
  have hr : ∑ i : Fin (m + 1),
      InterpolationMatrix.rowWeights v theta w i * (a i : ℝ) < H :=
    (Finset.mem_filter.mp ha).2
  simp only [Fin.sum_univ_succ, InterpolationMatrix.rowWeights,
    Fin.cases_zero, Fin.cases_succ] at hr
  have hs : 0 ≤ ∑ i : Fin m, (w i / theta) * (a i.succ : ℝ) :=
    Finset.sum_nonneg (fun i _ =>
      mul_nonneg (div_nonneg (hw i) htheta.le) (Nat.cast_nonneg _))
  apply (le_div_iff₀ hv).2
  nlinarith

set_option maxHeartbeats 4000000 in
theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ} (hH : 0 < H)
    (r : Row d H) (t : RowChoice d H r) :
    ‖choiceScalar d r t‖ ≤
      Real.exp (-nu * (translatedIndexWeight d t.1 -
        (∑ i : Fin d.m, (r.2.1 i.succ : ℝ) *
          MatrixArithmetic.logWeights (finiteDenominators d) i)) +
        H * d.translationError) := by
  classical
  let w : Fin d.m → ℝ := MatrixArithmetic.logWeights (finiteDenominators d)
  have hw_eq (i : Fin d.m) : w i = d.x (i.val + 1) := by
    exact (d.x_log i.val).symm
  have hw (i : Fin d.m) : d.wstar ≤ w i := by
    rw [hw_eq]
    exact d.wstar_lower i
  have hwpos (i : Fin d.m) : 0 < w i := d.wstar_pos.trans_le (hw i)
  have ha : ∑ i, w i * (t.1.1 i : ℝ) ≤ H :=
    mapped_simplex_weight_le w H t.1.1 t.1.2
  have hrow : (r.2.1 0 : ℝ) ≤ H / (d.v0 : ℝ) :=
    strict_simplex_zero_bound (d.v0 : ℝ) (d.base.theta : ℝ) w H r.2.1
      d.v0_pos d.base.theta_pos (fun i => (hwpos i).le) r.2.2
  have hk : ((t.2.2 : ℕ) : ℝ) ≤ H / (d.v0 : ℝ) := by
    have hnat : (t.2.2 : ℕ) ≤ r.2.1 0 := Nat.le_of_lt_succ t.2.2.isLt
    exact (by exact_mod_cast hnat : ((t.2.2 : ℕ) : ℝ) ≤ (r.2.1 0 : ℝ)).trans hrow
  have hT (i : Fin d.m) :
      1 ≤ MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i := by
    change 1 ≤ ⌈d.F0 * w i / (d.v0 : ℝ)⌉₊
    exact Nat.one_le_ceil_iff.mpr (div_pos (mul_pos d.F0_pos (hwpos i)) d.v0_pos)
  have hTw (i : Fin d.m) : d.F0 * w i ≤
      (d.v0 : ℝ) * (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℝ) := by
    have hi := (div_le_iff₀ d.v0_pos).mp (Nat.le_ceil (d.F0 * w i / (d.v0 : ℝ)))
    simpa only [MatrixArithmetic.truncationOrders, w, mul_comm] using hi
  have hK : (1 : ℝ) ≤ d.K := by exact_mod_cast d.K_pos
  have hC : 0 ≤ Real.log (2 * (d.K : ℝ)) + nu :=
    add_nonneg (Real.log_nonneg (by linarith)) hnu
  have heps (i : Fin d.m) :
      ‖(r.1.val : ℂ) *
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i - period)‖ ≤
      Real.exp ((Real.log (2 * (d.K : ℝ)) + nu) - nu * w i) := by
    have hi := MatrixArithmetic.approximation_center_exp_control
      (d.p i.val) (d.q i.val) r.1.val d.K nu d.K_pos r.1.isLt.le hnu
      (le_trans (by decide : 1 ≤ 2) (d.approximations i.val).1)
      (d.approximations i.val).2.2
    simpa only [MatrixArithmetic.rationalCenters, finiteNumerators, finiteDenominators,
      period, w, MatrixArithmetic.logWeights] using hi
  have hb := raw_scalar_bound
    (fun i => (r.1.val : ℂ) *
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i - period))
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
    (fun i => t.1.1 i) (fun i => r.2.1 i.succ) t.2.1 t.2.2 w
    (Real.log (2 * (d.K : ℝ)) + nu) nu H d.wstar d.v0 d.F0
    hC hnu d.wstar_pos d.v0_pos d.F0_pos hw ha hk hT hTw heps
  simpa only [choiceScalar, translatedIndexWeight, w,
    AdmissibleParameters.translationError, add_assoc, mul_comm] using hb
