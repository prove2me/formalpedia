-- Prove2me | solution 1 for MasulloRH.critical_half_weight_prime_mass_exceeds_summably_damped_interior_jets
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T04:50:40.595112+00:00
-- url     : https://prove2.me/submissions/dc777f83-1af0-4a3c-bd12-796f4ea0fbf6

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Real Filter Finset Asymptotics
open scoped Topology

private theorem eventual_theta_linear :
    ∀ᶠ m : ℕ in atTop, (m:ℝ)*Real.log 2 / 2 ≤ Chebyshev.theta m := by
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall := (isLittleO_log_rpow_atTop (r := 1/2) (by norm_num)).bound
    (show 0 < Real.log 2 / 8 by positivity)
  have hnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hsmall
  filter_upwards [hnat, eventually_ge_atTop (2:ℕ)] with m hm hm2
  have hmx : (2:ℝ) ≤ m := by exact_mod_cast hm2
  have hm1 : (1:ℝ) ≤ m := by linarith
  have hm0 : 0 ≤ (m:ℝ) := by positivity
  have hlog : 0 ≤ Real.log m := Real.log_nonneg hm1
  have hs : 1 ≤ Real.sqrt m := by simpa using Real.sqrt_le_sqrt hm1
  have hs0 : 0 ≤ Real.sqrt m := Real.sqrt_nonneg _
  have hlog' : Real.log m ≤ Real.log 2/8 * Real.sqrt m := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog, ← Real.sqrt_eq_rpow,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hm
  have hplus : Real.log ((m:ℝ)+1) ≤ 2*Real.log m := by
    calc
      _ ≤ Real.log ((m:ℝ)^2) := by
        apply Real.log_le_log (by positivity)
        nlinarith [mul_nonneg (sub_nonneg.mpr hmx) (by positivity : 0 ≤ (m:ℝ)+1)]
      _ = _ := by rw [Real.log_pow]; norm_num
  have hbound := Chebyshev.theta_ge m
  have hsquare := Real.sq_sqrt hm0
  have hmixed := mul_le_mul_of_nonneg_left hlog' hs0
  have hbig : 2*Real.log m ≤ 2*Real.sqrt m * Real.log m := by nlinarith [mul_nonneg (sub_nonneg.mpr hs) hlog]
  nlinarith [congrArg (fun t : ℝ => t * Real.log 2) hsquare]

private theorem block_lower :
    ∀ᶠ n : ℕ in atTop, let S := Nat.primesLE (8*n) \ Nat.primesLE n
      (Real.log 2 / Real.sqrt 8) * Real.sqrt n ≤
        ∑ p ∈ S, Real.log p / Real.sqrt p := by
  have hbig : Tendsto (fun n : ℕ => 8*n) atTop atTop := by
    refine tendsto_atTop.mpr (fun b => ?_)
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  filter_upwards [hbig.eventually eventual_theta_linear, eventually_ge_atTop (1:ℕ)] with n hl hn
  dsimp only
  have hreal : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have h8real : (0:ℝ)<8*n := by positivity
  let S := Nat.primesLE (8*n) \ Nat.primesLE n
  have hm : Nat.primesLE n ⊆ Nat.primesLE (8*n) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    exact ⟨hp.1.trans (by omega), hp.2⟩
  have ht : ∑ p ∈ S, Real.log (p:ℝ) = Chebyshev.theta (8*n:ℕ) - Chebyshev.theta n := by
    rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log]
    exact Finset.sum_sdiff_eq_sub hm
  have hu := Chebyshev.theta_le_log4_mul_x hreal.le
  have hfour : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^ (2:ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hfour] at hu
  have hc : (n:ℝ)*Real.log 2 ≤ ∑ p ∈ S, Real.log (p:ℝ) := by
    rw [ht]
    push_cast at hl ⊢
    nlinarith [mul_nonneg hreal.le (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))]
  have hb : (∑ p ∈ S, Real.log (p:ℝ)) / Real.sqrt (8*n) ≤
      ∑ p ∈ S, Real.log p / Real.sqrt p := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro p hp
    have h := Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1
    have hp0 : (0:ℝ) < p := by exact_mod_cast h.2.pos
    have hle : (p:ℝ) ≤ 8*n := by exact_mod_cast h.1
    apply div_le_div_of_nonneg_left (Real.log_nonneg (by exact_mod_cast h.2.one_le))
      (Real.sqrt_pos.mpr hp0) (Real.sqrt_le_sqrt hle)
  calc
    _ = (n:ℝ)*Real.log 2 / Real.sqrt (8*n) := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 8)]
      field_simp
      nlinarith [Real.sq_sqrt hreal.le]
    _ ≤ _ := (div_le_div_of_nonneg_right hc (Real.sqrt_nonneg _)).trans hb

private theorem jet_bound (n k : ℕ) {b : ℝ} (hb : 0 < b) :
    (n:ℝ)^k * Real.exp (-b*(n:ℝ)) ≤ (k.factorial:ℝ) / b^k := by
  have hx : 0 ≤ b*(n:ℝ) := by positivity
  have h := Real.pow_div_factorial_le_exp _ hx k
  have hk : (0:ℝ) < k.factorial := by positivity
  have hb' := pow_pos hb k
  have he := Real.exp_pos (b * (n:ℝ))
  rw [div_le_iff₀ hk, mul_pow] at h
  rw [neg_mul,Real.exp_neg]
  calc
    _ = (n:ℝ)^k / Real.exp (b*n) := by ring
    _ ≤ (k.factorial:ℝ)/b^k := by
      apply (div_le_div_iff₀ he hb').mpr
      nlinarith only [h]

theorem solution (a gap : ℕ → ℝ) (k : ℕ → ℕ) (ha : ∀ j, 0 ≤ a j) (hgap : ∀ j, 0 < gap j)
    (hsum : Summable (fun j => a j * ((k j).factorial:ℝ) / (gap j)^(k j))) :
    ∀ᶠ n : ℕ in atTop,
      let X := (2:ℕ)^n
      let S := Nat.primesLE (8*X) \ Nat.primesLE X
      (Real.log 2 / (2*Real.sqrt 8) +
        ∑' j, a j * ((n:ℝ)^(k j) * Real.exp (-(gap j)*(n:ℝ)))) * Real.sqrt (X:ℝ) ≤
        ∑ p ∈ S, Real.log p / Real.sqrt p := by
  have hmode : Tendsto (fun n : ℕ => ∑' j, a j * ((n:ℝ)^(k j) * Real.exp (-(gap j)*(n:ℝ)))) atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (g := fun _ : ℕ => (0:ℝ)) hsum
      (f := fun (n j : ℕ) => a j * ((n:ℝ)^(k j) * Real.exp (-(gap j)*(n:ℝ)))) (fun j => by
        have h0 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((k j):ℝ) (gap j) (hgap j)).comp
          (tendsto_natCast_atTop_atTop (R := ℝ))
        simpa [Function.comp_def] using h0.const_mul (a j))
      (Eventually.of_forall (fun (n j : ℕ) => by
        rw [Real.norm_of_nonneg (mul_nonneg (ha j) (by positivity)), mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (jet_bound n (k j) (hgap j)) (ha j)))
    simpa using h
  have hd : 0 < Real.log 2 / (2*Real.sqrt 8) := by
    exact div_pos (Real.log_pos (by norm_num)) (by positivity)
  have hsub := (tendsto_pow_atTop_atTop_of_one_lt (show (1:ℕ) < 2 by norm_num)).eventually block_lower
  filter_upwards [hsub, hmode.eventually_lt_const hd] with n hb hn
  dsimp only at hb ⊢
  apply le_trans _ hb
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  linarith [show Real.log 2 / (2 * Real.sqrt 8) * 2 = Real.log 2 / Real.sqrt 8 by ring]
