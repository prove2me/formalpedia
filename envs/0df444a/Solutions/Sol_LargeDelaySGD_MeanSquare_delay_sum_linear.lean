-- Prove2me | solution 1 for LargeDelaySGD.MeanSquare.delay_sum_linear
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:06:57.717678+00:00
-- url     : https://prove2.me/submissions/c93c92b0-0fad-4c52-a4d1-ae83bfcf4f3c

import Mathlib
import Definitions.Def_LargeDelaySGD_MeanSquare_Model

open Filter LargeDelaySGD.MeanSquare

namespace LDSSeries

lemma summable_of_telescope (a Ψ : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (n0 : ℕ)
    (hle : ∀ n ≥ n0, a n ≤ Ψ (n + 1) - Ψ n) (M : ℝ) (hM : ∀ n, Ψ n ≤ M) : Summable a := by
  rw [← summable_nat_add_iff n0]
  apply summable_of_sum_range_le (fun n => ha _) (c := M - Ψ n0)
  intro m
  have h : ∑ i ∈ Finset.range m, a (i + n0)
      ≤ ∑ i ∈ Finset.range m, (Ψ ((i + n0) + 1) - Ψ (i + n0)) :=
    Finset.sum_le_sum fun i _ => hle _ (by omega)
  have h2 : ∑ i ∈ Finset.range m, (Ψ ((i + n0) + 1) - Ψ (i + n0)) = Ψ (m + n0) - Ψ n0 := by
    have := Finset.sum_range_sub (fun i => Ψ (i + n0)) m
    simp only [zero_add] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show i + 1 + n0 = i + n0 + 1 by omega]
  linarith [hM (m + n0)]

lemma not_summable_of_telescope (a Ψ : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (n0 : ℕ)
    (hle : ∀ n ≥ n0, Ψ (n + 1) - Ψ n ≤ a n) (hΨ : Tendsto Ψ atTop atTop) : ¬ Summable a := by
  intro hs
  have hs' : Summable (fun i => a (i + n0)) := (summable_nat_add_iff n0).mpr hs
  obtain ⟨m, hm⟩ := (tendsto_atTop.mp (hΨ.comp (tendsto_add_atTop_nat n0)))
    (Ψ n0 + ∑' i, a (i + n0) + 1) |>.exists
  have h : ∑ i ∈ Finset.range m, (Ψ ((i + n0) + 1) - Ψ (i + n0))
      ≤ ∑ i ∈ Finset.range m, a (i + n0) :=
    Finset.sum_le_sum fun i _ => hle _ (by omega)
  have h2 : ∑ i ∈ Finset.range m, (Ψ ((i + n0) + 1) - Ψ (i + n0)) = Ψ (m + n0) - Ψ n0 := by
    have := Finset.sum_range_sub (fun i => Ψ (i + n0)) m
    simp only [zero_add] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show i + 1 + n0 = i + n0 + 1 by omega]
  have h3 := hs'.sum_le_tsum (Finset.range m) (fun i _ => ha _)
  simp only [Function.comp] at hm
  linarith

/-- `log x - log y ≤ (x - y) / y`. -/
lemma log_sub_le (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : Real.log x - Real.log y ≤ (x - y) / y := by
  rw [← Real.log_div hx.ne' hy.ne']
  have := Real.log_le_sub_one_of_pos (div_pos hx hy)
  rw [sub_div, div_self hy.ne'] 
  exact this

/-- `(x - y) / x ≤ log x - log y`. -/
lemma log_sub_ge (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x - y) / x ≤ Real.log x - Real.log y := by
  rw [← Real.log_div hx.ne' hy.ne']
  have := Real.one_sub_inv_le_log_of_pos (div_pos hx hy)
  rw [inv_div] at this
  rw [sub_div, div_self hx.ne']
  exact this

/-- If `α m = c / φ m` for `m ≥ N` and `φ m > 0` for `m ≥ m0`, then `α m ≤ C / φ m` for all
`m ≥ m0`, with a single constant `C > 0`. -/
lemma exists_bound (α φ : ℕ → ℝ) (hα : ∀ n, 0 < α n) (c : ℝ) (hc : 0 < c) (N m0 : ℕ)
    (hN : ∀ n ≥ N, α n = c / φ n) (hφ : ∀ m ≥ m0, 0 < φ m) :
    ∃ C > 0, ∀ m ≥ m0, α m ≤ C / φ m := by
  set C := c + ∑ m ∈ Finset.Ico m0 N, φ m * α m with hC
  have hsum : 0 ≤ ∑ m ∈ Finset.Ico m0 N, φ m * α m := Finset.sum_nonneg fun m hm =>
    mul_nonneg (hφ m (Finset.mem_Ico.mp hm).1).le (hα m).le
  refine ⟨C, by linarith, fun m hm => ?_⟩
  rcases Nat.lt_or_ge m N with h | h
  · rw [le_div_iff₀ (hφ m hm)]
    have : φ m * α m ≤ ∑ m ∈ Finset.Ico m0 N, φ m * α m :=
      Finset.single_le_sum (f := fun m => φ m * α m)
        (fun i hi => mul_nonneg (hφ i (Finset.mem_Ico.mp hi).1).le (hα i).le)
        (Finset.mem_Ico.mpr ⟨hm, h⟩)
    linarith
  · rw [hN m h]
    exact div_le_div_of_nonneg_right (by linarith) (hφ m hm).le

/-- `K ≥ 0` in the delay bound (evaluate at `n = 0`). -/
lemma K_nonneg (s : ℕ → ℕ) (hs : ∀ n, s n ≤ n) (p K : ℝ)
    (hK : ∀ n : ℕ, (n : ℝ) ≤ s n + K * ((s n : ℝ) + 1) ^ p) : 0 ≤ K := by
  have h := hK 0
  have : s 0 = 0 := Nat.le_zero.mp (hs 0)
  simp [this] at h
  exact h

end LDSSeries

namespace LDSSeries

lemma one_lt_log_three : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

lemma tendsto_log_succ : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

/-- Bertrand-type series `∑ 1 / ((n+1) log² (n+1))` converges (telescoping against `-1/log n`). -/
lemma summable_inv_mul_log_sq :
    Summable (fun n : ℕ => 1 / (((n : ℝ) + 1) * (Real.log ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1)))) := by
  have h1 : ∀ n : ℕ, 0 ≤ 1 / (((n : ℝ) + 1) * (Real.log ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1))) := by
    intro n
    have : 0 ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_nonneg (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
    positivity
  have h2 : ∀ n : ℕ, n ≥ 2 → 1 / (((n : ℝ) + 1) * (Real.log ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1)))
      ≤ -1 / Real.log ((n + 1 : ℕ) : ℝ) - -1 / Real.log (n : ℝ) := by
    intro n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hl0 : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hl1 : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    have hl1' : 0 < Real.log ((n : ℝ) + 1) := lt_of_lt_of_le hl0 hl1
    have hd := log_sub_ge ((n : ℝ) + 1) n (by linarith) (by linarith)
    rw [show ((n : ℝ) + 1 - n) = 1 by ring] at hd
    push_cast
    set l0 := Real.log (n : ℝ)
    set l1 := Real.log ((n : ℝ) + 1)
    calc 1 / (((n : ℝ) + 1) * (l1 * l1)) = (1 / ((n : ℝ) + 1)) / (l1 * l1) := by
          field_simp
      _ ≤ (l1 - l0) / (l1 * l1) := div_le_div_of_nonneg_right hd (by positivity)
      _ ≤ (l1 - l0) / (l0 * l1) :=
          div_le_div_of_nonneg_left (by linarith) (by positivity)
            (mul_le_mul_of_nonneg_right hl1 hl1'.le)
      _ = -1 / l1 - -1 / l0 := by field_simp; ring
  have h3 : ∀ n : ℕ, -1 / Real.log (n : ℝ) ≤ 0 := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast h)
      exact div_nonpos_of_nonpos_of_nonneg (by norm_num) this
  exact summable_of_telescope _ (fun n : ℕ => -1 / Real.log (n : ℝ)) h1 2 h2 0 h3

end LDSSeries

open LDSSeries in
theorem solution (α : ℕ → ℝ) (s : ℕ → ℕ) (hs : ∀ n, s n ≤ n) (hα : ∀ n, 0 < α n)
    (hreg : LinearRegime α s) :
    Summable (fun n => α (n + 1) ^ 2) ∧ ¬ Summable (fun n => α (n + 1)) ∧
      Summable (delaySum α s) := by
  obtain ⟨⟨K, hK⟩, c, hc, N, hN⟩ := hreg
  have hK0 : 0 ≤ K := by
    have h := hK 0
    have : s 0 = 0 := Nat.le_zero.mp (hs 0)
    simp [this] at h
    exact h
  have hφ : ∀ m : ℕ, m ≥ 2 → 0 < (m : ℝ) * Real.log m := by
    intro m hm
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have := Real.log_pos (by linarith : (1 : ℝ) < m)
    positivity
  obtain ⟨C, hC0, hCb⟩ := exists_bound α (fun m => (m : ℝ) * Real.log m) hα c hc N 2 hN hφ
  have hCb' : ∀ n : ℕ, 1 ≤ n →
      α (n + 1) ≤ C / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1)) := fun n hn => by
    have := hCb (n + 1) (by omega); push_cast at this; exact this
  refine ⟨?_, ?_, ?_⟩
  · -- square-summability: eventually `α (n+1) ≤ C / (n+1)`
    have hsum : Summable (fun n : ℕ => C ^ 2 * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
      ((summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num))).mul_left _
    refine hsum.of_norm_bounded_eventually_nat ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 1 ≤ Real.log ((n : ℝ) + 1) := by
      have := Real.log_le_log (by norm_num) (by linarith : (3 : ℝ) ≤ (n : ℝ) + 1)
      linarith [one_lt_log_three]
    have h1 : α (n + 1) ≤ C / ((n : ℝ) + 1) := by
      refine (hCb' n (by omega)).trans ?_
      apply div_le_div_of_nonneg_left hC0.le (by positivity)
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    push_cast
    calc α (n + 1) ^ 2 ≤ (C / ((n : ℝ) + 1)) ^ 2 := pow_le_pow_left₀ (hα _).le h1 2
      _ = C ^ 2 * (((n : ℝ) + 1) ^ 2)⁻¹ := by rw [div_pow, div_eq_mul_inv]
  · -- divergence: telescoping against `c log log (n + 1)`
    apply not_summable_of_telescope _ (fun n => c * Real.log (Real.log ((n : ℝ) + 1)))
      (fun n => (hα _).le) (N + 1)
    · intro n hn
      rw [hN (n + 1) (by omega)]
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have hl0 : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by linarith)
      have hl1 : 0 < Real.log ((n : ℝ) + 1 + 1) := Real.log_pos (by linarith)
      have h1 := log_sub_le (Real.log ((n : ℝ) + 1 + 1)) (Real.log ((n : ℝ) + 1)) hl1 hl0
      have h2 := log_sub_le ((n : ℝ) + 1 + 1) ((n : ℝ) + 1) (by positivity) (by positivity)
      rw [show ((n : ℝ) + 1 + 1 - ((n : ℝ) + 1)) = 1 by ring] at h2
      push_cast
      rw [← mul_sub]
      calc c * (Real.log (Real.log ((n : ℝ) + 1 + 1)) - Real.log (Real.log ((n : ℝ) + 1)))
          ≤ c * ((1 / ((n : ℝ) + 1)) / Real.log ((n : ℝ) + 1)) := by
            apply mul_le_mul_of_nonneg_left _ hc.le
            exact h1.trans (div_le_div_of_nonneg_right h2 hl0.le)
        _ = c / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1)) := by field_simp
    · exact Tendsto.const_mul_atTop hc (Real.tendsto_log_atTop.comp tendsto_log_succ)
  · -- the delay sum, eventually bounded by a Bertrand term
    have hsum := summable_inv_mul_log_sq.mul_left (2 * K * C ^ 2)
    refine hsum.of_norm_bounded_eventually_nat ?_
    have hev1 : ∀ᶠ n : ℕ in atTop, 2 * (K + 1) ≤ (n : ℝ) + 1 :=
      (tendsto_atTop.mp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)) _
    have hev2 : ∀ᶠ n : ℕ in atTop, 2 * Real.log (K + 1) + 1 ≤ Real.log ((n : ℝ) + 1) :=
      (tendsto_atTop.mp tendsto_log_succ) _
    filter_upwards [hev1, hev2, eventually_ge_atTop 1] with n hn1 hn2 hn3
    have hD0 : 0 ≤ delaySum α s n :=
      mul_nonneg (hα _).le (Finset.sum_nonneg fun r _ => (hα _).le)
    rw [Real.norm_eq_abs, abs_of_nonneg hD0]
    set t := s n with ht
    have htn : t ≤ n := hs n
    have hKn := hK n
    rw [← ht] at hKn
    have hlow : ((n : ℝ) + 1) / (K + 1) ≤ (t : ℝ) + 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have ht2 : (2 : ℝ) ≤ (t : ℝ) + 1 := by
      have : 2 ≤ ((n : ℝ) + 1) / (K + 1) := by rw [le_div_iff₀ (by linarith)]; linarith
      linarith
    have hlt0 : 0 < Real.log ((t : ℝ) + 1) := Real.log_pos (by linarith)
    have hLK : 0 ≤ Real.log (K + 1) := Real.log_nonneg (by linarith)
    -- `log (t+1) ≥ log (n+1) / 2`
    have hlogt : Real.log ((n : ℝ) + 1) / 2 ≤ Real.log ((t : ℝ) + 1) := by
      have h1 := Real.log_le_log (by positivity) hlow
      rw [Real.log_div (by positivity) (by positivity)] at h1
      linarith
    -- inner sum
    have hinner : ∑ r ∈ Finset.Ico t n, α (r + 1) ≤ K * C / Real.log ((t : ℝ) + 1) := by
      calc ∑ r ∈ Finset.Ico t n, α (r + 1)
          ≤ ∑ r ∈ Finset.Ico t n, C / (((t : ℝ) + 1) * Real.log ((t : ℝ) + 1)) := by
            apply Finset.sum_le_sum
            intro r hr
            have hr' : t ≤ r := (Finset.mem_Ico.mp hr).1
            have hrr : (t : ℝ) ≤ r := by exact_mod_cast hr'
            have hr1 : 1 ≤ r := by
              have : (1 : ℝ) ≤ r := by linarith
              exact_mod_cast this
            refine (hCb' r hr1).trans ?_
            apply div_le_div_of_nonneg_left hC0.le (by positivity)
            exact mul_le_mul (by linarith) (Real.log_le_log (by linarith) (by linarith))
              hlt0.le (by linarith)
        _ = ((n : ℝ) - t) * (C / (((t : ℝ) + 1) * Real.log ((t : ℝ) + 1))) := by
            rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub htn]
        _ ≤ (K * ((t : ℝ) + 1)) * (C / (((t : ℝ) + 1) * Real.log ((t : ℝ) + 1))) := by
            gcongr
            linarith
        _ = K * C / Real.log ((t : ℝ) + 1) := by
            field_simp
    have hin0 : 0 ≤ ∑ r ∈ Finset.Ico t n, α (r + 1) := Finset.sum_nonneg fun r _ => (hα _).le
    have hln : 0 < Real.log ((n : ℝ) + 1) := by linarith
    unfold delaySum
    rw [← ht]
    calc α (n + 1) * ∑ r ∈ Finset.Ico t n, α (r + 1)
        ≤ (C / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1))) * (K * C / (Real.log ((n : ℝ) + 1) / 2)) := by
          apply mul_le_mul (hCb' n hn3) (hinner.trans ?_) hin0 (by positivity)
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) hlogt
      _ = 2 * K * C ^ 2 * (1 / (((n : ℝ) + 1) *
            (Real.log ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1)))) := by
          field_simp
