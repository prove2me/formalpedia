-- Prove2me | solution 1 for LargeDelaySGD.MeanSquare.delay_sum_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:10:55.085986+00:00
-- url     : https://prove2.me/submissions/fa879d34-2898-4da1-81a7-d5179d07e2cb

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

lemma tendsto_log_cast : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma sum_Ico_telescope (f : ℕ → ℝ) (t : ℕ) :
    ∀ n, t ≤ n → ∑ r ∈ Finset.Ico t n, (f (r + 1) - f r) = f n - f t := by
  intro n htn
  induction n, htn using Nat.le_induction with
  | base => simp
  | succ n hkn ih => rw [Finset.sum_Ico_succ_top hkn, ih]; ring

/-- basic log facts for `x ≥ 3`: `log x > 1`, `log log x > 0`. -/
lemma log_facts (x : ℝ) (hx : 3 ≤ x) : 1 < Real.log x ∧ 0 < Real.log (Real.log x) := by
  have h1 : 1 < Real.log x := lt_of_lt_of_le one_lt_log_three (Real.log_le_log (by norm_num) hx)
  exact ⟨h1, Real.log_pos h1⟩

lemma inc_lower (x : ℝ) (hx : 3 ≤ x) :
    1 / ((x + 1) * Real.log (x + 1) * Real.log (Real.log (x + 1))) ≤
      Real.log (Real.log (Real.log (x + 1))) - Real.log (Real.log (Real.log x)) := by
  obtain ⟨ha1, hla⟩ := log_facts x hx
  obtain ⟨hb1, hlb⟩ := log_facts (x + 1) (by linarith)
  have hab : Real.log x ≤ Real.log (x + 1) := Real.log_le_log (by linarith) (by linarith)
  have h3 := log_sub_ge (x + 1) x (by linarith) (by linarith)
  have h2 := log_sub_ge (Real.log (x + 1)) (Real.log x) (by linarith) (by linarith)
  have h1 := log_sub_ge (Real.log (Real.log (x + 1))) (Real.log (Real.log x)) hlb hla
  rw [show x + 1 - x = 1 by ring] at h3
  calc 1 / ((x + 1) * Real.log (x + 1) * Real.log (Real.log (x + 1)))
      = ((1 / (x + 1)) / Real.log (x + 1)) / Real.log (Real.log (x + 1)) := by
        field_simp
    _ ≤ ((Real.log (x + 1) - Real.log x) / Real.log (x + 1)) / Real.log (Real.log (x + 1)) := by
        gcongr
    _ ≤ _ := le_trans (div_le_div_of_nonneg_right h2 hlb.le) h1

lemma inc_upper (x : ℝ) (hx : 3 ≤ x) :
    Real.log (Real.log (Real.log (x + 1))) - Real.log (Real.log (Real.log x)) ≤
      1 / (x * Real.log x * Real.log (Real.log x)) := by
  obtain ⟨ha1, hla⟩ := log_facts x hx
  obtain ⟨hb1, hlb⟩ := log_facts (x + 1) (by linarith)
  have h3 := log_sub_le (x + 1) x (by linarith) (by linarith)
  have h2 := log_sub_le (Real.log (x + 1)) (Real.log x) (by linarith) (by linarith)
  have h1 := log_sub_le (Real.log (Real.log (x + 1))) (Real.log (Real.log x)) hlb hla
  rw [show x + 1 - x = 1 by ring] at h3
  calc _ ≤ _ := h1
    _ ≤ ((1 / x) / Real.log x) / Real.log (Real.log x) := by
        apply div_le_div_of_nonneg_right _ hla.le
        exact h2.trans (div_le_div_of_nonneg_right h3 (by linarith))
    _ = 1 / (x * Real.log x * Real.log (Real.log x)) := by field_simp

lemma inc2_lower (x : ℝ) (hx : 3 ≤ x) :
    1 / ((x + 1) * Real.log (x + 1) * Real.log (Real.log (x + 1)) * Real.log (Real.log x)) ≤
      -1 / Real.log (Real.log (x + 1)) - -1 / Real.log (Real.log x) := by
  obtain ⟨ha1, hla⟩ := log_facts x hx
  obtain ⟨hb1, hlb⟩ := log_facts (x + 1) (by linarith)
  have h3 := log_sub_ge (x + 1) x (by linarith) (by linarith)
  have h2 := log_sub_ge (Real.log (x + 1)) (Real.log x) (by linarith) (by linarith)
  rw [show x + 1 - x = 1 by ring] at h3
  have hdiff : (1 / (x + 1)) / Real.log (x + 1) ≤
      Real.log (Real.log (x + 1)) - Real.log (Real.log x) :=
    le_trans (div_le_div_of_nonneg_right h3 (by linarith)) h2
  calc 1 / ((x + 1) * Real.log (x + 1) * Real.log (Real.log (x + 1)) * Real.log (Real.log x))
      = ((1 / (x + 1)) / Real.log (x + 1)) /
          (Real.log (Real.log (x + 1)) * Real.log (Real.log x)) := by field_simp
    _ ≤ (Real.log (Real.log (x + 1)) - Real.log (Real.log x)) /
          (Real.log (Real.log (x + 1)) * Real.log (Real.log x)) :=
        div_le_div_of_nonneg_right hdiff (by positivity)
    _ = _ := by field_simp; ring

/-- `∑ 1 / ((n+1) log (n+1) loglog (n+1) loglog n)` converges (telescoping against `-1/loglog n`). -/
lemma summable_poly_comparison :
    Summable (fun n : ℕ => if 3 ≤ n then 1 / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) *
      Real.log (Real.log ((n : ℝ) + 1)) * Real.log (Real.log (n : ℝ))) else 0) := by
  have h1 : ∀ n : ℕ, 0 ≤ (if 3 ≤ n then 1 / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) *
      Real.log (Real.log ((n : ℝ) + 1)) * Real.log (Real.log (n : ℝ))) else 0) := by
    intro n
    split_ifs with h
    · have hx : (3 : ℝ) ≤ n := by exact_mod_cast h
      obtain ⟨_, hla⟩ := log_facts (n : ℝ) hx
      obtain ⟨_, hlb⟩ := log_facts ((n : ℝ) + 1) (by linarith)
      have : 0 < Real.log ((n : ℝ) + 1) := by linarith
      positivity
    · exact le_rfl
  have h2 : ∀ n : ℕ, n ≥ 3 → (if 3 ≤ n then 1 / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) *
      Real.log (Real.log ((n : ℝ) + 1)) * Real.log (Real.log (n : ℝ))) else 0)
      ≤ -1 / Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - -1 / Real.log (Real.log (n : ℝ)) := by
    intro n hn
    rw [if_pos hn]
    push_cast
    exact inc2_lower (n : ℝ) (by exact_mod_cast hn)
  have h3 : ∀ n : ℕ, -1 / Real.log (Real.log (n : ℝ)) ≤
      max 0 (-1 / Real.log (Real.log ((2 : ℕ) : ℝ))) := by
    intro n
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n
      · simp
      · simp
      · exact le_max_right _ _
    · have hx : (3 : ℝ) ≤ n := by exact_mod_cast h
      obtain ⟨_, hla⟩ := log_facts (n : ℝ) hx
      exact le_trans (div_nonpos_of_nonpos_of_nonneg (by norm_num) hla.le) (le_max_left _ _)
  exact summable_of_telescope _ _ h1 3 h2 _ h3

end LDSSeries

open LDSSeries in
theorem solution (α : ℕ → ℝ) (s : ℕ → ℕ) (hs : ∀ n, s n ≤ n) (hα : ∀ n, 0 < α n)
    (hreg : PolynomialRegime α s) :
    Summable (fun n => α (n + 1) ^ 2) ∧ ¬ Summable (fun n => α (n + 1)) ∧
      Summable (delaySum α s) := by
  obtain ⟨q, hq1, ⟨K, hK⟩, c, hc, N, hN⟩ := hreg
  have hK0 : 0 ≤ K := K_nonneg s hs q K hK
  have hφ : ∀ m : ℕ, m ≥ 3 → 0 < (m : ℝ) * Real.log m * Real.log (Real.log m) := by
    intro m hm
    have hx : (3 : ℝ) ≤ m := by exact_mod_cast hm
    obtain ⟨h1, h2⟩ := log_facts (m : ℝ) hx
    have : 0 < Real.log (m : ℝ) := by linarith
    positivity
  obtain ⟨C, hC0, hCb⟩ := exists_bound α (fun m => (m : ℝ) * Real.log m * Real.log (Real.log m))
    hα c hc N 3 hN hφ
  have hCb' : ∀ n : ℕ, 2 ≤ n → α (n + 1) ≤ C / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) *
      Real.log (Real.log ((n : ℝ) + 1))) := fun n hn => by
    have := hCb (n + 1) (by omega); push_cast at this; exact this
  have tendsto_log_succ : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  refine ⟨?_, ?_, ?_⟩
  · -- square-summability
    have hsum : Summable (fun n : ℕ => C ^ 2 * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
      ((summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num))).mul_left _
    refine hsum.of_norm_bounded_eventually_nat ?_
    filter_upwards [eventually_ge_atTop 2, (tendsto_atTop.mp tendsto_log_succ) 3] with n hn hl
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    obtain ⟨h1, h2⟩ := log_facts ((n : ℝ) + 1) (by linarith)
    have hll : 1 ≤ Real.log (Real.log ((n : ℝ) + 1)) := by
      have := Real.log_le_log (by norm_num) hl
      linarith [one_lt_log_three]
    have h1' : α (n + 1) ≤ C / ((n : ℝ) + 1) := by
      refine (hCb' n hn).trans ?_
      apply div_le_div_of_nonneg_left hC0.le (by positivity)
      have : 1 ≤ Real.log ((n : ℝ) + 1) * Real.log (Real.log ((n : ℝ) + 1)) := by nlinarith
      calc (n : ℝ) + 1 = ((n : ℝ) + 1) * 1 := by ring
        _ ≤ ((n : ℝ) + 1) * (Real.log ((n : ℝ) + 1) * Real.log (Real.log ((n : ℝ) + 1))) := by
            gcongr
        _ = _ := by ring
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    push_cast
    calc α (n + 1) ^ 2 ≤ (C / ((n : ℝ) + 1)) ^ 2 := pow_le_pow_left₀ (hα _).le h1' 2
      _ = C ^ 2 * (((n : ℝ) + 1) ^ 2)⁻¹ := by rw [div_pow, div_eq_mul_inv]
  · -- divergence: telescoping against `c logloglog (n + 1)`
    apply not_summable_of_telescope _
      (fun n => c * Real.log (Real.log (Real.log ((n : ℝ) + 1)))) (fun n => (hα _).le) (N + 2)
    · intro n hn
      rw [hN (n + 1) (by omega)]
      have hx : (3 : ℝ) ≤ (n : ℝ) + 1 := by
        have : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
        linarith
      have h := inc_upper ((n : ℝ) + 1) hx
      push_cast
      rw [← mul_sub]
      calc c * (Real.log (Real.log (Real.log ((n : ℝ) + 1 + 1))) -
            Real.log (Real.log (Real.log ((n : ℝ) + 1))))
          ≤ c * (1 / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) *
              Real.log (Real.log ((n : ℝ) + 1)))) := mul_le_mul_of_nonneg_left h hc.le
        _ = _ := by ring
    · exact Tendsto.const_mul_atTop hc
        (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_log_succ))
  · -- the delay sum
    have hsum := summable_poly_comparison.mul_left (4 * q * C ^ 2)
    refine hsum.of_norm_bounded_eventually_nat ?_
    set A : ℝ := Real.log (K + 1) + q * Real.log 2 with hA
    have hA0 : 0 ≤ A := by
      have : 0 ≤ Real.log (K + 1) := Real.log_nonneg (by linarith)
      have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      positivity
    have hlogcast : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hevA : ∀ᶠ n : ℕ in atTop, 2 * A + 2 * q * Real.log 4 ≤ Real.log (n : ℝ) :=
      (tendsto_atTop.mp hlogcast) _
    have hevB : ∀ᶠ n : ℕ in atTop, 2 * Real.log (2 * q) + 1 ≤ Real.log (Real.log (n : ℝ)) :=
      (tendsto_atTop.mp (Real.tendsto_log_atTop.comp hlogcast)) _
    have hevD : ∀ᶠ n : ℕ in atTop, K + 2 ≤ (n : ℝ) :=
      (tendsto_atTop.mp tendsto_natCast_atTop_atTop) _
    filter_upwards [hevA, hevB, hevD, eventually_ge_atTop 3] with n hnA hnB hnD hn3
    have hD0 : 0 ≤ delaySum α s n :=
      mul_nonneg (hα _).le (Finset.sum_nonneg fun r _ => (hα _).le)
    rw [Real.norm_eq_abs, abs_of_nonneg hD0, if_pos hn3]
    have hn3' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    obtain ⟨hu1, hlu⟩ := log_facts (n : ℝ) hn3'
    set u := Real.log (n : ℝ) with hu
    set t := s n with ht
    have htn : t ≤ n := hs n
    have hKn := hK n
    rw [← ht] at hKn
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    have hpow1 : (t : ℝ) ≤ ((t : ℝ) + 1) ^ q := by
      have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ (t : ℝ) + 1) hq1
      rw [Real.rpow_one] at this
      linarith
    have hnK : (n : ℝ) ≤ (K + 1) * ((t : ℝ) + 1) ^ q := by nlinarith
    -- `t ≥ 1`
    have ht1 : (1 : ℝ) ≤ t := by
      by_contra hcon
      have : t = 0 := by
        have : (t : ℝ) < 1 := not_le.mp hcon
        exact_mod_cast (show (t : ℝ) = 0 by
          have h' : t < 1 := by exact_mod_cast this
          have : t = 0 := by omega
          simp [this])
      rw [this] at hnK
      simp at hnK
      linarith
    -- `log n ≤ A + q log t`
    have hlogn : u ≤ A + q * Real.log t := by
      have h2t : ((t : ℝ) + 1) ^ q ≤ (2 * (t : ℝ)) ^ q :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      have h1 : (n : ℝ) ≤ (K + 1) * (2 * (t : ℝ)) ^ q :=
        hnK.trans (mul_le_mul_of_nonneg_left h2t (by linarith))
      have h2 := Real.log_le_log (by linarith) h1
      rw [Real.log_mul (by linarith) (by positivity),
        Real.log_rpow (by positivity), Real.log_mul (by norm_num) (by linarith)] at h2
      rw [hA]
      linarith
    set w := Real.log (t : ℝ) with hw
    have hq0 : 0 < q := by linarith
    have hwu : u / (2 * q) ≤ w := by
      rw [div_le_iff₀ (by positivity)]
      have : 0 ≤ q * Real.log 4 := mul_nonneg hq0.le (Real.log_nonneg (by norm_num))
      linarith
    have hu0 : 0 < u := by linarith
    have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hwu
    -- `t ≥ 3`
    have ht3 : 3 ≤ t := by
      by_contra hcon
      have : (t : ℝ) ≤ 2 := by exact_mod_cast (show t ≤ 2 by omega)
      have h1 : w ≤ Real.log 2 := Real.log_le_log (by linarith) this
      have h2 : Real.log 2 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
      have h3 : Real.log 4 ≤ u / (2 * q) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      linarith
    -- inner sum, telescoped
    have hinner : ∑ r ∈ Finset.Ico t n, α (r + 1) ≤
        C * (Real.log (Real.log u) - Real.log (Real.log w)) := by
      have htel := sum_Ico_telescope (fun r => Real.log (Real.log (Real.log (r : ℝ)))) t n htn
      calc ∑ r ∈ Finset.Ico t n, α (r + 1)
          ≤ ∑ r ∈ Finset.Ico t n, C * (Real.log (Real.log (Real.log ((r + 1 : ℕ) : ℝ))) -
              Real.log (Real.log (Real.log (r : ℝ)))) := by
            apply Finset.sum_le_sum
            intro r hr
            have hr3 : 3 ≤ r := le_trans ht3 (Finset.mem_Ico.mp hr).1
            have hr' : (3 : ℝ) ≤ r := by exact_mod_cast hr3
            refine (hCb' r (by omega)).trans ?_
            have := inc_lower (r : ℝ) hr'
            push_cast
            rw [div_eq_mul_one_div C]
            exact mul_le_mul_of_nonneg_left this hC0.le
        _ = C * (Real.log (Real.log u) - Real.log (Real.log w)) := by
            rw [← Finset.mul_sum, htel]
    -- `log w ≥ log u / 2`
    have hlw : Real.log u / 2 ≤ Real.log w := by
      have h1 := Real.log_le_log (by positivity) hwu
      rw [Real.log_div hu0.ne' (by positivity)] at h1
      linarith
    have hlw0 : 0 < Real.log w := by linarith
    have hdiff1 : Real.log u - Real.log w ≤ 2 * q := by
      have h := log_sub_le u w hu0 hw0
      have : (u - w) / w ≤ u / w := div_le_div_of_nonneg_right (by linarith) hw0.le
      have h2 : u / w ≤ 2 * q := by
        rw [div_le_iff₀ hw0]
        rw [div_le_iff₀ (by positivity)] at hwu
        linarith
      linarith
    have hdiff2 : Real.log (Real.log u) - Real.log (Real.log w) ≤ 4 * q / Real.log u := by
      have h := log_sub_le (Real.log u) (Real.log w) hlu hlw0
      calc _ ≤ _ := h
        _ ≤ (2 * q) / Real.log w := div_le_div_of_nonneg_right (by linarith) hlw0.le
        _ ≤ (2 * q) / (Real.log u / 2) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hlw
        _ = 4 * q / Real.log u := by field_simp; ring
    have hin0 : 0 ≤ ∑ r ∈ Finset.Ico t n, α (r + 1) := Finset.sum_nonneg fun r _ => (hα _).le
    obtain ⟨hb1, hlb⟩ := log_facts ((n : ℝ) + 1) (by linarith)
    unfold delaySum
    rw [← ht]
    calc α (n + 1) * ∑ r ∈ Finset.Ico t n, α (r + 1)
        ≤ (C / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) * Real.log (Real.log ((n : ℝ) + 1)))) *
            (C * (4 * q / Real.log u)) := by
          apply mul_le_mul (hCb' n (by omega)) (hinner.trans ?_) hin0 (by positivity)
          exact mul_le_mul_of_nonneg_left hdiff2 hC0.le
      _ = 4 * q * C ^ 2 * (1 / (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) *
            Real.log (Real.log ((n : ℝ) + 1)) * Real.log (Real.log (n : ℝ)))) := by
          rw [hu]
          field_simp
