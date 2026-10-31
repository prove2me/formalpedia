-- Prove2me | solution 1 for LargeDelaySGD.MeanSquare.delay_sum_sublinear
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:04:46.298596+00:00
-- url     : https://prove2.me/submissions/2f0d4079-e22b-4b53-bec4-c38629203acd

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

open LDSSeries in
theorem solution (α : ℕ → ℝ) (s : ℕ → ℕ) (hs : ∀ n, s n ≤ n) (hα : ∀ n, 0 < α n)
    (hreg : SublinearRegime α s) :
    Summable (fun n => α (n + 1) ^ 2) ∧ ¬ Summable (fun n => α (n + 1)) ∧
      Summable (delaySum α s) := by
  obtain ⟨p, hp0, hp1, ⟨K, hK⟩, c, hc, N, hN⟩ := hreg
  have hK0 : 0 ≤ K := K_nonneg s hs p K hK
  obtain ⟨C, hC0, hCb⟩ := exists_bound α (fun m => (m : ℝ)) hα c hc N 1 hN
    (fun m hm => by exact_mod_cast hm)
  have hCb' : ∀ n : ℕ, α (n + 1) ≤ C / ((n : ℝ) + 1) := fun n => by
    have := hCb (n + 1) (by omega); push_cast at this; exact this
  refine ⟨?_, ?_, ?_⟩
  · -- square-summability
    have hsum : Summable (fun n : ℕ => C ^ 2 * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
      ((summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num))).mul_left _
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) hsum
    have h1 := hCb' n
    have h0 := (hα (n + 1)).le
    push_cast
    calc α (n + 1) ^ 2 ≤ (C / ((n : ℝ) + 1)) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = C ^ 2 * (((n : ℝ) + 1) ^ 2)⁻¹ := by rw [div_pow, div_eq_mul_inv]
  · -- divergence: telescoping against `c log (n + 1)`
    apply not_summable_of_telescope _ (fun n => c * Real.log ((n : ℝ) + 1)) (fun n => (hα _).le) N
    · intro n hn
      rw [hN (n + 1) (by omega)]
      have h := log_sub_le ((n : ℝ) + 1 + 1) ((n : ℝ) + 1) (by positivity) (by positivity)
      push_cast
      rw [← mul_sub]
      calc c * (Real.log ((n : ℝ) + 1 + 1) - Real.log ((n : ℝ) + 1))
          ≤ c * (((n : ℝ) + 1 + 1 - ((n : ℝ) + 1)) / ((n : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left h hc.le
        _ = c / ((n : ℝ) + 1) := by ring
    · exact Tendsto.const_mul_atTop hc (Real.tendsto_log_atTop.comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop))
  · -- the delay sum
    set D : ℝ := C ^ 2 * K / (K + 1) ^ (p - 1) with hD
    have hsum : Summable (fun n : ℕ => D * (((n + 1 : ℕ) : ℝ) ^ (p - 2))) :=
      ((summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith))).mul_left _
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hsum
    · exact mul_nonneg (hα _).le (Finset.sum_nonneg fun r _ => (hα _).le)
    set t := s n with ht
    have htn : t ≤ n := hs n
    have hKn := hK n
    rw [← ht] at hKn
    have ht1 : (1 : ℝ) ≤ (t : ℝ) + 1 := by linarith [(Nat.cast_nonneg t : (0:ℝ) ≤ t)]
    have htp : ((t : ℝ) + 1) ^ p ≤ (t : ℝ) + 1 := by
      have := Real.rpow_le_rpow_of_exponent_le ht1 hp1.le
      simpa using this
    have hlow : ((n : ℝ) + 1) / (K + 1) ≤ (t : ℝ) + 1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    -- inner sum
    have hinner : ∑ r ∈ Finset.Ico t n, α (r + 1) ≤ C * K * ((t : ℝ) + 1) ^ (p - 1) := by
      calc ∑ r ∈ Finset.Ico t n, α (r + 1) ≤ ∑ r ∈ Finset.Ico t n, C / ((t : ℝ) + 1) := by
            apply Finset.sum_le_sum
            intro r hr
            have hr' : t ≤ r := (Finset.mem_Ico.mp hr).1
            refine (hCb' r).trans ?_
            apply div_le_div_of_nonneg_left hC0.le (by positivity)
            have : (t : ℝ) ≤ r := by exact_mod_cast hr'
            linarith
        _ = ((n : ℝ) - t) * (C / ((t : ℝ) + 1)) := by
            rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub htn]
        _ ≤ (K * ((t : ℝ) + 1) ^ p) * (C / ((t : ℝ) + 1)) := by
            gcongr
            linarith
        _ = C * K * ((t : ℝ) + 1) ^ (p - 1) := by
            rw [Real.rpow_sub_one (by positivity)]
            ring
    have hpow : ((t : ℝ) + 1) ^ (p - 1) ≤ (((n : ℝ) + 1) / (K + 1)) ^ (p - 1) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hlow (by linarith)
    rw [Real.div_rpow (by positivity) (by positivity)] at hpow
    unfold delaySum
    rw [← ht]
    have hα1 := hCb' n
    have hin0 : 0 ≤ ∑ r ∈ Finset.Ico t n, α (r + 1) := Finset.sum_nonneg fun r _ => (hα _).le
    calc α (n + 1) * ∑ r ∈ Finset.Ico t n, α (r + 1)
        ≤ (C / ((n : ℝ) + 1)) * (C * K * (((n : ℝ) + 1) ^ (p - 1) / (K + 1) ^ (p - 1))) := by
          apply mul_le_mul hα1 (hinner.trans ?_) hin0 (by positivity)
          gcongr
      _ = D * (((n + 1 : ℕ) : ℝ) ^ (p - 2)) := by
          have hn0 : ((n : ℝ) + 1) ≠ 0 := by positivity
          rw [hD, show p - 2 = (p - 1) - 1 by ring]
          push_cast
          rw [Real.rpow_sub_one hn0 (p - 1)]
          field_simp
