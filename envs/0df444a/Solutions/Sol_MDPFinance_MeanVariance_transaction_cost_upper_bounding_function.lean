-- Prove2me | solution 1 for MDPFinance.MeanVariance.transaction_cost_upper_bounding_function
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T21:43:47.308922+00:00
-- url     : https://prove2.me/submissions/92e5d01f-6fc6-4a62-9d6a-955c622b4d6f

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_TransactionCostMarket

open MeasureTheory ProbabilityTheory

set_option autoImplicit false

namespace MDPFinance.MeanVariance.P4f29c0ca

open MDPFinance.MeanVariance

lemma U_affine_bound {Ω : Type*} [MeasurableSpace Ω] (M : TransactionCostMarket Ω) (t : ℝ)
    (ht : 0 ≤ t) : M.U t ≤ (|M.U 0| + (M.U 1 - M.U 0)) * (1 + t) := by
  have hK : 0 ≤ M.U 1 - M.U 0 := by
    have := M.hU_mono (Set.mem_Ici.2 (le_refl (0:ℝ)))
      (show (1:ℝ) ∈ Set.Ici 0 from Set.mem_Ici.2 zero_le_one) zero_lt_one
    linarith
  have h0 : M.U 0 ≤ |M.U 0| := le_abs_self _
  rcases le_total t 1 with h1 | h1
  · have hm : M.U t ≤ M.U 1 := M.hU_mono.monotoneOn (Set.mem_Ici.2 ht)
      (show (1:ℝ) ∈ Set.Ici 0 from Set.mem_Ici.2 zero_le_one) h1
    nlinarith [abs_nonneg (M.U 0)]
  · -- concavity between 0 and t at the point 1
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one h1
    have hc := M.hU_concave.concaveOn.2 (Set.mem_Ici.2 (le_refl (0:ℝ)))
      (Set.mem_Ici.2 ht)
      (show (0:ℝ) ≤ 1 - 1/t by rw [sub_nonneg, div_le_one htpos]; exact h1)
      (show (0:ℝ) ≤ 1/t by positivity) (show 1 - 1/t + 1/t = (1:ℝ) by ring)
    have e : (1 - 1/t) • (0:ℝ) + (1/t) • t = 1 := by
      simp [smul_eq_mul]; field_simp
    rw [e] at hc
    simp only [smul_eq_mul] at hc
    -- hc : (1 - 1/t) * U 0 + (1/t) * U t ≤ U 1
    have hc' : M.U t ≤ t * M.U 1 - (t - 1) * M.U 0 := by
      have := mul_le_mul_of_nonneg_left hc ht
      have e2 : t * ((1 - 1/t) * M.U 0 + (1/t) * M.U t) = (t - 1) * M.U 0 + M.U t := by
        field_simp
      rw [e2] at this
      linarith
    nlinarith [abs_nonneg (M.U 0)]

end MDPFinance.MeanVariance.P4f29c0ca

open MDPFinance.MeanVariance in
theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (M : TransactionCostMarket Ω) :
    ∃ cr cg αb : ℝ, 0 ≤ cr ∧ 0 ≤ cg ∧ 0 ≤ αb ∧
      (∀ x ∈ Estate, max (0 : ℝ) 0 ≤ cr * (1 + x.1 + x.2)) ∧
      (∀ x ∈ Estate, max (M.U (x.1 + x.2)) 0 ≤ cg * (1 + x.1 + x.2)) ∧
      (∀ n < M.N, ∀ x ∈ Estate, ∀ a ∈ M.Arange x.1 x.2,
        (∫ ω, (1 + M.h x.1 x.2 a * (1 + M.i (n + 1)) + a * M.Rtilde (n + 1) ω) ∂M.measIP) ≤
          αb * (1 + x.1 + x.2)) := by
  have := M.isProb
  have hK : 0 ≤ M.U 1 - M.U 0 := by
    have := M.hU_mono (Set.mem_Ici.2 (le_refl (0:ℝ)))
      (show (1:ℝ) ∈ Set.Ici 0 from Set.mem_Ici.2 zero_le_one) zero_lt_one
    linarith
  set T : ℕ → ℝ := fun k => |1 + M.i (k + 1)| + |∫ ω, M.Rtilde (k + 1) ω ∂M.measIP| with hT
  have hTnn : ∀ k, 0 ≤ T k := fun k => by simp only [hT]; positivity
  refine ⟨0, |M.U 0| + (M.U 1 - M.U 0), 1 + ∑ k ∈ Finset.range M.N, T k, le_refl _,
    by positivity, by positivity, ?_, ?_, ?_⟩
  · intro x _; simp
  · intro x hx
    obtain ⟨hx0, hx1⟩ := hx
    have hs : 0 ≤ x.1 + x.2 := by linarith
    have := P4f29c0ca.U_affine_bound M (x.1 + x.2) hs
    refine max_le ?_ ?_
    · have e : 1 + x.1 + x.2 = 1 + (x.1 + x.2) := by ring
      rw [e]; exact this
    · have : 0 ≤ |M.U 0| := abs_nonneg _
      positivity
  · intro n hn x hx a ha
    obtain ⟨hx0, hx1⟩ := hx
    obtain ⟨ha0, ha1⟩ := ha
    have hn1 : 1 ≤ n + 1 := by omega
    have hnN : n + 1 ≤ M.N := by omega
    have hint := M.hRtilde_int (n + 1) hn1 hnN
    have hipos := M.hi_pos (n + 1) hn1 hnN
    have hc0 := M.hc0
    have hc1 := M.hc1
    -- compute the integral
    have hI : (∫ ω, (1 + M.h x.1 x.2 a * (1 + M.i (n + 1)) + a * M.Rtilde (n + 1) ω) ∂M.measIP)
        = 1 + M.h x.1 x.2 a * (1 + M.i (n + 1)) + a * ∫ ω, M.Rtilde (n + 1) ω ∂M.measIP := by
      rw [integral_add (integrable_const _) (hint.const_mul a), integral_const, integral_const_mul]
      simp
    rw [hI]
    -- bounds
    have hh : M.h x.1 x.2 a ≤ x.1 + x.2 := by
      unfold TransactionCostMarket.h
      split_ifs with hax
      · nlinarith
      · have hax' := lt_of_not_ge hax; nlinarith
    have hdiv : x.2 + x.1 / (1 + M.c) ≤ x.1 + x.2 := by
      have : x.1 / (1 + M.c) ≤ x.1 := div_le_self hx0 (by linarith)
      linarith
    have ha2 : a ≤ x.1 + x.2 := le_trans ha1 hdiv
    set S := x.1 + x.2 with hS
    have hS0 : 0 ≤ S := by linarith
    set R := ∫ ω, M.Rtilde (n + 1) ω ∂M.measIP
    have b1 : M.h x.1 x.2 a * (1 + M.i (n + 1)) ≤ S * |1 + M.i (n + 1)| := by
      rw [abs_of_pos hipos]; exact mul_le_mul_of_nonneg_right hh hipos.le
    have b2 : a * R ≤ S * |R| := by
      calc a * R ≤ a * |R| := mul_le_mul_of_nonneg_left (le_abs_self _) ha0
        _ ≤ S * |R| := mul_le_mul_of_nonneg_right ha2 (abs_nonneg _)
    have hTn : T n ≤ ∑ k ∈ Finset.range M.N, T k :=
      Finset.single_le_sum (fun k _ => hTnn k) (Finset.mem_range.2 hn)
    have hTdef : T n = |1 + M.i (n + 1)| + |R| := rfl
    have hsum0 : 0 ≤ ∑ k ∈ Finset.range M.N, T k := Finset.sum_nonneg (fun k _ => hTnn k)
    have e : 1 + x.1 + x.2 = 1 + S := by rw [hS]; ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hTn hS0]
