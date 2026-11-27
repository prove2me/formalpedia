-- Prove2me | solution 3 for MasulloRH.compensated_resolvent_defect_low_high_split
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T03:26:55.346095+00:00
-- url     : https://prove2.me/submissions/1cf078c2-ac51-439a-a569-4241c94f04e1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_finite_prime_certificate_controls_every_complex_trace_window
import Theorems.Thm_MasulloRH_cofinal_approximate_prime_mass_certificates
import Theorems.Thm_MasulloRH_low_height_trace_zero_set_empty
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith

open MasulloRH ArithmeticFunction Filter Topology

private theorem primeTail_tends_to_zero :
    Tendsto (fun x : ℝ => ((2/3)*Real.log x+4/9)*x^(-(3/2):ℝ)) atTop (𝓝 0) := by
  have hp := tendsto_rpow_neg_atTop (show (0:ℝ) < 3/2 by norm_num)
  have hq := (isLittleO_log_rpow_atTop (show (0:ℝ) < 3/2 by norm_num)).tendsto_div_nhds_zero
  have hl : Tendsto (fun x : ℝ => Real.log x * x^(-(3/2):ℝ)) atTop (𝓝 0) := by
    apply hq.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    simp only [Real.rpow_neg hx.le, div_eq_mul_inv]
  have ht := (hl.const_mul (2/3:ℝ)).add (hp.const_mul (4/9:ℝ))
  simp only [mul_zero, add_zero] at ht
  apply ht.congr
  intro x
  ring

theorem solution
    (α : ℝ) (hα : 0 < α) (_hsmall : α < 1 / 2)
    (_hkernel :
      ∀ (β γ T : ℝ), 0 ≤ β → β ≤ 1 → 36 ≤ γ ^ 2 →
        let a := 3 - β
        let b := 5 / 2 - β
        let c0 := a / (a ^ 2 + γ ^ 2) - b / (b ^ 2 + γ ^ 2)
        let k := a / (a ^ 2 + (T - γ) ^ 2) - b / (b ^ 2 + γ ^ 2) + 8 * c0
        0 < k ∧ a / (a ^ 2 + (T - γ) ^ 2) ≤ k) :
    ∃ F : Set (ZetaZerosInTraceStrip (1 / 2)),
      F.Finite ∧
      (∀ ρ, |ρ.val.im| ^ 2 < 36 → ρ ∈ F) ∧
      ∃ fLow fHigh : ZetaZerosInTraceStrip (1 / 2) → ℝ,
        (∀ ρ, 0 ≤ fLow ρ) ∧
        (∀ ρ, 0 ≤ fHigh ρ) ∧
        (∀ ρ, ρ ∉ F → fLow ρ = 0) ∧
        (∀ ρ, ρ ∈ F → fHigh ρ = 0) ∧
        Summable fLow ∧ Summable fHigh ∧
        (regularizedTraceRHS α 3).re - (regularizedTraceRHS (1 / 2) 3).re =
          (∑' ρ, fLow ρ) + ∑' ρ, fHigh ρ := by
  classical
  let D := (regularizedTraceRHS (1/2) 3).re - (regularizedTraceRHS α 3).re
  let slack := fun k : ℕ => 1/(((k+3 : ℕ):ℝ)+1)
  let tail := fun n : ℕ => ((2/3)*Real.log n+4/9)*(n:ℝ)^(-(3/2):ℝ)
  have certificate (k : ℕ) : ∃ n : ℕ, k ≤ n ∧ 0 ≤ D ∧ D ≤ 2*(slack k + tail n) := by
    obtain ⟨N,hN,F,hF,hc⟩ := cofinal_approximate_prime_mass_certificates (k+3)
    have hprev : 2 ≤ N-1 := by omega
    have heq : N-1+1=N := by omega
    have hc' := finite_prime_certificate_controls_every_complex_trace_window (N-1) hprev (slack k) F hF
      (by rw [heq]; exact hc) α hα 3 (by norm_num)
    exact ⟨N-1,by omega,hc'.1,hc'.2.1⟩
  choose n hn hlo hhi using certificate
  have hnlim : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
  have ht : Tendsto (fun k => tail (n k)) atTop (𝓝 0) :=
    primeTail_tends_to_zero.comp (tendsto_natCast_atTop_atTop.comp hnlim)
  have hs : Tendsto slack atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 3)
  have hb := ((hs.add ht).const_mul (2:ℝ))
  simp only [zero_add, mul_zero] at hb
  have hD : D = 0 := le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds hb hhi) (hlo 0)
  refine ⟨∅, Set.finite_empty, ?_, fun _ => 0, fun _ => 0, fun _ => le_rfl, fun _ => le_rfl,
    fun _ _ => rfl, fun _ _ => rfl, summable_zero, summable_zero, ?_⟩
  · intro z hz
    rw [← low_height_trace_zero_set_empty]
    exact hz
  · simp only [tsum_zero, add_zero]
    dsimp [D] at hD
    linarith
