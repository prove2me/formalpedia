-- Prove2me | solution 1 for ImpulsiveISS.FixedDwell.descent_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:14:33.825667+00:00
-- url     : https://prove2.me/submissions/008355a5-2ada-488f-bf40-709090d4a2d7

import Mathlib
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_DiniDerivative
import Definitions.Def_ImpulsiveISS_FixedDwell_Setting

open scoped NNReal
open Filter Topology
open SmallGainISS.Lyapunov ProcessingNetworks.LyapunovCriteria

open ImpulsiveISS.FixedDwell in
theorem solution (φ : ℝ≥0 → ℝ≥0) (hφ : IsPosDef φ) (r : ℝ) (hr : 0 < r)
    (δ : ℝ) (hδ : 0 < δ) (z : ℕ → ℝ) (hz : ∀ i, 0 < z i)
    (hdesc : ∀ i, Fint φ r (z (i + 1)) ≤ Fint φ r (z i) - δ) :
    Tendsto z atTop (𝓝 0) := by
  set g : ℝ → ℝ := fun s => 1 / (φ s.toNNReal : ℝ) with hg
  have hg0 : ∀ s, 0 ≤ g s := fun s => by
    simp only [hg]; positivity
  have hint : ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable g MeasureTheory.volume a b := by
    intro a b ha hb
    apply ContinuousOn.intervalIntegrable
    have hpos : ∀ s ∈ Set.uIcc a b, 0 < s := by
      intro s hs
      rcases Set.mem_uIcc.mp hs with h | h
      · linarith [h.1]
      · linarith [h.1]
    apply ContinuousOn.div continuousOn_const
    · exact (NNReal.continuous_coe.comp (hφ.1.comp continuous_real_toNNReal)).continuousOn
    · intro s hs
      have hs0 := hpos s hs
      rw [NNReal.coe_ne_zero]
      intro h
      have := (hφ.2 _).mp h
      rw [Real.toNNReal_eq_zero] at this
      linarith
  have hF : ∀ q : ℝ, Fint φ r q = ∫ s in r..q, g s := fun q => rfl
  have hmono : ∀ ε q : ℝ, 0 < ε → ε ≤ q → Fint φ r ε ≤ Fint φ r q := by
    intro ε q hε hq
    rw [hF, hF, ← intervalIntegral.integral_add_adjacent_intervals (hint r ε hr hε)
      (hint ε q hε (by linarith))]
    have : 0 ≤ ∫ s in ε..q, g s := intervalIntegral.integral_nonneg hq (fun s _ => hg0 s)
    linarith
  have hiter : ∀ i : ℕ, Fint φ r (z i) ≤ Fint φ r (z 0) - i * δ := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have := hdesc i
      push_cast
      linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((Fint φ r (z 0) - Fint φ r ε) / δ)
  refine ⟨N, fun i hi => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_pos (hz i)]
  by_contra hge
  push_neg at hge
  have h1 := hmono ε (z i) hε hge
  have h2 := hiter i
  have hNi : (N : ℝ) ≤ i := by exact_mod_cast hi
  rw [div_lt_iff₀ hδ] at hN
  nlinarith
