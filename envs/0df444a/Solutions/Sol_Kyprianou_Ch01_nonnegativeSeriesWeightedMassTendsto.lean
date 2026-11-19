-- Prove2me | solution 1 for Kyprianou.Ch01.nonnegativeSeriesWeightedMassTendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T10:06:56.50797+00:00
-- url     : https://prove2.me/submissions/2ea417c5-3065-462b-abd9-000264e23217

import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Order.Basic
import Theorems.Thm_Kyprianou_Ch01_nonnegativeSeriesMinWeightedBounds
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped Topology BigOperators
set_option autoImplicit false

/-- Discrete Scheffe: pointwise and total nonnegative mass convergence
    control every bounded, nonnegative fixed weighting. -/
theorem solution
    {α : Type*} {F : Filter α} [NeBot F]
    (a : α → ℕ → ℝ) (b w : ℕ → ℝ)
    (ha : ∀ᶠ t in F, ∀ k, 0 ≤ a t k)
    (hasum : ∀ᶠ t in F, Summable (a t))
    (hb : ∀ k, 0 ≤ b k) (hbsum : Summable b)
    (hw : ∀ k, 0 ≤ w k ∧ w k ≤ 1)
    (hpoint : ∀ k, Tendsto (fun t => a t k) F (nhds (b k)))
    (hmass : Tendsto (fun t => ∑' k, a t k) F
      (nhds (∑' k, b k))) :
    Tendsto (fun t => ∑' k, a t k * w k) F
      (nhds (∑' k, b k * w k)) := by
  have hminlim (v : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k ∧ v k ≤ 1) :
      Tendsto (fun t => ∑' k, min (a t k) (b k) * v k) F
        (nhds (∑' k, b k * v k)) := by
    apply tendsto_tsum_of_dominated_convergence hbsum
    · intro k
      simpa only [min_self] using
        ((hpoint k).min (tendsto_const_nhds :
          Tendsto (fun _ : α => b k) F (𝓝 (b k)))).mul_const (v k)
    · filter_upwards [ha] with t ht k
      have h0 : 0 ≤ min (a t k) (b k) := le_min (ht k) (hb k)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (hv k).1)]
      calc
        min (a t k) (b k) * v k ≤ b k * v k :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (hv k).1
        _ ≤ b k * 1 := mul_le_mul_of_nonneg_left (hv k).2 (hb k)
        _ = b k := mul_one _
  have hminW := hminlim w hw
  have hminMass := hminlim (fun _ => (1 : ℝ))
    (fun _ => ⟨by norm_num, by norm_num⟩)
  simp only [mul_one] at hminMass
  have hbounds (t : α) (hat : ∀ k, 0 ≤ a t k)
      (hatSum : Summable (a t)) :
      (∑' k, min (a t k) (b k) * w k) ≤
        (∑' k, a t k * w k) ∧
      (∑' k, a t k * w k) ≤
        (∑' k, min (a t k) (b k) * w k) +
          (∑' k, a t k) - (∑' k, min (a t k) (b k)) :=
    Kyprianou.Ch01.nonnegativeSeriesMinWeightedBounds (a t) b w
      hat hatSum hb hbsum hw
  have hlow : ∀ᶠ t in F,
      (∑' k, min (a t k) (b k) * w k) ≤
        (∑' k, a t k * w k) := by
    filter_upwards [ha, hasum] with t ht hs
    exact (hbounds t ht hs).1
  have hhigh : ∀ᶠ t in F,
      (∑' k, a t k * w k) ≤
        (∑' k, min (a t k) (b k) * w k) +
          (∑' k, a t k) - (∑' k, min (a t k) (b k)) := by
    filter_upwards [ha, hasum] with t ht hs
    exact (hbounds t ht hs).2
  have hu := hminW.add (hmass.sub hminMass)
  have hu' : Tendsto
      (fun t => (∑' k, min (a t k) (b k) * w k) +
        (∑' k, a t k) - (∑' k, min (a t k) (b k))) F
      (nhds (∑' k, b k * w k)) := by
    simpa [sub_eq_add_neg, add_assoc] using hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hminW hu' hlow hhigh
