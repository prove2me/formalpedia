-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.dyadic_holder_chaining
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T09:43:38.747761+00:00
-- url     : https://prove2.me/submissions/53593e1a-e4ab-4f37-9447-fd8f7f465659

import Definitions.Def_LevyStochCalc_Brownian_ContinuityDyadicChaining_F000
import Definitions.Def_LevyStochCalc_Brownian_ContinuityDyadicChaining_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Dyadic chaining for the Kolmogorov-Chentsov theorem

The deterministic half of the Kolmogorov-Chentsov construction. A function that is
`α`-Hölder on a dense set `D ⊆ ℝ` at scales `≤ δ₀` is uniformly continuous on `D` and so
extends continuously to `ℝ`; the dyadic rationals `{k · 2^(-n) : k ∈ ℤ, n ∈ ℕ}` are such a
dense set, and the level-`n` dyadic truncation `⌊x · 2^n⌋ / 2^n` approximates each real from
below. Chaining these truncations turns a bound `b n` on the consecutive level-`n` dyadic
increments of `f` into `α`-Hölder continuity of `f` on the dyadics of `[0, 1)`
(`dyadic_holder_chaining`), for `b n = C · 2^(-α n)`.

No probability enters here; the random increment bounds are supplied in
`LevyStochCalc.Brownian.ContinuityKolmogorovBounds`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Continuity

/-! ### Deterministic dyadic chaining

A real function whose consecutive level-`n` dyadic increments on `[0,1]` are
bounded by `b n` (with `∑ b n` controlled) is Hölder on the dyadics of `[0,1)`.
This is the path-by-path core of the continuous-modification construction: the
a.s. Borel–Cantelli increment bounds feed `b n = C · 2^(-α n)`. -/


theorem _root_.solution {f : ℝ → ℝ} {α C : ℝ} {N : ℕ}
    (hα : 0 < α) (hC : 0 ≤ C)
    (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ C * ((1 / 2 : ℝ) ^ α) ^ n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ dyadicRationals, ∀ t ∈ dyadicRationals,
      0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 → |s - t| ≤ (1 / 2 : ℝ) ^ N →
      |f s - f t| ≤ K * |s - t| ^ α := by
  set r : ℝ := (1 / 2 : ℝ) ^ α with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  set b : ℕ → ℝ := fun n => C * r ^ n with hbdef
  have hb : ∀ n, 0 ≤ b n := fun n => mul_nonneg hC (pow_nonneg hr0.le n)
  have hf' : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ b n := hf
  set K : ℝ := C * (2 / (1 - r) + 1) * 2 ^ α with hK
  have h1r : 0 < 1 - r := by linarith
  have hK0 : 0 ≤ K := by positivity
  -- main bound for s < t
  have main : ∀ s ∈ dyadicRationals, ∀ t ∈ dyadicRationals,
      0 ≤ s → t ≤ 1 → s < t → t - s ≤ (1 / 2 : ℝ) ^ N →
      |f s - f t| ≤ K * (t - s) ^ α := by
    intro s hs t ht hs0 ht1 hst hclose
    have hd0 : 0 < t - s := by linarith
    have hd1 : t - s ≤ 1 := hclose.trans (pow_le_one₀ (by norm_num) (by norm_num))
    obtain ⟨m, hm1, hm2⟩ := exists_dyadic_scale hd0 hd1
    have hNm : N ≤ m := by
      by_contra h
      push_neg at h
      have : (1 / 2 : ℝ) ^ N ≤ (1 / 2) ^ (m + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) h
      linarith
    obtain ⟨L₁, hL₁⟩ := dyadicTrunc_eventually_eq hs
    obtain ⟨L₂, hL₂⟩ := dyadicTrunc_eventually_eq ht
    set L := max (max L₁ L₂) m
    have hmL : m ≤ L := le_max_right _ _
    have eS := hL₁ L (le_trans (le_max_left _ _) (le_max_left _ _))
    have eT := hL₂ L (le_trans (le_max_right _ _) (le_max_left _ _))
    have tS := dyadicTrunc_telescope hb hf' hs0 (by linarith) (m := m) (by omega) L hmL
    have tT := dyadicTrunc_telescope hb hf' (by linarith) ht1 (m := m) (by omega) L hmL
    have nS := dyadicTrunc_near_step hb hf' hNm hs0 ht1 hst.le hm2
    rw [eS] at tS
    rw [eT] at tT
    have hsum : ∑ n ∈ Finset.Ico (m + 1) (L + 1), b n ≤ C * (r ^ (m + 1) / (1 - r)) := by
      simp only [hbdef]
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_Ico_geometric_le hr0.le hr1 _ _) hC
    have hrm : r ^ (m + 1) ≤ r ^ m := pow_le_pow_of_le_one hr0.le hr1.le (by omega)
    have hgeo : C * (r ^ (m + 1) / (1 - r)) ≤ C * (r ^ m / (1 - r)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hrm h1r.le) hC
    have hrp := rpow_half_pow_le hα m hm1
    have htot : |f s - f t| ≤ C * (2 / (1 - r) + 1) * r ^ m := by
      have e : f s - f t = (f s - f (dyadicTrunc m s)) + (f (dyadicTrunc m s) - f (dyadicTrunc m t))
          + (f (dyadicTrunc m t) - f t) := by ring
      rw [e]
      have a1 := abs_add_le (f s - f (dyadicTrunc m s) + (f (dyadicTrunc m s) - f (dyadicTrunc m t)))
        (f (dyadicTrunc m t) - f t)
      have a2 := abs_add_le (f s - f (dyadicTrunc m s)) (f (dyadicTrunc m s) - f (dyadicTrunc m t))
      rw [abs_sub_comm (f (dyadicTrunc m t)) (f t)] at a1
      have : C * (2 / (1 - r) + 1) * r ^ m = 2 * (C * (r ^ m / (1 - r))) + C * r ^ m := by
        field_simp
      rw [this]
      have nS' : |f (dyadicTrunc m s) - f (dyadicTrunc m t)| ≤ C * r ^ m := nS
      linarith
    calc |f s - f t| ≤ C * (2 / (1 - r) + 1) * r ^ m := htot
      _ ≤ C * (2 / (1 - r) + 1) * ((2 : ℝ) ^ α * (t - s) ^ α) :=
          mul_le_mul_of_nonneg_left hrp (by positivity)
      _ = K * (t - s) ^ α := by rw [hK]; ring
  refine ⟨K, hK0, fun s hs t ht hs0 hs1 ht0 ht1 hclose => ?_⟩
  rcases lt_trichotomy s t with h | h | h
  · rw [abs_of_neg (by linarith : s - t < 0), neg_sub] at hclose ⊢
    exact main s hs t ht hs0 ht1 h hclose
  · subst h; simp [Real.zero_rpow hα.ne']
  · rw [abs_of_pos (by linarith : 0 < s - t)] at hclose ⊢
    rw [abs_sub_comm]
    exact main t ht s hs ht0 hs1 h hclose

end LevyStochCalc.Brownian.Continuity
