-- Prove2me | solution 1 for LNChannels.SmallRate.alpha_small_rate
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T21:07:35.870767+00:00
-- url     : https://prove2.me/submissions/d4e151a9-0e73-4347-b378-252d8318e855

import Mathlib
import Definitions.Def_LNChannels_Exact_alphaPlus
import Definitions.Def_LNChannels_Exact_alphaMinus

set_option autoImplicit false
open Filter Asymptotics

namespace LNSHelp

lemma key (lam r : ℝ) (hlam : 0 < lam) (hr : 0 < r) :
    ∃ e : ℝ, 0 ≤ e ∧ e ≤ (1 / (8 * Real.sqrt lam ^ 3)) * r ^ (3 / 2 : ℝ) ∧
      LNChannels.Exact.alphaPlus lam lam r - (1 + Real.sqrt (r / lam) + r / (2 * lam)) = e ∧
      LNChannels.Exact.alphaMinus lam lam r - (1 - Real.sqrt (r / lam) + r / (2 * lam)) = -e := by
  obtain ⟨σ, hσ, hσ2, hσdef⟩ : ∃ σ : ℝ, 0 < σ ∧ σ ^ 2 = lam ∧ σ = Real.sqrt lam :=
    ⟨Real.sqrt lam, Real.sqrt_pos.2 hlam, Real.sq_sqrt hlam.le, rfl⟩
  obtain ⟨ρ, hρ, hρ2, hρdef⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ^ 2 = r ∧ ρ = Real.sqrt r :=
    ⟨Real.sqrt r, Real.sqrt_pos.2 hr, Real.sq_sqrt hr.le, rfl⟩
  have hq : Real.sqrt (r / lam) = ρ / σ := by
    rw [Real.sqrt_div hr.le, ← hρdef, ← hσdef]
  have hr32 : r ^ (3 / 2 : ℝ) = ρ ^ 3 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hr, Real.rpow_one,
      ← Real.sqrt_eq_rpow, ← hρdef, ← hρ2]
    ring
  obtain ⟨w, hw0, hw2, hwdef⟩ : ∃ w : ℝ, 0 ≤ w ∧ w ^ 2 = ρ ^ 2 + 4 * σ ^ 2 ∧
      w = Real.sqrt (ρ ^ 2 + 4 * σ ^ 2) :=
    ⟨Real.sqrt (ρ ^ 2 + 4 * σ ^ 2), Real.sqrt_nonneg _, Real.sq_sqrt (by positivity), rfl⟩
  have hw2s : 2 * σ ≤ w := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hsq : Real.sqrt (r ^ 2 + 4 * r * lam) = ρ * w := by
    have : r ^ 2 + 4 * r * lam = (ρ * w) ^ 2 := by
      rw [mul_pow, hw2, ← hρ2, ← hσ2]; ring
    rw [this]
    exact Real.sqrt_sq (by positivity)
  have hwb : w - 2 * σ ≤ ρ ^ 2 / (4 * σ) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (w - 2 * σ)]
  refine ⟨ρ * (w - 2 * σ) / (2 * σ ^ 2), ?_, ?_, ?_, ?_⟩
  · exact div_nonneg (mul_nonneg hρ.le (by linarith)) (by positivity)
  · rw [← hσdef, hr32]
    calc ρ * (w - 2 * σ) / (2 * σ ^ 2) ≤ ρ * (ρ ^ 2 / (4 * σ)) / (2 * σ ^ 2) := by gcongr
      _ = 1 / (8 * σ ^ 3) * ρ ^ 3 := by field_simp; ring
  · unfold LNChannels.Exact.alphaPlus
    have h : (lam - lam) ^ 2 + r ^ 2 + 2 * r * (lam + lam) = r ^ 2 + 4 * r * lam := by ring
    rw [h, hsq, hq]
    subst hρ2 hσ2
    field_simp
    ring
  · unfold LNChannels.Exact.alphaMinus
    have h : (lam - lam) ^ 2 + r ^ 2 + 2 * r * (lam + lam) = r ^ 2 + 4 * r * lam := by ring
    rw [h, hsq, hq]
    subst hρ2 hσ2
    field_simp
    ring

end LNSHelp

theorem solution (lam : ℝ) (hlam : 0 < lam) :
    (∀ r : ℝ, 0 < r →
      LNChannels.Exact.alphaPlus lam lam r = 1 + (r + Real.sqrt (r ^ 2 + 4 * r * lam)) / (2 * lam) ∧
      LNChannels.Exact.alphaMinus lam lam r = 1 + (r - Real.sqrt (r ^ 2 + 4 * r * lam)) / (2 * lam)) ∧
    (fun r : ℝ => LNChannels.Exact.alphaPlus lam lam r -
      (1 + Real.sqrt (r / lam) + r / (2 * lam)))
      =O[nhdsWithin 0 (Set.Ioi 0)] (fun r : ℝ => r ^ (3 / 2 : ℝ)) ∧
    (fun r : ℝ => LNChannels.Exact.alphaMinus lam lam r -
      (1 - Real.sqrt (r / lam) + r / (2 * lam)))
      =O[nhdsWithin 0 (Set.Ioi 0)] (fun r : ℝ => r ^ (3 / 2 : ℝ)) := by
  have hl : lam ≠ 0 := hlam.ne'
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    have h : (lam - lam) ^ 2 + r ^ 2 + 2 * r * (lam + lam) = r ^ 2 + 4 * r * lam := by ring
    constructor
    · unfold LNChannels.Exact.alphaPlus
      rw [h]; field_simp; ring
    · unfold LNChannels.Exact.alphaMinus
      rw [h]; field_simp; ring
  · refine IsBigO.of_bound (1 / (8 * Real.sqrt lam ^ 3)) ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    obtain ⟨e, he0, heb, h1, h2⟩ := LNSHelp.key lam r hlam hr
    rw [h1, Real.norm_eq_abs, abs_of_nonneg he0, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hr _)]
    exact heb
  · refine IsBigO.of_bound (1 / (8 * Real.sqrt lam ^ 3)) ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    obtain ⟨e, he0, heb, h1, h2⟩ := LNSHelp.key lam r hlam hr
    rw [h2, norm_neg, Real.norm_eq_abs, abs_of_nonneg he0, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hr _)]
    exact heb
