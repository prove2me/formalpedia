-- Prove2me | solution 1 for LowerFareFirst.Critical.note2b_critical_sign
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:10:29.412908+00:00
-- url     : https://prove2.me/submissions/be63cd70-31ab-413f-ad93-33593964328c

import Mathlib
import Definitions.Def_LowerFareFirst_Critical_Model

set_option autoImplicit false

open MeasureTheory LowerFareFirst.Critical

theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : ℕ → Ω → ℕ) (r : ℕ → ℝ) (m k : ℕ) (hm : 2 ≤ m)
    (hdec : ∀ n : ℕ, 1 ≤ n → dZ μ D r (m - 1) (n + 1) ≤ dZ μ D r (m - 1) n)
    (hk : IsCriticalValue μ D r m k) :
    (∀ n : ℕ, 1 ≤ n → n ≤ k → r m < dZ μ D r (m - 1) n) ∧
      (∀ n : ℕ, k + 1 ≤ n → dZ μ D r (m - 1) n ≤ r m) := by
  obtain ⟨⟨hk1, hkr⟩, hkmax⟩ := hk
  refine ⟨fun n hn hnk => ?_, fun n hn => ?_⟩
  · have key : ∀ d n : ℕ, 1 ≤ n → n + d = k →
        dZ μ D r (m - 1) k ≤ dZ μ D r (m - 1) n := by
      intro d
      induction d with
      | zero => intro n _ h; simp at h; rw [h]
      | succ d ih =>
        intro n hn h
        exact (ih (n + 1) (by omega) (by omega)).trans (hdec n hn)
    exact lt_of_lt_of_le hkr (key (k - n) n hn (by omega))
  · by_contra hcon
    push_neg at hcon
    have := hkmax ⟨by omega, hcon⟩
    omega
