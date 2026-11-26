-- Prove2me | solution 1 for Kyprianou.Ch04.positiveSecantProbabilityFull
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:42:34.994306+00:00
-- url     : https://prove2.me/submissions/077dfa2b-8d0f-49a0-8fac-24fcda039b16

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- A positive infimum of secants and the transform bound force full mass. -/
theorem solution
    (f : ℝ → ℝ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hm : 0 < max 0 (sInf ((fun b : ℝ => f b / b) '' Ioi 0)))
    (hbound : ∀ b : ℝ, 0 < b →
      max 0 (sInf ((fun b : ℝ => f b / b) '' Ioi 0)) * b / f b ≤ p) :
    p = 1 := by
  let S := (fun b : ℝ => f b / b) '' Ioi 0
  let m := sInf S
  change 0 < max 0 m at hm
  have hm' : 0 < m := (lt_max_iff.mp hm).resolve_left (lt_irrefl 0)
  have hmax : max 0 m = m := max_eq_right hm'.le
  have hbd : BddBelow S := by
    by_contra h
    have hz : m = 0 := Real.sInf_of_not_bddBelow h
    linarith
  have hne : S.Nonempty := ⟨f 1 / 1,1,by norm_num,rfl⟩
  have hs (b : ℝ) (hb : 0 < b) : m ≤ f b / b := csInf_le hbd ⟨b,hb,rfl⟩
  have hf (b : ℝ) (hb : 0 < b) : 0 < f b := by
    have h := hm'.trans_le (hs b hb)
    simpa using (lt_div_iff₀ hb).1 h
  have hp : 0 < p := by
    have h := hbound 1 (by norm_num)
    change max 0 m * 1 / f 1 ≤ p at h
    rw [hmax] at h
    exact (div_pos (mul_pos hm' (by norm_num)) (hf 1 (by norm_num))).trans_le h
  have hlower : ∀ y ∈ S, m / p ≤ y := by
    rintro y ⟨b,hb,rfl⟩
    have h := hbound b hb
    change max 0 m * b / f b ≤ p at h
    rw [hmax] at h
    have h' := (div_le_iff₀ (hf b hb)).1 h
    change 0 < b at hb
    change m / p ≤ f b / b
    apply (div_le_iff₀ hp).2
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hb).2
    nlinarith
  have hle := le_csInf hne hlower
  have h := (div_le_iff₀ hp).1 hle
  nlinarith
