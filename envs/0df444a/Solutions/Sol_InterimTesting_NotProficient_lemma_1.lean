-- Prove2me | solution 1 for InterimTesting.NotProficient.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T02:43:44.242122+00:00
-- url     : https://prove2.me/submissions/dc4a509e-6c27-412e-ad7e-1fb3881fd5f1

import Mathlib
import Definitions.Def_InterimTesting_NotProficient_Model

open InterimTesting.NotProficient in
theorem solution (θ : Params) (hθ : θ.Standing) (π p : ℝ) (hπ : 0 ≤ π)
    (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    e1Star θ π p = if T1p θ p ≤ π then 1 else 0 := by
  obtain ⟨hA, hB, hAB, hμ0, hμ1, hN, hNP, hP1⟩ := hθ
  have hk : 0 < (1 - θ.μ) * p + θ.μ := by nlinarith [hp.1]
  have hAk : 0 < θ.A * ((1 - θ.μ) * p + θ.μ) := mul_pos hA hk
  have hobj : ∀ e, obj1 θ π p e = π * ((1 - θ.μ) * p + θ.μ) * θ.B
      + (π * ((1 - θ.μ) * p + θ.μ) * θ.A - 1) * e := by
    intro e; simp only [obj1, finalP, toP]; ring
  unfold e1Star
  split_ifs with h
  · have hs : 0 ≤ π * ((1 - θ.μ) * p + θ.μ) * θ.A - 1 := by
      unfold T1p at h; rw [div_le_iff₀ hAk] at h; nlinarith
    apply IsGreatest.csSup_eq
    refine ⟨⟨⟨zero_le_one, le_rfl⟩, fun e' he' => ?_⟩, fun e he => he.1.2⟩
    rw [hobj, hobj]; nlinarith [he'.2]
  · have hs : π * ((1 - θ.μ) * p + θ.μ) * θ.A - 1 < 0 := by
      unfold T1p at h; push_neg at h; rw [lt_div_iff₀ hAk] at h; nlinarith
    apply IsGreatest.csSup_eq
    refine ⟨⟨⟨le_rfl, zero_le_one⟩, fun e' he' => ?_⟩, fun e he => ?_⟩
    · rw [hobj, hobj]; nlinarith [he'.1]
    · have := he.2 0 ⟨le_rfl, zero_le_one⟩
      rw [hobj, hobj] at this
      nlinarith [he.1.1]
