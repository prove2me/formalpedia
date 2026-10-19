-- Prove2me | solution 1 for GoodmanWitten.lower_mass_limit_aluminium
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:50:13.43986+00:00
-- url     : https://prove2.me/submissions/98fee12a-a8c4-498f-b9e3-d06b53d59351

import Mathlib
import Definitions.Def_GoodmanWitten_basic
open GoodmanWitten

theorem solution (ε : ℝ) (hε₁ : 50e-9 ≤ ε) (hε₂ : ε ≤ 100e-9) :
    ∃ mmin : ℝ, 1 ≤ mmin ∧ mmin ≤ 2 ∧
      ∀ m : ℝ, 0 < m →
        (ε ≤ maxRecoilEnergy m (nucleusMass 27) (2e7 / speedOfLight) ↔ mmin ≤ m) := by
  set M := nucleusMass 27 with hMdef
  set v := 2e7 / speedOfLight with hvdef
  have hM : M = 27 * 0.9383 := by rw [hMdef]; unfold nucleusMass nucleonMass; norm_num
  have hv : v = 2e7 / 2.99792458e10 := by rw [hvdef]; unfold speedOfLight; rfl
  have hMp : 0 < M := by rw [hM]; norm_num
  have hvp : 0 < v := by rw [hv]; norm_num
  refine ⟨Real.sqrt (2 * M * ε) / (2 * v), ?_, ?_, fun m hm => ?_⟩
  · rw [le_div_iff₀ (by positivity), one_mul, Real.le_sqrt (by positivity) (by positivity), hM, hv]
    nlinarith
  · rw [div_le_iff₀ (by positivity), Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [hM, hv]
    nlinarith
  · unfold maxRecoilEnergy
    rw [le_div_iff₀ (by positivity), div_le_iff₀ (by positivity),
      Real.sqrt_le_iff]
    constructor
    · intro h; exact ⟨by positivity, by nlinarith⟩
    · intro h; nlinarith [h.2]
