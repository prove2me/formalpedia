-- Prove2me | solution 1 for HighEntropyLimit.gaussian_entropy_zero_points
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:36:25.533054+00:00
-- url     : https://prove2.me/submissions/bf74b891-e5f4-4d76-8735-d1c614b3079b

import Mathlib
import Definitions.Def_HighEntropyLimit_gaussian_entropy

open HighEntropyLimit in
theorem solution (hbar : ℝ) (hhbar : 0 < hbar) :
    quantumGaussianEntropy hbar (hbar / 2) = 0 ∧
    (∀ Sig : ℝ, hbar / 2 < Sig → 0 < quantumGaussianEntropy hbar Sig) ∧
    classicalGaussianEntropy hbar (hbar / Real.exp 1) = 0 ∧
    (∀ Sig : ℝ, 0 < Sig → Sig < hbar / Real.exp 1 → classicalGaussianEntropy hbar Sig < 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold quantumGaussianEntropy
    rw [show hbar / 2 / hbar = 1 / 2 by field_simp]
    norm_num
  · intro Sig hS
    unfold quantumGaussianEntropy
    set u := Sig / hbar - 1 / 2 with hu
    have hu0 : 0 < u := by
      rw [hu, sub_pos, lt_div_iff₀ hhbar]; linarith
    have hv : Sig / hbar + 1 / 2 = u + 1 := by rw [hu]; ring
    rw [hv]
    -- (u+1) log(u+1) - u log u = u log((u+1)/u) + log(u+1) > 0
    have h1 : Real.log u < Real.log (u + 1) := Real.log_lt_log hu0 (by linarith)
    have h2 : 0 < Real.log (u + 1) := Real.log_pos (by linarith)
    nlinarith
  · unfold classicalGaussianEntropy
    rw [show hbar / Real.exp 1 / hbar = (Real.exp 1)⁻¹ by field_simp, Real.log_inv, Real.log_exp]
    ring
  · intro Sig hS hS2
    unfold classicalGaussianEntropy
    have h1 : Sig / hbar < (Real.exp 1)⁻¹ := by
      rw [div_lt_iff₀ hhbar]; calc Sig < hbar / Real.exp 1 := hS2
        _ = (Real.exp 1)⁻¹ * hbar := by ring
    have h2 : Real.log (Sig / hbar) < Real.log (Real.exp 1)⁻¹ :=
      Real.log_lt_log (div_pos hS hhbar) h1
    rw [Real.log_inv, Real.log_exp] at h2
    linarith
