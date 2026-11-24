-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.EisTube.dom_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:45:20.576306+00:00
-- url     : https://prove2.me/submissions/4f804a83-ebe9-4100-afec-a9257191fa5a

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableExpNegSumAbs
import Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_norm_ker_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube
namespace GlobalTheory.CompanionTheory.EisTube
theorem _root_.solution {ι : Type} [Fintype ι] {P : Type u} {h : P → ℝ} (hh : ∀ p, 0 ≤ h p)
    {ψ : P → (ι → ℝ) → ℂ} {C B : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ p t, ‖ψ p t‖ ≤ C * h p * Real.exp (-(2 * Real.pi * ((B + 1) * ∑ i, |t i|))))
    {z : ι → ℂ} (hz : ∀ i, |(z i).re| ≤ B) (p : P) (t : ι → ℝ) :
    ‖ψ p t * ker z t‖ ≤ C * h p * Real.exp (-(2 * Real.pi * ∑ i, |t i|)) := by
  rw [norm_mul]
  calc ‖ψ p t‖ * ‖ker z t‖
      ≤ (C * h p * Real.exp (-(2 * Real.pi * ((B + 1) * ∑ i, |t i|)))) *
          Real.exp (2 * Real.pi * (B * ∑ i, |t i|)) :=
        mul_le_mul (hC p t) (norm_ker_le hz t) (norm_nonneg _)
          (mul_nonneg (mul_nonneg hC0 (hh p)) (Real.exp_pos _).le)
    _ = C * h p * Real.exp (-(2 * Real.pi * ∑ i, |t i|)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
end GlobalTheory.CompanionTheory.EisTube
