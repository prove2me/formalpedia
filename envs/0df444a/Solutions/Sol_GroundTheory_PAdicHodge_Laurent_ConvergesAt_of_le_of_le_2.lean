-- Prove2me | solution 2 for GroundTheory.PAdicHodge.Laurent.ConvergesAt.of_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:49:42.435569+00:00
-- url     : https://prove2.me/submissions/e221ede8-ca60-43b1-977c-395a47fa6cc8

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
import Theorems.Thm_GroundTheory_PAdicHodge_Laurent_ConvergesAt_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Filter Topology
open GroundTheory.PAdicHodge.Laurent
set_option linter.unusedSectionVars false
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {a b c : ℤ → K} {ρ : ℝ}
namespace GroundTheory.PAdicHodge.Laurent
namespace ConvergesAt
theorem _root_.solution {ρ₁ ρ₂ : ℝ} (h₁ : ConvergesAt a ρ₁) (h₂ : ConvergesAt a ρ₂)
    (hρ₁ : 0 < ρ₁) (h1 : ρ₁ ≤ ρ) (h2 : ρ ≤ ρ₂) : ConvergesAt a ρ := by
  have hρ : 0 < ρ := hρ₁.trans_le h1
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) (by simpa using Tendsto.add h₁ h₂)
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rcases le_total 0 n with hn | hn
  · have := zpow_le_zpow_left₀ hn hρ.le h2
    have : 0 ≤ ρ₁ ^ n := by positivity
    linarith
  · have h3 : ρ ^ n ≤ ρ₁ ^ n := by
      rw [show ρ ^ n = (ρ ^ (-n))⁻¹ by rw [zpow_neg, inv_inv],
        show ρ₁ ^ n = (ρ₁ ^ (-n))⁻¹ by rw [zpow_neg, inv_inv]]
      exact inv_anti₀ (by positivity) (zpow_le_zpow_left₀ (neg_nonneg.2 hn) hρ₁.le h1)
    have hρ₂ : 0 < ρ₂ := by linarith
    have : 0 ≤ ρ₂ ^ n := by positivity
    linarith
end ConvergesAt
end GroundTheory.PAdicHodge.Laurent
