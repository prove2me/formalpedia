-- Prove2me | solution 1 for GlobalTheory.mul_mem_thetaLevelChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:16:40.136815+00:00
-- url     : https://prove2.me/submissions/199fd480-f15c-4dc2-b0da-6bca49e9802c

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Theorems.Thm_GlobalTheory_mem_thetaLevelChar_iff_autFactor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open GlobalTheory
variable {ι : Type} [Fintype ι]
variable {N M : ℕ} {τ : Matrix ι ι ℂ} {a b : ι → ℝ} {f g : (ι → ℂ) → ℂ}
namespace GlobalTheory
theorem _root_.solution (hf : f ∈ thetaLevelChar a b N τ)
    (hg : g ∈ thetaLevelChar a b M τ) : f * g ∈ thetaLevelChar a b (N + M) τ := by
  rw [mem_thetaLevelChar_iff_autFactor] at *
  exact ⟨hf.1.mul hg.1, fun n n' z => by simp only [Pi.mul_apply, hf.2, hg.2]; ring⟩
end GlobalTheory
