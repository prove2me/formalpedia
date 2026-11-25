-- Prove2me | solution 1 for GlobalTheory.pow_mem_thetaLevelChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:31:26.714187+00:00
-- url     : https://prove2.me/submissions/6d3965af-1044-4e53-ba61-aec820811b28

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Theorems.Thm_GlobalTheory_prod_mem_thetaLevelChar

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
theorem _root_.solution (hf : f ∈ thetaLevelChar a b N τ) (k : ℕ) :
    f ^ k ∈ thetaLevelChar a b (k * N) τ := by
  simpa using prod_mem_thetaLevelChar (Finset.range k) (d := fun _ => N) (F := fun _ => f)
    fun _ _ => hf
end GlobalTheory
