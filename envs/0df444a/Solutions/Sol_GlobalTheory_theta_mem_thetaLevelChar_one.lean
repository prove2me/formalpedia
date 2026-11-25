-- Prove2me | solution 1 for GlobalTheory.theta_mem_thetaLevelChar_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:12:28.106696+00:00
-- url     : https://prove2.me/submissions/7f658ac4-3f05-4e4c-a113-312e77fc12f8

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Theorems.Thm_GlobalTheory_levelTheta_one

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
theorem _root_.solution (hτ : τ ∈ SiegelH ι) :
    (fun z => theta a b z τ) ∈ thetaLevelChar a b 1 τ :=
  levelTheta_one (a := a) (b := b) (τ := τ) ▸ levelTheta_mem hτ one_pos 0
end GlobalTheory
