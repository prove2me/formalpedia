-- Prove2me | solution 1 for GlobalTheory.thetaLevelChar_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:10:46.966244+00:00
-- url     : https://prove2.me/submissions/aea77da2-8b32-4f4e-8085-42379d5dd025

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
    thetaLevelChar a b 1 τ = Submodule.span ℂ {fun z => theta a b z τ} := by
  rw [← span_levelTheta hτ one_pos (r := fun _ : Unit => 0)
    ⟨fun _ _ _ => rfl, fun c => ⟨(), Subsingleton.elim _ _⟩⟩, levelTheta_one, Set.range_const]
end GlobalTheory
