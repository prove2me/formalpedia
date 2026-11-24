-- Prove2me | solution 1 for GlobalTheory.hasFDerivAt_Hf_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:58:23.950976+00:00
-- url     : https://prove2.me/submissions/2f33cd1a-a97c-42ab-acc0-40d145b4e6d5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelThreeSeparatesTangents

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2 Filter Topology
open GlobalTheory
variable {ι : Type} [Fintype ι]
namespace GlobalTheory
theorem _root_.solution (γ v : EuclideanSpace ℂ ι) :
    ∃ A : EuclideanSpace ℂ ι →L[ℂ] ℂ, (∀ c, A c = Hf c γ) ∧ HasFDerivAt (fun v => Hf v γ) A v := by
  have h : ∀ c : EuclideanSpace ℂ ι, innerSL ℂ γ c = Hf c γ := fun c => by
    simp [Hf, PiLp.inner_apply]
  refine ⟨innerSL ℂ γ, h, ?_⟩
  have : (fun v => Hf v γ) = innerSL ℂ γ := by funext v; exact (h v).symm
  rw [this]
  exact (innerSL ℂ γ).hasFDerivAt
end GlobalTheory
