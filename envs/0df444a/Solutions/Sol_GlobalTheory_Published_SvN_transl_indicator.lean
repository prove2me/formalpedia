-- Prove2me | solution 1 for GlobalTheory.Published.SvN.transl_indicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:40:03.857677+00:00
-- url     : https://prove2.me/submissions/bcd2762c-d01e-4259-b9bd-2e1e6b22457a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
variable {W M : Type} [AddCommGroup W] [AddCommGroup M] [Module ℂ M]
variable {c : W → W → ℂ}
variable {ρ : W → Module.End ℂ M}
variable {A : AddSubgroup W} {α : W → ℂ}
namespace GlobalTheory.Published.SvN
theorem _root_.solution (hα : Splits c A α) (a : W) (ha : a ∈ A) :
    transl c a ((A : Set W).indicator α) = α a • (A : Set W).indicator α := by
  funext z
  show c z a * (A : Set W).indicator α (z + a) = α a * (A : Set W).indicator α z
  by_cases hz : z ∈ A
  · rw [Set.indicator_of_mem (A.add_mem hz ha), Set.indicator_of_mem hz, mul_comm (α a), hα.mul z hz a ha]
  · have : z + a ∉ A := fun h => hz (by simpa using A.sub_mem h ha)
    simp [hz, this]
end GlobalTheory.Published.SvN
