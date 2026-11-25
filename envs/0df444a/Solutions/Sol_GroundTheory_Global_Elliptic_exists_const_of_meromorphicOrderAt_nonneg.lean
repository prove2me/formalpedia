-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.exists_const_of_meromorphicOrderAt_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:18:59.133329+00:00
-- url     : https://prove2.me/submissions/7beb5f91-ebb9-45e9-8f78-7ab784978e06

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Theorems.Thm_GroundTheory_Global_Elliptic_limPunctured_eq_of_continuousAt
import Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_limPunctured
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_limPunctured_add
import Theorems.Thm_GroundTheory_Global_Elliptic_eq_of_differentiable_of_isPeriodic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {E : Type*} [NormedAddCommGroup E]
variable [NormedSpace ℂ E]
variable {L : PeriodPair}
variable (L)
namespace GroundTheory.Global.Elliptic
theorem _root_.solution [CompleteSpace E] {f : ℂ → E} (hf : Meromorphic f)
    (hp : IsPeriodic L f) (ho : ∀ z, 0 ≤ meromorphicOrderAt f z) :
    ∃ c : E, ∀ z, AnalyticAt ℂ f z → f z = c := by
  have hd : Differentiable ℂ (limPunctured f) := fun z ↦
    (analyticAt_limPunctured (hf z) (ho z)).differentiableAt
  have hFp : IsPeriodic L (limPunctured f) := fun z l hl ↦
    hp.limPunctured_add hl (hf z) (ho z)
  refine ⟨limPunctured f 0, fun z hz ↦ ?_⟩
  rw [← limPunctured_eq_of_continuousAt hz.continuousAt]
  exact eq_of_differentiable_of_isPeriodic L hd hFp z 0
end GroundTheory.Global.Elliptic
