-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.quotSum_def
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:03:14.694968+00:00
-- url     : https://prove2.me/submissions/0449c5b4-a6ae-4be7-a300-a3d35caa0d35

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SupercuspidalCoefficients
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingSums

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
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Function
open scoped Pointwise
variable {G : Type*} [Group G] (H : Subgroup G) {M : Type*} [AddCommMonoid M]
variable {H}
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (Φ : G → M) : quotSum H Φ = ∑ᶠ q : G ⧸ H, Φ q.out := rfl
end GroundTheory.Automorphic.Parabolic
