-- Prove2me | solution 1 for GroundTheory.Automorphic.coe_polarExpHomeomorphReal_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:44:45.822078+00:00
-- url     : https://prove2.me/submissions/c3715766-c3b2-4860-b718-44141c48983d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsPolar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
namespace GroundTheory.Automorphic
theorem _root_.solution
    (kX : unitaryGroup n ℝ × {X : Matrix n n ℝ // X.IsHermitian}) :
    ((polarExpHomeomorphReal kX : GL n ℝ) : Matrix n n ℝ) = kX.1 * NormedSpace.exp kX.2.1 :=
  rfl
end GroundTheory.Automorphic
