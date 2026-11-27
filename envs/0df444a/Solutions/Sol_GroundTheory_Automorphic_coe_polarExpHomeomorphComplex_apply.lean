-- Prove2me | solution 1 for GroundTheory.Automorphic.coe_polarExpHomeomorphComplex_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:44:43.313823+00:00
-- url     : https://prove2.me/submissions/37c8bcde-d66b-4d02-aff6-69902ee0c742

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
    (kX : unitaryGroup n ℂ × {X : Matrix n n ℂ // X.IsHermitian}) :
    ((polarExpHomeomorphComplex kX : GL n ℂ) : Matrix n n ℂ) = kX.1 * NormedSpace.exp kX.2.1 :=
  rfl
end GroundTheory.Automorphic
