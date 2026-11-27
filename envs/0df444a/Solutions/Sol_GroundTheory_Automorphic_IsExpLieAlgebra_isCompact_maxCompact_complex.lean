-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.isCompact_maxCompact_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:44:16.31514+00:00
-- url     : https://prove2.me/submissions/d7fabc70-dc2d-4cf6-92bb-9422c2696f79

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_isClosed
import Theorems.Thm_GroundTheory_Automorphic_isCompact_maxCompact_of_isClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology NormedSpace
open scoped NNReal ENNReal
set_option linter.unusedSectionVars false
open Matrix
open scoped Matrix.Norms.L2Operator
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Automorphic
namespace IsExpLieAlgebra
theorem _root_.solution {G : Subgroup (Matrix ι ι ℂ)ˣ}
    {𝔤 : Submodule ℝ (Matrix ι ι ℂ)} (h : IsExpLieAlgebra G 𝔤) :
    IsCompact ((maxCompact G : Subgroup G) : Set G) :=
  isCompact_maxCompact_of_isClosed h.isClosed
end IsExpLieAlgebra
end GroundTheory.Automorphic
