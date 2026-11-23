-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:16:54.25557+00:00
-- url     : https://prove2.me/submissions/3b167476-6235-41d6-b1fc-9f71153d9be1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_LieAlgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open NormedSpace Set Filter Topology
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
include h
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution (X Y : 𝔤) : ((h.bracket X Y : 𝔤) : 𝔸) = (X : 𝔸) * Y - Y * X :=
  Ring.lie_def _ _
end GroundTheory.Automorphic.IsExpLieAlgebra
