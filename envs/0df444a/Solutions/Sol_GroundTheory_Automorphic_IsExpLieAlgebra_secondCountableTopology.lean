-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.secondCountableTopology
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:46.88481+00:00
-- url     : https://prove2.me/submissions/43a2e34e-2b0d-4931-9b37-5004a3bf675b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarCoord
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_isEmbedding_coe_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set Filter
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable {G : Subgroup 𝔸ˣ} (h : IsExpLieAlgebra G 𝔤)
include h
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution : SecondCountableTopology G :=
  isEmbedding_coe_coe.secondCountableTopology
end GroundTheory.Automorphic.IsExpLieAlgebra
