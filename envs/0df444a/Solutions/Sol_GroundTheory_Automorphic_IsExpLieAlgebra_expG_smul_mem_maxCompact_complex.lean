-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.expG_smul_mem_maxCompact_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:09.009798+00:00
-- url     : https://prove2.me/submissions/5d7a6ae5-6496-4faf-8808-43489824f181

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis
import Theorems.Thm_GroundTheory_Automorphic_mem_maxCompact
import Theorems.Thm_GroundTheory_Automorphic_exp_mem_unitaryGroup

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
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
open NormedSpace
open scoped Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Automorphic
namespace IsExpLieAlgebra
theorem _root_.solution {G : Subgroup (Matrix ι ι ℂ)ˣ}
    {𝔤 : Submodule ℝ (Matrix ι ι ℂ)} (h : IsExpLieAlgebra G 𝔤) {X : 𝔤}
    (hX : (X : Matrix ι ι ℂ)ᴴ = -(X : Matrix ι ι ℂ)) (t : ℝ) :
    h.expG (t • X) ∈ maxCompact G := by
  rw [mem_maxCompact, IsExpLieAlgebra.coe_expG]
  apply exp_mem_unitaryGroup
  change (t • (X : Matrix ι ι ℂ))ᴴ = -(t • (X : Matrix ι ι ℂ))
  rw [conjTranspose_smul, star_trivial, hX, smul_neg]
end IsExpLieAlgebra
end GroundTheory.Automorphic
