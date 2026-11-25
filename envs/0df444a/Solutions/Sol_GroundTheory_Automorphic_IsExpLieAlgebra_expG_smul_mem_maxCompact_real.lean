-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.expG_smul_mem_maxCompact_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:37:09.900416+00:00
-- url     : https://prove2.me/submissions/9d1523cd-fa62-4174-8fa3-1edb7d48d112

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
theorem _root_.solution {G : Subgroup (Matrix ι ι ℝ)ˣ}
    {𝔤 : Submodule ℝ (Matrix ι ι ℝ)} (h : IsExpLieAlgebra G 𝔤) {X : 𝔤}
    (hX : (X : Matrix ι ι ℝ)ᴴ = -(X : Matrix ι ι ℝ)) (t : ℝ) :
    h.expG (t • X) ∈ maxCompact G := by
  rw [mem_maxCompact, IsExpLieAlgebra.coe_expG]
  apply exp_mem_unitaryGroup
  change (t • (X : Matrix ι ι ℝ))ᴴ = -(t • (X : Matrix ι ι ℝ))
  rw [conjTranspose_smul, star_trivial, hX, smul_neg]
end IsExpLieAlgebra
end GroundTheory.Automorphic
