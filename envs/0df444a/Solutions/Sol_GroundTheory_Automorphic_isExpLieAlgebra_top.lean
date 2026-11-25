-- Prove2me | solution 1 for GroundTheory.Automorphic.isExpLieAlgebra_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:33:57.275445+00:00
-- url     : https://prove2.me/submissions/053df476-40d2-421b-a333-e6490e319194

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsLie
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_CartanBasis

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
namespace GroundTheory.Automorphic
theorem _root_.solution {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] : IsExpLieAlgebra (⊤ : Subgroup 𝔸ˣ) (⊤ : Submodule ℝ 𝔸) where
  expUnit_mem _ _ := Subgroup.mem_top _
  exists_nhds := ⟨(expPartialHomeomorph ℝ 𝔸).source, (expPartialHomeomorph ℝ 𝔸).open_source,
    zero_mem_expPartialHomeomorph_source ℝ 𝔸, subset_rfl, fun _ _ _ => Submodule.mem_top⟩
end GroundTheory.Automorphic
