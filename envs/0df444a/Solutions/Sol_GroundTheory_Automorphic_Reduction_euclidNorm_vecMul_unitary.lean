-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.euclidNorm_vecMul_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:23:53.996929+00:00
-- url     : https://prove2.me/submissions/a903a252-ea13-479a-b3a9-ee65f1d5efe8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIwasawa
import Theorems.Thm_GroundTheory_Automorphic_Reduction_sum_norm_sq_vecMul_unitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution {U : Matrix (Fin n) (Fin n) 𝕜} (hU : U ∈ unitaryGroup (Fin n) 𝕜)
    (z : Fin n → 𝕜) : euclidNorm (z ᵥ* U) = euclidNorm z := by
  rw [euclidNorm, euclidNorm, sum_norm_sq_vecMul_unitary hU]
end GroundTheory.Automorphic.Reduction
