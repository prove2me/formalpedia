-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.one_le_height_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:46:20.901804+00:00
-- url     : https://prove2.me/submissions/5862cad1-1c31-4124-9a89-f39ad127abe5

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Theorems.Thm_GroundTheory_Automorphic_Reduction_one_le_adelicNorm_ratVec

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
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution {x : Fin n → K} (hx : x ≠ 0) : 1 ≤ height 1 x := by
  rw [height, Units.val_one, vecMul_one]
  exact one_le_adelicNorm_ratVec hx
end GroundTheory.Automorphic.Reduction
