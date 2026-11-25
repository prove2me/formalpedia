-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.height_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:30:19.785092+00:00
-- url     : https://prove2.me/submissions/27b039f3-33de-4728-97f6-84680659dbd2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Theorems.Thm_GroundTheory_Automorphic_Reduction_ratVec_smul
import Theorems.Thm_GroundTheory_Automorphic_Reduction_adelicNorm_smul_rat
import Theorems.Thm_GroundTheory_Automorphic_Reduction_hasFiniteContent_height

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
theorem _root_.solution (g : AdelicGLn.AdelicGL K n) {x : Fin n → K} (hx : x ≠ 0) {c : K}
    (hc : c ≠ 0) : height g (c • x) = height g x := by
  rw [height, ratVec_smul, smul_vecMul, adelicNorm_smul_rat (hasFiniteContent_height g hx) hc,
    height]
end GroundTheory.Automorphic.Reduction
