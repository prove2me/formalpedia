-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.hasFiniteContent_height
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:07:25.456479+00:00
-- url     : https://prove2.me/submissions/1c239e8c-75f2-402f-a6e7-1705343fc74f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Theorems.Thm_GroundTheory_Automorphic_Reduction_HasFiniteContent_vecMul
import Theorems.Thm_GroundTheory_Automorphic_Reduction_hasFiniteContent_ratVec

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
theorem _root_.solution (g : AdelicGLn.AdelicGL K n) {x : Fin n → K} (hx : x ≠ 0) :
    HasFiniteContent (ratVec x ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K])) :=
  (hasFiniteContent_ratVec hx).vecMul g
end GroundTheory.Automorphic.Reduction
