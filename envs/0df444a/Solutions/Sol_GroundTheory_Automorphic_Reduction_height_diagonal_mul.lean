-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.height_diagonal_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:41:17.337961+00:00
-- url     : https://prove2.me/submissions/267641e2-4de7-4522-945a-648045719f3e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Theorems.Thm_GroundTheory_Automorphic_Reduction_ratVec_vecMul

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
theorem _root_.solution (γ : GL (Fin n) K) (g : AdelicGLn.AdelicGL K n) (x : Fin n → K) :
    height (AdelicGLn.diagonal K n γ * g) x = height g (x ᵥ* (γ : Matrix (Fin n) (Fin n) K)) := by
  rw [height, height, Units.val_mul, ← vecMul_vecMul, ratVec_vecMul]
  rfl
end GroundTheory.Automorphic.Reduction
