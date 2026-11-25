-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.infComp_vecMul_GL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:46:24.701847+00:00
-- url     : https://prove2.me/submissions/a16a7afa-9ea4-426a-a68e-a2af39bec36e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Theorems.Thm_GroundTheory_Automorphic_Reduction_infComp_vecMul

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
theorem _root_.solution (w : InfinitePlace K) (y : Fin n → 𝔸[K]) (g : AdelicGLn.AdelicGL K n) :
    infComp w (y ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K])) =
      infComp w y ᵥ* (infAt w g : Matrix (Fin n) (Fin n) w.Completion) := by
  rw [infComp_vecMul]
  rfl
end GroundTheory.Automorphic.Reduction
