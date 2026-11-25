-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.norm_le_euclidNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:11:37.069807+00:00
-- url     : https://prove2.me/submissions/5ddcc3d3-4f1f-4e54-89d1-198b8ad6db87

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight

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
variable {E : Type*} [NormedField E] {n : ℕ}
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution (y : Fin n → E) (i : Fin n) : ‖y i‖ ≤ euclidNorm y := by
  rw [euclidNorm]
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun j => ‖y j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
end GroundTheory.Automorphic.Reduction
