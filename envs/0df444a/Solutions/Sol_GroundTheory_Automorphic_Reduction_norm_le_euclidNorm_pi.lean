-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.norm_le_euclidNorm_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:40:34.859694+00:00
-- url     : https://prove2.me/submissions/d4652c6c-e0c2-485b-9a3a-19fed43e106a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Theorems.Thm_GroundTheory_Automorphic_Reduction_euclidNorm_nonneg
import Theorems.Thm_GroundTheory_Automorphic_Reduction_norm_le_euclidNorm

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
theorem _root_.solution (y : Fin n → E) : ‖y‖ ≤ euclidNorm y :=
  (pi_norm_le_iff_of_nonneg (euclidNorm_nonneg y)).2 fun i => norm_le_euclidNorm y i
end GroundTheory.Automorphic.Reduction
