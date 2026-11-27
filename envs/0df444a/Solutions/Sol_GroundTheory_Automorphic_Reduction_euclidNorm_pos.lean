-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.euclidNorm_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:44:21.611685+00:00
-- url     : https://prove2.me/submissions/7c15e5c9-ac21-4c72-a801-b15559d5d004

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Theorems.Thm_GroundTheory_Automorphic_Reduction_norm_le_euclidNorm_pi

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
theorem _root_.solution {y : Fin n → E} (hy : y ≠ 0) : 0 < euclidNorm y :=
  lt_of_lt_of_le (norm_pos_iff.2 hy) (norm_le_euclidNorm_pi y)
end GroundTheory.Automorphic.Reduction
