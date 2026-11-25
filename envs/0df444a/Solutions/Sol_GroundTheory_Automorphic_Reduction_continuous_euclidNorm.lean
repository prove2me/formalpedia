-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.continuous_euclidNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:22:37.082873+00:00
-- url     : https://prove2.me/submissions/da35ac9d-0c6b-424a-a62f-7723e96d9a0a

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
theorem _root_.solution : Continuous (euclidNorm : (Fin n → E) → ℝ) :=
  Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
    (continuous_norm.comp (continuous_apply i)).pow 2)
end GroundTheory.Automorphic.Reduction
