-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.euclidNorm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:22:24.070376+00:00
-- url     : https://prove2.me/submissions/705e2feb-2edb-49ee-9cbb-3197b47e6a2f

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
theorem _root_.solution (y : Fin n → E) : 0 ≤ euclidNorm y := Real.sqrt_nonneg _
end GroundTheory.Automorphic.Reduction
