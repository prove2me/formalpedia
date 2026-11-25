-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.adelicNorm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:40:16.565126+00:00
-- url     : https://prove2.me/submissions/e92a0435-c226-494c-b537-e4e8af45ce34

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Theorems.Thm_GroundTheory_Automorphic_Reduction_euclidNorm_nonneg

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
theorem _root_.solution (y : Fin n → 𝔸[K]) : 0 ≤ adelicNorm y :=
  mul_nonneg (Finset.prod_nonneg fun _ _ => pow_nonneg (euclidNorm_nonneg _) _)
    (finprod_nonneg fun _ => norm_nonneg _)
end GroundTheory.Automorphic.Reduction
