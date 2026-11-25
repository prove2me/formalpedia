-- Prove2me | solution 1 for GroundTheory.Automorphic.realEmb_eq_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:04:23.455889+00:00
-- url     : https://prove2.me/submissions/3d0e2f15-4f09-4f65-8e51-e548b290bd5f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Places

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct NumberField NumberField.InfinitePlace
variable {K : Type*} [Field K] [NumberField K]
omit [NumberField K]
namespace GroundTheory.Automorphic
theorem _root_.solution (hreal : ∀ w : InfinitePlace K, w.IsReal) (w : InfinitePlace K)
    (k : K) : Completion.extensionEmbeddingOfIsReal (hreal w) (algebraMap K w.Completion k) =
      realEmb hreal w k := by
  rw [Completion.algebraMap_apply]
  exact Completion.extensionEmbeddingOfIsReal_coe (hreal w) _
end GroundTheory.Automorphic
