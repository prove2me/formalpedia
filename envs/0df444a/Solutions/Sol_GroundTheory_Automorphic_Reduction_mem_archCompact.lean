-- Prove2me | solution 1 for GroundTheory.Automorphic.Reduction.mem_archCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:52:09.357639+00:00
-- url     : https://prove2.me/submissions/9e1c29cc-27e3-4fbf-8bfc-f05da11c3dbe

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIwasawa

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
variable {K : Type*} [Field K] {n : ℕ}
namespace GroundTheory.Automorphic.Reduction
theorem _root_.solution {w : InfinitePlace K} {k : GL (Fin n) w.Completion} :
    k ∈ archCompact w ↔ ∀ y : Fin n → w.Completion,
      euclidNorm (y ᵥ* (k : Matrix (Fin n) (Fin n) w.Completion)) = euclidNorm y :=
  Iff.rfl
end GroundTheory.Automorphic.Reduction
