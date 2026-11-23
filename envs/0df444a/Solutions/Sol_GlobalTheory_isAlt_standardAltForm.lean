-- Prove2me | solution 1 for GlobalTheory.isAlt_standardAltForm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:22:10.864275+00:00
-- url     : https://prove2.me/submissions/1e63e516-289b-44d0-98e9-3ba46794eb48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_standardAltForm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open GlobalTheory
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
namespace GlobalTheory
theorem _root_.solution [Fintype ι] [DecidableEq ι] (d : ι → R) :
    (standardAltForm d).IsAlt := fun x => by
  rw [standardAltForm_apply]
  exact Finset.sum_eq_zero fun i _ => by ring
end GlobalTheory
