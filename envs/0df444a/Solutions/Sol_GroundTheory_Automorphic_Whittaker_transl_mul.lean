-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.transl_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:51.087796+00:00
-- url     : https://prove2.me/submissions/3d3b4a1f-b082-410d-834c-1942a2bd6c8b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Whittaker.transl_apply

set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction
open scoped Pointwise
variable {X : Type*} {H : Type*} [Group H] [MulAction H X]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (h k : H) (f : X → ℂ) : transl (h * k) f = transl h (transl k f) := by
  funext x
  simp [transl, mul_inv_rev, mul_smul]
end GroundTheory.Automorphic.Whittaker
