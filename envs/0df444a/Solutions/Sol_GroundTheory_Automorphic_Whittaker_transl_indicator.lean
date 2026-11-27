-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.transl_indicator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:44:26.658815+00:00
-- url     : https://prove2.me/submissions/001c094d-6d80-47df-9ae3-a5a1d9af4b50

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
theorem _root_.solution (h : H) (A : Set X) : transl h (A.indicator 1) = (h • A).indicator 1 := by
  funext x
  simp only [transl_apply]
  by_cases hx : h⁻¹ • x ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (Set.mem_smul_set_iff_inv_smul_mem.2 hx)]
    rfl
  · rw [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (fun h' => hx (Set.mem_smul_set_iff_inv_smul_mem.1 h'))]
end GroundTheory.Automorphic.Whittaker
