-- Prove2me | solution 1 for GroundTheory.ProfCoh.QZDual.eval_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:05:44.904944+00:00
-- url     : https://prove2.me/submissions/cb37e089-ae9e-4b98-b70f-fe84d73a9a8d

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open Topology
open GroundTheory.ProfCoh.QZDual
variable {A B C : Type*} [AddCommGroup A] [TopologicalSpace A] [AddCommGroup B]
  [TopologicalSpace B] [AddCommGroup C] [TopologicalSpace C]
namespace GroundTheory.ProfCoh.QZDual
theorem _root_.solution (a : A) (χ : QZDual A) : eval A a χ = χ a :=
  rfl
end GroundTheory.ProfCoh.QZDual
