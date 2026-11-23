-- Prove2me | solution 1 for GroundTheory.ProfCoh.modN_mk_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:10:09.458518+00:00
-- url     : https://prove2.me/submissions/9d288fa2-39c2-4ef1-8eed-8938b31c28fe

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveSnake
import Theorems.Thm_GroundTheory_ProfCoh_coe_torsNRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_modNRep_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.ProfCoh.coe_torsNRep_apply
attribute [local simp] GroundTheory.ProfCoh.modNRep_mk



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u v
open Representation
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] (n : ℕ)
namespace GroundTheory.ProfCoh
theorem _root_.solution (x : A) :
    (Submodule.Quotient.mk x : ModN A n) = 0 ↔ ∃ y : A, n • y = x := by
  rw [Submodule.Quotient.mk_eq_zero]
  simp
end GroundTheory.ProfCoh
