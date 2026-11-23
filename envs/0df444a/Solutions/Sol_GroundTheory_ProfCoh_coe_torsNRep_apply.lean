-- Prove2me | solution 1 for GroundTheory.ProfCoh.coe_torsNRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:47.598816+00:00
-- url     : https://prove2.me/submissions/0a9c61b6-79a6-4563-97f7-6210f4caa874

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_AdditiveDefs

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
universe u v
open Representation
variable {Γ : Type*} [Group Γ]
variable (Γ) (A : Type*) [AddCommGroup A] [DistribMulAction Γ A] (n : ℕ)
namespace GroundTheory.ProfCoh
theorem _root_.solution (γ : Γ) (x : TorsN A n) :
    ((torsNRep Γ A n γ x : TorsN A n) : A) = γ • (x : A) :=
  rfl
end GroundTheory.ProfCoh
