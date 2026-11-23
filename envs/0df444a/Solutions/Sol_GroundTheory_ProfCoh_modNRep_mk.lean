-- Prove2me | solution 1 for GroundTheory.ProfCoh.modNRep_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:47.023954+00:00
-- url     : https://prove2.me/submissions/7cf9ae93-9301-454b-94b9-0f35c5065bcc

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
theorem _root_.solution (γ : Γ) (x : A) :
    modNRep Γ A n γ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (γ • x) :=
  rfl
end GroundTheory.ProfCoh
