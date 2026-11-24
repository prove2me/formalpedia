-- Prove2me | solution 1 for GroundTheory.ProfCoh.finite_modN_uliftInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:04:42.693418+00:00
-- url     : https://prove2.me/submissions/3cd3bd49-172d-4499-a759-694920b25db9

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_AdicCompleteRootExistence_exists_root_of_dvd__8130b8fccf10


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
universe u
open GroundTheory.LocalField ValuativeRel IsLocalRing
namespace GroundTheory.ProfCoh
theorem _root_.solution (l : ℕ) [NeZero l] : Finite (ModN (ULift.{u} ℤ) l) := by
  let e : ULift.{u} ℤ ≃+ ℤ := AddEquiv.ulift
  let b : Module.Basis Unit ℤ (ULift.{u} ℤ) :=
    (Module.Basis.singleton Unit ℤ).map e.symm.toIntLinearEquiv
  exact Finite.of_equiv _ (ModN.basis (n := l) b).equivFun.symm.toEquiv
end GroundTheory.ProfCoh
