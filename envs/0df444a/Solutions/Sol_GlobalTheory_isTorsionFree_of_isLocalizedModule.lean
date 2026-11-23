-- Prove2me | solution 1 for GlobalTheory.isTorsionFree_of_isLocalizedModule
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:31.947369+00:00
-- url     : https://prove2.me/submissions/2ca0b8f7-d81f-4a99-9b01-cd067abcc5c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors TensorProduct WithZero
open GlobalTheory
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
variable [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
variable {V : Type*} [AddCommGroup V] [Module A V]
omit [IsNoetherianRing A] [IsIntegrallyClosed A]
namespace GlobalTheory
theorem _root_.solution (f : M →ₗ[A] V) [IsLocalizedModule A⁰ f] :
    Module.IsTorsionFree A V :=
  ⟨fun r hr => ((Module.End.isUnit_iff _).mp
    (IsLocalizedModule.map_units f (⟨r, hr.mem_nonZeroDivisors⟩ : A⁰))).1⟩
end GlobalTheory
