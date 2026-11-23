-- Prove2me | solution 1 for GlobalTheory.injective_of_isLocalizedModule_nonZeroDivisors
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:31.889048+00:00
-- url     : https://prove2.me/submissions/0145f093-b967-42db-bcb9-08735772f47c

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
omit [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
namespace GlobalTheory
theorem _root_.solution [Module.IsTorsionFree A M]
    (f : M →ₗ[A] V) [IsLocalizedModule A⁰ f] : Function.Injective f :=
  (IsLocalizedModule.injective_iff_isRegular A⁰ f).mpr fun c =>
    (isRegular_iff_mem_nonZeroDivisors.mpr c.2).isSMulRegular
end GlobalTheory
