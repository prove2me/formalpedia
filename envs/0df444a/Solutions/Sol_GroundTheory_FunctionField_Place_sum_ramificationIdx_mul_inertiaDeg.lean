-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.sum_ramificationIdx_mul_inertiaDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:41:49.87116+00:00
-- url     : https://prove2.me/submissions/36d2b1e6-5e92-4825-ae12-2cb1e7021ef5

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove
import Definitions.Def_GroundTheory_FunctionField_PlaceSum
import Theorems.Thm_GroundTheory_FunctionField_Place_finrank_closure
import Theorems.Thm_GroundTheory_FunctionField_Place_ramificationIdx_primeOfPlace_eq
import Theorems.Thm_GroundTheory_FunctionField_Place_inertiaDeg_primeOfPlace_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open IsDedekindDomain IsLocalRing
open scoped WithZero
open GroundTheory.FunctionField.Place
variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  [Algebra K K'] [IsScalarTower k K K']
attribute [local instance low] algebraExt
attribute [local instance] isScalarTower_ext
attribute [local instance] isTorsionFree_ext
variable [IsFunctionField k K] [IsFunctionField k K'] [FiniteDimensional K K']
  [Algebra.IsSeparable K K'] (v : Place k K)
attribute [local instance] isDedekindDomain_closure isFractionRing_closure finite_closure
  isTorsionFree_closure
namespace GroundTheory.FunctionField.Place
theorem _root_.solution :
    ∑ w ∈ (v.finite_liesOver (K' := K')).toFinset, w.ramificationIdx v * w.inertiaDeg v =
      Module.finrank K K' := by
  classical
  have hfin : ((maximalIdeal v.ring).primesOver (integralClosure v.ring K')).Finite :=
    Algebra.QuasiFinite.finite_primesOver _
  let : Fintype ((maximalIdeal v.ring).primesOver (integralClosure v.ring K')) := hfin.fintype
  let : Fintype {w : Place k K' // w.LiesOver v} := Fintype.ofEquiv _ v.primesOverEquiv
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (maximalIdeal v.ring)
    (integralClosure v.ring K')
  rw [finrank_closure] at hsum
  have hs : ∀ w : Place k K', w ∈ (v.finite_liesOver (K' := K')).toFinset ↔ w.LiesOver v :=
    fun w => Set.Finite.mem_toFinset _
  rw [← hsum, Finset.sum_subtype _ hs]
  refine (Fintype.sum_equiv v.primesOverEquiv _ _ fun q => ?_).symm
  rw [ramificationIdx_primeOfPlace_eq, inertiaDeg_primeOfPlace_eq]
  rfl
end GroundTheory.FunctionField.Place
