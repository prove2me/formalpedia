-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.isSeparable_adjoin_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:47:41.86322+00:00
-- url     : https://prove2.me/submissions/6be28129-0477-48dc-be95-82458941ccb1

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceSum
import Definitions.Def_GroundTheory_FunctionField_PlaceBridge
import Theorems.Thm_GroundTheory_FunctionField_Place_adjoin_inv_eq

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
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
open scoped IntermediateField.algebraAdjoinAdjoin
variable [IsFunctionField k K] (t : K) [Algebra.IsSeparable (IntermediateField.adjoin k {t}) K]
attribute [local instance] isDedekindDomain_closure_adjoin isFractionRing_closure_adjoin
omit [IsFunctionField k K]
namespace GroundTheory.FunctionField.Place
theorem _root_.solution : Algebra.IsSeparable (IntermediateField.adjoin k {t⁻¹}) K := by
  rw [adjoin_inv_eq]
  infer_instance
end GroundTheory.FunctionField.Place
