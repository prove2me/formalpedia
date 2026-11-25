-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.adjoin_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:24:06.235899+00:00
-- url     : https://prove2.me/submissions/df4c600c-5f55-4909-817d-027558815ee1

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceSum
import Definitions.Def_GroundTheory_FunctionField_PlaceBridge

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
omit [IsFunctionField k K] [Algebra.IsSeparable (IntermediateField.adjoin k {t}) K]
namespace GroundTheory.FunctionField.Place
theorem _root_.solution : IntermediateField.adjoin k {t⁻¹} = IntermediateField.adjoin k {t} := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact inv_mem (IntermediateField.mem_adjoin_simple_self k t)
  · rw [IntermediateField.adjoin_simple_le_iff]
    have := inv_mem (IntermediateField.mem_adjoin_simple_self k t⁻¹)
    rwa [inv_inv] at this
end GroundTheory.FunctionField.Place
