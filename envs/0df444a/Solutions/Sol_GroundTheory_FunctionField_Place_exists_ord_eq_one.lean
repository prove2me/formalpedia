-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.exists_ord_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:19:12.914041+00:00
-- url     : https://prove2.me/submissions/40747e51-d9f2-4195-9db5-3f1c0eacfbbf

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open IntermediateField
open scoped WithZero
open Polynomial
variable (k K : Type*) [Field k] [Field K] [Algebra k K]
open GroundTheory.FunctionField.Place
variable {k K} (v : Place k K)
variable [IsFunctionField k K]
namespace GroundTheory.FunctionField.Place
theorem _root_.solution : ∃ π : K, v.ord π = 1 := by
  obtain ⟨π, hπ⟩ := v.heightOneSpectrum.valuation_exists_uniformizer K
  refine ⟨π, ?_⟩
  change -WithZero.log (v.heightOneSpectrum.valuation K π) = 1
  rw [hπ, WithZero.log_exp, neg_neg]
end GroundTheory.FunctionField.Place
