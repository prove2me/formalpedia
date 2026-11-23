-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.valuation_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:15:51.655599+00:00
-- url     : https://prove2.me/submissions/af14be31-165a-49c4-9aec-04efd8777f7c

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
theorem _root_.solution : Function.Surjective v.valuation :=
  IsDedekindDomain.HeightOneSpectrum.valuation_surjective K v.heightOneSpectrum
end GroundTheory.FunctionField.Place
