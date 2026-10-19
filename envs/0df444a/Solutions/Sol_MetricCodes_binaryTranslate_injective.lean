-- Prove2me | solution 1 for MetricCodes.binaryTranslate_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/b7beb6bb-5d83-4a42-ba72-80a4d5f0325f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset
namespace MetricCodes
theorem _root_.solution {n : ℕ} (x : BinaryWord n) :
    Function.Injective (binaryTranslate x) := by
  intro y z h
  have := congrArg (binaryTranslate x) h
  simpa using this
end MetricCodes
