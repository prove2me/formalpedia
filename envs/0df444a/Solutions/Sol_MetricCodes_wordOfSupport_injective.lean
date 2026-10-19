-- Prove2me | solution 1 for MetricCodes.wordOfSupport_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/d96366c8-2637-4823-a22f-2a5112546782

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset
namespace MetricCodes
theorem _root_.solution {n : ℕ} :
    Function.Injective (wordOfSupport (n := n)) :=
  (binaryWordEquivFinset n).symm.injective
end MetricCodes
