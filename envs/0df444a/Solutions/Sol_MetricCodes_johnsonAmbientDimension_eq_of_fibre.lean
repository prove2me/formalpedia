-- Prove2me | solution 1 for MetricCodes.johnsonAmbientDimension_eq_of_fibre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/33a7aa2b-d8be-4bf6-be69-6b12d5c1c709

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_johnsonAmbientDimension_eq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset
namespace MetricCodes
theorem _root_.solution (n p q L : ℕ)
    (hpq : p + q ≤ L) (hL : L ≤ n / 2) :
    johnsonAmbientDimension n (p + q) L =
      n.choose L - precedingBinomial n (p + q) :=
  johnsonAmbientDimension_eq n (p + q) L hpq hL
end MetricCodes
