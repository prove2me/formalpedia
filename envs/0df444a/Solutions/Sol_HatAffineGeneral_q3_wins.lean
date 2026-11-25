-- Prove2me | solution 1 for HatAffineGeneral.q3_wins
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:21:45.999075+00:00
-- url     : https://prove2.me/submissions/3dd2ea5b-4673-4b69-9ee0-5cd165fb0184

import Mathlib
import Definitions.Def_HatAffineGeneral_Discovery

set_option autoImplicit true
open scoped BigOperators
open HatAffineGeneral
universe u v w
attribute [local instance] HatAffineGeneral.three_is_prime
set_option maxRecDepth 100000
namespace HatAffineGeneral
theorem _root_.solution : Wins q3F q3G := by
  unfold Wins
  decide
end HatAffineGeneral
