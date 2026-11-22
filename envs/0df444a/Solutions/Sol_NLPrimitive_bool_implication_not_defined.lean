-- Prove2me | solution 1 for NLPrimitive.bool_implication_not_defined
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:18:54.885578+00:00
-- url     : https://prove2.me/submissions/5ebcbb7b-8e7d-42ce-afd8-f91c33e3631c

import Std
import Definitions.Def_NLPrimitive

set_option autoImplicit true
set_option autoImplicit false
open NLPrimitive
namespace NLPrimitive
theorem _root_.solution :
    boolOps.arr false false ≠
    boolOps.neg (boolOps.compat false (boolOps.neg false)) := by
  decide
end NLPrimitive
