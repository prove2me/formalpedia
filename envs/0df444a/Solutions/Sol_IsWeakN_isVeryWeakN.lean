-- Prove2me | solution 1 for IsWeakN.isVeryWeakN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T15:07:52.624536+00:00
-- url     : https://prove2.me/submissions/e7993831-1b4b-480c-a4e2-8a66c421d6fa

import Mathlib
import Definitions.Def_Basic

set_option autoImplicit true
variable {O : Type*} [Orthoset O]
variable {P : Type*} [PartialOrder P]
namespace IsWeakN
theorem _root_.solution {a b c d : P} (h : IsWeakN a b c d) : IsVeryWeakN a b c d :=
  ⟨h.1, h.2.1.lt, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
end IsWeakN
