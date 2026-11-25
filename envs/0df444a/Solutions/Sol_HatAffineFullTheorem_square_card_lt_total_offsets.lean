-- Prove2me | solution 1 for HatAffineFullTheorem.square_card_lt_total_offsets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:38:24.752845+00:00
-- url     : https://prove2.me/submissions/c06d37fb-4f39-4f6d-a647-0e13d0e6fa3a

import Definitions.Def_HatAffineFullTheorem_LeadingClassification
import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
import Definitions.Def_HatAffineFullTheorem_GeneralNoGo

set_option autoImplicit true
open scoped BigOperators
open HatAffineFullTheorem
universe u
attribute [local instance] HatAffineFullTheorem._p2m_local_instance_f43eda1e4a_11
namespace HatAffineFullTheorem
theorem _root_.solution
    (q : Nat) (hq : 4 ≤ q) :
    q ^ 2 < q ^ (q - 1) := by
  exact Nat.pow_lt_pow_right (by omega) (by omega)
end HatAffineFullTheorem
