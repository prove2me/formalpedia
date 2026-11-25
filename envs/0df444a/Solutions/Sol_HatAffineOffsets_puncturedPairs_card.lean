-- Prove2me | solution 1 for HatAffineOffsets.puncturedPairs_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:17:36.173847+00:00
-- url     : https://prove2.me/submissions/0bf7e3a0-bfa1-4ac2-ae76-7d2e91e3b090

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII
import Theorems.Thm_HatAffineOffsets_nonzeroFinset_card

set_option autoImplicit true
open HatAffineOffsets
universe u
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_68713dd93e_9
namespace HatAffineOffsets
theorem _root_.solution
    {K : Type u} [Fintype K] [Zero K] [DecidableEq K] :
    (puncturedPairs K).card = (Fintype.card K - 1) ^ 2 := by
  calc
    (puncturedPairs K).card =
        (nonzeroFinset K).card * (nonzeroFinset K).card := by
      exact Finset.card_product (nonzeroFinset K) (nonzeroFinset K)
    _ = (Fintype.card K - 1) ^ 2 := by
      rw [nonzeroFinset_card]
      ring
end HatAffineOffsets
