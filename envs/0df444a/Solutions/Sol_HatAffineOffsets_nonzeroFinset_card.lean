-- Prove2me | solution 1 for HatAffineOffsets.nonzeroFinset_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:12:03.332954+00:00
-- url     : https://prove2.me/submissions/7c121ef3-0214-4aca-96a0-bc5a1222db80

import Definitions.Def_HatAffineOffsets_TypeI
import Definitions.Def_HatAffineOffsets_TypeII

set_option autoImplicit true
open HatAffineOffsets
universe u
open Finset
attribute [local instance] HatAffineOffsets._p2m_local_instance_68713dd93e_9
namespace HatAffineOffsets
theorem _root_.solution
    {K : Type u} [Fintype K] [Zero K] [DecidableEq K] :
    (nonzeroFinset K).card = Fintype.card K - 1 := by
  rw [nonzeroFinset, Finset.card_erase_of_mem (Finset.mem_univ 0),
    Finset.card_univ]
end HatAffineOffsets
