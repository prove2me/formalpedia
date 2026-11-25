-- Prove2me | solution 1 for HatAffineOffsets.nonzero_subtype_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:16:48.626399+00:00
-- url     : https://prove2.me/submissions/d447c082-bc9b-4a4f-8f5f-f3512e6f1293

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
    Fintype.card {z : K // z ≠ 0} = Fintype.card K - 1 := by
  calc
    Fintype.card {z : K // z ≠ 0} =
        (Finset.univ.filter (fun z : K => z ≠ 0)).card :=
      Fintype.card_subtype _
    _ = (Finset.univ.erase (0 : K)).card := by
      rw [Finset.filter_ne' (Finset.univ : Finset K) (0 : K)]
    _ = Fintype.card K - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : K)), Finset.card_univ]
end HatAffineOffsets
