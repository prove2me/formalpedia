-- Prove2me | solution 1 for OAI.SnakyCertificate.Check.cache_summary_615
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T00:22:08.314608+00:00
-- url     : https://prove2.me/submissions/0d1f9be3-8032-41c3-b036-9ff8daecbeea

import Mathlib
import Definitions.Def_SnakyCertificate
import Definitions.Def_OAIQ114S000

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Summaries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem cache_615_H_isChain :
    List.IsChain (fun a b : Cell => toLex a < toLex b) cache_615_H := by
  decide +kernel

theorem cache_615_H_length : cache_615_H.length = 686 := by
  decide +kernel

theorem cache_summary_615_oai :
    (denote cache_615).A = {(1, 0)} ∧
    (denote cache_615).H.card = 686 ∧
    (denote cache_615).height = 34 := by
  refine ⟨by decide +kernel, ?_, rfl⟩
  have hp := List.isChain_iff_pairwise.1 cache_615_H_isChain
  have hnd : cache_615_H.Nodup := hp.imp (fun h e => by subst e; exact lt_irrefl _ h)
  change cache_615_H.toFinset.card = 686
  rw [List.toFinset_card_of_nodup hnd, cache_615_H_length]

end SnakyCertificate.Check

end OAI
end

theorem solution : type_of% @OAI.SnakyCertificate.Check.cache_summary_615_oai := @OAI.SnakyCertificate.Check.cache_summary_615_oai
