-- Prove2me | solution 1 for OAI.Snaky21.Certificate.catalog_correct
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-09T08:55:45.565001+00:00
-- url     : https://prove2.me/submissions/71037adb-ce7c-4ecb-9bd2-d9e6d37c4641

import Definitions.Def_Snaky21Catalog
open OAI.Snaky21.Certificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem solution : numberedCards.length = 728 ∧ (numberedCards.map (fun c => decide (0 < c.height ∧ c.height ≤ 21))).all id = true := by
  decide +kernel

#print axioms solution
