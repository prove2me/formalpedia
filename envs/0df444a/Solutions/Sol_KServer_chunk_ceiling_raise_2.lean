-- Prove2me | solution 2 for KServer.chunk_ceiling_raise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T10:19:07.580155+00:00
-- url     : https://prove2.me/submissions/d7be8bef-7d94-4278-877c-c1d1a3de1e38

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b

open KServer

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

theorem solution {X : Type*} [MetricSpace X] {s t : X}
    {cA cB cB' total price : ℝ} {mLo : ℕ}
    (C : ChunkSystemB X s t cA cB total price mLo) (hB : cB ≤ cB') :
    ∃ C' : ChunkSystemB X s t cA cB' total price mLo, C'.m = C.m :=
  ⟨{ C with
      hsize := fun ω i => ⟨(C.hsize ω i).1, le_trans (C.hsize ω i).2 hB⟩ }, rfl⟩
