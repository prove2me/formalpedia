-- Prove2me | solution 2 for KServer.chunk_zero_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T09:23:06.906498+00:00
-- url     : https://prove2.me/submissions/a0719d4b-1ca5-4cb8-a854-ae6d2dd0e695

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b

open KServer

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

theorem solution {X : Type*} [MetricSpace X] {s t : X}
    {cA cHi total price : ℝ} {mLo : ℕ}
    (C : ChunkSystemB X s t cA cHi total price mLo) (hA : 0 ≤ cA) :
    ∃ C' : ChunkSystemB X s t 0 cHi total price mLo, C'.m = C.m :=
  ⟨{ C with
      hsize := fun ω i => ⟨le_trans hA (C.hsize ω i).1, (C.hsize ω i).2⟩ }, rfl⟩
