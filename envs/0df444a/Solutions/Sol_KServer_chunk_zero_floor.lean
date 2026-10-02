-- Prove2me | solution 1 for KServer.chunk_zero_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T09:22:44.012491+00:00
-- url     : https://prove2.me/submissions/4fe1a6aa-7122-4fe8-96f2-85001b209b58

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b

open KServer

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- The size floor of a chunk system is a one-sided parameter, so it can be
lowered to zero at no cost: the same chunk data, on the same space, is a valid
chunk system at floor `0`, with the same number of chunks. -/
theorem solution {X : Type*} [MetricSpace X] {s t : X}
    {cA cHi total price : ℝ} {mLo : ℕ}
    (C : ChunkSystemB X s t cA cHi total price mLo) (hA : 0 ≤ cA) :
    ∃ C' : ChunkSystemB X s t 0 cHi total price mLo, C'.m = C.m :=
  ⟨{ Ω := C.Ω
     instFin := C.instFin
     instDec := C.instDec
     P := C.P
     m := C.m
     hist := C.hist
     chunk := C.chunk
     size := C.size
     hP := C.hP
     hPsum := C.hPsum
     hm := C.hm
     hm0 := C.hm0
     href := C.href
     hadapt := C.hadapt
     hsmeas := C.hsmeas
     hne := C.hne
     hlast := C.hlast
     hopt := C.hopt
     hsize := fun _ _ => ⟨le_trans hA (C.hsize _ _).1, (C.hsize _ _).2⟩
     hcost := C.hcost
     htotal := C.htotal }, rfl⟩
