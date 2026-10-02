-- Prove2me | solution 1 for KServer.chunk_ceiling_raise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T10:18:04.045513+00:00
-- url     : https://prove2.me/submissions/5abc4163-bca4-4460-9a54-6a5cb04da110

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
     hsize := fun _ _ => ⟨(C.hsize _ _).1, le_trans (C.hsize _ _).2 hB⟩
     hcost := C.hcost
     htotal := C.htotal }, rfl⟩
