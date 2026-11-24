-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_q5q7_3
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:17:50.268013+00:00
-- url     : https://prove2.me/submissions/941e6ca7-4af7-483e-833e-f25960227e9c

import Definitions.Def_HodgeComputerSSR_Q5Weights
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem solution :
    SymmetricSexticResidual.LocalResidueQ5.checkQ5Q7Chunk 6 10 = true :=
  by decide +kernel
