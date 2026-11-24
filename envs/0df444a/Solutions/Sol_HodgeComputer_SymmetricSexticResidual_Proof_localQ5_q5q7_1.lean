-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_q5q7_1
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:17:14.54832+00:00
-- url     : https://prove2.me/submissions/30c9647f-f563-4c7a-b151-572a8d415127

import Definitions.Def_HodgeComputerSSR_Q5Weights
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem solution :
    SymmetricSexticResidual.LocalResidueQ5.checkQ5Q7Chunk (-14) 10 = true :=
  by decide +kernel
