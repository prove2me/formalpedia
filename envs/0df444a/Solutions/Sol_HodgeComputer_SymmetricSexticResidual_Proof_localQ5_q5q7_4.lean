-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_q5q7_4
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:17:56.30049+00:00
-- url     : https://prove2.me/submissions/c8aa096e-caf1-4347-a389-49f2b5988153

import Definitions.Def_HodgeComputerSSR_Q5Weights
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem solution :
    SymmetricSexticResidual.LocalResidueQ5.checkQ5Q7Chunk 16 10 = true :=
  by decide +kernel
