-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_q5q7_2
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:17:46.346266+00:00
-- url     : https://prove2.me/submissions/a0ec19fe-cea1-4e5b-a038-cba6773d9899

import Definitions.Def_HodgeComputerSSR_Q5Weights
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem solution :
    SymmetricSexticResidual.LocalResidueQ5.checkQ5Q7Chunk (-4) 10 = true :=
  by decide +kernel
