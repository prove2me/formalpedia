-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_t_4
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:34:25.641133+00:00
-- url     : https://prove2.me/submissions/a5679c58-b6e7-4da7-b363-b73cfa130bd5

import Definitions.Def_HodgeComputerSSR_Q5Master
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem solution :
    SymmetricSexticResidual.LocalResidueQ5.checkMasterTChunk (-1) 2 = true := by
  decide +kernel
