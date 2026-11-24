-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_t_0
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:30:54.898354+00:00
-- url     : https://prove2.me/submissions/ab252945-3fad-4fee-a18c-cee2b7b4dd13

import Definitions.Def_HodgeComputerSSR_Q5Master
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem solution :
    SymmetricSexticResidual.LocalResidueQ5.checkMasterTChunk (-9) 2 = true := by
  decide +kernel
