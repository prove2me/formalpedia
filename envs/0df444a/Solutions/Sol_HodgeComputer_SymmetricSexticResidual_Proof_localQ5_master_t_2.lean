-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_t_2
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:32:15.393568+00:00
-- url     : https://prove2.me/submissions/0f1e9d2c-d786-44a8-bf7e-3fe1ff848cdc

import Definitions.Def_HodgeComputerSSR_Q5Master
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem solution :
    SymmetricSexticResidual.LocalResidueQ5.checkMasterTChunk (-5) 2 = true := by
  decide +kernel
