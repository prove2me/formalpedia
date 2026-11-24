-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_t_6
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:36:57.386865+00:00
-- url     : https://prove2.me/submissions/42a9d00d-b9bd-46fa-9a4a-f7738da32f0e

import Definitions.Def_HodgeComputerSSR_Q5Master
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem solution :
    SymmetricSexticResidual.LocalResidueQ5.checkMasterTChunk (3) 2 = true := by
  decide +kernel
