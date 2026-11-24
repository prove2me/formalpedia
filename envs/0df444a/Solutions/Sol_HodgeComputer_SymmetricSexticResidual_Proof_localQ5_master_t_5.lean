-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_t_5
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:35:35.012575+00:00
-- url     : https://prove2.me/submissions/3b947fb0-b26b-41a4-a162-0d8af2a2e456

import Definitions.Def_HodgeComputerSSR_Q5Master
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem solution :
    SymmetricSexticResidual.LocalResidueQ5.checkMasterTChunk (1) 2 = true := by
  decide +kernel
