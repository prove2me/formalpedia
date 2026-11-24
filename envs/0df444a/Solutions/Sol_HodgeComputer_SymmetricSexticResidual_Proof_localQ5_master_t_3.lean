-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_t_3
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:32:34.617474+00:00
-- url     : https://prove2.me/submissions/a7b76cbe-3518-4ce1-a743-2b52336c7801

import Definitions.Def_HodgeComputerSSR_Q5Master
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem solution :
    SymmetricSexticResidual.LocalResidueQ5.checkMasterTChunk (-3) 2 = true := by
  decide +kernel
