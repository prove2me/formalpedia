-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_t_1
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:32:11.320882+00:00
-- url     : https://prove2.me/submissions/aaf6dbd1-5968-4a8d-8dbb-d09bfd8e6d0e

import Definitions.Def_HodgeComputerSSR_Q5Master
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem solution :
    SymmetricSexticResidual.LocalResidueQ5.checkMasterTChunk (-7) 2 = true := by
  decide +kernel
