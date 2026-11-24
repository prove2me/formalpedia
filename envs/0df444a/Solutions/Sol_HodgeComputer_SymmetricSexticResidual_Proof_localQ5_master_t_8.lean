-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_t_8
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:39:14.14826+00:00
-- url     : https://prove2.me/submissions/f61465a7-cc4e-41e2-a403-bca81ef7972b

import Definitions.Def_HodgeComputerSSR_Q5Master
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem solution :
    SymmetricSexticResidual.LocalResidueQ5.checkMasterTChunk (7) 2 = true := by
  decide +kernel
