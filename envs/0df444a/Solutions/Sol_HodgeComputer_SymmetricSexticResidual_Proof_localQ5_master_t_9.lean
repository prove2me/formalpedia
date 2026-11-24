-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_t_9
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:39:17.953498+00:00
-- url     : https://prove2.me/submissions/32429b06-ac9c-4bcc-8f18-eab153a90818

import Definitions.Def_HodgeComputerSSR_Q5Master
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem solution :
    SymmetricSexticResidual.LocalResidueQ5.checkMasterTChunk (9) 2 = true := by
  decide +kernel
