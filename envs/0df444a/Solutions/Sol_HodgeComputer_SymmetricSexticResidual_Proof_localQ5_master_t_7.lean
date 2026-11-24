-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_t_7
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:37:17.624807+00:00
-- url     : https://prove2.me/submissions/3237264c-ca43-44ea-8f33-4f2798d93918

import Definitions.Def_HodgeComputerSSR_Q5Master
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem solution :
    SymmetricSexticResidual.LocalResidueQ5.checkMasterTChunk (5) 2 = true := by
  decide +kernel
