-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_master_bounds
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:29:32.591597+00:00
-- url     : https://prove2.me/submissions/95818554-645f-4ca0-8b94-b2bb23a23afe

import Definitions.Def_HodgeComputerSSR_Q5Master
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem solution :
    SymmetricSexticResidual.LocalResidueQ5.checkMasterBounds = true := by
  decide +kernel
