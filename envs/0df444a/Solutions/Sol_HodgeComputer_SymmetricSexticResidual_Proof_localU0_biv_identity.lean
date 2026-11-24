-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localU0_biv_identity
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T10:12:47.592524+00:00
-- url     : https://prove2.me/submissions/d3e50c36-db31-4b0f-a11e-d4a883276a7a

import Definitions.Def_HodgeComputerSSR_U0Biv
import Theorems.Thm_HodgeComputer_Formal_KroneckerCheck_biv_denote_eq_of_kronecker3

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem solution :
    SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueU0.LHS_U0_biv =
      SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueU0.RHS_U0_biv := by
  apply HodgeComputer.Formal.KroneckerCheck.biv_denote_eq_of_kronecker3
    SymmetricSexticResidual.LocalResidueU0.vK5
    SymmetricSexticResidual.K5Field.x_K SymmetricSexticResidual.K5Field.y_K
    20 16 18 (2 ^ 140)
    SymmetricSexticResidual.LocalResidueU0.LHS_U0_biv
    SymmetricSexticResidual.LocalResidueU0.RHS_U0_biv
  decide +kernel
