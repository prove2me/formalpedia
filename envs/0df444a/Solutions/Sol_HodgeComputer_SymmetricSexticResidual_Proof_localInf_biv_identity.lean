-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localInf_biv_identity
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T17:55:03.269202+00:00
-- url     : https://prove2.me/submissions/6ae882fc-3704-4ef5-b808-d0b6d80400d7

import Definitions.Def_HodgeComputerSSR_LocalInfBivId
import Theorems.Thm_HodgeComputer_Formal_KroneckerCheck_biv_denote_eq_of_kronecker3

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem solution :
    SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.LHS_Uinf_biv =
      SymmetricSexticResidual.LocalResidueU0.evalBivK5 SymmetricSexticResidual.LocalResidueInf.RHS_Uinf_biv := by
  exact HodgeComputer.Formal.KroneckerCheck.biv_denote_eq_of_kronecker3
    SymmetricSexticResidual.LocalResidueU0.vK5
    SymmetricSexticResidual.K5Field.x_K SymmetricSexticResidual.K5Field.y_K
    19 16 22 (2 ^ 136)
    SymmetricSexticResidual.LocalResidueInf.LHS_Uinf_biv
    SymmetricSexticResidual.LocalResidueInf.RHS_Uinf_biv
    (by decide +kernel)
