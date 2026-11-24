-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.global_biv_x0
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:47:36.23882+00:00
-- url     : https://prove2.me/submissions/29b36ac1-7231-4d62-9bee-46c88791cd08

import Definitions.Def_HodgeComputerSSR_GlobalBiv
import Theorems.Thm_HodgeComputer_Formal_KroneckerCheck_biv_denote_eq_of_kronecker3

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem solution :
    SymmetricSexticResidual.LocalResidueU0.evalBivK5
      (SymmetricSexticResidual.LocalResidueU0.bivFilterX0
        SymmetricSexticResidual.LocalResidueQ5.LHS_glob_biv) = 0 := by
  have h := HodgeComputer.Formal.KroneckerCheck.biv_denote_eq_of_kronecker3
    SymmetricSexticResidual.LocalResidueU0.vK5
    SymmetricSexticResidual.K5Field.x_K SymmetricSexticResidual.K5Field.y_K
    18 16 16 (2 ^ 105)
    (SymmetricSexticResidual.LocalResidueU0.bivFilterX0 SymmetricSexticResidual.LocalResidueQ5.LHS_glob_biv)
    .nil (by decide +kernel)
  simpa only [SymmetricSexticResidual.LocalResidueU0.evalBivK5,
    PolynomialEncoding.BivariateExpressions.denote] using h
