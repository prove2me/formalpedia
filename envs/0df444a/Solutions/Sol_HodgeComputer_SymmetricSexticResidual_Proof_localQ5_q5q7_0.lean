-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.localQ5_q5q7_0
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T22:17:10.541294+00:00
-- url     : https://prove2.me/submissions/5837bccc-d448-4510-861d-0ab9a4ede038

import Definitions.Def_HodgeComputerSSR_Q5Weights
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem solution :
    SymmetricSexticResidual.LocalResidueQ5.checkQ5Q7Bounds = true ∧ SymmetricSexticResidual.LocalResidueQ5.checkQ5Q7Chunk (-24) 10 = true :=
  ⟨by decide +kernel, by decide +kernel⟩
