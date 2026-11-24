-- Prove2me | solution 3 for HodgeComputer.SymmetricSexticResidual.certificate
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T23:19:29.745659+00:00
-- url     : https://prove2.me/submissions/a2bf1bcb-0230-407f-9034-c990923d82a7

import Definitions.Def_DiamondCertificate
import Definitions.Def_HodgeComputerSymmetricSexticResidual
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_certificate_of_K5_pde
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_exists_K5_pde_solution

set_option autoImplicit false

theorem solution :
    HodgeComputer.HasCertificate
      (n := HodgeComputer.SymmetricSexticResidual.n)
      HodgeComputer.SymmetricSexticResidual.F
      HodgeComputer.SymmetricSexticResidual.A
      HodgeComputer.SymmetricSexticResidual.d
      HodgeComputer.SymmetricSexticResidual.q := by
  obtain ⟨w, hw⟩ := HodgeComputer.SymmetricSexticResidual.Proof.exists_K5_pde_solution
  exact HodgeComputer.SymmetricSexticResidual.Proof.certificate_of_K5_pde w hw
