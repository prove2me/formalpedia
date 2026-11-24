-- Prove2me | solution 1 for HodgeComputer.SymmetricSexticResidual.Proof.cover_X15_dvd
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-24T08:47:18.379917+00:00
-- url     : https://prove2.me/submissions/3a5e0be7-a4fa-4da4-9e54-018f841cb31c

import Definitions.Def_HodgeComputerFormal_LaurentJets
import Definitions.Def_HodgeComputerSSR_K5Field
import Definitions.Def_HodgeComputerSSR_CoverParams
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_X15_W1_val
import Theorems.Thm_HodgeComputer_SymmetricSexticResidual_Proof_cover_X15_W2_val

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SymmetricSexticResidual.CoverAlgebra
open SymmetricSexticResidual.K5Field QuadraticCovers Polynomial
open scoped LaurentSeries PowerSeries

noncomputable section CoverX15Dvd

lemma X_pow_15_dvd_nm_z_K5 : (X : K5[X]) ^ 15 ∣ k5Params.nm_z := by
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  apply coeff_eq_zero_of_HasValGe_evalT (d := 15) _ hk
  have hnm : evalT k5Params.nm_z =
      PairAlg.evalAt W1_0 (PairAlg.map evalT k5Params.res_z) *
      PairAlg.evalAt W2_0 (PairAlg.map evalT k5Params.res_z) := by
    rw [CoverParams.nm_z, CoverParams.pnm, PairAlg.map_nm]
    exact PairAlg.evalAt_nm _ _ W1_0 W2_0 W1_W2_0_sum W1_W2_0_prod _
  rw [hnm]
  exact (HodgeComputer.SymmetricSexticResidual.Proof.cover_X15_W1_val.mul
    HodgeComputer.SymmetricSexticResidual.Proof.cover_X15_W2_val).mono (by omega)

end CoverX15Dvd
end SymmetricSexticResidual.CoverAlgebra

theorem solution :
    (Polynomial.X : Polynomial SymmetricSexticResidual.K5Field.K5) ^ 15 ∣
      SymmetricSexticResidual.CoverAlgebra.k5Params.nm_z :=
  SymmetricSexticResidual.CoverAlgebra.X_pow_15_dvd_nm_z_K5
