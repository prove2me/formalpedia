-- Prove2me | solution 1 for IsLocalRing.etale_of_finite_of_finrank_eq_finrank_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/2c22f351-c0e5-58de-a1ca-4d1f4989f3eb

import Mathlib
import Theorems.Thm_Algebra_Etale_of_etale_adicCompletion_tensorProduct
import Theorems.Thm_IsLocalRing_etale_adicCompletion_tensorProduct_of_finite_of_finrank_eq_finrank_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_etale_of_finite_of_finrank_eq_finrank_residueField

set_option autoImplicit false

theorem solution
    {O C : Type*} [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsLocalRing O]
    [CommRing C] [IsDomain C] [IsNoetherianRing C] [IsLocalRing C]
    [Algebra O C] [Module.Finite O C] [FaithfulSMul O C] [IsLocalHom (algebraMap O C)]
    (hO : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal O) O) ∧
      IsIntegrallyClosed (AdicCompletion (IsLocalRing.maximalIdeal O) O))
    (hC : IsDomain (AdicCompletion (IsLocalRing.maximalIdeal C) C))
    (K₁ K : Type*) [Field K₁] [Field K] [Algebra O K₁] [IsFractionRing O K₁]
    [Algebra C K] [IsFractionRing C K] [Algebra K₁ K] [Algebra O K]
    [IsScalarTower O C K] [IsScalarTower O K₁ K]
    [Algebra.IsSeparable (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField C)]
    (hcount : Module.finrank K₁ K =
      Module.finrank (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField C)) :
    Algebra.Etale O C :=
  Algebra.Etale.of_etale_adicCompletion_tensorProduct
    (IsLocalRing.etale_adicCompletion_tensorProduct_of_finite_of_finrank_eq_finrank_residueField hO hC K₁ K hcount)

end S_IsLocalRing_etale_of_finite_of_finrank_eq_finrank_residueField
end P2MW
export P2MW.S_IsLocalRing_etale_of_finite_of_finrank_eq_finrank_residueField (solution)
