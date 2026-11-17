-- Prove2me | solution 1 for N25.GlobalKummer.quotientDivisionCocycle_levelS
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:39:22.588741+00:00
-- url     : https://prove2.me/submissions/2ca398fc-8096-4dbd-87cf-415a95a2a53d

import Definitions.Def_N25_GlobalKummerQuotient
import Theorems.Thm_N25_GlobalKummer_divisionCocycle_levelS
import Definitions.Def_N25_GlobalKummerRamification
import Definitions.Def_N25_LocalKummerKernel
import Definitions.Def_N25_KummerFactorization
import Definitions.Def_N25_LocalKummerEquivariance
import Theorems.Thm_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd
import Theorems.Thm_ModularCurve_reductionQExpModL_gammaH_smul_eq_self_of_mem_inertiaSubgroupIn
import Theorems.Thm_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq_place_laurentBaseChange
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC
import Theorems.Thm_groupCohomology_exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth

set_option autoImplicit false

noncomputable section

namespace N25.GlobalKummer

/-- The literal quotient cocycle retains the actual S-unramified finite level. -/
theorem _root_.solution (hPhi : PhiFiveZero) (K2 : K2Rows)
    (P : ↥M) (Q : J) (hQ : piEnd Q = (P : J)) :
    groupCohomology.IsLevelConstantS₁ ramificationSet
      (quotientDivisionCocycle hPhi K2 P Q hQ) := by
  exact (divisionCocycle_levelS hPhi K2 P Q hQ).comp K2.q

end N25.GlobalKummer
