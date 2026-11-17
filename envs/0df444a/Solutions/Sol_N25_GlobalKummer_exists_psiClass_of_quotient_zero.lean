-- Prove2me | solution 1 for N25.GlobalKummer.exists_psiClass_of_quotient_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:40.234556+00:00
-- url     : https://prove2.me/submissions/3a2cd18c-6a9f-4d05-8348-60c2bcbe0e58

import Theorems.Thm_N25_GlobalKummer_continuous_exact
import Definitions.Def_N25_GlobalKummerSequence
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
import Theorems.Thm_groupCohomology_exists_les_continuousHS_of_shortExact_of_isLevelConstant

set_option autoImplicit false

noncomputable section

namespace N25.GlobalKummer

/-- A selected-kernel S-class whose cyclotomic quotient is zero lifts to
an actual S-class of the frozen order-five character line. -/
theorem _root_.solution (hPhi : PhiFiveZero) (K2 : K2Rows)
    (x : ↥(groupCohomology.continuousH1S ramificationSet (vRep hPhi)))
    (hx : (groupCohomology.map (MonoidHom.id Gal) (kernelQuotient hPhi K2) 1).hom
      (x : groupCohomology.H1 (vRep hPhi)) = 0) :
    ∃ a : ↥(groupCohomology.continuousH1S ramificationSet psiRep),
      (groupCohomology.map (MonoidHom.id Gal) (kernelInclusion hPhi K2) 1).hom
        (a : groupCohomology.H1 psiRep) = (x : groupCohomology.H1 (vRep hPhi)) := by
  obtain ⟨i, q, hi, hq, hex⟩ := continuous_exact hPhi K2
  have hqx : q x = 0 := by
    apply Subtype.ext
    rw [hq x]
    exact hx
  obtain ⟨a, ha⟩ := (hex x).mp hqx
  refine ⟨a, ?_⟩
  rw [← hi a, ha]

end N25.GlobalKummer
