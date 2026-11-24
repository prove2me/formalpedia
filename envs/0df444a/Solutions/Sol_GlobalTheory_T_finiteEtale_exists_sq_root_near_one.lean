-- Prove2me | solution 1 for GlobalTheory.T.finiteEtale_exists_sq_root_near_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:09:38.122494+00:00
-- url     : https://prove2.me/submissions/c1912f2f-223d-4667-8ad6-81fdf0137bde

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteEtaleExistsSqRootNearOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteEtaleExistsSqRootNearOneStatement
import Theorems.Thm_GlobalTheory_JR_SqrtNearOne_exists_sq_eq_inv_near_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ∀ U ∈ 𝓝 (1 : A.K), ∀ᶠ v in 𝓝 (1 : A.K), ∃ s ∈ U, ∃ s' ∈ U, s * s' = 1 ∧ s ^ 2 = v := by
  first | exact @GlobalTheory.JR.SqrtNearOne.exists_sq_eq_inv_near_one | exact GlobalTheory.JR.SqrtNearOne.exists_sq_eq_inv_near_one | (intros; apply GlobalTheory.JR.SqrtNearOne.exists_sq_eq_inv_near_one <;> assumption)
end _root_.GlobalTheory.T
