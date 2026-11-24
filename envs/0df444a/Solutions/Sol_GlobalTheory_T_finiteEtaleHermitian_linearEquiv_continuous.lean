-- Prove2me | solution 1 for GlobalTheory.T.finiteEtaleHermitian_linearEquiv_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:09:37.283901+00:00
-- url     : https://prove2.me/submissions/80d9739a-746f-4cce-bf5c-cf82282f6fce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteEtaleHermitianLinearEquivContinuous
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteEtaleHermitianLinearEquivContinuousStatement
import Theorems.Thm_GlobalTheory_JR_et_equiv_continuous


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), Continuous j ∧ Continuous j.symm := by
  first | exact @GlobalTheory.JR.et_equiv_continuous | exact GlobalTheory.JR.et_equiv_continuous | (intros; apply GlobalTheory.JR.et_equiv_continuous <;> assumption)
end _root_.GlobalTheory.T
