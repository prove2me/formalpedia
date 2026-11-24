-- Prove2me | solution 1 for GlobalTheory.T.kerL_eq_trace_dotProduct_of_isIsom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:17:11.552802+00:00
-- url     : https://prove2.me/submissions/ef858d83-403a-4afb-81a7-fbbaf8b8d1ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KerLEqTraceDotProductOfIsIsom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_KerLEqTraceDotProductOfIsIsomStatement
import Theorems.Thm_GlobalTheory_JR_Et_kerL_eq_of_isIsom


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ y' y : A.L, A.kerL ψ x y' y = ψ (Algebra.trace F E (star (j y') ⬝ᵥ j y)) := by
  first | exact @GlobalTheory.JR.Et.kerL_eq_of_isIsom | exact GlobalTheory.JR.Et.kerL_eq_of_isIsom | (intros; apply GlobalTheory.JR.Et.kerL_eq_of_isIsom <;> assumption)
end _root_.GlobalTheory.T
