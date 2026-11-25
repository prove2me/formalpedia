-- Prove2me | solution 1 for GlobalTheory.T.exists_weilRepresentation_hyperbolic_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:32:25.617978+00:00
-- url     : https://prove2.me/submissions/222d9c34-456d-4148-824e-051e53cf1a10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWeilRepresentationHyperbolicSplit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWeilRepresentationHyperbolicSplitStatement
import Theorems.Thm_GlobalTheory_JR_weil_hyperbolic


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → IsField A.K → ¬ IsField A.L → ∀ (x : A.Kˣ) (μ : Measure A.L), SelfDual μ (A.kerL ψ x) → ∃ W, A.IsWeil ψ x A.etaK μ 1 W := by
  first | exact @GlobalTheory.JR.weil_hyperbolic | exact GlobalTheory.JR.weil_hyperbolic | (intros; apply GlobalTheory.JR.weil_hyperbolic <;> assumption)
end _root_.GlobalTheory.T
