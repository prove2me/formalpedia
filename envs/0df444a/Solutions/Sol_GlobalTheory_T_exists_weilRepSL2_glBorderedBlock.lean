-- Prove2me | solution 1 for GlobalTheory.T.exists_weilRepSL2_glBorderedBlock
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:21:31.196652+00:00
-- url     : https://prove2.me/submissions/41f24ea0-eaf0-40d6-85ce-6260202a1b6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWeilRepSL2GlBorderedBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWeilRepSL2GlBorderedBlockStatement
import Theorems.Thm_GlobalTheory_JR_weil_repG


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
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∃ W : SpecialLinearGroup (Fin 2) F → (Gl r F → ℂ) → Gl r F → ℂ, IsTestRep W ∧ ∀ f, IsTest f → (∀ t Y, W (nS t) f Y = ψ (t * mom Y 0) * f Y) ∧ W (wS F) f = fourG M ψ f := by
  first | exact @GlobalTheory.JR.weil_repG | exact GlobalTheory.JR.weil_repG | (intros; apply GlobalTheory.JR.weil_repG <;> assumption)
end _root_.GlobalTheory.T
