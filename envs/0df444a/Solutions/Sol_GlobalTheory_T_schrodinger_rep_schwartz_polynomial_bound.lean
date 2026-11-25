-- Prove2me | solution 1 for GlobalTheory.T.schrodinger_rep_schwartz_polynomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:24:37.654808+00:00
-- url     : https://prove2.me/submissions/3c8d77ce-49af-4c4c-a0e7-f673c5c0a84e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchrodingerRepSchwartzPolynomialBound
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchrodingerRepSchwartzPolynomialBoundStatement
import Theorems.Thm_GlobalTheory_RealWeil_SchrFamily_exists_continuous_schwartz_rhoFun


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ) (f : Sch (Fin n)), ∃ G : (Fin n ⊕ Fin n → ℝ) → Sch (Fin n), Continuous G ∧
    (∀ w, ⇑(G w) = rhoFun w ⇑f) ∧
    ∀ k m : ℕ, ∃ (C : ℝ) (N : ℕ), ∀ w, SchwartzMap.seminorm ℂ k m (G w) ≤ C * (1 + ‖w‖) ^ N := by
  first | exact @GlobalTheory.RealWeil.SchrFamily.exists_continuous_schwartz_rhoFun | exact GlobalTheory.RealWeil.SchrFamily.exists_continuous_schwartz_rhoFun | (intros; apply GlobalTheory.RealWeil.SchrFamily.exists_continuous_schwartz_rhoFun <;> assumption)
end _root_.GlobalTheory.T
