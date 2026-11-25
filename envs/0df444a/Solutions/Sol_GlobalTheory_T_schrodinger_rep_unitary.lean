-- Prove2me | solution 1 for GlobalTheory.T.schrodinger_rep_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:24:41.127186+00:00
-- url     : https://prove2.me/submissions/6f1f8883-4164-41f0-a858-2ca68a5f4f07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchrodingerRepUnitary
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchrodingerRepUnitaryStatement
import Theorems.Thm_GlobalTheory_RealWeil_integral_rhoFun_mul_conj


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
theorem _root_.solution : ∀ (n : ℕ) (w : Fin n ⊕ Fin n → ℝ) (u v : EuclideanSpace ℝ (Fin n) → ℂ),
    ∫ x, rhoFun w u x * starRingEnd ℂ (rhoFun w v x) = ∫ x, u x * starRingEnd ℂ (v x) := by
  first | exact @GlobalTheory.RealWeil.integral_rhoFun_mul_conj | exact GlobalTheory.RealWeil.integral_rhoFun_mul_conj | (intros; apply GlobalTheory.RealWeil.integral_rhoFun_mul_conj <;> assumption)
end _root_.GlobalTheory.T
