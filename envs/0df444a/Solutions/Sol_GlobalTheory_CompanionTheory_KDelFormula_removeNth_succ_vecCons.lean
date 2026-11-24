-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KDelFormula.removeNth_succ_vecCons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:40:49.923979+00:00
-- url     : https://prove2.me/submissions/6f8ccf21-9ae2-454f-b88e-910a58ae3bf7

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RemoveNthSuccVecCons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Cz Fin Function
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KDelFormula
variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M]
namespace GlobalTheory.CompanionTheory.KDelFormula
theorem _root_.solution {n : ℕ} (x : P) (Y : Fin (n + 1) → P) (t : Fin (n + 1)) :
    t.succ.removeNth (Matrix.vecCons x Y) = Matrix.vecCons x (t.removeNth Y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Fin.removeNth]
  · simp [Fin.removeNth, Fin.succ_succAbove_succ]
end GlobalTheory.CompanionTheory.KDelFormula
