-- Prove2me | solution 1 for GlobalTheory.RootEx.UnfoldShape.colMat_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:06:17.508425+00:00
-- url     : https://prove2.me/submissions/5beb9945-2c5e-464b-b582-e475f8d75aca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_ExponentTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnfoldShape
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms
variable {k : Type} [Field k] [ValuativeRel k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [ValuativeRel k] [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
variable {k : Type} [Field k] [ValuativeRel k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [ValuativeRel k] [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
namespace GlobalTheory.RootEx.UnfoldShape
namespace _root_.GlobalTheory.RootEx.UnfoldShape
theorem _root_.solution (a : k) (y : Fin c → (n ⊕ Fin c → k)) :
    _root_.GlobalTheory.RootEx.UnfoldShape.colMat n' (a • y) = a • _root_.GlobalTheory.RootEx.UnfoldShape.colMat n' y := by
  ext r (s | j)
  · simp [_root_.GlobalTheory.RootEx.UnfoldShape.colMat]
  · refine Fin.cases ?_ (fun i => ?_) j <;> simp [_root_.GlobalTheory.RootEx.UnfoldShape.colMat]
end _root_.GlobalTheory.RootEx.UnfoldShape
end GlobalTheory.RootEx.UnfoldShape
