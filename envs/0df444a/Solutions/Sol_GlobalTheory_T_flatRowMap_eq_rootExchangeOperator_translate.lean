-- Prove2me | solution 1 for GlobalTheory.T.flatRowMap_eq_rootExchangeOperator_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:21:09.766436+00:00
-- url     : https://prove2.me/submissions/d880daa6-2b38-416f-8ad9-3e980922d5dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatRowMapEqRootExchangeOperatorTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatRowMapEqRootExchangeOperatorTranslateStatement
import Theorems.Thm_GlobalTheory_LocFlat_flRow_eq_opE_rowE


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ x : Matrix (n ⊕ Unit) n' k, GlobalTheory.LocFlat.flRow ψ ν p Φ x = opE ψ ν p (fun z => Φ (z * (rowE (c + 1) p (x (Sum.inr ()))).val)) x.toRows₁ := by
  first | exact @GlobalTheory.LocFlat.flRow_eq_opE_rowE | exact GlobalTheory.LocFlat.flRow_eq_opE_rowE | (intros; apply GlobalTheory.LocFlat.flRow_eq_opE_rowE <;> assumption)
end _root_.GlobalTheory.T
