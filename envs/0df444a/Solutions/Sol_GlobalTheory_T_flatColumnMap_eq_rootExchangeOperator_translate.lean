-- Prove2me | solution 1 for GlobalTheory.T.flatColumnMap_eq_rootExchangeOperator_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:13:05.491035+00:00
-- url     : https://prove2.me/submissions/13a9b333-400e-42c7-a6ab-74efab38c624

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnMapEqRootExchangeOperatorTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnMapEqRootExchangeOperatorTranslateStatement
import Theorems.Thm_GlobalTheory_LocFlat_flCol_eq_opE_colE


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), ∀ x : Matrix n (n' ⊕ Unit) k, GlobalTheory.LocFlat.flCol ψ ν p Φ x = opE ψ ν p (fun z => Φ ((colE c p fun r => x r (Sum.inr ())).val * z)) x.toCols₁ := by
  first | exact @GlobalTheory.LocFlat.flCol_eq_opE_colE | exact GlobalTheory.LocFlat.flCol_eq_opE_colE | (intros; apply GlobalTheory.LocFlat.flCol_eq_opE_colE <;> assumption)
end _root_.GlobalTheory.T
