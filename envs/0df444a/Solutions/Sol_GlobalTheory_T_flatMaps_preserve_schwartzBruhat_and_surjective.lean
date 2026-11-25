-- Prove2me | solution 1 for GlobalTheory.T.flatMaps_preserve_schwartzBruhat_and_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:17:58.48612+00:00
-- url     : https://prove2.me/submissions/cdb93c96-1866-4a2a-a888-7179cc8e2d01

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjectiveStatement
import Theorems.Thm_GlobalTheory_LocFlat_flat_SB_onto


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → (p ≤ c + 1 → (∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.LocFlat.flCol ψ ν p Φ ∈ SB _) ∧ ∀ Ψ ∈ SB (Matrix n (n' ⊕ Unit) k), ∃ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.LocFlat.flCol ψ ν p Φ = Ψ) ∧ (p ≤ c → (∀ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.LocFlat.flRow ψ ν p Φ ∈ SB _) ∧ ∀ Ψ ∈ SB (Matrix (n ⊕ Unit) n' k), ∃ Φ ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), GlobalTheory.LocFlat.flRow ψ ν p Φ = Ψ) := by
  first | exact @GlobalTheory.LocFlat.flat_SB_onto | exact GlobalTheory.LocFlat.flat_SB_onto | (intros; apply GlobalTheory.LocFlat.flat_SB_onto <;> assumption)
end _root_.GlobalTheory.T
