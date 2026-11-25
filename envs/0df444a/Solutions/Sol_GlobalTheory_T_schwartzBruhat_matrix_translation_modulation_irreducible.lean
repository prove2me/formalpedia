-- Prove2me | solution 1 for GlobalTheory.T.schwartzBruhat_matrix_translation_modulation_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:25:06.628026+00:00
-- url     : https://prove2.me/submissions/4c697e58-028e-4125-a520-9a51d5e7f506

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreduc
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMatrixTranslationModulationIrreducStatement
import Theorems.Thm_GlobalTheory_IrredSB_sb_irreducible


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ W : Submodule ℂ (Matrix Y Y' k → ℂ), W ≤ SB (Matrix Y Y' k) → (∀ Φ ∈ W, ∀ x : Matrix Y Y' k, (fun t => Φ (t + x)) ∈ SB (Matrix Y Y' k) → (fun t => Φ (t + x)) ∈ W) → (∀ Φ ∈ W, ∀ b : Matrix Y Y' k, (fun t => (ψk (∑ r, ∑ q, b r q * t r q) : ℂ) * Φ t) ∈ SB (Matrix Y Y' k) → (fun t => (ψk (∑ r, ∑ q, b r q * t r q) : ℂ) * Φ t) ∈ W) → ∀ Φ₀ ∈ W, Φ₀ ≠ 0 → W = SB (Matrix Y Y' k) := by
  first | exact @GlobalTheory.IrredSB.sb_irreducible | exact GlobalTheory.IrredSB.sb_irreducible | (intros; apply GlobalTheory.IrredSB.sb_irreducible <;> assumption)
end _root_.GlobalTheory.T
