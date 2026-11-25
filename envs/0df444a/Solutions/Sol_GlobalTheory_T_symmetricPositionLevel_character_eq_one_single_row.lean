-- Prove2me | solution 1 for GlobalTheory.T.symmetricPositionLevel_character_eq_one_single_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:19:27.931223+00:00
-- url     : https://prove2.me/submissions/2e3e4478-902e-44d1-852a-cebaddd85777

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricPositionLevelCharacterEqOneSingleRow
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricPositionLevelCharacterEqOneSingleRowStatement
import Theorems.Thm_GlobalTheory_lam_purerow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (ϖ : kˣ) (ρ κ l : ℕ) (P : TypeDatum k (Fin κ ⊕ Fin l)), GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsSymLevel ψ ϖ ρ P → ∀ (i₀ : Fin l) (g : P.J), (∀ a b, a ≠ Sum.inr i₀ → (g : GL (Fin κ ⊕ Fin l) k).val a b = (1 : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) a b) → (∀ i : Fin l, i.val = i₀.val + 1 → (g : GL (Fin κ ⊕ Fin l) k).val (Sum.inr i₀) (Sum.inr i) = 0) → P.lam g = 1 := by
  first | exact @GlobalTheory.lam_purerow | exact GlobalTheory.lam_purerow | (intros; apply GlobalTheory.lam_purerow <;> assumption)
end _root_.GlobalTheory.T
