-- Prove2me | solution 1 for GlobalTheory.T.unitary_generated_by_quasiReflections_and_witt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:28:51.290179+00:00
-- url     : https://prove2.me/submissions/245af852-f5f1-4cc0-b6df-102124cd3981

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryGeneratedByQuasiReflectionsAndWitt
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryGeneratedByQuasiReflectionsAndWittStatement
import Theorems.Thm_GlobalTheory_UTrans_ReflChar0_gen_and_witt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), GlobalTheory.UTrans.IsHerm σ G → (∀ γ, GlobalTheory.UTrans.IsU σ G γ → ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, GlobalTheory.UTrans.hf σ G p.1 p.1 ≠ 0 ∧ p.2 * σ p.2 = 1) ∧ γ = (l.map fun p => GlobalTheory.UTrans.tv σ G p.1 ((p.2 - 1) / GlobalTheory.UTrans.hf σ G p.1 p.1)).prod) ∧ ∀ x z : Fin n → E, GlobalTheory.UTrans.hf σ G x x ≠ 0 → GlobalTheory.UTrans.hf σ G z z = GlobalTheory.UTrans.hf σ G x x → ∃ γ, GlobalTheory.UTrans.IsU σ G γ ∧ γ *ᵥ z = x := by
  first | exact @GlobalTheory.UTrans.ReflChar0.gen_and_witt | exact GlobalTheory.UTrans.ReflChar0.gen_and_witt | (intros; apply GlobalTheory.UTrans.ReflChar0.gen_and_witt <;> assumption)
end _root_.GlobalTheory.T
