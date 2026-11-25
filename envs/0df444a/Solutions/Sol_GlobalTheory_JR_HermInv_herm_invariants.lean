-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.herm_invariants
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:54:11.977013+00:00
-- url     : https://prove2.me/submissions/c6441cd0-9ae6-4630-94e2-c1b9146714f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
import Theorems.Thm_GlobalTheory_JR_HermInv_part1
import Theorems.Thm_GlobalTheory_JR_HermInv_part2
import Theorems.Thm_GlobalTheory_JR_HermInv_part3
import Theorems.Thm_GlobalTheory_JR_HermInv_part4

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.HermInv
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), (∀ X : Hn r F E, ∃ a : Inv r F, HasInv X a) ∧ (∀ (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) (a : Inv r F), HasInv X a → HasInv (actU g X) a) ∧ (∀ (X₁ X₂ : Hn r F E) (a : Inv r F), Delta a ≠ 0 → HasInv X₁ a → HasInv X₂ a → ∃! g : Matrix.unitaryGroup (Fin r) E, actU g X₁ = X₂) ∧ ∀ a : Inv r F, Delta a ≠ 0 → ((∃ X : Hn r F E, HasInv X a) ↔ ∃ h : Matrix (Fin r) (Fin r) E, hᴴ * h = (hankel a).map (algebraMap F E)) := by
  intro F E _ _ _ _ _ r
  exact ⟨fun X => part1 X, fun g X a h => part2 g X a h, fun X₁ X₂ a hΔ h₁ h₂ => part3 X₁ X₂ a hΔ h₁ h₂,
    fun a hΔ => part4 a hΔ⟩
end GlobalTheory.JR.HermInv
