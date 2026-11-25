-- Prove2me | solution 1 for GlobalTheory.T.unitary_action_hermitian_invariants_transitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:11:57.08798+00:00
-- url     : https://prove2.me/submissions/fa60a685-80ad-423f-bfbd-16a3d6dd2a57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitiveStatement
import Theorems.Thm_GlobalTheory_JR_HermInv_herm_invariants


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), (∀ X : Hn r F E, ∃ a : Inv r F, HasInv X a) ∧ (∀ (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) (a : Inv r F), HasInv X a → HasInv (actU g X) a) ∧ (∀ (X₁ X₂ : Hn r F E) (a : Inv r F), Delta a ≠ 0 → HasInv X₁ a → HasInv X₂ a → ∃! g : Matrix.unitaryGroup (Fin r) E, actU g X₁ = X₂) ∧ ∀ a : Inv r F, Delta a ≠ 0 → ((∃ X : Hn r F E, HasInv X a) ↔ ∃ h : Matrix (Fin r) (Fin r) E, hᴴ * h = (hankel a).map (algebraMap F E)) := by
  first | exact @GlobalTheory.JR.HermInv.herm_invariants | exact GlobalTheory.JR.HermInv.herm_invariants | (intros; apply GlobalTheory.JR.HermInv.herm_invariants <;> assumption)
end _root_.GlobalTheory.T
