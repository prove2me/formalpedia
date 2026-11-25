-- Prove2me | solution 1 for GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:18:56.33231+00:00
-- url     : https://prove2.me/submissions/f663a8a4-5dbb-4cfc-b516-1ce43af5c9ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerFixedIffMemCompletedIntegers
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTowerFixedIffMemCompletedIntegersStatement
import Theorems.Thm_GlobalTheory_CycInvariants_fixed_iff_mem_Ohat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)), IsActC act → ∀ (K : FinExt l) (y : PadicComplex l), ‖y‖ ≤ 1 → ((∀ h ∈ Hinf K, act h y = y) ↔ y ∈ Ohat K) := by
  first | exact @GlobalTheory.CycInvariants.fixed_iff_mem_Ohat | exact GlobalTheory.CycInvariants.fixed_iff_mem_Ohat | (intros; apply GlobalTheory.CycInvariants.fixed_iff_mem_Ohat <;> assumption)
end _root_.GlobalTheory.T
