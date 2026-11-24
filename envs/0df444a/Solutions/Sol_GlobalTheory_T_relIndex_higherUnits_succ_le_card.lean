-- Prove2me | solution 1 for GlobalTheory.T.relIndex_higherUnits_succ_le_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:21:17.826325+00:00
-- url     : https://prove2.me/submissions/4c75eb35-339a-4679-ba31-aac7f32a8501

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexHigherUnitsSuccLeCard
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexHigherUnitsSuccLeCardStatement
import Theorems.Thm_GlobalTheory_QNorm_relIndex_hiUnits_succ_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (π : K) (R : Finset K) (n : ℕ), w π = WithZero.exp (-1) → (∀ x : K, w x ≤ 1 → ∃ r ∈ R, w (x - r) < 1) → (hiUnits w (n + 1)).relIndex (hiUnits w n) ≠ 0 ∧ (hiUnits w (n + 1)).relIndex (hiUnits w n) ≤ R.card := by
  first | exact @GlobalTheory.QNorm.relIndex_hiUnits_succ_le | exact GlobalTheory.QNorm.relIndex_hiUnits_succ_le | (intros; apply GlobalTheory.QNorm.relIndex_hiUnits_succ_le <;> assumption)
end _root_.GlobalTheory.T
