-- Prove2me | solution 1 for GlobalTheory.T.integers_eq_sum_zeta_pow_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:42:21.45644+00:00
-- url     : https://prove2.me/submissions/49c8cbe2-5253-4ce9-aaef-666d6ef852ce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPow
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Theorems.Thm_GlobalTheory_Cyc_integers_eq_sum_zeta_pow


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
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (i : ℕ), 2 ≤ i → ∀ ζ : Om l, IsPrimitiveRoot ζ (l ^ i) → (∀ x : Om l, x ∈ Ks K i → ‖x‖ ≤ 1 → ∃ y : Fin l → Om l, (∀ a, y a ∈ Ks K (i - 1) ∧ ‖y a‖ ≤ 1) ∧ x = ∑ a : Fin l, ζ ^ (a : ℕ) * y a) ∧ ∀ y : Fin l → Om l, (∀ a, y a ∈ Ks K (i - 1)) → ∑ a : Fin l, ζ ^ (a : ℕ) * y a = 0 → ∀ a, y a = 0 := by
  first | exact @GlobalTheory.Cyc.integers_eq_sum_zeta_pow | exact GlobalTheory.Cyc.integers_eq_sum_zeta_pow | (intros; apply GlobalTheory.Cyc.integers_eq_sum_zeta_pow <;> assumption)
end _root_.GlobalTheory.T
