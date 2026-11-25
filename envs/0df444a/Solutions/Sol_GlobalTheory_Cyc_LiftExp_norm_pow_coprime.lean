-- Prove2me | solution 1 for GlobalTheory.Cyc.LiftExp.norm_pow_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:13:36.432822+00:00
-- url     : https://prove2.me/submissions/9ba3da76-e7c5-4aab-b684-3e910b082056

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Theorems.Thm_GlobalTheory_Cyc_LiftExp_norm_pow_sub_one_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.LiftExp
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.Cyc.LiftExp
theorem _root_.solution (j : ℕ) (hj : 1 ≤ j) (u : ℚ_[l]) (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ)))
    (n : ℕ) (hn : ¬ l ∣ n) : ‖u ^ n - 1‖ = (l : ℝ) ^ (-(j : ℤ)) := by
  have := norm_pow_sub_one_of j hj u hu n 0 0
    (by
      rw [neg_zero, zpow_zero, Padic.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hn)
    (by rw [neg_zero, zpow_zero]; exact IsUltrametricDist.norm_natCast_le_one _ _)
    (by omega) (by omega)
  simpa using this
end GlobalTheory.Cyc.LiftExp
