-- Prove2me | solution 1 for GlobalTheory.Cyc.norm_pow_pow_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:17:25.205695+00:00
-- url     : https://prove2.me/submissions/ac97ae27-82c5-477c-847b-fac795164113

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValIntStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowSubOneLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorProperties
import Theorems.Thm_GlobalTheory_T_padic_norm_zpow_sub_one_padicValInt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc
theorem _root_.solution (j : ℕ) (hj : Lev l j) (u : ℚ_[l])
    (hu : ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ))) (b : ℕ) :
    ‖u ^ (l ^ b) - 1‖ = (l : ℝ) ^ (-((j + b : ℕ) : ℤ)) := by
  have hl : l.Prime := Fact.out
  have h := GlobalTheory.T.padic_norm_zpow_sub_one_padicValInt l j hj u hu ((l ^ b : ℕ) : ℤ) (by exact_mod_cast pow_ne_zero _ hl.ne_zero)
  rw [zpow_natCast, padicValInt.of_nat, padicValNat.prime_pow] at h
  rw [h]; push_cast; rfl
end GlobalTheory.Cyc
