-- Prove2me | solution 1 for GlobalTheory.T.norm_mem_cyclotomic_layer_prime_rpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:55:16.498882+00:00
-- url     : https://prove2.me/submissions/433e1287-5674-487a-a2fb-d381ee60bd73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMemCyclotomicLayerPrimeRpow
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMemCyclotomicLayerPrimeRpowStatement
import Theorems.Thm_GlobalTheory_Cyc_norm_of_mem_Ks


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
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (j : ℕ), 1 ≤ j → ∀ x : Om l, x ∈ Ks K j → x ≠ 0 → ∃ n : ℤ, ‖x‖ = (l : ℝ) ^ ((n : ℝ) / ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1))) := by
  first | exact @GlobalTheory.Cyc.norm_of_mem_Ks | exact GlobalTheory.Cyc.norm_of_mem_Ks | (intros; apply GlobalTheory.Cyc.norm_of_mem_Ks <;> assumption)
end _root_.GlobalTheory.T
