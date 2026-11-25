-- Prove2me | solution 1 for GlobalTheory.T.cyclotomic_tate_maximalIdeal_kills_first_cohomology
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:04:08.347796+00:00
-- url     : https://prove2.me/submissions/fe06a911-a06f-4af1-8cca-613187994869

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTateMaximalIdealKillsFirstCohomology
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicTateMaximalIdealKillsFirstCohomologyStatement
import Theorems.Thm_GlobalTheory_Cyc_AveragingRankOne_cyclotomic_maximalIdeal_smul_cocycle_isCoboundary


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
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)), IsActC act → ∀ (K : FinExt l) (r : ℕ) (a : PadicComplex l), a ∈ inC (Kinf K) → ‖a‖ < 1 → ∀ c : GQ l → Fin r → PadicComplex l, CocOn (Hinf K) (fun g y k => act g (y k)) (ball l r) c → CobOn (Hinf K) (fun g y k => act g (y k)) (ball l r) (fun g => a • c g) := by
  first | exact @GlobalTheory.Cyc.AveragingRankOne.cyclotomic_maximalIdeal_smul_cocycle_isCoboundary | exact GlobalTheory.Cyc.AveragingRankOne.cyclotomic_maximalIdeal_smul_cocycle_isCoboundary | (intros; apply GlobalTheory.Cyc.AveragingRankOne.cyclotomic_maximalIdeal_smul_cocycle_isCoboundary <;> assumption)
end _root_.GlobalTheory.T
