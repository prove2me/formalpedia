-- Prove2me | solution 1 for GlobalTheory.Cyc.LiftExp.zpow_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:52:01.567142+00:00
-- url     : https://prove2.me/submissions/5b37e1ef-ab6f-49dd-9c60-46c9965d7ebf

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Theorems.Thm_GlobalTheory_Cyc_LiftExp_one_lt_l

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
theorem _root_.solution {a b : ℤ} (h : a < b) : (l : ℝ) ^ a < (l : ℝ) ^ b :=
  zpow_lt_zpow_right₀ one_lt_l h
end GlobalTheory.Cyc.LiftExp
