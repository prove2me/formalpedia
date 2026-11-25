-- Prove2me | solution 1 for GlobalTheory.TateDecomp.norm_l_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:49:02.372075+00:00
-- url     : https://prove2.me/submissions/f0504c24-95e9-4151-8e7f-f41803589691

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers
import Theorems.Thm_GlobalTheory_TateDecomp_norm_io

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.TateDecomp
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.TateDecomp
theorem _root_.solution : ‖(l : PadicComplex l)‖ < 1 := by
  have h : (l : PadicComplex l) = io l (algebraMap ℚ_[l] (Om l) (l : ℚ_[l])) := by simp
  rw [h, norm_io, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one
end GlobalTheory.TateDecomp
