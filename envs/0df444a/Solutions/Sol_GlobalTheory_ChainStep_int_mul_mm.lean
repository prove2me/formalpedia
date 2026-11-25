-- Prove2me | solution 1 for GlobalTheory.ChainStep.int_mul_mm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:40:52.962229+00:00
-- url     : https://prove2.me/submissions/f103506a-3d65-4613-9e91-443b8a7cad30

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainStepKernelRankLeModMaxIdeal
import Theorems.Thm_GlobalTheory_ChainStep_mm_mul_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
noncomputable section
open GlobalTheory GlobalTheory.ChainStep
variable {C : Type} [Field C] {V : VF C}
namespace GlobalTheory.ChainStep
theorem _root_.solution {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  rw [mul_comm]; exact mm_mul_int hb ha
end GlobalTheory.ChainStep
