-- Prove2me | solution 1 for GlobalTheory.ChainStep.mm_mul_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:33:57.376029+00:00
-- url     : https://prove2.me/submissions/f17a7cca-df6e-4f57-8df6-4def2beab100

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainStepKernelRankLeModMaxIdeal

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
theorem _root_.solution {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  unfold VF.MM at *
  unfold VF.Ge at hb
  rw [V.v.map_mul]
  exact lt_of_lt_of_le ha (le_add_of_nonneg_right (by simpa using hb))
end GlobalTheory.ChainStep
