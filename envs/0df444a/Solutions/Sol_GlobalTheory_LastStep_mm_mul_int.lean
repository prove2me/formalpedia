-- Prove2me | solution 1 for GlobalTheory.LastStep.mm_mul_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:38:56.932295+00:00
-- url     : https://prove2.me/submissions/48d347f2-c15b-4234-8120-34c50f62d3f8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowAdditiveAndRoots
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IndependentModFirstCoeffChainLastStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical GlobalTheory.FrobRoot
open GlobalTheory GlobalTheory.LastStep
namespace GlobalTheory.LastStep
theorem _root_.solution {C : Type} [Field C] {V : VF C} {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) :
    V.MM (a * b) := by
  unfold VF.MM VF.Ge at *
  rw [V.v.map_mul]
  exact add_pos_of_pos_of_nonneg ha (by simpa using hb)
end GlobalTheory.LastStep
