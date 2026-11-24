-- Prove2me | solution 1 for GlobalTheory.HaarScaleMatrix.secondCountable_of_localField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:11:21.766474+00:00
-- url     : https://prove2.me/submissions/ab67630a-6ca2-49f7-8656-7caf3af596d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRk
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarMeasureAdditiveAutomorphismScale
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.FullRankCoinv MeasureTheory
open GlobalTheory GlobalTheory.HaarScaleMatrix
open scoped Matrix
open MeasureTheory
namespace GlobalTheory.HaarScaleMatrix
namespace _root_.GlobalTheory.HaarScaleMatrix
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] : SecondCountableTopology k :=
  _root_.GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field.1
end _root_.GlobalTheory.HaarScaleMatrix
end GlobalTheory.HaarScaleMatrix
