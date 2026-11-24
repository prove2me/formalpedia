-- Prove2me | solution 1 for GlobalTheory.PosOne.Unif.comb_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:55:30.850722+00:00
-- url     : https://prove2.me/submissions/0a287da0-83c5-4d35-9e41-9b2cda095f7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ToOneSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExchangeEqFiniteTranslateCombOfLevelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExDownExUpAndExUpExDown
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegrableOfMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExchangeToPositionOneUniformInLevel
import Theorems.Thm_GlobalTheory_PosOne_Unif_comb_eq_lc
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
open GlobalTheory GlobalTheory.PosOne GlobalTheory.PosOne.Unif
namespace GlobalTheory.PosOne.Unif
theorem _root_.solution {G : Type} [Group G] (e : G →₀ ℂ) (f : G → G →₀ ℂ) (F : G → ℂ) :
    comb e (fun g => comb (f g) (fun h => F (h * g))) =
      comb (e.sum fun g a => a • (f g).mapDomain (· * g)) F := by
  conv_rhs => rw [comb_eq_lc]
  simp only [Finsupp.sum, map_sum, map_smul, Finsupp.linearCombination_mapDomain, comb_eq_lc, smul_eq_mul]
  rfl
end GlobalTheory.PosOne.Unif
