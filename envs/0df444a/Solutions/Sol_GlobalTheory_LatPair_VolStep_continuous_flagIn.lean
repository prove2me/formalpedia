-- Prove2me | solution 1 for GlobalTheory.LatPair.VolStep.continuous_flagIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:37:37.606971+00:00
-- url     : https://prove2.me/submissions/b670b1ab-c153-4480-931b-dbe036fa81dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FlagVolumeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FlagVolumeOpenFiniteNonzero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LatPair GlobalTheory.IndefiniteRowSideFullHecke.FlagVolumeFiltration
open scoped Pointwise ENNReal
noncomputable section
open GlobalTheory GlobalTheory.LatPair GlobalTheory.LatPair.VolStep
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
omit [ValuativeRel k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.LatPair.VolStep
theorem _root_.solution {n : Type} (c i : ℕ) : Continuous (flagIn (k := k) (n := n) c i) := by
  refine continuous_pi fun j => ?_
  rcases j with r | l
  · exact continuous_apply _
  · by_cases h : l.val < i
    · simp only [flagIn, Sum.elim_inr, dif_pos h]
      exact continuous_apply _
    · simp only [flagIn, Sum.elim_inr, dif_neg h]
      exact continuous_const
end GlobalTheory.LatPair.VolStep
