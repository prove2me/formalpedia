-- Prove2me | solution 1 for GlobalTheory.LatPair.VolStep.region_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:37:39.020708+00:00
-- url     : https://prove2.me/submissions/f9945bef-2169-4a9c-8e14-6110a4e61441

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
namespace GlobalTheory.LatPair.VolStep
theorem _root_.solution {n : Type} (c : ℕ) (q : Unif k) (L : Submodule 𝒪[k] (n ⊕ Fin c → k)) (i : ℕ) :
    {y : n ⊕ Fin i → k | flagIn c i y ∈ qStep q L i} =
      (fun y : n ⊕ Fin i → k => q.inv • flagIn c i y) ⁻¹' (L : Set (n ⊕ Fin c → k)) := by
  ext y
  refine ⟨fun h => h.1, fun h => ⟨h, fun l hl => ?_⟩⟩
  simp [flagIn, not_lt.2 hl]
end GlobalTheory.LatPair.VolStep
