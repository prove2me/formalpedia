-- Prove2me | solution 1 for GlobalTheory.IdealChain.monLat_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:49:28.534415+00:00
-- url     : https://prove2.me/submissions/691518cf-6cd0-4128-b94f-2c6ab9ee3de7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_HalfPowerSpherical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NabsDetEqOfActEq
import Theorems.Thm_GlobalTheory_IdealChain_mem_monLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical GlobalTheory.LatPair GlobalTheory.StepData
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.IdealChain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.IdealChain
theorem _root_.solution {n : Type} {c : ℕ} (L : Submodule 𝒪[k] (n → k)) {b b' : ℕ → kˣ}
    (h : ∀ i, 1 ≤ i → i ≤ c → idl (b i) = idl (b' i)) : monLat c L b = monLat c L b' := by
  ext v
  simp only [mem_monLat]
  exact and_congr_right' (forall_congr' fun i => by rw [h _ (by omega) i.2])
end GlobalTheory.IdealChain
