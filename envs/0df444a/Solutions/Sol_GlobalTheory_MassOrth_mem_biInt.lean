-- Prove2me | solution 1 for GlobalTheory.MassOrth.mem_biInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:01:18.453977+00:00
-- url     : https://prove2.me/submissions/4ff623c1-4125-4a49-878b-627dc6be1e44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaxVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.MassOrth
variable {K V Γ : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
namespace GlobalTheory.MassOrth
theorem _root_.solution {k : K} : k ∈ biInt v ↔ v k ≤ 1 ∧ v (star k) ≤ 1 := Iff.rfl
end GlobalTheory.MassOrth
