-- Prove2me | solution 1 for GlobalTheory.Mass.SemiBasis.alg_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:53.263101+00:00
-- url     : https://prove2.me/submissions/c9b35b68-e465-4d7f-848d-f1ed1b236725

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemLocDIffSpan

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
noncomputable section
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.SemiBasis
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Mass.SemiBasis
theorem _root_.solution {d : ℕ} (hd : 2 ≤ d) {s : 𝓞 K}
    (hs : s ∈ primeTo (d : 𝓞 K)) : algebraMap (𝓞 K) K s ≠ 0 :=
  IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (primeTo_le hd hs)
end GlobalTheory.Mass.SemiBasis
