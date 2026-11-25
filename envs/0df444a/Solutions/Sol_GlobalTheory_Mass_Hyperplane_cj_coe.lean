-- Prove2me | solution 1 for GlobalTheory.Mass.Hyperplane.cj_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:57:56.298824+00:00
-- url     : https://prove2.me/submissions/e7523372-5ff6-41bd-879b-5425b3f5d0d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StarMemLocR

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Hyperplane
variable {K : Type} [Field K] [StarRing K]
namespace GlobalTheory.Mass.Hyperplane
theorem _root_.solution (s : 𝓞 K) : algebraMap (𝓞 K) K (cj K s) = star (algebraMap (𝓞 K) K s) := rfl
end GlobalTheory.Mass.Hyperplane
