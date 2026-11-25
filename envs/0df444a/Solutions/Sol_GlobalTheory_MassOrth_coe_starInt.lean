-- Prove2me | solution 1 for GlobalTheory.MassOrth.coe_starInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:34:43.166636+00:00
-- url     : https://prove2.me/submissions/9e2c3cae-7eba-4f91-89f0-a321b3075ee8

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
open IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] [StarRing K]
omit [NumberField K]
namespace GlobalTheory.MassOrth
theorem _root_.solution (s : 𝓞 K) : algebraMap (𝓞 K) K (starInt s) = star (algebraMap (𝓞 K) K s) := rfl
end GlobalTheory.MassOrth
