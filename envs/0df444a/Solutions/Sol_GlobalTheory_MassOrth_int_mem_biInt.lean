-- Prove2me | solution 1 for GlobalTheory.MassOrth.int_mem_biInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:12:20.066521+00:00
-- url     : https://prove2.me/submissions/0c4c915d-a0bc-42cb-9ebe-132de249aafd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaxVector
import Theorems.Thm_GlobalTheory_MassOrth_coe_starInt

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
namespace GlobalTheory.MassOrth
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    algebraMap (𝓞 K) K a ∈ biInt (w.valuation K) :=
  ⟨w.valuation_le_one a, by rw [← coe_starInt]; exact w.valuation_le_one _⟩
end GlobalTheory.MassOrth
