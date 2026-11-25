-- Prove2me | solution 1 for GlobalTheory.Mass.LocWitt.star_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:31:01.073689+00:00
-- url     : https://prove2.me/submissions/7f391020-eaec-4532-a128-a5d90eff81bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemHcompl

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.LocWitt
namespace GlobalTheory.Mass.LocWitt
theorem _root_.solution {K : Type} [Field K] [NumberField K] [StarRing K] (r : 𝓞 K) :
    ∃ t : 𝓞 K, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K r) :=
  ⟨⟨star (r : K), (r.isIntegral_coe).map (starRingEnd K).toIntAlgHom⟩, rfl⟩
end GlobalTheory.Mass.LocWitt
