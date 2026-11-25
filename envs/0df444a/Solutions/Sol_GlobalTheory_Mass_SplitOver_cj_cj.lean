-- Prove2me | solution 1 for GlobalTheory.Mass.SplitOver.cj_cj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:55:07.04081+00:00
-- url     : https://prove2.me/submissions/7431f1ed-7ed0-4343-8721-f4bcf70500fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUnimodularOverlatticeCyclicSplitDiscrimina
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_sigma_spec


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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.SplitOver
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.Mass.SplitOver
theorem _root_.solution (r : 𝓞 K) : cj (cj r) = r := genusCovol_hinj (by
  rw [locBasic_sigma_spec, locBasic_sigma_spec, star_star])
end GlobalTheory.Mass.SplitOver
