-- Prove2me | solution 1 for GlobalTheory.Mass.SplitOver.mem_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:10:15.875625+00:00
-- url     : https://prove2.me/submissions/efe3bb90-e1bc-4103-abe3-568cb261a28a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUnimodularOverlatticeCyclicSplitDiscrimina
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_conj_eq


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
theorem _root_.solution (P : Ideal (𝓞 K)) (r : 𝓞 K) : r ∈ conjIdeal (K := K) P ↔ cj r ∈ P := by
  rw [locBasic_conj_eq genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range, Ideal.mem_comap]
end GlobalTheory.Mass.SplitOver
