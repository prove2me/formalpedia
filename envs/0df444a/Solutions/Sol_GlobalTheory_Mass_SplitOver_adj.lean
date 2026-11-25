-- Prove2me | solution 1 for GlobalTheory.Mass.SplitOver.adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:12:50.331342+00:00
-- url     : https://prove2.me/submissions/0d6fb647-ca9c-4d62-8c3d-617551e20f90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUnimodularOverlatticeCyclicSplitDiscrimina
import Theorems.Thm_GlobalTheory_Mass_SplitOver_cj_cj
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_hsmul_left
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_hsmul_right


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
omit [FiniteDimensional K V]
namespace GlobalTheory.Mass.SplitOver
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (r : 𝓞 K) (v w : V) : h v (r • w) = h (cj r • v) w := by
  rw [genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range, genusBasic_hsmul_right]
  exact congrArg (fun t => algebraMap (𝓞 K) K t * h v w) (cj_cj r).symm
end GlobalTheory.Mass.SplitOver
