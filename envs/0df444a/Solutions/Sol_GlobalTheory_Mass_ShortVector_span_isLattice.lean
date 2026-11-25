-- Prove2me | solution 1 for GlobalTheory.Mass.ShortVector.span_isLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:09:55.907039+00:00
-- url     : https://prove2.me/submissions/c57241e6-e261-4f5d-b496-46eefa252929

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RegulatorLeSumSmallIdealsInClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsShortVectorIntegralHermitianLatticeRankOne

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.ShortVector
open GlobalTheory.Mass.DiscOrder
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [StarRing K]
namespace GlobalTheory.Mass.ShortVector
theorem _root_.solution (h1 : Module.finrank K V = 1) {x : V} (hx : x ≠ 0) :
    Submodule.IsLattice K (Submodule.span (𝓞 K) {x}) := by
  have : FiniteDimensional K V := Module.finite_of_finrank_eq_succ h1
  refine ⟨Submodule.fg_span_singleton x, ?_⟩
  rw [Submodule.span_span_of_tower]
  exact (finrank_eq_one_iff_of_nonzero x hx).mp h1
end GlobalTheory.Mass.ShortVector
