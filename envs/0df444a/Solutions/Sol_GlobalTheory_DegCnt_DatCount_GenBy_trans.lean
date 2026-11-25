-- Prove2me | solution 1 for GlobalTheory.DegCnt.DatCount.GenBy.trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:16:04.03245+00:00
-- url     : https://prove2.me/submissions/1983e935-7e38-4041-8b53-cfae75e260f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEmbeddedDataWithGivenFixedLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.DatCount
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [NumberField K] [StarRing K] [Module K V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.DatCount
namespace GenBy
theorem _root_.solution {A B C : Submodule (𝓞 K) V} {e e' : ℕ} (h1 : GenBy A B e) (h2 : GenBy B C e') :
    GenBy A C (e + e') := by
  obtain ⟨t, hc, rfl⟩ := h1
  obtain ⟨t', hc', rfl⟩ := h2
  refine ⟨t ∪ t', (Finset.card_union_le _ _).trans (by omega), ?_⟩
  rw [Finset.coe_union, Submodule.span_union, sup_assoc, sup_comm (Submodule.span _ (t' : Set V))]
end GenBy
end GlobalTheory.DegCnt.DatCount
