-- Prove2me | solution 1 for GlobalTheory.DegCnt.DatCount.fixLat_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:11:35.66539+00:00
-- url     : https://prove2.me/submissions/bb72d773-1b8f-4668-b04c-9206a7ff11db

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
omit [NumberField K] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.DegCnt.DatCount
theorem _root_.solution {H : HermSpace K V} {g : 𝓞 K} {L' L : Submodule (𝓞 K) V} {Γ : Submodule (𝓞 K) (V × V)}
    (hΓ : IsModIso H g L' L Γ) : fixLat Γ ≤ L' ∧ fixLat Γ ≤ L :=
  ⟨fun _ hx => (hΓ.1 hx).1, fun _ hx => (hΓ.1 hx).2⟩
end GlobalTheory.DegCnt.DatCount
