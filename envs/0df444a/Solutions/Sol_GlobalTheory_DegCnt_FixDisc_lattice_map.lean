-- Prove2me | solution 1 for GlobalTheory.DegCnt.FixDisc.lattice_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:15:50.587157+00:00
-- url     : https://prove2.me/submissions/5d6dc8e8-6e83-4e0d-b2c0-8075f2399501

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DiscriminantOrderCommonFixedLatticeEmbeddedData

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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.FixDisc
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [NumberField K]
namespace GlobalTheory.DegCnt.FixDisc
theorem _root_.solution {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    {A : Submodule (𝓞 K) V} (hA : Submodule.IsLattice K A) (f : V →ₗ[K] W) (hf : Function.Surjective f) :
    Submodule.IsLattice K (A.map (f.restrictScalars (𝓞 K))) := by
  refine ⟨hA.fg.map _, ?_⟩
  have : ((A.map (f.restrictScalars (𝓞 K)) : Submodule (𝓞 K) W) : Set W) = f '' A := rfl
  rw [this, ← Submodule.map_span, hA.span_eq_top, Submodule.map_top, LinearMap.range_eq_top.2 hf]
end GlobalTheory.DegCnt.FixDisc
