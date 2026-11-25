-- Prove2me | solution 1 for GlobalTheory.Mass.PrimDisc.lat_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:59:32.238885+00:00
-- url     : https://prove2.me/submissions/f907704b-cbd4-47b5-b447-2ddb2ac87d09

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCountStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveHermitianSublatticeDiscriminantGenerato

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.PrimDisc
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [StarRing K] [FiniteDimensional K V]
namespace GlobalTheory.Mass.PrimDisc
theorem _root_.solution (A : Submodule K V) (p : V →ₗ[K] A) (hp : Function.Surjective p)
    (N : Submodule (𝓞 K) V) (hN : Submodule.IsLattice K N) :
    Submodule.IsLattice K (N.map (p.restrictScalars (𝓞 K))) := by
  refine ⟨hN.fg.map _, ?_⟩
  have e : ((N.map (p.restrictScalars (𝓞 K)) : Submodule (𝓞 K) A) : Set A) = p '' (N : Set V) := rfl
  rw [e, ← Submodule.map_span, hN.span_eq_top, Submodule.map_top, LinearMap.range_eq_top.2 hp]
end GlobalTheory.Mass.PrimDisc
