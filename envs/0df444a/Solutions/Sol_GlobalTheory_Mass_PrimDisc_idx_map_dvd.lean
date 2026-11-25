-- Prove2me | solution 1 for GlobalTheory.Mass.PrimDisc.idx_map_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:09:53.212941+00:00
-- url     : https://prove2.me/submissions/5e815316-c26d-4d9c-8a1b-b10ead5c19b2

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
omit [StarRing K] [FiniteDimensional K V] [NumberField K]
namespace GlobalTheory.Mass.PrimDisc
theorem _root_.solution (A : Submodule K V) (p : V →ₗ[K] A) (L N : Submodule (𝓞 K) V) :
    idxN (N.map (p.restrictScalars (𝓞 K))) (L.map (p.restrictScalars (𝓞 K))) ∣ idxN N L := by
  unfold idxN
  rw [Submodule.map_toAddSubgroup _ N, ← AddSubgroup.relIndex_comap]
  exact AddSubgroup.relIndex_dvd_of_le_left _ fun x hx => ⟨x, hx, rfl⟩
end GlobalTheory.Mass.PrimDisc
