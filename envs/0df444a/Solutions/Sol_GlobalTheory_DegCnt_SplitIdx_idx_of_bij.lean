-- Prove2me | solution 1 for GlobalTheory.DegCnt.SplitIdx.idx_of_bij
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:42:51.912139+00:00
-- url     : https://prove2.me/submissions/900f468e-7bb4-46eb-acf5-89b5dd4d8192

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFlagPairLatticeSumDiscriminantEqNormMinorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormalFormTerminalDeterminant

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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.SplitIdx
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder GlobalTheory.DegCnt.DelScale
variable {R W W' : Type} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
namespace GlobalTheory.DegCnt.SplitIdx
theorem _root_.solution (f : W →+ W) (hf : Function.Bijective f) {A B A' B' : Submodule R W}
    (hA : ∀ x, f x ∈ A' ↔ x ∈ A) (hB : ∀ x, f x ∈ B' ↔ x ∈ B) : idx A' B' = idx A B := by
  have key : ∀ {C C' : Submodule R W}, (∀ x, f x ∈ C' ↔ x ∈ C) → C'.toAddSubgroup = C.toAddSubgroup.map f := by
    intro C C' h
    ext y
    obtain ⟨x, rfl⟩ := hf.2 y
    rw [AddSubgroup.mem_map]
    exact ⟨fun hx => ⟨x, (h x).1 hx, rfl⟩, fun ⟨z, hz, e⟩ => e ▸ (h z).2 hz⟩
  unfold idx
  rw [key hA, key hB]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ hf.1
end GlobalTheory.DegCnt.SplitIdx
