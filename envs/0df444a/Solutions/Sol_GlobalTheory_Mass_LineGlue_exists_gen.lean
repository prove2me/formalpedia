-- Prove2me | solution 1 for GlobalTheory.Mass.LineGlue.exists_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:56:46.085907+00:00
-- url     : https://prove2.me/submissions/4470bda3-e776-4b50-a6b2-b7f8385187a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianLatticesGluedAlongLine
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_ne_zero
import Theorems.Thm_GlobalTheory_Mass_LatticeGens_gens_and_count


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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.LineGlue
variable {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
namespace GlobalTheory.Mass.LineGlue
theorem _root_.solution (h1 : Module.finrank K W = 1) {B C : Submodule (𝓞 K) W}
    (hB : Submodule.IsLattice K B) (hBC : B ≤ C) (hC : C.FG) :
    ∃ y, C = B ⊔ Submodule.span (𝓞 K) {y} := by
  obtain ⟨t, ht, e⟩ := (LatticeGens.gens_and_count K W B C hBC
    (DiscOrder.idxN_ne_zero hB hC)).1 hC
  rw [h1] at ht
  obtain ⟨y, hy⟩ := Finset.card_le_one_iff_subset_singleton.1 ht
  rcases Finset.subset_singleton_iff.1 hy with rfl | rfl
  · exact ⟨0, by simpa using e⟩
  · exact ⟨y, by simpa using e⟩
end GlobalTheory.Mass.LineGlue
