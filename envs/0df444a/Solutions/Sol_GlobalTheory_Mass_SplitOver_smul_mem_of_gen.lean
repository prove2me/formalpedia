-- Prove2me | solution 1 for GlobalTheory.Mass.SplitOver.smul_mem_of_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:55:24.221801+00:00
-- url     : https://prove2.me/submissions/b8861808-3bac-47e7-a415-e4aff8b2515e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUnimodularOverlatticeCyclicSplitDiscrimina

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
theorem _root_.solution {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] {A B : Submodule R W}
    {I : Ideal R} {x : W} (h1 : ∀ y ∈ A, ∃ r : R, y - r • x ∈ B) (h2 : ∀ r : R, r • x ∈ B ↔ r ∈ I)
    {s : R} (hs : s ∈ I) {y : W} (hy : y ∈ A) : s • y ∈ B := by
  obtain ⟨r, hr⟩ := h1 y hy
  have : s • y = s • (y - r • x) + (s * r) • x := by rw [smul_sub, mul_smul, sub_add_cancel]
  rw [this]
  exact B.add_mem (B.smul_mem s hr) ((h2 _).2 (I.mul_mem_right r hs))
end GlobalTheory.Mass.SplitOver
