-- Prove2me | solution 1 for GlobalTheory.T.relIndex_congruence_subgroup_le_absNorm_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:29:10.516365+00:00
-- url     : https://prove2.me/submissions/16d7be79-7090-4e7e-b0dd-5ba6773007d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexCongruenceSubgroupLeAbsNormPow
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexCongruenceSubgroupLeAbsNormPowStatement
import Theorems.Thm_GlobalTheory_CongIndex_relIndex_le


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (G : Subgroup (V ≃ₗ[K] V)) (M : Submodule (𝓞 K) V) (𝔪 : Ideal (𝓞 K)) (B : Subgroup (V ≃ₗ[K] V)), M.FG → 𝔪 ≠ ⊥ → (∀ s ∈ G, s • M = M) → (∀ s ∈ G, (∀ x ∈ M, s x - x ∈ 𝔪 • M) → s ∈ B) → B.relIndex G ≠ 0 ∧ B.relIndex G ≤ Ideal.absNorm 𝔪 ^ (Module.finrank K (Submodule.span K (M : Set V)) ^ 2) := by
  first | exact @GlobalTheory.CongIndex.relIndex_le | exact GlobalTheory.CongIndex.relIndex_le | (intros; apply GlobalTheory.CongIndex.relIndex_le <;> assumption)
end _root_.GlobalTheory.T
