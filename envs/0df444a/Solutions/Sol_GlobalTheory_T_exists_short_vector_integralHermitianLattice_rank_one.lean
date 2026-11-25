-- Prove2me | solution 1 for GlobalTheory.T.exists_short_vector_integralHermitianLattice_rank_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:58:10.365674+00:00
-- url     : https://prove2.me/submissions/7ae2a954-1924-4e02-84ec-b23e95e3101e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsShortVectorIntegralHermitianLatticeRankOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsShortVectorIntegralHermitianLatticeRankOneStatement
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_main
import Theorems.Thm_GlobalTheory_Mass_ShortVector_main


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → Module.finrank K V = 1 → ∀ M : Submodule (𝓞 K) V, IsIntLat h M → ∃ x ∈ M, x ≠ 0 ∧ ∀ τ : K →+* ℂ, (τ (h x x)).re ≤ (2 * vInv K) * (discN h M : ℝ) ^ ((1 : ℝ) / (2 * fDeg K)) := by
  first | exact @GlobalTheory.Mass.ShortVector.main | exact GlobalTheory.Mass.ShortVector.main | (intros; apply GlobalTheory.Mass.ShortVector.main <;> assumption)
end _root_.GlobalTheory.T
