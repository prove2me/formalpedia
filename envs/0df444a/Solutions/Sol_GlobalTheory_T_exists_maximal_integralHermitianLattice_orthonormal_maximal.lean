-- Prove2me | solution 1 for GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:40:45.572864+00:00
-- url     : https://prove2.me/submissions/b20e08e2-402c-454b-9f88-779e68940455

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaximalIntegralHermitianLatticeOrthonormal
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaximalIntegralHermitianLatticeOrthonormalStatement
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_main
import Theorems.Thm_GlobalTheory_Mass_MaxExists_main


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
theorem _root_.solution : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → (∀ M : Submodule (𝓞 K) V, IsIntLat h M → ∃ M', IsMaxLat h M' ∧ M ≤ M') ∧ (∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M → IsUnimodular h M → IsMaxLat h M ∧ badP h M = ∅ ∧ lamMax h M = 1) ∧ (∀ (M : Submodule (𝓞 K) V) (n : ℕ), IsOrthoLattice h M n → Submodule.IsLattice K M ∧ IsUnimodular h M ∧ Module.finrank K V = n) := by
  first | exact @GlobalTheory.Mass.MaxExists.main | exact GlobalTheory.Mass.MaxExists.main | (intros; apply GlobalTheory.Mass.MaxExists.main <;> assumption)
end _root_.GlobalTheory.T
