-- Prove2me | solution 1 for GlobalTheory.T.orbitStabilizerMass_eq_weightedSum_fibres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:03:39.534959+00:00
-- url     : https://prove2.me/submissions/06484cf6-00d9-4b93-b84f-3f83180ed457

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitStabilizerMassEqWeightedSumFibres
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitStabilizerMassEqWeightedSumFibresStatement
import Theorems.Thm_GlobalTheory_Mass_orbMass_eq_orbSum_fibre


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
theorem _root_.solution : ∀ (G α β : Type) [Group G] [MulAction G α] [MulAction G β] (X : Set α) (Y : Set β) (π : α → β), (∀ (g : G) x, π (g • x) = g • π x) → Stable G X → Stable G Y → Set.MapsTo π X Y → (∀ y ∈ Y, Finite (MulAction.stabilizer G y)) → orbMass G X = orbSum G Y (fun y => (((X ∩ π ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞)) := by
  first | exact @GlobalTheory.Mass.orbMass_eq_orbSum_fibre | exact GlobalTheory.Mass.orbMass_eq_orbSum_fibre | (intros; apply GlobalTheory.Mass.orbMass_eq_orbSum_fibre <;> assumption)
end _root_.GlobalTheory.T
