-- Prove2me | solution 1 for GlobalTheory.Mass.Slice.card_stabilizer_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:30:28.43119+00:00
-- url     : https://prove2.me/submissions/b3077382-8042-41d1-9a74-6b6421916399

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitWeightedStabilizerSumRestrictSlice

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Slice
namespace GlobalTheory.Mass.Slice
theorem _root_.solution (G : Type) {α : Type} [Group G] [MulAction G α] (g : G) (x : α) :
    ENat.card (MulAction.stabilizer G (g • x)) = ENat.card (MulAction.stabilizer G x) := by
  have h : (MulAction.orbitRel G α) (g • x) x :=
    MulAction.orbitRel_apply.mpr (MulAction.mem_orbit x g)
  exact ENat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel h).toEquiv
end GlobalTheory.Mass.Slice
