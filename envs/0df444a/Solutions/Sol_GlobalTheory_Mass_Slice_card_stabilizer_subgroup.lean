-- Prove2me | solution 1 for GlobalTheory.Mass.Slice.card_stabilizer_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:30:30.516695+00:00
-- url     : https://prove2.me/submissions/41510253-1725-452f-8f55-22acf6942c2c

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
theorem _root_.solution {G α : Type} [Group G] [MulAction G α] (H : Subgroup G) (x : α)
    (h : ∀ g : G, g • x = x → g ∈ H) :
    ENat.card (MulAction.stabilizer H x) = ENat.card (MulAction.stabilizer G x) :=
  ENat.card_congr
    { toFun := fun a => ⟨(a.1 : G), a.2⟩
      invFun := fun a => ⟨⟨a.1, h a.1 a.2⟩, a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
end GlobalTheory.Mass.Slice
