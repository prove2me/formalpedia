-- Prove2me | solution 1 for GlobalTheory.Mass.Slice.exists_smul_eq_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:31:27.184398+00:00
-- url     : https://prove2.me/submissions/d5aff9f4-9326-4dab-b3e0-7c0a238e38cb

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
theorem _root_.solution (G : Type) {α : Type} [Group G] [MulAction G α] (x : α) :
    ∃ g : G, g • x = Quotient.out (Quotient.mk (MulAction.orbitRel G α) x) := by
  have h : (MulAction.orbitRel G α) (Quotient.out (Quotient.mk (MulAction.orbitRel G α) x)) x :=
    Quotient.exact (Quotient.out_eq _)
  exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
end GlobalTheory.Mass.Slice
