-- Prove2me | solution 1 for GlobalTheory.LocMod.Inhab.finite_box
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:06.220548+00:00
-- url     : https://prove2.me/submissions/87d797bd-e1c5-4524-b784-8cf77eec55a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Theorems.Thm_GlobalTheory_LocMod_Inhab_isCompact_box
import Theorems.Thm_GlobalTheory_LocMod_Inhab_isOpen_box

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.PlaceModel Filter
open scoped Topology
open GlobalTheory GlobalTheory.LocMod GlobalTheory.LocMod.Inhab
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
namespace GlobalTheory.LocMod.Inhab
theorem _root_.solution (a b : kˣ) : Finite (box Y Y' a ⧸ (box Y Y' b).addSubgroupOf (box Y Y' a)) := by
  haveI : CompactSpace (box Y Y' a) := isCompact_iff_compactSpace.1 (isCompact_box a)
  exact AddSubgroup.quotient_finite_of_isOpen _ ((isOpen_box b).preimage continuous_subtype_val)
end GlobalTheory.LocMod.Inhab
