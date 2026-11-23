-- Prove2me | solution 1 for GlobalTheory.LocMod.Inhab.isCompact_box
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:32.69694+00:00
-- url     : https://prove2.me/submissions/7fe05b47-4af1-4ddb-9207-88cefb21f84b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AddCharConductorAndHaarIntegersExist
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Theorems.Thm_GlobalTheory_LocMod_Inhab_box_eq
import Theorems.Thm_GlobalTheory_SplitWeil_isCompact_cball


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
theorem _root_.solution (a : kˣ) : IsCompact (box Y Y' a : Set (Matrix Y Y' k)) := by
  rw [box_eq]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_cball a
end GlobalTheory.LocMod.Inhab
