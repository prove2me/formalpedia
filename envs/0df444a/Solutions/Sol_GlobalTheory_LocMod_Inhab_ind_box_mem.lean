-- Prove2me | solution 1 for GlobalTheory.LocMod.Inhab.ind_box_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:47:09.964369+00:00
-- url     : https://prove2.me/submissions/83c9509e-1acc-4097-9013-b8a0785f6c52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_InvariantOfTsupport
import Theorems.Thm_GlobalTheory_LocMod_Inhab_isCompact_box
import Theorems.Thm_GlobalTheory_LocMod_Inhab_isOpen_box
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_isLocallyConstant


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
theorem _root_.solution (a : kˣ) : ind (box Y Y' a) ∈ SB (Matrix Y Y' k) := by
  have hcl : IsClopen (box Y Y' a : Set (Matrix Y Y' k)) := ⟨AddSubgroup.isClosed_of_isOpen _ (isOpen_box a), isOpen_box a⟩
  have e : ind (box Y Y' a) = (box Y Y' a : Set (Matrix Y Y' k)).indicator fun _ => (1 : ℂ) := by
    funext t
    by_cases ht : t ∈ box Y Y' a <;> simp [ind, ht]
  rw [e]
  exact ⟨(LocallyConstant.indicator (LocallyConstant.const _ (1 : ℂ)) hcl).isLocallyConstant,
    HasCompactSupport.intro (isCompact_box a) fun x hx => Set.indicator_of_notMem hx _⟩
end GlobalTheory.LocMod.Inhab
