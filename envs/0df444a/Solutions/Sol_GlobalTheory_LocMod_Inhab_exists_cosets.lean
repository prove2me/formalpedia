-- Prove2me | solution 1 for GlobalTheory.LocMod.Inhab.exists_cosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:47:04.600856+00:00
-- url     : https://prove2.me/submissions/bc42093a-a24d-40d6-b179-cda34bf59a37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_InvariantOfTsupport
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
theorem _root_.solution {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) (a : kˣ) :
    ∃ R : Finset (Matrix Y Y' k), ∀ t, Φ t ≠ 0 → ∃ r ∈ R, t - r ∈ box Y Y' a := by
  obtain ⟨R, -, hR⟩ := hΦ.2.isCompact.elim_nhds_subcover (fun r => {t | t - r ∈ box Y Y' a}) fun r _ =>
    ((isOpen_box a).preimage (continuous_sub_right r)).mem_nhds (by simp)
  exact ⟨R, fun t ht => by simpa using hR (subset_tsupport Φ ht)⟩
end GlobalTheory.LocMod.Inhab
