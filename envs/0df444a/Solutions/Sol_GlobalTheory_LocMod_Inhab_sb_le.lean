-- Prove2me | solution 1 for GlobalTheory.LocMod.Inhab.sb_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:24:29.705287+00:00
-- url     : https://prove2.me/submissions/96a7e03f-83dc-4b32-bbab-29404ada6651

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_InvariantOfTsupport
import Theorems.Thm_GlobalTheory_LocMod_Inhab_ind_mem
import Theorems.Thm_GlobalTheory_LocMod_Inhab_mem_of_ind_mem
import Theorems.Thm_GlobalTheory_LocMod_Inhab_eventually_invariant
import Theorems.Thm_GlobalTheory_LocMod_Inhab_invariant_of_tsupport
import Theorems.Thm_GlobalTheory_LocMod_Inhab_exists_cosets
import Theorems.Thm_GlobalTheory_LocMod_Inhab_exists_box_subset
import Theorems.Thm_GlobalTheory_LocMod_Inhab_exists_sep
import Theorems.Thm_GlobalTheory_LocMod_Inhab_isBichar_pairing
import Theorems.Thm_GlobalTheory_LocMod_Inhab_pairing_box


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
theorem _root_.solution {ψ : AddChar k Circle} {d : kˣ} (hd : HasConductor ψ d) {N : Submodule ℂ (Matrix Y Y' k → ℂ)}
    (hN : ∀ x, ∀ Φ ∈ N, (fun t => Φ (t + x)) ∈ N) (hN' : ∀ y, ∀ Φ ∈ N, (fun t => pairing ψ t y * Φ t) ∈ N)
    {Φ : Matrix Y Y' k → ℂ} (hΦ : Φ ∈ SB (Matrix Y Y' k)) (h0 : Φ ≠ 0) (hΦN : Φ ∈ N) : SB (Matrix Y Y' k) ≤ N := by
  classical
  intro Ψ hΨ
  obtain ⟨a, ha⟩ := exists_box_subset ((eventually_invariant hΦ).and (eventually_invariant hΨ))
  obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
  obtain ⟨R, hR⟩ := exists_cosets hΦ a
  obtain ⟨R', hR'⟩ := exists_cosets hΨ a
  refine mem_of_ind_mem hN (ind_mem (isBichar_pairing ψ) hN'
    (fun u hu => let ⟨y, hy, hne⟩ := exists_sep hd a hu; ⟨y, fun κ hκ => pairing_box hd hκ hy, hne⟩)
    (R.image (· - x)) _ (hN x Φ hΦN) (fun u hu t => ?_) (by rwa [zero_add]) fun t ht => ?_) R' Ψ
    (invariant_of_tsupport fun u hu => (ha u hu).2) hR'
  · rw [add_right_comm]
    exact invariant_of_tsupport (fun u hu => (ha u hu).1) u hu _
  · obtain ⟨r, hr, h⟩ := hR _ ht
    exact Or.inr ⟨_, Finset.mem_image_of_mem _ hr, by convert h using 1; abel⟩
end GlobalTheory.LocMod.Inhab
