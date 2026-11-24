-- Prove2me | solution 1 for GlobalTheory.LocMod.Inhab.mem_of_ind_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:48:51.341265+00:00
-- url     : https://prove2.me/submissions/8a85f992-cce2-4017-b574-225c8cf54c07

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_InvariantOfTsupport
import Theorems.Thm_GlobalTheory_PlaceModel_ind_add


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
variable {G : Type} [AddCommGroup G] {χ : G → G → ℂ} {N : Submodule ℂ (G → ℂ)} {K : AddSubgroup G}
namespace GlobalTheory.LocMod.Inhab
theorem _root_.solution (hN : ∀ x, ∀ Φ ∈ N, (fun t => Φ (t + x)) ∈ N) (hK : ind K ∈ N) (R : Finset G) :
    ∀ Φ : G → ℂ, (∀ u ∈ K, ∀ t, Φ (t + u) = Φ t) → (∀ t, Φ t ≠ 0 → ∃ r ∈ R, t - r ∈ K) → Φ ∈ N := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    intro Φ _ h3
    convert N.zero_mem using 1
    funext t
    by_contra ht
    simpa using h3 t ht
  | insert s R _ ih =>
    intro Φ h2 h3
    have hm := N.smul_mem (Φ s) (hN (-s) _ hK)
    have hval : ∀ t, (Φ - Φ s • fun t => ind K (t + -s)) t ≠ 0 → Φ t ≠ 0 ∧ t + -s ∉ K := by
      intro t ht
      have hn : t + -s ∉ K := fun hh => ht (by
        have := h2 _ hh s
        rw [show s + (t + -s) = t by abel] at this
        simp [ind, hh, this])
      exact ⟨by simpa [ind, hn] using ht, hn⟩
    have := ih (Φ - Φ s • fun t => ind K (t + -s)) (fun u hu t => by
      simp only [Pi.sub_apply, Pi.smul_apply, h2 u hu]
      rw [add_right_comm, ind_add K _ hu]) fun t ht => by
        obtain ⟨s', hs', hu⟩ := h3 t (hval t ht).1
        rcases Finset.mem_insert.1 hs' with rfl | hs'
        · exact absurd (by rwa [← sub_eq_add_neg]) (hval _ ht).2
        · exact ⟨s', hs', hu⟩
    simpa using add_mem this hm
end GlobalTheory.LocMod.Inhab
