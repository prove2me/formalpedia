-- Prove2me | solution 1 for GlobalTheory.LocMod.Inhab.ind_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:47:11.93412+00:00
-- url     : https://prove2.me/submissions/2a881d4d-d974-4ca9-aa0e-753b81a07bc2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_InvariantOfTsupport

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
theorem _root_.solution (h : IsBichar χ) (hN : ∀ y, ∀ Φ ∈ N, (fun t => χ t y * Φ t) ∈ N)
    (hsep : ∀ u, u ∉ K → ∃ y, (∀ κ ∈ K, χ κ y = 1) ∧ χ u y ≠ 1) (R : Finset G) :
    ∀ Φ ∈ N, (∀ u ∈ K, ∀ t, Φ (t + u) = Φ t) → Φ 0 ≠ 0 → (∀ t, Φ t ≠ 0 → t ∈ K ∨ ∃ r ∈ R, t - r ∈ K) → ind K ∈ N := by
  classical
  induction R using Finset.induction_on with
  | empty =>
    intro Φ hΦ h1 h2 h3
    convert N.smul_mem (Φ 0)⁻¹ hΦ using 1
    funext t
    by_cases ht : t ∈ K
    · have := h1 t ht 0
      rw [zero_add] at this
      simp [ind, ht, this, h2]
    · have : Φ t = 0 := by_contra fun hh => by simpa [ht] using h3 t hh
      simp [ind, ht, this]
  | insert r R _ ih =>
    intro Φ hΦ h1 h2 h3
    by_cases hr : r ∈ K
    · refine ih Φ hΦ h1 h2 fun t ht => ?_
      rcases h3 t ht with hh | ⟨s, hs, hh⟩
      · exact Or.inl hh
      · rcases Finset.mem_insert.1 hs with rfl | hs
        · exact Or.inl (by simpa using add_mem hh hr)
        · exact Or.inr ⟨s, hs, hh⟩
    · obtain ⟨y, hy, hne⟩ := hsep r hr
      refine ih _ (N.sub_mem (hN y Φ hΦ) (N.smul_mem (χ r y) hΦ)) (fun u hu t => ?_) ?_ fun t ht => ?_
      · simp only [Pi.sub_apply, Pi.smul_apply, h.left, hy u hu, h1 u hu, mul_one]
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h.zero_left, ← sub_mul]
        exact mul_ne_zero (sub_ne_zero.2 hne.symm) h2
      · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← sub_mul] at ht
        rcases h3 t (right_ne_zero_of_mul ht) with hh | ⟨s, hs, hh⟩
        · exact Or.inl hh
        · rcases Finset.mem_insert.1 hs with rfl | hs
          · refine absurd ?_ (left_ne_zero_of_mul ht)
            rw [← add_sub_cancel s t, h.left, hy _ hh, mul_one, sub_self]
          · exact Or.inr ⟨s, hs, hh⟩
end GlobalTheory.LocMod.Inhab
