-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.exists_rational_support_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:29:24.758524+00:00
-- url     : https://prove2.me/submissions/73df8727-d552-466c-8847-28f088d4b266

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Theorems.Thm_GlobalTheory_GaloisDescent_repr_apply_of_semilinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L M G ι : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module L M]
namespace GlobalTheory.GaloisDescent
theorem _root_.solution (s : G → L →+* L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    (b : Basis ι L M) (φ : G → M →+ M) (hφ : ∀ g a i, φ g (a • b i) = s g a • b i)
    (W : Submodule L M) (hW : ∀ g, ∀ w ∈ W, φ g w ∈ W) (w : M) (hw : w ∈ W) (h0 : w ≠ 0) :
    ∃ u ∈ W, (∀ i, b.repr u i ∈ Set.range (algebraMap K L)) ∧
      (b.repr u).support ⊆ (b.repr w).support ∧ ∃ i, b.repr u i = 1 := by
  classical
  induction h : (b.repr w).support.card using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    obtain ⟨i, hi⟩ : ∃ i, b.repr w i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact h0 (b.repr.map_eq_zero_iff.1 (Finsupp.ext hcon))
    set w' := (b.repr w i)⁻¹ • w with hw'
    have hw'W : w' ∈ W := W.smul_mem _ hw
    have hrep : ∀ j, b.repr w' j = (b.repr w i)⁻¹ * b.repr w j := fun j => by simp [hw']
    have hi' : b.repr w' i = 1 := by rw [hrep, inv_mul_cancel₀ hi]
    have hsub : (b.repr w').support ⊆ (b.repr w).support := fun j hj => by
      rw [Finsupp.mem_support_iff] at hj ⊢
      intro hj0
      exact hj (by rw [hrep, hj0, mul_zero])
    by_cases hfix : ∀ g, φ g w' = w'
    · refine ⟨w', hw'W, fun j => hs _ fun g => ?_, hsub, i, hi'⟩
      rw [← repr_apply_of_semilinear (s g) b (φ g) (hφ g), hfix]
    · push Not at hfix
      obtain ⟨g, hg⟩ := hfix
      have hd : (b.repr (φ g w' - w')).support ⊆ (b.repr w).support.erase i := fun j hj => by
        rw [Finsupp.mem_support_iff, map_sub, Finsupp.sub_apply,
          repr_apply_of_semilinear (s g) b (φ g) (hφ g)] at hj
        rw [Finset.mem_erase, Finsupp.mem_support_iff]
        constructor
        · rintro rfl
          exact hj (by rw [hi', map_one, sub_self])
        · intro hj0
          exact hj (by rw [hrep, hj0, mul_zero, map_zero, sub_self])
      have hlt : (b.repr (φ g w' - w')).support.card < n := by
        rw [← h]
        exact (Finset.card_le_card hd).trans_lt
          (Finset.card_erase_lt_of_mem (Finsupp.mem_support_iff.2 hi))
      obtain ⟨u, hu, hur, hus, hui⟩ := ih _ hlt (φ g w' - w') (W.sub_mem (hW g _ hw'W) hw'W)
        (sub_ne_zero.2 hg) rfl
      exact ⟨u, hu, hur, hus.trans (hd.trans (Finset.erase_subset _ _)), hui⟩
end GlobalTheory.GaloisDescent
