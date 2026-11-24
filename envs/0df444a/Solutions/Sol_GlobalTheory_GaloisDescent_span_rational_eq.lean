-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.span_rational_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:05:15.127797+00:00
-- url     : https://prove2.me/submissions/ad53727f-58a5-4da1-b0f4-989fdf02862d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
import Theorems.Thm_GlobalTheory_GaloisDescent_exists_rational_support_subset

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
    (W : Submodule L M) (hW : ∀ g, ∀ w ∈ W, φ g w ∈ W) :
    Submodule.span L {u | u ∈ W ∧ ∀ i, b.repr u i ∈ Set.range (algebraMap K L)} = W := by
  classical
  refine le_antisymm (Submodule.span_le.2 fun u hu => hu.1) fun w hw => ?_
  induction h : (b.repr w).support.card using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    by_cases h0 : w = 0
    · rw [h0]; exact Submodule.zero_mem _
    obtain ⟨u, hu, hur, hus, i, hi⟩ := exists_rational_support_subset s hs b φ hφ W hW w hw h0
    have hiw : i ∈ (b.repr w).support := hus (Finsupp.mem_support_iff.2 (by simp [hi]))
    have hd : (b.repr (w - b.repr w i • u)).support ⊆ (b.repr w).support.erase i := fun j hj => by
      rw [Finsupp.mem_support_iff, map_sub, Finsupp.sub_apply, map_smul, Finsupp.smul_apply,
        smul_eq_mul] at hj
      rw [Finset.mem_erase]
      constructor
      · rintro rfl
        exact hj (by rw [hi, mul_one, sub_self])
      · by_contra hj0
        have h1 : b.repr u j = 0 := Finsupp.notMem_support_iff.1 fun h => hj0 (hus h)
        exact hj (by rw [h1, Finsupp.notMem_support_iff.1 hj0, mul_zero, sub_self])
    have hlt : (b.repr (w - b.repr w i • u)).support.card < n := by
      rw [← h]
      exact (Finset.card_le_card hd).trans_lt (Finset.card_erase_lt_of_mem hiw)
    have h1 := ih _ hlt _ (W.sub_mem hw (W.smul_mem _ hu)) rfl
    have h2 := Submodule.add_mem _ h1 (Submodule.smul_mem _ (b.repr w i)
      (Submodule.subset_span (R := L) (s := {u | u ∈ W ∧
        ∀ i, b.repr u i ∈ Set.range (algebraMap K L)}) ⟨hu, hur⟩))
    rwa [sub_add_cancel] at h2
end GlobalTheory.GaloisDescent
