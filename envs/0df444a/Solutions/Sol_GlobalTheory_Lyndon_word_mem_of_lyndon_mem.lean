-- Prove2me | solution 1 for GlobalTheory.Lyndon.word_mem_of_lyndon_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:28:44.173139+00:00
-- url     : https://prove2.me/submissions/7ec21d18-b9a9-483c-8bfb-245ff55295a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Theorems.Thm_GlobalTheory_Lyndon_exists_factors
import Theorems.Thm_GlobalTheory_Lyndon_repr_prod_self
import Theorems.Thm_GlobalTheory_Lyndon_le_of_repr_prod_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Shuffle
open GlobalTheory.Lyndon
variable {A : Type} [LinearOrder A]
open ShuffleAlgebra
variable (K : Type) [Field K]
namespace GlobalTheory.Lyndon
theorem _root_.solution [CharZero K] (B : Subalgebra K (ShuffleAlgebra K A))
    (hB : ∀ l, IsLyndon l → word K l ∈ B) (w : List A) : word K w ∈ B := by
  classical
  induction hn : (w.permutations.toFinset.filter (· < w)).card using Nat.strong_induction_on
    generalizing w with
  | _ n ih =>
    obtain ⟨L, hL, rfl⟩ := exists_factors w
    set x := (L.map (word K)).prod with hx
    have hxB : x ∈ B := B.list_prod_mem fun y hy => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hy
      exact hB l (hL.1 l hl)
    have hc := repr_prod_self K L
    rw [← hx] at hc
    have hsum : x = ∑ v ∈ ((wordBasis K A).repr x).support,
        (wordBasis K A).repr x v • word K v := by
      conv_lhs => rw [← (wordBasis K A).linearCombination_repr x]
      rfl
    rw [← Finset.add_sum_erase _ _ (Finsupp.mem_support_iff.2 hc)] at hsum
    have hrest : ∑ v ∈ ((wordBasis K A).repr x).support.erase L.flatten,
        (wordBasis K A).repr x v • word K v ∈ B := by
      refine B.sum_mem fun v hv => B.smul_mem ?_ _
      obtain ⟨hne, hv⟩ := Finset.mem_erase.1 hv
      obtain ⟨hp, hle⟩ := le_of_repr_prod_ne_zero K hL (Finsupp.mem_support_iff.1 hv)
      have hlt := lt_of_le_of_ne hle hne
      refine ih _ ?_ v rfl
      rw [← hn]
      refine Finset.card_lt_card ⟨fun y hy => ?_, fun hsub => ?_⟩
      · simp only [Finset.mem_filter, List.mem_toFinset, List.mem_permutations] at hy ⊢
        exact ⟨hy.1.trans hp, hy.2.trans hlt⟩
      · have := @hsub v (by
          simp only [Finset.mem_filter, List.mem_toFinset, List.mem_permutations]
          exact ⟨hp, hlt⟩)
        simp at this
    have h1 : (wordBasis K A).repr x L.flatten • word K L.flatten ∈ B := by
      rw [eq_sub_iff_add_eq.2 hsum.symm]
      exact B.sub_mem hxB hrest
    have h2 := B.smul_mem h1 ((wordBasis K A).repr x L.flatten)⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2
end GlobalTheory.Lyndon
