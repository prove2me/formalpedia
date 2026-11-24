-- Prove2me | solution 1 for GlobalTheory.KeyKa.KosGr.exact_dd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:52:04.152432+00:00
-- url     : https://prove2.me/submissions/1e1de5cb-6c4b-4ae3-8336-d709ace9395e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KoszulExactOfGradedRegular
import Theorems.Thm_GlobalTheory_KeyKa_KosGr_dd_congr
import Theorems.Thm_GlobalTheory_KeyKa_KosGr_dd_succ
import Theorems.Thm_GlobalTheory_KeyKa_KosGr_dd_succ_insert
import Theorems.Thm_GlobalTheory_KeyKa_KosGr_exists_sum_of_mem_iSup
import Theorems.Thm_GlobalTheory_KeyKa_KosGr_card_le_of_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
noncomputable section
open GlobalTheory GlobalTheory.KeyKa GlobalTheory.KeyKa.KosGr
variable {K : Type} [CommRing K] {g : ℕ} {V : ℕ → Type} [∀ j, AddCommGroup (V j)]
  [∀ j, Module K (V j)]
namespace GlobalTheory.KeyKa.KosGr
theorem _root_.solution (x : Fin g → ∀ j, V (j + 1) →ₗ[K] V j)
    (hc : ∀ i i' j (y : V (j + 2)), j + 2 ≤ g → x i j (x i' (j + 1) y) = x i' j (x i (j + 1) y))
    (hr : ∀ (i : Fin g) (j : ℕ) (y : V (j + 1)), j + 1 + i ≤ g →
      x i j y ∈ (⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (x i' j)) →
      y ∈ ⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (x i' (j + 1)))
    (r : ℕ) : ∀ (j₀ : ℕ), j₀ + r ≤ g → ∀ c : Finset (Fin g) → ∀ j, V j,
      (∀ I : Finset (Fin g), (∀ k ∈ I, k.val < r) → ∀ j, j = j₀ + I.card → dd x r c I j = 0) →
      ∃ w : Finset (Fin g) → ∀ j, V j, ∀ I : Finset (Fin g), (∀ k ∈ I, k.val < r) → I ≠ ∅ →
        ∀ j, j = j₀ + I.card → c I j = dd x r w I j := by
  induction r with
  | zero =>
    intro j₀ _ c _
    refine ⟨c, fun I hI hne j _ => ?_⟩
    obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    exact absurd (hI k hk) (Nat.not_lt_zero _)
  | succ r ih =>
    intro j₀ hj₀ c hcyc
    obtain ⟨t, htv⟩ : ∃ t : Fin g, t.val = r := ⟨⟨r, by omega⟩, rfl⟩
    have hsub : ∀ I : Finset (Fin g), (∀ k ∈ I, k.val < r) → ∀ k ∈ I, k.val < r + 1 :=
      fun I hI k hk => Nat.lt_succ_of_lt (hI k hk)
    have hlt : ∀ I : Finset (Fin g), (∀ k ∈ I, k.val < r) → ∀ k ∈ I, k.val < t.val := by
      intro I hI k hk; rw [htv]; exact hI k hk
    have htI : ∀ I : Finset (Fin g), (∀ k ∈ I, k.val < r) → t ∉ I := by
      intro I hI h
      have := hI t h
      rw [htv] at this
      exact lt_irrefl _ this
    have hins : ∀ I : Finset (Fin g), (∀ k ∈ I, k.val < r) → ∀ k ∈ insert t I, k.val < r + 1 := by
      intro I hI k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · rw [htv]; exact Nat.lt_succ_self r
      · exact Nat.lt_succ_of_lt (hI k hk)
    have hC2 : ∀ J : Finset (Fin g), (∀ k ∈ J, k.val < r) → ∀ j, j = (j₀ + 1) + J.card →
        dd x r (fun J => c (insert t J)) J j = 0 := by
      intro J hJ j hj
      have h1 := hcyc (insert t J) (hins J hJ) j
        (by rw [Finset.card_insert_of_notMem (htI J hJ)]; omega)
      have e := dd_succ_insert x t c J j
      rw [htv] at e
      rw [e] at h1
      exact h1
    obtain ⟨u, hu⟩ := ih (j₀ + 1) (by omega) (fun J => c (insert t J)) hC2
    have h0 := hcyc ∅ (by simp) j₀ (by simp)
    have e0 := dd_succ x t c ∅ (by simp) j₀
    rw [htv, h0] at e0
    have hmem : x t j₀ (c (insert t ∅) (j₀ + 1)) ∈
        ⨆ (i' : Fin g) (_ : i' < t), LinearMap.range (x i' j₀) := by
      have hsum : dd x r c ∅ j₀ ∈ ⨆ (i' : Fin g) (_ : i' < t), LinearMap.range (x i' j₀) := by
        unfold dd
        refine Submodule.sum_mem _ fun i _ => ?_
        split_ifs with hi
        · refine Submodule.smul_mem _ _ ?_
          have hit : i < t := Fin.lt_def.mpr (by rw [htv]; exact hi.1)
          exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hit (LinearMap.mem_range_self _ _))
        · exact Submodule.zero_mem _
      have e1 : x t j₀ (c (insert t ∅) (j₀ + 1)) = -dd x r c ∅ j₀ := by
        rw [Finset.card_empty, pow_zero, one_smul] at e0
        exact eq_neg_of_add_eq_zero_right e0.symm
      rw [e1]
      exact Submodule.neg_mem _ hsum
    have hy := hr t j₀ (c (insert t ∅) (j₀ + 1)) (by rw [htv]; omega) hmem
    obtain ⟨z, hz⟩ := exists_sum_of_mem_iSup (fun i => x i (j₀ + 1)) t _ hy
    let w₁ : Finset (Fin g) → ∀ j, V j := fun J =>
      if J.card = 1 then Function.update (0 : ∀ j, V j) (j₀ + 1 + 1) (∑ i, if J = {i} then z i else 0)
      else u J
    have hw₁ : ∀ J : Finset (Fin g), (∀ k ∈ J, k.val < r) → ∀ j, j = j₀ + 1 + J.card →
        c (insert t J) j = dd x r w₁ J j := by
      intro J hJ j hj
      rcases J.eq_empty_or_nonempty with rfl | hne
      · rw [Finset.card_empty, add_zero] at hj
        subst hj
        rw [hz]
        unfold dd
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : i.val < r
        · rw [if_pos (by rw [htv]; exact hi), if_pos ⟨hi, Finset.notMem_empty i⟩]
          simp [w₁]
        · rw [if_neg (by rw [htv]; exact hi), if_neg (fun h => hi h.1)]
      · rw [dd_congr x r w₁ u J j (fun i hi hiJ => ?_)]
        · exact hu J hJ hne.ne_empty j hj
        · have hc1 : (insert i J).card ≠ 1 := by
            rw [Finset.card_insert_of_notMem hiJ]
            have := hne.card_pos
            omega
          simp only [w₁, if_neg hc1]
    let d : Finset (Fin g) → ∀ j, V j := fun I j => c I j - (-1 : K) ^ I.card • x t j (w₁ I (j + 1))
    have hdcyc : ∀ I : Finset (Fin g), (∀ k ∈ I, k.val < r) → ∀ j, j = j₀ + I.card →
        dd x r d I j = 0 := by
      intro I hI j hj
      have hcI := hcyc I (hsub I hI) j hj
      have e := dd_succ x t c I (hlt I hI) j
      rw [htv, hcI] at e
      have hcw := hw₁ I hI (j + 1) (by rw [hj]; ring)
      rw [hcw] at e
      rw [e]
      unfold dd
      rw [map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hi
      · have hcard : (insert i I).card ≤ r := card_le_of_lt (insert i I) r (by
          intro k hk
          rcases Finset.mem_insert.mp hk with rfl | hk
          · exact hi.1
          · exact hI k hk)
        rw [Finset.card_insert_of_notMem hi.2] at hcard
        simp only [d, map_sub, map_smul, Finset.card_insert_of_notMem hi.2]
        rw [hc i t j _ (by omega), pow_succ]
        module
      · simp
    obtain ⟨w₀, hw₀⟩ := ih j₀ (by omega) d hdcyc
    refine ⟨fun I => if t ∈ I then w₁ (I.erase t) else w₀ I, ?_⟩
    intro I hI hne j hj
    by_cases htI' : t ∈ I
    · obtain ⟨J, htJ, rfl⟩ : ∃ J, t ∉ J ∧ I = insert t J :=
        ⟨I.erase t, Finset.notMem_erase t I, (Finset.insert_erase htI').symm⟩
      have hJ : ∀ k ∈ J, k.val < r := by
        intro k hk
        have h1 := hI k (Finset.mem_insert_of_mem hk)
        have h2 : k.val ≠ r := fun h => htJ (by rwa [show k = t from Fin.ext (h.trans htv.symm)] at hk)
        omega
      have e := dd_succ_insert x t (fun I => if t ∈ I then w₁ (I.erase t) else w₀ I) J j
      rw [htv] at e
      rw [e, dd_congr x r _ w₁ J j (fun i hi hiJ => ?_)]
      · exact hw₁ J hJ j (by rw [hj, Finset.card_insert_of_notMem htJ]; ring)
      · have hti : t ∉ insert i J := by
          rw [Finset.mem_insert, not_or]
          refine ⟨fun h => ?_, htJ⟩
          rw [← h, htv] at hi
          exact lt_irrefl _ hi
        simp only [Finset.mem_insert_self, ↓reduceIte, Finset.erase_insert hti]
    · have hI' : ∀ k ∈ I, k.val < r := by
        intro k hk
        have h1 := hI k hk
        have h2 : k.val ≠ r := fun h => htI' (by rwa [show k = t from Fin.ext (h.trans htv.symm)] at hk)
        omega
      have e := dd_succ x t (fun I => if t ∈ I then w₁ (I.erase t) else w₀ I) I (hlt I hI') j
      rw [htv] at e
      rw [e, dd_congr x r _ w₀ I j (fun i hi hiI => ?_)]
      · simp only [Finset.mem_insert_self, ↓reduceIte, Finset.erase_insert htI']
        have h1 := hw₀ I hI' hne j hj
        simp only [d] at h1
        rw [← h1, sub_add_cancel]
      · have hti : t ∉ insert i I := by
          rw [Finset.mem_insert, not_or]
          refine ⟨fun h => ?_, htI'⟩
          rw [← h, htv] at hi
          exact lt_irrefl _ hi
        simp only [hti, ↓reduceIte]
end GlobalTheory.KeyKa.KosGr
