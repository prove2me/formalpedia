-- Prove2me | solution 1 for GlobalTheory.hasSum_eq_sum_of_matching_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T06:04:09.857795+00:00
-- url     : https://prove2.me/submissions/acfd2e7d-53e8-4a28-97d2-9092db9159db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumEqSumOfMatchingFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (C : Type 1) (n : ℕ) (m : C → ℕ) (t : C → ℂ) (m' : Fin n → ℕ) (c : Fin n → ℂ) (R : C → Fin n → Prop) (s : ℂ), HasSum (fun x => (m x : ℂ) * t x) s → (∀ x, m x ≠ 0 → t x ≠ 0 → ∃ i, R x i) → (∀ i, m' i ≠ 0 → ∃ x, R x i) → (∀ x i, R x i → m x = m' i ∧ t x = c i) → (∀ x i j, R x i → R x j → i = j) → (∀ x y i, R x i → R y i → x = y) → s = ∑ i, (m' i : ℂ) * c i := by
  intro C n m t m' c R s hs h1 h2 h3 h4 h5
  classical
  set P : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => m' i ≠ 0) with hPdef
  let g : P → C := fun i => Classical.choose (h2 i.1 (Finset.mem_filter.1 i.2).2)
  have hg : ∀ i : P, R (g i) i.1 := fun i => Classical.choose_spec (h2 i.1 (Finset.mem_filter.1 i.2).2)
  have ginj : Function.Injective g := by
    intro i j hij
    apply Subtype.ext
    have hj := hg j
    rw [← hij] at hj
    exact h4 _ _ _ (hg i) hj
  have hT : ∀ x ∉ (Finset.univ.image g), (m x : ℂ) * t x = 0 := by
    intro x hx
    by_contra hne
    have hm : m x ≠ 0 := by intro h; apply hne; simp [h]
    have ht : t x ≠ 0 := by intro h; apply hne; simp [h]
    obtain ⟨i, hi⟩ := h1 x hm ht
    have hmi : m' i ≠ 0 := by rw [← (h3 x i hi).1]; exact hm
    have hiP : i ∈ P := Finset.mem_filter.2 ⟨Finset.mem_univ _, hmi⟩
    apply hx
    rw [Finset.mem_image]
    exact ⟨⟨i, hiP⟩, Finset.mem_univ _, h5 _ _ _ (hg ⟨i, hiP⟩) hi⟩
  have hs2 : HasSum (fun x => (m x : ℂ) * t x) (∑ x ∈ Finset.univ.image g, (m x : ℂ) * t x) := hasSum_sum_of_ne_finset_zero hT
  rw [hs.unique hs2, Finset.sum_image (fun i _ j _ h => ginj h)]
  rw [← Finset.sum_filter_of_ne (p := fun i => m' i ≠ 0) (fun i _ hne => by intro h; apply hne; simp [h])]
  rw [← hPdef, ← Finset.sum_attach P (fun i => (m' i : ℂ) * c i), Finset.univ_eq_attach]
  apply Finset.sum_congr rfl
  intro i _
  rw [(h3 _ _ (hg i)).1, (h3 _ _ (hg i)).2]
end GlobalTheory
