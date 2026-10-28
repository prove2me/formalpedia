-- Prove2me | solution 1 for MultiStoreAssort.SQR.lemmaB1_nested
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T15:56:13.032932+00:00
-- url     : https://prove2.me/submissions/7dbda266-4939-411b-94a6-ae5da2fb4ad5

import Mathlib
import Definitions.Def_MultiStoreAssort_SQR_Model
import Theorems.Thm_MultiStoreAssort_SQR_propositionB2_nested_revenue_ordered

open MultiStoreAssort.SQR in
theorem solution {M n : ℕ} (lam : Fin (M + 2) → ℝ) (r v : Fin n → ℝ)
    (c : Fin (M + 2) → Fin (M + 2) → Fin n → ℝ) (cs : Fin (M + 2) → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) (hr : StrictAnti r)
    (hrpos : ∀ k, 0 < r k) (hv : ∀ k, 0 < v k) (hcii : ∀ i k, c i i k = 0)
    (hsw : StoreWiseHomog c cs) (hmin : ∀ i, lam (Fin.last (M + 1)) ≤ lam i)
    (hmono : Monotone cs) :
    ∃ S : Fin (M + 2) → Finset (Fin n), IsOptQ lam r v c S ∧ ∀ i j, i ≤ j → S i ⊆ S j := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨fun _ => ∅, ?_, fun _ _ _ => le_rfl⟩
    intro S'
    have : S' = fun _ => ∅ := funext fun i => Finset.eq_empty_of_forall_notMem (fun k => k.elim0)
    rw [this]
  · obtain ⟨S, hS, hch, -⟩ := propositionB2_nested_revenue_ordered lam r v c cs hn hlam hlam1 hr
      hrpos hv hcii hsw hmin hmono
    exact ⟨S, hS, hch⟩
