-- Prove2me | solution 1 for MajorityAttack.NegCost.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T22:43:04.301351+00:00
-- url     : https://prove2.me/submissions/bf153621-f3f7-4bec-afe1-23292956b48b

import Mathlib
import Definitions.Def_MajorityAttack_NegCost_Model
import Theorems.Thm_MajorityAttack_NegCost_lemma_1
import Theorems.Thm_MajorityAttack_NegCost_lemma_2

open MajorityAttack.NegCost

theorem solution {ι : Type*} [Fintype ι]
    (τ H R L : ℝ) (hτ : 0 < τ) (hH : 0 < H) (hL : 0 < L)
    (μ : MeasureTheory.Measure ℝ) (hμ : FeeLaw μ)
    (b n n' : ℕ) (hb : 0 < b) (hbn : b < n) (hnn' : n < n')
    (c : ι → ℝ → ℝ) (hc : ∀ i, CostStanding (c i))
    (htil : ι → ℝ)
    (hopt : ∀ i, IsAttackOptimum (τ * H) (R + blockFees μ b n') (c i) (htil i)) :
    ∃ hhat : ℝ, 0 < hhat ∧ hhat < H / 2 ∧
      ∀ hstar : ι → ℝ, (∀ j, 0 ≤ hstar j) → (∑ j, hstar j) = H →
        ∀ i, 0 ≤ flowProfit (τ * H) (R + blockFees μ b n) (c i) (hstar i) →
          hhat < hstar i → ∀ V : ℝ, 0 ≤ V →
            ¬ NoAttackEquilibrium τ H L R (blockFees μ b n) (blockFees μ b n')
                c htil hstar V := by
  classical
  have hfee := MajorityAttack.NegCost.lemma_2 μ hμ b n n' hb hbn hnn'
  have hl1 := fun i => MajorityAttack.NegCost.lemma_1 τ H L (R + blockFees μ b n)
    (R + blockFees μ b n') (c i) (htil i) hτ hH hL (by linarith) (hc i) (hopt i)
  choose hh hh0 hhH hhneg using hl1
  let S : Finset ℝ := insert (H / 4) (Finset.univ.image hh)
  have hSne : S.Nonempty := ⟨H / 4, Finset.mem_insert_self _ _⟩
  refine ⟨S.max' hSne, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (by linarith) (S.le_max' (H / 4) (Finset.mem_insert_self _ _))
  · rw [Finset.max'_lt_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with h | h
    · rw [h]; linarith
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      exact hhH i
  · intro hstar _ _ i hact hlt V hV hNAE
    have hle : hh i ≤ S.max' hSne :=
      S.le_max' (hh i) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem hh (Finset.mem_univ i)))
    have hneg := hhneg i (hstar i) (by linarith)
    have := hNAE i hact
    linarith
