-- Prove2me | solution 1 for MLRPCake.EnvyFree.Supplement.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:10:30.961083+00:00
-- url     : https://prove2.me/submissions/aef457f7-216f-4386-965a-0cfbee2b469f

import Mathlib
import Definitions.Def_MLRPCake_EnvyFree_Model
import Definitions.Def_MLRPCake_EnvyFree_Supplement_MovingKnife

open MLRPCake
open MLRPCake.EnvyFree
open MLRPCake.EnvyFree.Supplement

/-- Proposition 2, p. 21: for every cake-division instance and every `i ∈ [n]`, the moving-knife
function `MK_i` is monotonically (weakly) increasing on `τ ≥ 0`. -/
theorem solution {n : ℕ} (f : Fin n → ℝ → ℝ) (hf : IsInstance f) (i : ℕ) (hi1 : 1 ≤ i)
    (hin : i ≤ n) :
    ∀ τ τ' : ℝ, 0 ≤ τ → τ ≤ τ' → mk f i τ ≤ mk f i τ' := by
      have hd : ∀ k, (∀ x ∈ Set.Icc (0:ℝ) 1, 0 ≤ dens f k x) ∧
          IntervalIntegrable (dens f k) MeasureTheory.volume 0 1 := by
        intro k
        unfold dens
        split_ifs with h
        · exact ⟨(hf ⟨k, h⟩).1, (hf ⟨k, h⟩).2.2.1⟩
        · exact ⟨fun _ _ => le_refl 0, intervalIntegrable_const⟩
      have hrange : ∀ k ℓ τ, ℓ ≤ 1 → ℓ ≤ cut f k ℓ τ ∧ cut f k ℓ τ ≤ 1 := by
        intro k ℓ τ hℓ
        unfold cut
        split_ifs with h
        · obtain ⟨y, hy, hv⟩ := h
          constructor
          · exact le_csInf ⟨y, hy, hv⟩ (fun z hz => hz.1.1)
          · exact csInf_le_of_le ⟨ℓ, fun z hz => hz.1.1⟩ ⟨hy, hv⟩ hy.2
        · exact ⟨hℓ, le_rfl⟩
      have hmk : ∀ j τ, 0 ≤ mk f j τ ∧ mk f j τ ≤ 1 := by
        intro j τ
        induction j with
        | zero => simp [mk]
        | succ j ih =>
          have := hrange j (mk f j τ) τ ih.2
          exact ⟨ih.1.trans this.1, this.2⟩
      have key : ∀ k : ℕ, ∀ ℓ ℓ' τ τ' : ℝ, 0 ≤ ℓ → ℓ ≤ ℓ' → ℓ' ≤ 1 → 0 ≤ τ → τ ≤ τ' →
          cut f k ℓ τ ≤ cut f k ℓ' τ' := by
        intro k ℓ ℓ' τ τ' h0 hll hl1 hτ hττ
        obtain ⟨hnn, hint⟩ := hd k
        have hint' : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
            IntervalIntegrable (dens f k) MeasureTheory.volume a b := by
          intro a b ha0 ha1 hb0 hb1
          apply hint.mono_set
          rw [Set.uIcc_of_le (zero_le_one' ℝ)]
          exact Set.uIcc_subset_Icc ⟨ha0, ha1⟩ ⟨hb0, hb1⟩
        by_cases h' : ∃ y ∈ Set.Icc ℓ' 1, val f k ℓ' y = τ'
        · have e : cut f k ℓ' τ' = sInf {y | y ∈ Set.Icc ℓ' 1 ∧ val f k ℓ' y = τ'} := by
            unfold cut; rw [if_pos h']
          rw [e]
          obtain ⟨y0, hy0, hv0⟩ := h'
          apply le_csInf (⟨y0, hy0, hv0⟩ : Set.Nonempty {y | y ∈ Set.Icc ℓ' 1 ∧ val f k ℓ' y = τ'})
          rintro y' ⟨hy', hv'⟩
          have hsplit : val f k ℓ y' = val f k ℓ ℓ' + val f k ℓ' y' := by
            unfold val
            rw [intervalIntegral.integral_add_adjacent_intervals
              (hint' ℓ ℓ' h0 (hll.trans hl1) (h0.trans hll) hl1)
              (hint' ℓ' y' (h0.trans hll) hl1 (h0.trans (hll.trans hy'.1)) hy'.2)]
          have hnn' : 0 ≤ val f k ℓ ℓ' :=
            intervalIntegral.integral_nonneg hll (fun u hu => hnn u ⟨h0.trans hu.1, hu.2.trans hl1⟩)
          have hly : ℓ ≤ y' := hll.trans hy'.1
          have hcont : ContinuousOn (fun y => val f k ℓ y) (Set.Icc ℓ y') := by
            have := intervalIntegral.continuousOn_primitive_interval (μ := MeasureTheory.volume)
              ((intervalIntegrable_iff').mp (hint' ℓ y' h0 (hly.trans hy'.2) (h0.trans hly) hy'.2))
            rw [Set.uIcc_of_le hly] at this
            exact this
          obtain ⟨y, hy, hvy⟩ := intermediate_value_Icc hly hcont
            (show τ ∈ Set.Icc (val f k ℓ ℓ) (val f k ℓ y') from
              ⟨by simp [val]; exact hτ, by linarith⟩)
          have hyS : y ∈ Set.Icc ℓ 1 ∧ val f k ℓ y = τ := ⟨⟨hy.1, hy.2.trans hy'.2⟩, hvy⟩
          have hex : ∃ y ∈ Set.Icc ℓ 1, val f k ℓ y = τ := ⟨y, hyS.1, hyS.2⟩
          have e2 : cut f k ℓ τ = sInf {y | y ∈ Set.Icc ℓ 1 ∧ val f k ℓ y = τ} := by
            unfold cut; rw [if_pos hex]
          rw [e2]
          exact csInf_le_of_le ⟨ℓ, fun z hz => hz.1.1⟩ hyS hy.2
        · have e : cut f k ℓ' τ' = 1 := by unfold cut; rw [if_neg h']
          rw [e]
          exact (hrange k ℓ τ (hll.trans hl1)).2
      intro τ τ' hτ hττ
      have : ∀ j, mk f j τ ≤ mk f j τ' := by
        intro j
        induction j with
        | zero => simp [mk]
        | succ j ih =>
          exact key j _ _ τ τ' (hmk j τ).1 ih (hmk j τ').2 hτ hττ
      exact this i
