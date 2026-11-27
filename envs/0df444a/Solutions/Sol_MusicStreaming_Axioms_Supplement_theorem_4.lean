-- Prove2me | solution 1 for MusicStreaming.Axioms.Supplement.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:12:11.599971+00:00
-- url     : https://prove2.me/submissions/2b498299-910c-4c96-bffa-62aefbb3e1ea

import Mathlib
import Definitions.Def_MusicStreaming_Axioms_Setting
import Definitions.Def_MusicStreaming_Axioms_Supplement_Bankruptcy
import Definitions.Def_MusicStreaming_Axioms_Supplement_Claims
import Definitions.Def_MusicStreaming_Axioms_Supplement_TwoStage
import Definitions.Def_MusicStreaming_Axioms_Supplement_AssociatedClaims

open MusicStreaming
open MusicStreaming.Axioms
open MusicStreaming.Axioms.Supplement

open MusicStreaming.Axioms

theorem solution :
    (∃ ωP ωU : WeightFunction ℕ, IsWeightFunction ωP ∧ IsWeightFunction ωU ∧
      ∀ (n : ℕ) (t : Problem n),
        reward proRata t = weightedProportional ωP (assocClaims t) ∧
        reward userCentric t = weightedProportional ωU (assocClaims t)) ∧
    (∀ (n : ℕ) (t : Problem n),
      reward proRata t = twoStage proportional proportional (assocClaims t)) ∧
    (∀ (n : ℕ) (t : Problem n),
      userCentric t = twoStage cea proportional (assocClaims t)) := by
        classical
        -- positivity of user totals
        have hpos : ∀ (n : ℕ) (t : Problem n), ∀ j ∈ t.support, (0:ℝ) < ∑ i, (t j i : ℝ) := by
          intro n t j hj
          rw [Finsupp.mem_support_iff] at hj
          obtain ⟨i, hi⟩ := Function.ne_iff.mp hj
          have h1 : (0:ℝ) < (t j i : ℝ) := by
            have : 0 < t j i := Nat.pos_of_ne_zero hi
            exact_mod_cast this
          calc (0:ℝ) < (t j i : ℝ) := h1
            _ ≤ ∑ i, (t j i : ℝ) :=
              Finset.single_le_sum (f := fun i => (t j i : ℝ)) (fun _ _ => by positivity) (Finset.mem_univ i)
        have hge1 : ∀ (n : ℕ) (t : Problem n), ∀ j ∈ t.support, (1:ℝ) ≤ ∑ i, (t j i : ℝ) := by
          intro n t j hj
          have h := hpos n t j hj
          have : (∑ i, (t j i : ℝ)) = ((∑ i, t j i : ℕ) : ℝ) := by push_cast; rfl
          rw [this] at h ⊢
          have : 0 < ∑ i, t j i := by exact_mod_cast h
          exact_mod_cast this
        -- pro-rata closed form
        have hPR : ∀ (n : ℕ) (t : Problem n) (i : Fin n),
            reward proRata t i = ∑ j ∈ t.support, (t j i : ℝ) /
              (∑ j ∈ t.support, ∑ i', (t j i' : ℝ)) * t.support.card := by
          intro n t i
          simp only [reward, proRata, artistTotal]
          push_cast
          rw [Finset.sum_comm (s := Finset.univ), ← Finset.sum_mul, ← Finset.sum_div]
        have hUC : ∀ (n : ℕ) (t : Problem n) (i : Fin n),
            userCentric t i = ∑ j ∈ t.support, (t j i : ℝ) / ∑ i', (t j i' : ℝ) := by
          intro n t i
          simp only [userCentric, userTotal]
          push_cast
          rfl
        have hUsum : ∀ (n : ℕ) (t : Problem n), ∑ i, userCentric t i = t.support.card := by
          intro n t
          simp only [hUC]
          rw [Finset.sum_comm]
          rw [Finset.card_eq_sum_ones]
          push_cast
          refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [← Finset.sum_div, div_self (hpos n t j hj).ne']
        refine ⟨⟨fun K C _ j => if ∑ k ∈ K, C k = 0 then 1 / (K.card : ℝ) else C j / ∑ k ∈ K, C k,
          fun K _ _ _ => 1 / (K.card : ℝ), ?_, ?_, ?_⟩, ?_, ?_⟩
        · constructor
          · intro K C E hK hC hE
            have hc : (K.card : ℝ) ≠ 0 := by exact_mod_cast hK.card_pos.ne'
            have hc1 : (1:ℝ) ≤ K.card := by exact_mod_cast hK.card_pos
            by_cases hS : ∑ k ∈ K, C k = 0
            · simp only [hS, if_true]
              refine ⟨fun j _ => ⟨by positivity, ?_⟩, ?_⟩
              · rw [div_le_one (by positivity)]; exact hc1
              · rw [Finset.sum_const, nsmul_eq_mul]; field_simp
            · simp only [hS, if_false]
              have hS0 : 0 < ∑ k ∈ K, C k := lt_of_le_of_ne (Finset.sum_nonneg hC) (Ne.symm hS)
              refine ⟨fun j hj => ⟨div_nonneg (hC j hj) hS0.le, ?_⟩, ?_⟩
              · rw [div_le_one hS0]; exact Finset.single_le_sum hC hj
              · rw [← Finset.sum_div, div_self hS]
          · intro K C C' E h j hj
            simp only
            rw [Finset.sum_congr rfl h, h j hj]
        · constructor
          · intro K C E hK hC hE
            have hc : (K.card : ℝ) ≠ 0 := by exact_mod_cast hK.card_pos.ne'
            have hc1 : (1:ℝ) ≤ K.card := by exact_mod_cast hK.card_pos
            refine ⟨fun j _ => ⟨by positivity, ?_⟩, ?_⟩
            · rw [div_le_one (by positivity)]; exact hc1
            · rw [Finset.sum_const, nsmul_eq_mul]; field_simp
          · intro K C C' E h j hj
            rfl
        · intro n t
          constructor
          · funext i
            rw [hPR]
            rcases t.support.eq_empty_or_nonempty with he | hne
            · simp [he, weightedProportional, assocClaims]
            · have hS : 0 < ∑ j ∈ t.support, ∑ i', (t j i' : ℝ) := Finset.sum_pos (hpos n t) hne
              have hS' : ∑ k ∈ (assocClaims t).K, (assocClaims t).issueTotal k ≠ 0 := hS.ne'
              simp only [weightedProportional, if_neg hS']
              dsimp only [assocClaims, ClaimsProblem.issueTotal]
              refine Finset.sum_congr rfl (fun j hj => ?_)
              have := (hpos n t j hj).ne'
              field_simp
          · funext i
            simp only [weightedProportional, assocClaims, ClaimsProblem.issueTotal, reward, hUsum]
            rcases t.support.eq_empty_or_nonempty with he | hne
            · simp [he]
            · have hc : (t.support.card : ℝ) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
              rw [hUC, div_mul_cancel₀ _ hc]
              refine Finset.sum_congr rfl (fun j hj => ?_)
              field_simp
        · intro n t
          funext i
          rw [hPR]
          simp only [twoStage, proportional, ClaimsProblem.secondStage, ClaimsProblem.issueProblem,
            assocClaims, ClaimsProblem.issueTotal]
          refine Finset.sum_congr rfl (fun j hj => ?_)
          have := (hpos n t j hj).ne'
          field_simp
        · have hcea : ∀ (n : ℕ) (t : Problem n), ∀ j ∈ t.support,
              cea (assocClaims t).issueProblem j = 1 := by
            intro n t j hj
            have hne : (ceaCutoffs (assocClaims t).issueProblem).Nonempty := ⟨1, by
              refine ⟨zero_le_one, ?_⟩
              simp only [ClaimsProblem.issueProblem, assocClaims, ClaimsProblem.issueTotal]
              rw [Finset.card_eq_sum_ones]; push_cast
              exact Finset.sum_congr rfl (fun k hk => min_eq_left (hge1 n t k hk))⟩
            simp only [cea]
            rw [dif_pos hne]
            obtain ⟨hl0, hl⟩ := hne.choose_spec
            set l := hne.choose
            simp only [ClaimsProblem.issueProblem, assocClaims, ClaimsProblem.issueTotal] at hl ⊢
            rw [Finset.card_eq_sum_ones] at hl; push_cast at hl
            by_cases h1 : 1 ≤ l
            · have := (Finset.sum_eq_sum_iff_of_le
                (fun k hk => le_min h1 (hge1 n t k hk))).mp hl.symm j hj
              exact this.symm
            · exfalso
              push Not at h1
              have : ∑ k ∈ t.support, min l (∑ i, (t k i:ℝ)) < ∑ k ∈ t.support, (1:ℝ) :=
                Finset.sum_lt_sum_of_nonempty ⟨j, hj⟩
                  (fun k hk => lt_of_le_of_lt (min_le_left _ _) h1)
              linarith
          intro n t
          funext i
          rw [hUC]
          simp only [twoStage, proportional]
          refine Finset.sum_congr rfl (fun j hj => ?_)
          rw [hcea n t j hj]
          simp only [ClaimsProblem.secondStage, assocClaims, mul_one]
