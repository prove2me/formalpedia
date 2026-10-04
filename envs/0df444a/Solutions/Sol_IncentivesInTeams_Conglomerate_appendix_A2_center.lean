-- Prove2me | solution 1 for IncentivesInTeams.Conglomerate.appendix_A2_center
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-03T12:51:34.908035+00:00
-- url     : https://prove2.me/submissions/47e3dcae-2ae1-48cd-8414-a5f70ca5ada7

import Theorems.Thm_IncentivesInTeams_Conglomerate_cond_expectation_factorizes

open IncentivesInTeams.Conglomerate Finset

namespace OwnProfitExpectation

open Classical

private theorem finite_tower {α Y : Type*} [Fintype α]
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (g : α → Y) (X : α → ℝ) :
    (∑ a, w a * X a) =
      ∑ a, w a * condAvg w {t | g t = g a} X := by
  classical
  have hg : ∀ a ∈ (univ : Finset α), g a ∈ univ.image g :=
    fun a ha => mem_image_of_mem g ha
  rw [← sum_fiberwise_of_maps_to hg (fun a => w a * X a),
    ← sum_fiberwise_of_maps_to hg (fun a => w a * condAvg w {t | g t = g a} X)]
  apply sum_congr rfl
  intro y _
  have hc : (∑ a ∈ univ.filter (fun a => g a = y),
      w a * condAvg w {t | g t = g a} X) =
      (∑ a ∈ univ.filter (fun a => g a = y), w a) * condAvg w {t | g t = y} X := by
    rw [sum_mul]
    apply sum_congr rfl
    intro a ha
    rw [(mem_filter.mp ha).2]
  rw [hc]
  simp only [condAvg, Set.mem_ofPred_eq]
  by_cases hz : (∑ a ∈ univ.filter (fun a => g a = y), w a) = 0
  · have hzero : ∀ a ∈ univ.filter (fun a => g a = y), w a = 0 :=
      (sum_eq_zero_iff_of_nonneg (fun a _ => hw a)).mp hz
    have hn : (∑ a ∈ univ.filter (fun a => g a = y), w a * X a) = 0 := by
      apply sum_eq_zero
      intro a ha
      rw [hzero a ha, zero_mul]
    rw [hn, zero_div, mul_zero]
  · field_simp

end OwnProfitExpectation

open OwnProfitExpectation

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {S₀ : Type*} [Fintype S₀] {S : ι → Type*}
    [∀ i, Fintype (S i)] {Z₀ : Type*} {Z M₀ M : ι → Type*} {D₀ : Type*} {D : ι → Type*}
    (T : Model S₀ S Z₀ Z M₀ M D₀ D) (hT : T.WeightsOK)
    (βs : JointStrategy S₀ S Z₀ Z M₀ M D₀ D) (i : ι)
    (b : SubStrategy (S i) (Z i) (M₀ i) (M i) (D i)) (hb : b ∈ T.B i) :
    T.expect (T.headPayoff (βs.update i b)) =
      T.expect (fun s => T.headFactor βs ((βs.update i b).headInfo s)) := by
  classical
  have hp : ∀ s, 0 ≤ T.prob s := fun s =>
    mul_nonneg (hT.1.1 s.1) (prod_nonneg (fun k _ => (hT.2 k).1 (s.2 k)))
  calc
    _ = T.expect (fun s => T.literalHeadCondExp (βs.update i b)
        ((βs.update i b).headInfo s)) :=
      finite_tower T.prob hp (βs.update i b).headInfo (T.headPayoff (βs.update i b))
    _ = _ := by
      apply sum_congr rfl
      intro s _
      by_cases hs : T.prob s = 0
      · simp only [hs, zero_mul]
      · have hpos : 0 < T.expect (Set.indicator
            {t | (βs.update i b).headInfo t = (βs.update i b).headInfo s}
            (fun _ => (1 : ℝ))) := by
          unfold Model.expect
          apply sum_pos'
          · intro t _
            apply mul_nonneg (hp t)
            simp only [Set.indicator, Set.mem_ofPred_eq]
            split_ifs <;> norm_num
          · exact ⟨s, mem_univ s, by
              simpa [Set.indicator] using
                (lt_of_le_of_ne (hp s) (Ne.symm hs))⟩
        have h := (cond_expectation_factorizes T hT (βs.update i b)
          ((βs.update i b).headInfo s) hpos).2
        exact congrArg (fun r => T.prob s * r) h
