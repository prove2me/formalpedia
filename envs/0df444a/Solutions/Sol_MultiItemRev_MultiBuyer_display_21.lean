-- Prove2me | solution 1 for MultiItemRev.MultiBuyer.display_21
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T15:49:19.280666+00:00
-- url     : https://prove2.me/submissions/55451776-a2e1-4588-97d3-3fc2dae5c292

import Mathlib
import Definitions.Def_MultiItemRev_MultiBuyer_Model

open MeasureTheory
open scoped NNReal ENNReal

open MultiItemRev.MultiBuyer in
theorem solution {n : ℕ} (hn : 1 ≤ n) (μY : Measure (Fin n → ℝ≥0)) [IsProbabilityMeasure μY]
    (t : ℝ≥0) :
    (t : ℝ≥0∞) * μY {y | t ≤ maxCoord y} ≤ RevDS (oneGoodN μY) := by
  classical
  -- the winner predicate: the first buyer whose value is at least the posted price `t`
  let W : (Fin n → Unit → ℝ≥0) → Fin n → Prop := fun y j => t ≤ y j () ∧ ∀ l, l < j → y l () < t
  have hWuniq : ∀ y j k, W y j → W y k → j = k := by
    intro y j k hj hk
    rcases lt_trichotomy j k with h | h | h
    · exact absurd hj.1 (not_le.2 (hk.2 j h))
    · exact h
    · exact absurd hk.1 (not_le.2 (hj.2 k h))
  have hWex : ∀ y, (∃ j, t ≤ y j ()) → ∃ j, W y j := by
    intro y ⟨j, hj⟩
    let S := Finset.univ.filter (fun j => t ≤ y j ())
    have hS : S.Nonempty := ⟨j, by simp [S, hj]⟩
    refine ⟨S.min' hS, ?_, ?_⟩
    · have := S.min'_mem hS
      simpa [S] using this
    · intro l hl
      by_contra hc
      have hlS : l ∈ S := by simp [S]; exact not_lt.1 hc
      exact absurd (S.min'_le l hlS) (not_le.2 hl)
  let M : MechanismN n Unit :=
    { q := fun y j _ => if W y j then 1 else 0
      s := fun y j => if W y j then (t : ℝ) else 0 }
  have hWupd : ∀ (x : Fin n → Unit → ℝ≥0) j (x' : Unit → ℝ≥0),
      W (Function.update x j x') j ↔ (t ≤ x' () ∧ ∀ l, l < j → x l () < t) := by
    intro x j x'
    simp only [W, Function.update_self]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun l hl => ?_⟩
      have := h2 l hl
      rwa [Function.update_of_ne (ne_of_lt hl)] at this
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun l hl => ?_⟩
      rw [Function.update_of_ne (ne_of_lt hl)]
      exact h2 l hl
  have hpay : ∀ x j, payoffN M x j = if W x j then ((x j () : ℝ) - t) else 0 := by
    intro x j
    simp only [payoffN, M, Finset.univ_unique, Finset.sum_singleton]
    split_ifs <;> ring
  have hadm : IsAdmissibleDS M := by
    refine ⟨⟨fun x j i => ?_, fun x i => ?_⟩, ?_, ?_, ?_⟩
    · simp only [M]; split_ifs <;> norm_num
    · simp only [M]
      by_cases h : ∃ j, W x j
      · obtain ⟨j0, hj0⟩ := h
        rw [Finset.sum_eq_single j0]
        · simp [hj0]
        · intro b _ hb
          have : ¬ W x b := fun hW => hb (hWuniq x b j0 hW hj0)
          simp [this]
        · simp
      · push_neg at h
        simp [h]
    · intro x j x'
      rw [hpay]
      simp only [M, Finset.univ_unique, Finset.sum_singleton]
      have key := hWupd x j x'
      by_cases hP : ∀ l, l < j → x l () < t
      · by_cases htx : t ≤ x j ()
        · have hW : W x j := ⟨htx, hP⟩
          simp only [hW, if_true]
          split_ifs <;> simp [htx]
        · have hW : ¬ W x j := fun h => htx h.1
          simp only [hW, if_false]
          split_ifs with h1
          · push_neg at htx; simp; exact_mod_cast htx.le
          · simp
      · have hW' : ¬ W (Function.update x j x') j := fun h => hP (key.1 h).2
        have hW : ¬ W x j := fun h => hP h.2
        simp [hW, hW']
    · intro x j
      rw [hpay]
      split_ifs with h
      · have := h.1; simp; exact_mod_cast this
      · exact le_refl _
    · intro j
      have hmeas : MeasurableSet {y : Fin n → Unit → ℝ≥0 | W y j} := by
        simp only [W, Set.setOf_and]
        refine MeasurableSet.inter ?_ ?_
        · exact measurableSet_le measurable_const ((measurable_pi_apply ()).comp (measurable_pi_apply j))
        · rw [Set.setOf_forall]
          refine MeasurableSet.iInter fun l => ?_
          rw [Set.setOf_forall]
          refine MeasurableSet.iInter fun _ => ?_
          exact measurableSet_lt ((measurable_pi_apply ()).comp (measurable_pi_apply l)) measurable_const
      exact Measurable.ite hmeas measurable_const measurable_const
  -- seller revenue
  have hS : ∀ y : Fin n → Unit → ℝ≥0,
      sellerRevenue M y = if ∃ j, t ≤ y j () then (t : ℝ) else 0 := by
    intro y
    simp only [sellerRevenue, M]
    by_cases h : ∃ j, t ≤ y j ()
    · obtain ⟨j0, hj0⟩ := hWex y h
      rw [if_pos h, Finset.sum_eq_single j0]
      · simp [hj0]
      · intro b _ hb
        have : ¬ W y b := fun hW => hb (hWuniq y b j0 hW hj0)
        simp [this]
      · simp
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro j _
      have : ¬ W y j := fun hW => h ⟨j, hW.1⟩
      simp [this]
  have hset : ∀ y : Fin n → ℝ≥0, (∃ j, t ≤ (fun j (_ : Unit) => y j) j ()) ↔ t ≤ maxCoord y := by
    intro y
    rcases eq_or_ne t 0 with ht | ht
    · subst ht
      exact ⟨fun _ => bot_le, fun _ => ⟨⟨0, hn⟩, bot_le⟩⟩
    · simp only [maxCoord]
      rw [Finset.le_sup_iff (bot_lt_iff_ne_bot.2 ht)]
      simp
  have hsetM : MeasurableSet {y : Fin n → ℝ≥0 | t ≤ maxCoord y} := by
    have : {y : Fin n → ℝ≥0 | t ≤ maxCoord y} = ⋃ j, {y | t ≤ y j} := by
      ext y; simp only [Set.mem_setOf_eq, Set.mem_iUnion, ← hset y]
    rw [this]
    exact MeasurableSet.iUnion fun j => measurableSet_le measurable_const (measurable_pi_apply j)
  have hSmeas : Measurable (fun x => sellerRevenue M x) := by
    simp only [sellerRevenue]
    exact Finset.measurable_sum _ fun j _ => hadm.2.2.2 j
  have hg : Measurable (fun (y : Fin n → ℝ≥0) (j : Fin n) (_ : Unit) => y j) := by
    measurability
  have hpos : ∫⁻ x, ENNReal.ofReal (sellerRevenue M x) ∂(oneGoodN μY) =
      (t : ℝ≥0∞) * μY {y | t ≤ maxCoord y} := by
    rw [oneGoodN, lintegral_map hSmeas.ennreal_ofReal hg]
    have : (fun y : Fin n → ℝ≥0 => ENNReal.ofReal (sellerRevenue M (fun j _ => y j))) =
        {y | t ≤ maxCoord y}.indicator (fun _ => (t : ℝ≥0∞)) := by
      funext y
      rw [hS, Set.indicator_apply]
      simp only [Set.mem_setOf_eq]
      by_cases h : t ≤ maxCoord y
      · have h' := (hset y).2 h
        simp only at h'
        simp [h, h']
      · have h' : ¬ ∃ j, t ≤ y j := fun hh => h ((hset y).1 hh)
        simp [h, h']
    rw [this, lintegral_indicator_const hsetM]
  have hneg : ∫⁻ x, ENNReal.ofReal (-sellerRevenue M x) ∂(oneGoodN μY) = 0 := by
    have : (fun x => ENNReal.ofReal (-sellerRevenue M x)) = fun _ => 0 := by
      funext x
      rw [hS]
      split_ifs <;> simp
    rw [this, lintegral_zero]
  have hrev : (expRevenueN (oneGoodN μY) M).toENNReal = (t : ℝ≥0∞) * μY {y | t ≤ maxCoord y} := by
    rw [expRevenueN, hpos, hneg]
    simp only [EReal.coe_ennreal_zero, sub_zero, EReal.toENNReal_coe]
  rw [← hrev]
  exact le_iSup₂ (f := fun (M : MechanismN n Unit) (_ : IsAdmissibleDS M) =>
    (expRevenueN (oneGoodN μY) M).toENNReal) M hadm
