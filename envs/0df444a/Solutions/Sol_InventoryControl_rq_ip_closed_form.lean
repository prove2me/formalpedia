-- Prove2me | solution 1 for InventoryControl.rq_ip_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T20:09:35.150505+00:00
-- url     : https://prove2.me/submissions/a1baaa95-6850-45e7-9df6-40fbba1778ba

import Mathlib
import Definitions.Def_InventoryControl_rqPolicy

set_option autoImplicit false

open InventoryControl in
lemma p200_band (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (z : ℤ) :
    R + 1 ≤ reduceToBand R Q z ∧ reduceToBand R Q z ≤ R + Q ∧
      (Q : ℤ) ∣ reduceToBand R Q z - z := by
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
  unfold reduceToBand
  refine ⟨?_, ?_, ?_⟩
  · have := Int.emod_nonneg (z - (R + 1)) hQ'.ne'
    linarith
  · have := Int.emod_lt_of_pos (z - (R + 1)) hQ'
    linarith
  · have h := Int.emod_add_mul_ediv (z - (R + 1)) (Q : ℤ)
    exact ⟨-((z - (R + 1)) / (Q : ℤ)), by linear_combination h⟩

open InventoryControl in
lemma p200_uniq (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (z w : ℤ) (h1 : R + 1 ≤ w) (h2 : w ≤ R + Q)
    (hd : (Q : ℤ) ∣ w - z) : w = reduceToBand R Q z := by
  obtain ⟨b1, b2, b3⟩ := p200_band R Q hQ z
  have hx : (Q : ℤ) ∣ w - reduceToBand R Q z := by
    have := dvd_sub hd b3
    rwa [show w - z - (reduceToBand R Q z - z) = w - reduceToBand R Q z by ring] at this
  have := Int.eq_zero_of_abs_lt_dvd hx (by rw [abs_lt]; constructor <;> linarith)
  linarith

open InventoryControl in
lemma p200_order (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (y : ℤ) :
    y + (Q : ℤ) * ((R + 1 - y + (Q : ℤ) - 1) / (Q : ℤ)) = reduceToBand R Q y := by
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
  have h := Int.emod_add_mul_ediv (R + 1 - y + (Q : ℤ) - 1) (Q : ℤ)
  have h2 := Int.emod_lt_of_pos (R + 1 - y + (Q : ℤ) - 1) hQ'
  have h3 := Int.emod_nonneg (R + 1 - y + (Q : ℤ) - 1) hQ'.ne'
  apply p200_uniq R Q hQ
  · linarith
  · linarith
  · exact ⟨(R + 1 - y + (Q : ℤ) - 1) / (Q : ℤ), by ring⟩

open InventoryControl in
lemma p200_succ {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : CompoundPoissonDemand P) (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (y0 : ℤ) (n : ℕ) (ω : Ω) :
    rqIP X R Q y0 (n + 1) ω
      = if R + 1 ≤ rqIP X R Q y0 n ω - (X.dem n ω : ℤ) then rqIP X R Q y0 n ω - (X.dem n ω : ℤ)
        else reduceToBand R Q (rqIP X R Q y0 n ω - (X.dem n ω : ℤ)) := by
  simp only [rqIP]
  split_ifs with h
  · rfl
  · exact p200_order R Q hQ _

open InventoryControl in
lemma p200_cum {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : CompoundPoissonDemand P) (n : ℕ) (ω : Ω) :
    (X.cumDemand (n + 1) ω : ℤ) = (X.cumDemand n ω : ℤ) + (X.dem n ω : ℤ) := by
  unfold CompoundPoissonDemand.cumDemand
  rw [Finset.sum_range_succ]
  push_cast
  ring

open InventoryControl in
lemma p200_main {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : CompoundPoissonDemand P) (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (y0 : ℤ) (ω : Ω) (n : ℕ) :
    (0 < n ∨ R + 1 ≤ y0 →
      rqIP X R Q y0 n ω
        = (if R + 1 ≤ y0 - (X.cumDemand n ω : ℤ) then y0 - (X.cumDemand n ω : ℤ)
           else reduceToBand R Q (y0 - (X.cumDemand n ω : ℤ)))) := by
  induction n with
  | zero =>
    intro h
    have hy : R + 1 ≤ y0 := by
      rcases h with h | h
      · omega
      · exact h
    have hS : (X.cumDemand 0 ω : ℤ) = 0 := by simp [CompoundPoissonDemand.cumDemand]
    rw [hS, sub_zero, if_pos hy]
    rfl
  | succ n ih =>
    intro _
    rw [p200_succ X R Q hQ y0 n ω, p200_cum X n ω]
    have hd : (0 : ℤ) ≤ (X.dem n ω : ℤ) := by positivity
    rw [show y0 - ((X.cumDemand n ω : ℤ) + (X.dem n ω : ℤ))
        = (y0 - (X.cumDemand n ω : ℤ)) - (X.dem n ω : ℤ) by ring]
    set z := y0 - (X.cumDemand n ω : ℤ) with hz
    set d := (X.dem n ω : ℤ) with hdd
    by_cases h0 : 0 < n ∨ R + 1 ≤ y0
    · have ih' := ih h0
      by_cases hzR : R + 1 ≤ z
      · rw [ih', if_pos hzR]
      · rw [ih', if_neg hzR]
        have hzd : ¬ R + 1 ≤ z - d := by omega
        rw [if_neg hzd]
        obtain ⟨b1, b2, b3⟩ := p200_band R Q hQ z
        split_ifs with hb
        · apply p200_uniq R Q hQ
          · exact hb
          · linarith
          · rwa [show reduceToBand R Q z - d - (z - d) = reduceToBand R Q z - z by ring]
        · obtain ⟨c1, c2, c3⟩ := p200_band R Q hQ (reduceToBand R Q z - d)
          apply p200_uniq R Q hQ
          · exact c1
          · exact c2
          · have := dvd_add c3 b3
            rwa [show reduceToBand R Q (reduceToBand R Q z - d) - (reduceToBand R Q z - d)
                + (reduceToBand R Q z - z)
                = reduceToBand R Q (reduceToBand R Q z - d) - (z - d) by ring] at this
    · have hn : n = 0 := by omega
      have hy : ¬ R + 1 ≤ y0 := fun h => h0 (Or.inr h)
      subst hn
      have hS : (X.cumDemand 0 ω : ℤ) = 0 := by simp [CompoundPoissonDemand.cumDemand]
      have hr : rqIP X R Q y0 0 ω = z := by
        rw [hz, hS, sub_zero]
        rfl
      rw [hr]

open InventoryControl in
lemma p200_ip {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : CompoundPoissonDemand P) (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (y0 : ℤ) (ω : Ω) (n : ℕ) :
    ipPath X Q y0 (rqOrders X R Q y0) n ω = rqIP X R Q y0 n ω := by
  have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
  induction n with
  | zero => rfl
  | succ n ih =>
    have hdiff : ∃ c : ℤ, 0 ≤ c ∧
        rqIP X R Q y0 (n + 1) ω - (rqIP X R Q y0 n ω - (X.dem n ω : ℤ)) = (Q : ℤ) * c := by
      rw [p200_succ X R Q hQ y0 n ω]
      split_ifs with h
      · exact ⟨0, le_refl _, by ring⟩
      · rw [← p200_order R Q hQ]
        refine ⟨(R + 1 - (rqIP X R Q y0 n ω - (X.dem n ω : ℤ)) + (Q : ℤ) - 1) / (Q : ℤ), ?_,
          by ring⟩
        apply Int.ediv_nonneg
        · omega
        · exact hQ'.le
    obtain ⟨c, hc0, hc⟩ := hdiff
    simp only [ipPath]
    rw [ih]
    unfold rqOrders
    rw [hc, Int.mul_ediv_cancel_left c hQ'.ne', Int.toNat_of_nonneg hc0]
    linarith

open InventoryControl in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    (X : CompoundPoissonDemand P) (R : ℤ) (Q : ℕ) (hQ : 0 < Q) (y0 : ℤ) (n : ℕ) (ω : Ω) :
    (0 < n ∨ R + 1 ≤ y0 →
      rqIP X R Q y0 n ω
        = (if R + 1 ≤ y0 - (X.cumDemand n ω : ℤ) then y0 - (X.cumDemand n ω : ℤ)
           else reduceToBand R Q (y0 - (X.cumDemand n ω : ℤ))))
      ∧ ipPath X Q y0 (rqOrders X R Q y0) n ω = rqIP X R Q y0 n ω := by
  exact ⟨p200_main X R Q hQ y0 ω n, p200_ip X R Q hQ y0 ω n⟩
