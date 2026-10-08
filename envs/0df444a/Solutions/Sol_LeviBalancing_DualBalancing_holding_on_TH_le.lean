-- Prove2me | solution 1 for LeviBalancing.DualBalancing.holding_on_TH_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:04:49.060673+00:00
-- url     : https://prove2.me/submissions/b87c49af-17a3-442f-8f72-a02c7dab25e3

import Mathlib
import Definitions.Def_LeviBalancing_DualBalancing_Model
open Finset

namespace LeviBalancingAux_b476

theorem tele (f : ℤ → ℝ) (n : ℤ) (hn : 0 ≤ n) :
    ∑ s ∈ Finset.Icc (1 : ℤ) n, (f (s + 1) - f s) = f (n + 1) - f 1 := by
  induction n, hn using Int.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.sum_insert (by simp), ih]
    ring

theorem keyB (g : ℝ → ℝ) (hg : Monotone g) (a b : ℤ → ℝ) (h1 : a 1 = b 1) (n : ℤ) (hn : 0 ≤ n) :
    (∀ t, 1 ≤ t → t ≤ n → a t ≤ a (t + 1)) → (∀ t, 1 ≤ t → t ≤ n → b t ≤ b (t + 1)) →
    ∑ t ∈ (Finset.Icc (1 : ℤ) n).filter (fun t => a (t + 1) < b (t + 1)), (g (a (t + 1)) - g (a t))
      ≤ g (min (a (n + 1)) (b (n + 1))) - g (a 1) := by
  induction n, hn using Int.le_induction with
  | base => intro _ _; simp [h1]
  | succ n hn ih =>
    intro ha hb
    have ih' := ih (fun t h1 h2 => ha t h1 (by omega)) (fun t h1 h2 => hb t h1 (by omega))
    have han := ha (n + 1) (by omega) le_rfl
    have hbn := hb (n + 1) (by omega) le_rfl
    rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.filter_insert]
    split_ifs with hc
    · rw [Finset.sum_insert (by simp)]
      have hm : min (a (n + 1 + 1)) (b (n + 1 + 1)) = a (n + 1 + 1) := min_eq_left hc.le
      rw [hm]
      have : g (min (a (n + 1)) (b (n + 1))) ≤ g (a (n + 1)) := hg (min_le_left _ _)
      linarith
    · have : g (min (a (n + 1)) (b (n + 1))) ≤ g (min (a (n + 1 + 1)) (b (n + 1 + 1))) :=
        hg (min_le_min han hbn)
      linarith

theorem maxid (o c x : ℝ) (ho : 0 ≤ o) :
    max (o - max (c - x) 0) 0 = max (x + o - c) 0 - max (x - c) 0 := by
  simp only [max_def]
  split_ifs <;> linarith

open LeviBalancing.DualBalancing in
theorem cumD_split (d : ℤ → ℝ) (t j : ℤ) (ht : 1 ≤ t) (hj : t ≤ j + 1) :
    cumDemand d 1 j = cumDemand d 1 (t - 1) + cumDemand d t j := by
  unfold cumDemand
  rw [max_eq_left (le_refl (1:ℤ)), max_eq_left ht]
  have hj' : t - 1 ≤ j := by omega
  clear hj
  induction j, hj' using Int.le_induction with
  | base => simp
  | succ j hj ih =>
    rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega),
      ← Finset.insert_Icc_right_eq_Icc_add_one (a := t) (by omega),
      Finset.sum_insert (by simp), Finset.sum_insert (by simp), ih]
    ring

open LeviBalancing.DualBalancing in
/-- cumulative supply before period t -/
noncomputable def cumA (I : Instance) (Q : ℤ → ℝ) (t : ℤ) : ℝ :=
  I.ni0 + ∑ i ∈ Finset.Ico (1 - (I.L : ℤ)) t, order I Q i

open LeviBalancing.DualBalancing in
theorem cumA_succ (I : Instance) (Q : ℤ → ℝ) (t : ℤ) (ht : 1 - (I.L : ℤ) ≤ t) :
    cumA I Q (t + 1) = cumA I Q t + order I Q t := by
  unfold cumA
  rw [← Finset.insert_Ico_right_eq_Ico_add_one_of_not_isMax ht (not_isMax t),
    Finset.sum_insert (by simp)]
  ring

open LeviBalancing.DualBalancing in
theorem cumA_one (I : Instance) (Q R : ℤ → ℝ) : cumA I Q 1 = cumA I R 1 := by
  unfold cumA
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_Ico] at hi
  simp [order, show i ≤ 0 by omega]

open LeviBalancing.DualBalancing in
theorem invPos_eq (I : Instance) (d Q : ℤ → ℝ) (t : ℤ) :
    invPosition I d Q t = cumA I Q t - cumDemand d 1 (t - 1) := by
  unfold invPosition cumA; ring

open LeviBalancing.DualBalancing in
theorem invPosAfter_eq (I : Instance) (d Q : ℤ → ℝ) (t : ℤ) (ht : 1 ≤ t) :
    invPositionAfter I d Q t = cumA I Q (t + 1) - cumDemand d 1 (t - 1) := by
  unfold invPositionAfter
  rw [invPos_eq, cumA_succ I Q t (by omega)]; ring

open LeviBalancing.DualBalancing in
theorem mh_eq (I : Instance) (d Q : ℤ → ℝ) (hQ : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) → 0 ≤ Q t)
    (t : ℤ) (ht1 : 1 ≤ t) (ht2 : t ≤ (I.T : ℤ)) :
    marginalHolding I d Q t = ∑ j ∈ Finset.Icc (t + I.L) (I.T : ℤ),
      I.h j * (max (cumA I Q (t + 1) - cumDemand d 1 j) 0 - max (cumA I Q t - cumDemand d 1 j) 0) := by
  unfold marginalHolding
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_Icc] at hj
  congr 1
  have ho : order I Q t = Q t := by simp [order, show ¬ t ≤ 0 by omega]
  have hs := cumD_split d t j ht1 (by omega)
  rw [maxid _ _ _ (by rw [ho]; exact hQ t ht1 ht2), invPos_eq, cumA_succ I Q t (by omega)]
  congr 2 <;> linarith

end LeviBalancingAux_b476

open LeviBalancingAux_b476 in
open Finset LeviBalancing.DualBalancing in
theorem solution (I : Instance) (d : ℤ → ℝ)
    (hd : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) → 0 ≤ d t) (qB qP : ℤ → ℝ)
    (hqB : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) → 0 ≤ qB t)
    (hqP : ∀ t : ℤ, 1 ≤ t → t ≤ (I.T : ℤ) → 0 ≤ qP t) :
    ∑ t ∈ (Icc (1 : ℤ) ((I.T : ℤ) - I.L)).filter
        (fun t => invPositionAfter I d qB t < invPositionAfter I d qP t),
        marginalHolding I d qB t ≤
      ∑ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L), marginalHolding I d qP t := by
  set g : ℤ → ℝ → ℝ := fun j x => max (x - cumDemand d 1 j) 0 with hg
  have hgm : ∀ j, Monotone (g j) := fun j x y h => max_le_max (by linarith) le_rfl
  -- rewrite the filter
  have hfilt : (Icc (1 : ℤ) ((I.T : ℤ) - I.L)).filter
        (fun t => invPositionAfter I d qB t < invPositionAfter I d qP t) =
      (Icc (1 : ℤ) ((I.T : ℤ) - I.L)).filter
        (fun t => cumA I qB (t + 1) < cumA I qP (t + 1)) := by
    apply Finset.filter_congr
    intro t ht
    simp only [Finset.mem_Icc] at ht
    rw [invPosAfter_eq I d qB t ht.1, invPosAfter_eq I d qP t ht.1]
    constructor <;> intro h <;> linarith
  rw [hfilt]
  have hL : ∀ t ∈ (Icc (1 : ℤ) ((I.T : ℤ) - I.L)).filter
        (fun t => cumA I qB (t + 1) < cumA I qP (t + 1)),
      marginalHolding I d qB t = ∑ j ∈ Finset.Icc (t + I.L) (I.T : ℤ),
        I.h j * (g j (cumA I qB (t + 1)) - g j (cumA I qB t)) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_Icc] at ht
    exact mh_eq I d qB hqB t ht.1.1 (by omega)
  have hR : ∀ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L),
      marginalHolding I d qP t = ∑ j ∈ Finset.Icc (t + I.L) (I.T : ℤ),
        I.h j * (g j (cumA I qP (t + 1)) - g j (cumA I qP t)) := by
    intro t ht
    simp only [Finset.mem_Icc] at ht
    exact mh_eq I d qP hqP t ht.1 (by omega)
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR]
  have swB : (∑ t ∈ (Icc (1 : ℤ) ((I.T : ℤ) - I.L)).filter
        (fun t => cumA I qB (t + 1) < cumA I qP (t + 1)), ∑ j ∈ Finset.Icc (t + I.L) (I.T : ℤ),
        I.h j * (g j (cumA I qB (t + 1)) - g j (cumA I qB t))) =
      ∑ j ∈ Finset.Icc (1 + (I.L : ℤ)) (I.T : ℤ), ∑ t ∈ (Icc (1 : ℤ) (j - I.L)).filter
        (fun t => cumA I qB (t + 1) < cumA I qP (t + 1)),
        I.h j * (g j (cumA I qB (t + 1)) - g j (cumA I qB t)) := by
    apply Finset.sum_comm'
    intro t j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩
      exact ⟨⟨⟨h1, by omega⟩, h3⟩, by omega, h5⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩
      exact ⟨⟨⟨h1, by omega⟩, h3⟩, by omega, h5⟩
  have swP : (∑ t ∈ Icc (1 : ℤ) ((I.T : ℤ) - I.L), ∑ j ∈ Finset.Icc (t + I.L) (I.T : ℤ),
        I.h j * (g j (cumA I qP (t + 1)) - g j (cumA I qP t))) =
      ∑ j ∈ Finset.Icc (1 + (I.L : ℤ)) (I.T : ℤ), ∑ t ∈ Icc (1 : ℤ) (j - I.L),
        I.h j * (g j (cumA I qP (t + 1)) - g j (cumA I qP t)) := by
    apply Finset.sum_comm'
    intro t j
    simp only [Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h4, h5⟩
      exact ⟨⟨h1, by omega⟩, by omega, h5⟩
    · rintro ⟨⟨h1, h2⟩, h4, h5⟩
      exact ⟨⟨h1, by omega⟩, by omega, h5⟩
  rw [swB, swP]
  apply Finset.sum_le_sum
  intro j hj
  simp only [Finset.mem_Icc] at hj
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (I.h_nonneg j (by omega) hj.2)
  have hn : (0 : ℤ) ≤ j - I.L := by omega
  have hB := keyB (g j) (hgm j) (cumA I qB) (cumA I qP) (cumA_one I qB qP) (j - I.L) hn
    (fun t h1 h2 => by
      rw [cumA_succ I qB t (by omega)]
      have : order I qB t = qB t := by simp [order, show ¬ t ≤ 0 by omega]
      rw [this]; linarith [hqB t h1 (by omega)])
    (fun t h1 h2 => by
      rw [cumA_succ I qP t (by omega)]
      have : order I qP t = qP t := by simp [order, show ¬ t ≤ 0 by omega]
      rw [this]; linarith [hqP t h1 (by omega)])
  rw [tele (fun s => g j (cumA I qP s)) (j - I.L) hn]
  have h1 := cumA_one I qB qP
  have : g j (min (cumA I qB (j - I.L + 1)) (cumA I qP (j - I.L + 1))) ≤ g j (cumA I qP (j - I.L + 1)) :=
    hgm j (min_le_right _ _)
  rw [h1] at hB
  linarith
