-- Prove2me | solution 1 for MultiPriceOnline.Ratios.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:32:16.696255+00:00
-- url     : https://prove2.me/submissions/b32cc1f5-c99d-49d6-ba82-d2f4b7ab3ba4

import Mathlib
import Definitions.Def_MultiPriceOnline_Ratios_Setting

namespace RRAux_MultiPriceOnline_Ratios_proposition_2

theorem exp_chord (x y t : ℝ) (hxy : x ≠ y) (ht0 : 0 < t) (ht1 : t < 1) :
    Real.exp ((1 - t) * x + t * y) < (1 - t) * Real.exp x + t * Real.exp y := by
  have := strictConvexOn_exp.2 (Set.mem_univ x) (Set.mem_univ y) hxy
    (show 0 < 1 - t by linarith) ht0 (by ring)
  simpa [smul_eq_mul] using this

theorem ineq_i (x : ℝ) (h0 : 0 < x) (h1 : x < 1) :
    (1 - Real.exp (-1)) * x < 1 - Real.exp (-x) := by
  have := exp_chord 0 (-1) x (by norm_num) h0 h1
  rw [show (1 - x) * 0 + x * (-1) = -x by ring, Real.exp_zero] at this
  nlinarith

theorem ineq_ii (σ c : ℝ) (hσ : 0 < σ) (h0 : 0 < c) (h1 : c < 1) :
    Real.exp (-(σ * c)) < 1 - (1 - Real.exp (-σ)) * c := by
  have := exp_chord 0 (-σ) c (by linarith) h0 h1
  rw [show (1 - c) * 0 + c * (-σ) = -(σ * c) by ring, Real.exp_zero] at this
  nlinarith

theorem ineq_iv (F c : ℝ) (hF0 : 0 < F) (hF1 : F < 1) (h0 : 0 < c) (h1 : c < 1) :
    Real.exp (F * Real.log (1 - c)) < 1 - F * c := by
  have hL : Real.log (1 - c) ≠ 0 := by
    have := Real.log_neg (show 0 < 1 - c by linarith) (by linarith); linarith
  have := exp_chord 0 (Real.log (1 - c)) F (Ne.symm hL) hF0 hF1
  rw [show (1 - F) * 0 + F * Real.log (1 - c) = F * Real.log (1 - c) by ring, Real.exp_zero,
    Real.exp_log (by linarith)] at this
  nlinarith

theorem telescope (g : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.Ioc 1 n, (g j - g (j - 1)) = g n - g 1 := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Ioc_succ_top hk, ih]
    simp

end RRAux_MultiPriceOnline_Ratios_proposition_2

open MultiPriceOnline.Ratios in
open RRAux_MultiPriceOnline_Ratios_proposition_2 in
theorem solution (m : ℕ) (hm : 2 ≤ m) (r : ℕ → ℝ) (hr : MultiPriceOnline.Balance.IsPriceSet m r)
    (α : ℕ → ℝ) (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) (σ : ℕ → ℝ) (hσ : MultiPriceOnline.Balance.IsBQLimits m r σ) :
    ((1 - Real.exp (-1)) * σ 1 < 1 - Real.exp (-σ 1) ∧
      1 - Real.exp (-σ 1) < 1 - Real.exp (-α 1)) ∧
    1 / (1 + Real.log (r m / r 1)) < σ 1 ∧
    ∀ a : ℝ, 1 - Real.exp (-a) = (1 - a) / Real.log (r m / r 1) →
      1 - Real.exp (-a) < 1 - Real.exp (-α 1) := by
  obtain ⟨hr1, hrinc⟩ := hr
  obtain ⟨hαpos, hαsum, hα7⟩ := hα
  obtain ⟨hσpos, hσsum, hσ8⟩ := hσ
  have hm1 : 1 ≤ m := by omega
  have hrpos : ∀ j, 1 ≤ j → j ≤ m → 0 < r j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; exact hr1
    | succ k hk ih =>
      intro hkm
      have := hrinc k hk (by omega)
      have := ih (by omega)
      linarith
  have hmem : ∀ j ∈ Finset.Ioc 1 m, 2 ≤ j ∧ j ≤ m := by
    intro j hj; rw [Finset.mem_Ioc] at hj; omega
  have hlt : ∀ j, 2 ≤ j → j ≤ m → r (j - 1) < r j := by
    intro j h2 hj
    have := hrinc (j - 1) (by omega) (by omega)
    rwa [show j - 1 + 1 = j by omega] at this
  -- c_j
  have hc : ∀ j, 2 ≤ j → j ≤ m → 0 < 1 - r (j - 1) / r j ∧ 1 - r (j - 1) / r j < 1 := by
    intro j h2 hj
    have hp := hrpos j (by omega) hj
    have hp' := hrpos (j - 1) (by omega) (by omega)
    have := hlt j h2 hj
    constructor
    · have : r (j - 1) / r j < 1 := (div_lt_one hp).mpr this
      linarith
    · have : 0 < r (j - 1) / r j := div_pos hp' hp
      linarith
  have hσj : ∀ j, 2 ≤ j → j ≤ m → σ j = σ 1 * (1 - r (j - 1) / r j) := by
    intro j h2 hj
    have := hσ8 j h2 hj
    have hne := (hc j h2 hj).1.ne'
    rw [this]; field_simp
  have hαj : ∀ j, 2 ≤ j → j ≤ m →
      Real.exp (-α j) = 1 - (1 - Real.exp (-α 1)) * (1 - r (j - 1) / r j) := by
    intro j h2 hj
    have := hα7 j h2 hj
    have hne := (hc j h2 hj).1.ne'
    rw [this]; field_simp; ring
  have hσs : σ 1 + ∑ j ∈ Finset.Ioc 1 m, σ j = 1 := by
    rw [Finset.add_sum_Ioc_eq_sum_Icc hm1]; exact hσsum
  have hαs : α 1 + ∑ j ∈ Finset.Ioc 1 m, α j = 1 := by
    rw [Finset.add_sum_Ioc_eq_sum_Icc hm1]; exact hαsum
  have hne : (Finset.Ioc 1 m).Nonempty := ⟨2, Finset.mem_Ioc.mpr ⟨by norm_num, hm⟩⟩
  have hσ1 : 0 < σ 1 := hσpos 1 le_rfl hm1
  have hα1 : 0 < α 1 := hαpos 1 le_rfl hm1
  have hσlt : σ 1 < 1 := by
    have : 0 < ∑ j ∈ Finset.Ioc 1 m, σ j :=
      Finset.sum_pos (fun j hj => hσpos j (by have := hmem j hj; omega) (hmem j hj).2) hne
    linarith
  have hαlt : α 1 < 1 := by
    have : 0 < ∑ j ∈ Finset.Ioc 1 m, α j :=
      Finset.sum_pos (fun j hj => hαpos j (by have := hmem j hj; omega) (hmem j hj).2) hne
    linarith
  -- (ii)
  have hσα : σ 1 < α 1 := by
    by_contra hcon
    push Not at hcon
    have hFG : 1 - Real.exp (-α 1) ≤ 1 - Real.exp (-σ 1) := by
      have := Real.exp_le_exp.mpr (show -σ 1 ≤ -α 1 by linarith); linarith
    have hlt' : ∀ j ∈ Finset.Ioc 1 m, α j < σ j := by
      intro j hj
      obtain ⟨h2, hjm⟩ := hmem j hj
      obtain ⟨c0, c1⟩ := hc j h2 hjm
      have e1 := hαj j h2 hjm
      have e2 := ineq_ii (σ 1) _ hσ1 c0 c1
      have : 1 - (1 - Real.exp (-σ 1)) * (1 - r (j - 1) / r j) ≤
          1 - (1 - Real.exp (-α 1)) * (1 - r (j - 1) / r j) := by nlinarith
      have : Real.exp (-(σ 1 * (1 - r (j - 1) / r j))) < Real.exp (-α j) := by linarith
      rw [Real.exp_lt_exp] at this
      rw [hσj j h2 hjm]; linarith
    have := Finset.sum_lt_sum_of_nonempty hne hlt'
    linarith
  -- logs
  have hrm := hrpos m hm1 le_rfl
  have hlogR : Real.log (r m / r 1) = ∑ j ∈ Finset.Ioc 1 m,
      (Real.log (r j) - Real.log (r (j - 1))) := by
    rw [telescope (fun j => Real.log (r j)) m hm1, Real.log_div hrm.ne' hr1.ne']
  have hlogj : ∀ j ∈ Finset.Ioc 1 m, Real.log (r j) - Real.log (r (j - 1)) =
      -Real.log (1 - (1 - r (j - 1) / r j)) := by
    intro j hj
    obtain ⟨h2, hjm⟩ := hmem j hj
    have hp := hrpos j (by omega) hjm
    have hp' := hrpos (j - 1) (by omega) (by omega)
    rw [sub_sub_cancel, Real.log_div hp'.ne' hp.ne']; ring
  have hcsum : ∑ j ∈ Finset.Ioc 1 m, (1 - r (j - 1) / r j) < Real.log (r m / r 1) := by
    rw [hlogR]
    refine Finset.sum_lt_sum_of_nonempty hne fun j hj => ?_
    rw [hlogj j hj]
    obtain ⟨h2, hjm⟩ := hmem j hj
    obtain ⟨c0, c1⟩ := hc j h2 hjm
    have := Real.log_lt_sub_one_of_pos (show 0 < 1 - (1 - r (j - 1) / r j) by linarith)
      (by linarith)
    linarith
  have hσc : σ 1 * (1 + ∑ j ∈ Finset.Ioc 1 m, (1 - r (j - 1) / r j)) = 1 := by
    have := (Finset.sum_congr rfl fun j hj => hσj j (hmem j hj).1 (hmem j hj).2)
    rw [mul_add, mul_one, Finset.mul_sum, ← this]
    exact hσs
  have hcpos : 0 < ∑ j ∈ Finset.Ioc 1 m, (1 - r (j - 1) / r j) :=
    Finset.sum_pos (fun j hj => (hc j (hmem j hj).1 (hmem j hj).2).1) hne
  have hlogpos : 0 < Real.log (r m / r 1) := by linarith
  refine ⟨⟨ineq_i (σ 1) hσ1 hσlt, ?_⟩, ?_, ?_⟩
  · have := Real.exp_lt_exp.mpr (show -α 1 < -σ 1 by linarith); linarith
  · rw [div_lt_iff₀ (by linarith)]
    nlinarith
  · intro a ha
    set F := 1 - Real.exp (-α 1) with hF
    have hF0 : 0 < F := by
      have := Real.exp_lt_one_iff.mpr (show -α 1 < 0 by linarith); linarith
    have hF1 : F < 1 := by have := Real.exp_pos (-α 1); linarith
    have hsumα : ∑ j ∈ Finset.Ioc 1 m, α j < F * Real.log (r m / r 1) := by
      rw [hlogR, Finset.mul_sum]
      refine Finset.sum_lt_sum_of_nonempty hne fun j hj => ?_
      rw [hlogj j hj]
      obtain ⟨h2, hjm⟩ := hmem j hj
      obtain ⟨c0, c1⟩ := hc j h2 hjm
      have e1 := hαj j h2 hjm
      have e2 := ineq_iv F _ hF0 hF1 c0 c1
      have : Real.exp (F * Real.log (1 - (1 - r (j - 1) / r j))) < Real.exp (-α j) := by
        linarith
      rw [Real.exp_lt_exp] at this
      linarith
    have ha' : (1 - Real.exp (-a)) * Real.log (r m / r 1) = 1 - a := by
      rw [ha]; field_simp
    by_contra hcon
    push Not at hcon
    have hge : α 1 ≤ a := by
      by_contra h'
      push Not at h'
      have := Real.exp_lt_exp.mpr (show -α 1 < -a by linarith)
      linarith
    have : F * Real.log (r m / r 1) ≤ (1 - Real.exp (-a)) * Real.log (r m / r 1) :=
      mul_le_mul_of_nonneg_right hcon hlogpos.le
    linarith

#print axioms solution
