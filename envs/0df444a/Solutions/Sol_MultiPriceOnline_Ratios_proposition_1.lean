-- Prove2me | solution 1 for MultiPriceOnline.Ratios.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:46:06.574956+00:00
-- url     : https://prove2.me/submissions/a460feaf-db99-4b78-91e8-6289274910fb

import Mathlib
import Definitions.Def_MultiPriceOnline_Ratios_Setting

set_option autoImplicit false
open Finset

namespace MPOAux
open MultiPriceOnline.Balance

lemma price_pos (m : ℕ) (r : ℕ → ℝ) (hr : IsPriceSet m r) : ∀ j, 1 ≤ j → j ≤ m → 0 < r j := by
  obtain ⟨hr1, hrm⟩ := hr
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => intro _; exact hr1
  | succ k hk ih =>
    intro hkm
    have := hrm k hk (by omega)
    linarith [ih (by omega)]

lemma c_pos (m : ℕ) (r : ℕ → ℝ) (hr : IsPriceSet m r) (j : ℕ) (hj : 2 ≤ j) (hjm : j ≤ m) :
    0 < 1 - r (j - 1) / r j := by
  have h1 := hr.2 (j - 1) (by omega) (by omega)
  have e : j - 1 + 1 = j := by omega
  rw [e] at h1
  have h2 := price_pos m r hr j (by omega) hjm
  rw [sub_pos, div_lt_one h2]
  exact h1

lemma c_lt_one (m : ℕ) (r : ℕ → ℝ) (hr : IsPriceSet m r) (j : ℕ) (hj : 2 ≤ j) (hjm : j ≤ m) :
    1 - r (j - 1) / r j < 1 := by
  have h1 := price_pos m r hr (j - 1) (by omega) (by omega)
  have h2 := price_pos m r hr j (by omega) hjm
  have : 0 < r (j - 1) / r j := by positivity
  linarith

lemma hsplit (m : ℕ) (hm : 1 ≤ m) (f : ℕ → ℝ) :
    ∑ j ∈ Icc 1 m, f j = f 1 + ∑ j ∈ Icc 2 m, f j := by
  have : Icc 1 m = insert 1 (Icc 2 m) := by ext x; simp; omega
  rw [this, Finset.sum_insert (by simp)]

lemma arg_pos (x c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    0 < 1 - (1 - Real.exp (-x)) * c := by
  have : 1 - (1 - Real.exp (-x)) * c = (1 - c) + Real.exp (-x) * c := by ring
  rw [this]
  exact add_pos (sub_pos.2 hc1) (mul_pos (Real.exp_pos _) hc0)

noncomputable def phi (m : ℕ) (r : ℕ → ℝ) (x : ℝ) : ℝ :=
  x + ∑ j ∈ Icc 2 m, -Real.log (1 - (1 - Real.exp (-x)) * (1 - r (j - 1) / r j))

lemma phi_strictMono (m : ℕ) (r : ℕ → ℝ) (hr : IsPriceSet m r) : StrictMono (phi m r) := by
  intro x y hxy
  unfold phi
  refine add_lt_add_of_lt_of_le hxy (Finset.sum_le_sum fun j hj => ?_)
  rw [Finset.mem_Icc] at hj
  have hc0 := c_pos m r hr j hj.1 hj.2
  have hc1 := c_lt_one m r hr j hj.1 hj.2
  have hy := arg_pos y _ hc0 hc1
  have hle : 1 - (1 - Real.exp (-y)) * (1 - r (j - 1) / r j)
      ≤ 1 - (1 - Real.exp (-x)) * (1 - r (j - 1) / r j) := by
    have : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.2 (by linarith)
    nlinarith
  have := Real.log_le_log hy hle
  linarith

lemma phi_continuous (m : ℕ) (r : ℕ → ℝ) (hr : IsPriceSet m r) : Continuous (phi m r) := by
  unfold phi
  refine continuous_id.add (continuous_finsetSum _ fun j hj => ?_)
  rw [Finset.mem_Icc] at hj
  have hc0 := c_pos m r hr j hj.1 hj.2
  have hc1 := c_lt_one m r hr j hj.1 hj.2
  refine Continuous.neg (Continuous.log (by fun_prop) fun t => (arg_pos t _ hc0 hc1).ne')

lemma phi_zero (m : ℕ) (r : ℕ → ℝ) : phi m r 0 = 0 := by
  unfold phi
  simp

lemma phi_one_ge (m : ℕ) (r : ℕ → ℝ) (hr : IsPriceSet m r) : 1 ≤ phi m r 1 := by
  unfold phi
  have : 0 ≤ ∑ j ∈ Icc 2 m, -Real.log (1 - (1 - Real.exp (-1)) * (1 - r (j - 1) / r j)) := by
    refine Finset.sum_nonneg fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    have hc0 := c_pos m r hr j hj.1 hj.2
    have hc1 := c_lt_one m r hr j hj.1 hj.2
    have hp := arg_pos 1 _ hc0 hc1
    have he : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
    have : 1 - (1 - Real.exp (-1)) * (1 - r (j - 1) / r j) ≤ 1 := by nlinarith
    have := Real.log_nonpos hp.le this
    linarith
  linarith

lemma exists_root (m : ℕ) (r : ℕ → ℝ) (hr : IsPriceSet m r) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ phi m r a = 1 := by
  have h := intermediate_value_Icc (zero_le_one' ℝ) (phi_continuous m r hr).continuousOn
  have h1 : (1 : ℝ) ∈ Set.Icc (phi m r 0) (phi m r 1) := by
    rw [phi_zero]; exact ⟨zero_le_one, phi_one_ge m r hr⟩
  obtain ⟨a, ⟨ha0, ha1⟩, hpa⟩ := h h1
  refine ⟨a, ?_, ha1, hpa⟩
  rcases eq_or_lt_of_le ha0 with h0 | h0
  · subst h0; rw [phi_zero] at hpa; norm_num at hpa
  · exact h0

lemma booking_eq (m : ℕ) (hm : 1 ≤ m) (r α : ℕ → ℝ) (hr : IsPriceSet m r)
    (hα : IsBookingLimits m r α) :
    (∀ j ∈ Icc 2 m, α j = -Real.log (1 - (1 - Real.exp (-α 1)) * (1 - r (j - 1) / r j))) ∧
      phi m r (α 1) = 1 := by
  obtain ⟨hpos, hsum, h7⟩ := hα
  have hj : ∀ j ∈ Icc 2 m, α j = -Real.log (1 - (1 - Real.exp (-α 1)) * (1 - r (j - 1) / r j)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have h := h7 j hj.1 hj.2
    have hc := c_pos m r hr j hj.1 hj.2
    rw [eq_div_iff hc.ne'] at h
    have : 1 - (1 - Real.exp (-α 1)) * (1 - r (j - 1) / r j) = Real.exp (-α j) := by linarith
    rw [this, Real.log_exp]; ring
  refine ⟨hj, ?_⟩
  unfold phi
  rw [← Finset.sum_congr rfl hj]
  have := hsum
  rw [hsplit m hm] at this
  exact this

lemma bq_formula (m : ℕ) (hm : 1 ≤ m) (r σ : ℕ → ℝ) (hr : IsPriceSet m r)
    (hσ : IsBQLimits m r σ) :
    (∀ j ∈ Icc 2 m, σ j = σ 1 * (1 - r (j - 1) / r j)) ∧
      σ 1 * (1 + ∑ j ∈ Icc 2 m, (1 - r (j - 1) / r j)) = 1 := by
  obtain ⟨hσpos, hσsum, hσrel⟩ := hσ
  have hσj : ∀ j ∈ Icc 2 m, σ j = σ 1 * (1 - r (j - 1) / r j) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have h := hσrel j hj.1 hj.2
    have hcj := c_pos m r hr j hj.1 hj.2
    rw [eq_div_iff hcj.ne'] at h
    linarith
  refine ⟨hσj, ?_⟩
  have := hσsum
  rw [hsplit m hm, Finset.sum_congr rfl hσj, ← Finset.mul_sum] at this
  linarith

lemma S_pos (m : ℕ) (r : ℕ → ℝ) (hr : IsPriceSet m r) :
    0 < 1 + ∑ j ∈ Icc 2 m, (1 - r (j - 1) / r j) := by
  have : 0 ≤ ∑ j ∈ Icc 2 m, (1 - r (j - 1) / r j) := Finset.sum_nonneg (fun j hj => by
    rw [Finset.mem_Icc] at hj; exact (c_pos m r hr j hj.1 hj.2).le)
  linarith

end MPOAux

open MPOAux in
theorem solution (m : ℕ) (hm : 1 ≤ m) (r : ℕ → ℝ) (hr : MultiPriceOnline.Balance.IsPriceSet m r) :
    ((∃ α : ℕ → ℝ, MultiPriceOnline.Balance.IsBookingLimits m r α) ∧
      ∀ α α' : ℕ → ℝ, MultiPriceOnline.Balance.IsBookingLimits m r α → MultiPriceOnline.Balance.IsBookingLimits m r α' →
        ∀ j ∈ Icc 1 m, α j = α' j) ∧
    ((∃ σ : ℕ → ℝ, MultiPriceOnline.Balance.IsBQLimits m r σ) ∧
      ∀ σ σ' : ℕ → ℝ, MultiPriceOnline.Balance.IsBQLimits m r σ → MultiPriceOnline.Balance.IsBQLimits m r σ' →
        ∀ j ∈ Icc 1 m, σ j = σ' j) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- existence of booking limits
    obtain ⟨a, ha0, ha1, hpa⟩ := exists_root m r hr
    have hu : 0 < 1 - Real.exp (-a) := by
      have : Real.exp (-a) < 1 := by rw [Real.exp_lt_one_iff]; linarith
      linarith
    obtain ⟨f, hf1, hfj⟩ : ∃ f : ℕ → ℝ, f 1 = a ∧ ∀ j, 2 ≤ j →
        f j = -Real.log (1 - (1 - Real.exp (-a)) * (1 - r (j - 1) / r j)) :=
      ⟨fun j => if j = 1 then a else
        -Real.log (1 - (1 - Real.exp (-a)) * (1 - r (j - 1) / r j)),
        by simp, fun j hj => by simp [show j ≠ 1 by omega]⟩
    refine ⟨f, ?_, ?_, ?_⟩
    · intro j hj1 hjm
      by_cases h1 : j = 1
      · rw [h1, hf1]; exact ha0
      · have hj2 : 2 ≤ j := by omega
        rw [hfj j hj2]
        have hc0 := c_pos m r hr j hj2 hjm
        have hc1 := c_lt_one m r hr j hj2 hjm
        have hA := arg_pos a _ hc0 hc1
        have hAlt : 1 - (1 - Real.exp (-a)) * (1 - r (j - 1) / r j) < 1 := by nlinarith
        have := Real.log_neg hA hAlt
        linarith
    · rw [hsplit m hm, hf1, Finset.sum_congr rfl (fun j hj => hfj j (Finset.mem_Icc.1 hj).1)]
      have h := hpa
      unfold phi at h
      exact h
    · intro j hj2 hjm
      have hc0 := c_pos m r hr j hj2 hjm
      have hc1 := c_lt_one m r hr j hj2 hjm
      have hA := arg_pos a _ hc0 hc1
      rw [hf1, hfj j hj2, neg_neg, Real.exp_log hA, eq_div_iff hc0.ne']
      ring
  · intro α α' hα hα' j hj
    have h1 := booking_eq m hm r α hr hα
    have h2 := booking_eq m hm r α' hr hα'
    have e : α 1 = α' 1 := (phi_strictMono m r hr).injective (h1.2.trans h2.2.symm)
    rw [Finset.mem_Icc] at hj
    by_cases hj1 : j = 1
    · subst hj1; exact e
    · have hj2 : j ∈ Icc 2 m := by rw [Finset.mem_Icc]; omega
      rw [h1.1 j hj2, h2.1 j hj2, e]
  · -- existence of BQ limits
    have hSp := S_pos m r hr
    set S : ℝ := ∑ j ∈ Icc 2 m, (1 - r (j - 1) / r j) with hS
    obtain ⟨f, hf1, hfj⟩ : ∃ f : ℕ → ℝ, f 1 = 1 / (1 + S) ∧ ∀ j, 2 ≤ j →
        f j = (1 - r (j - 1) / r j) / (1 + S) :=
      ⟨fun j => if j = 1 then 1 / (1 + S) else (1 - r (j - 1) / r j) / (1 + S),
        by simp, fun j hj => by simp [show j ≠ 1 by omega]⟩
    refine ⟨f, ?_, ?_, ?_⟩
    · intro j hj1 hjm
      by_cases h1 : j = 1
      · rw [h1, hf1]; positivity
      · rw [hfj j (by omega)]
        have := c_pos m r hr j (by omega) hjm
        positivity
    · rw [hsplit m hm, hf1, Finset.sum_congr rfl (fun j hj => hfj j (Finset.mem_Icc.1 hj).1),
        ← Finset.sum_div, ← hS]
      field_simp
    · intro j hj2 hjm
      have hc0 := c_pos m r hr j hj2 hjm
      rw [hf1, hfj j hj2]
      field_simp
  · intro σ σ' hσ hσ' j hj
    have h1 := bq_formula m hm r σ hr hσ
    have h2 := bq_formula m hm r σ' hr hσ'
    have hSp := S_pos m r hr
    have e : σ 1 = σ' 1 := by
      have := h1.2.trans h2.2.symm
      exact mul_right_cancel₀ hSp.ne' this
    rw [Finset.mem_Icc] at hj
    by_cases hj1 : j = 1
    · subst hj1; exact e
    · have hj2 : j ∈ Icc 2 m := by rw [Finset.mem_Icc]; omega
      rw [h1.1 j hj2, h2.1 j hj2, e]
