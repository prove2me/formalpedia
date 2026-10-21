-- Prove2me | solution 1 for MultiPriceOnline.Ratios.eq_34
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:50:31.063554+00:00
-- url     : https://prove2.me/submissions/7dd31261-21d4-4c3c-a850-cae50f5fb8e1

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


lemma tele (m : ℕ) (r : ℕ → ℝ) (hr : IsPriceSet m r) : ∀ k, 1 ≤ k → k ≤ m →
    ∑ j ∈ Icc 2 k, Real.log (r j / r (j - 1)) = Real.log (r k) - Real.log (r 1) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => intro _; simp
  | succ k hk ih =>
    intro hkm
    rw [Finset.sum_Icc_succ_top (by omega), ih (by omega)]
    have h1 := price_pos m r hr (k + 1) (by omega) hkm
    have h2 := price_pos m r hr k hk (by omega)
    rw [Real.log_div h1.ne' (by simpa using h2.ne')]
    simp

end MPOAux

open MPOAux in
theorem solution (m : ℕ) (hm : 2 ≤ m) (r : ℕ → ℝ) (hr : MultiPriceOnline.Balance.IsPriceSet m r) :
    (∀ a : ℝ, 1 - Real.exp (-a) = (1 - a) / Real.log (r m / r 1) ↔
      a + ∑ j ∈ Icc 2 m, (1 - Real.exp (-a)) * Real.log (r j / r (j - 1)) = 1) ∧
    (∃! a : ℝ, a + ∑ j ∈ Icc 2 m, (1 - Real.exp (-a)) * Real.log (r j / r (j - 1)) = 1) ∧
    ∀ a : ℝ, a + ∑ j ∈ Icc 2 m, (1 - Real.exp (-a)) * Real.log (r j / r (j - 1)) = 1 →
      0 < a ∧ a < 1 := by
  set L : ℝ := Real.log (r m / r 1) with hLdef
  have hLsum : ∑ j ∈ Icc 2 m, Real.log (r j / r (j - 1)) = L := by
    rw [tele m r hr m (by omega) le_rfl, hLdef,
      Real.log_div (price_pos m r hr m (by omega) le_rfl).ne'
        (price_pos m r hr 1 le_rfl (by omega)).ne']
  have hLpos : 0 < L := by
    rw [← hLsum]
    refine Finset.sum_pos (fun j hj => ?_) ⟨2, Finset.mem_Icc.2 ⟨le_rfl, hm⟩⟩
    rw [Finset.mem_Icc] at hj
    have h1 := hr.2 (j - 1) (by omega) (by omega)
    have e : j - 1 + 1 = j := by omega
    rw [e] at h1
    have h2 := price_pos m r hr (j - 1) (by omega) (by omega)
    exact Real.log_pos ((one_lt_div h2).2 h1)
  have hψ : ∀ a : ℝ, a + ∑ j ∈ Icc 2 m, (1 - Real.exp (-a)) * Real.log (r j / r (j - 1))
      = a + (1 - Real.exp (-a)) * L := by
    intro a
    rw [← Finset.mul_sum, hLsum]
  set g : ℝ → ℝ := fun a => a + (1 - Real.exp (-a)) * L with hg
  have hgm : StrictMono g := by
    intro x y hxy
    have : Real.exp (-y) < Real.exp (-x) := Real.exp_lt_exp.2 (by linarith)
    simp only [hg]
    nlinarith
  have hgc : Continuous g := by simp only [hg]; fun_prop
  have hg0 : g 0 = 0 := by simp [hg]
  have hg1 : 1 < g 1 := by
    have : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    simp only [hg]
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rw [hψ, eq_div_iff hLpos.ne']
    constructor <;> intro h <;> linarith
  · have h := intermediate_value_Icc (zero_le_one' ℝ) hgc.continuousOn
    have h1 : (1 : ℝ) ∈ Set.Icc (g 0) (g 1) := by rw [hg0]; exact ⟨zero_le_one, hg1.le⟩
    obtain ⟨a, _, hpa⟩ := h h1
    refine ⟨a, ?_, ?_⟩
    · show a + ∑ j ∈ Icc 2 m, (1 - Real.exp (-a)) * Real.log (r j / r (j - 1)) = 1
      rw [hψ]; exact hpa
    · intro b hb
      rw [hψ] at hb
      exact hgm.injective (hb.trans hpa.symm)
  · intro a ha
    rw [hψ] at ha
    have ha' : g a = 1 := ha
    refine ⟨?_, ?_⟩
    · by_contra hneg
      push_neg at hneg
      have := hgm.monotone hneg
      linarith
    · by_contra hneg
      push_neg at hneg
      have := hgm.monotone hneg
      linarith
