-- Prove2me | solution 1 for LocalLemmaHierarchy.Completeness.lemma_F_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:21:51.774977+00:00
-- url     : https://prove2.me/submissions/871e5c7b-4f3f-4f8c-9f07-19fb45613e22

import Mathlib
import Definitions.Def_LocalLemmaHierarchy_Completeness_Weights

section
set_option autoImplicit false

namespace LocalLemmaHierarchy.Completeness.Dev.F3

open Finset LocalLemmaHierarchy.Completeness

noncomputable def th (q : ℕ) : ℝ := Real.pi / ((q : ℝ) + 1)

noncomputable def u (q j : ℕ) : ℝ := Real.sin ((j : ℝ) * th q)

noncomputable def vv (q : ℕ) (w : ℕ → ℝ) (i : ℕ) : ℝ := Real.sqrt (extWeights q w i)

noncomputable def pic (q : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ i ∈ range (q + 1), (vv q w i * u q (i + 1) - vv q w (i + 1) * u q i) ^ 2 /
    (u q i * u q (i + 1))

theorem th_pos (q : ℕ) : 0 < th q := by unfold th; positivity

theorem u_zero (q : ℕ) : u q 0 = 0 := by simp [u]

theorem u_last (q : ℕ) : u q (q + 1) = 0 := by
  unfold u th
  have : ((q + 1 : ℕ) : ℝ) * (Real.pi / ((q : ℝ) + 1)) = Real.pi := by
    push_cast; field_simp
  rw [this, Real.sin_pi]

theorem u_nonneg (q j : ℕ) (hj : j ≤ q + 1) : 0 ≤ u q j := by
  unfold u
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · have := th_pos q; positivity
  · have h : ((j : ℕ) : ℝ) ≤ (q : ℝ) + 1 := by exact_mod_cast hj
    calc (j : ℝ) * th q ≤ ((q : ℝ) + 1) * th q := by
          exact mul_le_mul_of_nonneg_right h (th_pos q).le
      _ = Real.pi := by unfold th; field_simp

theorem u_pos (q j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ q) : 0 < u q j := by
  unfold u
  apply Real.sin_pos_of_pos_of_lt_pi
  · have := th_pos q
    have : (1 : ℝ) ≤ j := by exact_mod_cast h1
    positivity
  · have h : ((j : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast h2
    calc (j : ℝ) * th q ≤ (q : ℝ) * th q := mul_le_mul_of_nonneg_right h (th_pos q).le
      _ < ((q : ℝ) + 1) * th q := by nlinarith [th_pos q]
      _ = Real.pi := by unfold th; field_simp

theorem u_rec (q k : ℕ) :
    u q (k + 2) + u q k = 2 * Real.cos (th q) * u q (k + 1) := by
  unfold u
  have h1 : ((k + 2 : ℕ) : ℝ) * th q = ((k + 1 : ℕ) : ℝ) * th q + th q := by push_cast; ring
  have h2 : ((k : ℕ) : ℝ) * th q = ((k + 1 : ℕ) : ℝ) * th q - th q := by push_cast; ring
  rw [h1, h2, Real.sin_add, Real.sin_sub]; ring

theorem cos_sum (q n : ℕ) :
    2 * Real.sin (th q) * ∑ j ∈ range n, Real.cos (2 * (j : ℝ) * th q) =
      Real.sin ((2 * (n : ℝ) - 1) * th q) + Real.sin (th q) := by
  induction n with
  | zero => simp [Real.sin_neg]
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h1 : (2 * ((n + 1 : ℕ) : ℝ) - 1) * th q = 2 * (n : ℝ) * th q + th q := by
      push_cast; ring
    have h2 : (2 * (n : ℝ) - 1) * th q = 2 * (n : ℝ) * th q - th q := by ring
    rw [h1, h2, Real.sin_add, Real.sin_sub]; ring

theorem sum_sq (q : ℕ) (hq : 1 ≤ q) : ∑ j ∈ Icc 1 q, u q j ^ 2 = ((q : ℝ) + 1) / 2 := by
  have hs : 0 < Real.sin (th q) := by
    apply Real.sin_pos_of_pos_of_lt_pi (th_pos q)
    unfold th
    rw [div_lt_iff₀ (by positivity)]
    have : (1:ℝ) ≤ q := by exact_mod_cast hq
    nlinarith [Real.pi_pos]
  have hc : ∑ j ∈ range (q + 1), Real.cos (2 * (j : ℝ) * th q) = 0 := by
    have h := cos_sum q (q + 1)
    have : Real.sin ((2 * ((q + 1 : ℕ) : ℝ) - 1) * th q) = - Real.sin (th q) := by
      have : (2 * ((q + 1 : ℕ) : ℝ) - 1) * th q = 2 * Real.pi - th q := by
        unfold th; push_cast; field_simp
      rw [this, Real.sin_two_pi_sub]
    rw [this] at h
    have : 2 * Real.sin (th q) * ∑ j ∈ range (q + 1), Real.cos (2 * (j : ℝ) * th q) = 0 := by
      linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact h
  have hIcc : Icc 1 q = Ico 1 (q + 1) := by ext; simp
  have e : ∀ j ∈ range (q + 1), u q j ^ 2 = 1 / 2 - 1 / 2 * Real.cos (2 * (j : ℝ) * th q) := by
    intro j _
    unfold u
    rw [show 2 * (j : ℝ) * th q = 2 * ((j : ℝ) * th q) by ring, Real.cos_two_mul]
    have := Real.sin_sq_add_cos_sq ((j : ℝ) * th q)
    linarith
  have h0 : ∑ j ∈ range (q + 1), u q j ^ 2 = ((q : ℝ) + 1) / 2 := by
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.mul_sum, hc]
    simp; ring
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)] at h0
  rw [hIcc]
  simpa [u_zero] using h0

theorem energy_eq (q : ℕ) (hq : 1 ≤ q) (w : ℕ → ℝ) (hw : ∀ j ∈ Icc 1 q, 0 ≤ w j) :
    dirichletEnergy q w = dq q * ∑ j ∈ Icc 1 q, w j + pic q w := by
  have hv0 : vv q w 0 = 0 := by simp [vv, extWeights]
  have hvq : vv q w (q + 1) = 0 := by simp [vv, extWeights]
  have hd : dq q = 2 - 2 * Real.cos (th q) := by unfold dq th; ring
  have hsq : ∀ j ∈ Icc 1 q, vv q w j ^ 2 = w j := by
    intro j hj
    have h := mem_Icc.mp hj
    unfold vv extWeights
    rw [if_pos h, Real.sq_sqrt (hw j hj)]
  -- per-edge identity
  let B : ℕ → ℝ := fun j => vv q w j ^ 2 * (1 - u q (j + 1) / u q j)
  let C : ℕ → ℝ := fun j => vv q w j ^ 2 * (1 - u q (j - 1) / u q j)
  have edge : ∀ i ∈ range (q + 1),
      (vv q w (i + 1) - vv q w i) ^ 2 =
        (vv q w i * u q (i + 1) - vv q w (i + 1) * u q i) ^ 2 / (u q i * u q (i + 1))
          + (B i + C (i + 1)) := by
    intro i hi
    have hi' : i ≤ q := by simpa [Nat.lt_succ_iff] using hi
    simp only [B, C, Nat.add_sub_cancel]
    by_cases h0 : i = 0
    · subst h0
      simp [hv0, u_zero]
    by_cases h1 : i = q
    · subst h1
      simp [hvq, u_last]
    have p1 := u_pos q i (by omega) hi'
    have p2 := u_pos q (i + 1) (by omega) (by omega)
    field_simp
    ring
  have inner : ∀ j ∈ range (q + 2), B j + C j = dq q * vv q w j ^ 2 := by
    intro j hj
    have hj' : j < q + 2 := mem_range.mp hj
    by_cases h0 : j = 0
    · subst h0; simp [B, C, hv0]
    by_cases h1 : j = q + 1
    · subst h1; simp [B, C, hvq]
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have p := u_pos q (k + 1) (by omega) (by omega)
    have r := u_rec q k
    simp only [B, C, Nat.add_sub_cancel, hd]
    field_simp
    linear_combination (-(vv q w (k + 1)) ^ 2) * r
  have hsum1 : ∑ i ∈ range (q + 1), (B i + C (i + 1)) = dq q * ∑ j ∈ Icc 1 q, w j := by
    rw [Finset.sum_add_distrib]
    have a1 := Finset.sum_range_succ B (q + 1)
    have a2 := Finset.sum_range_succ' C (q + 1)
    have hB : B (q + 1) = 0 := by simp [B, hvq]
    have hC : C 0 = 0 := by simp [C, hv0]
    have a3 : ∑ j ∈ range (q + 2), (B j + C j) = ∑ j ∈ range (q + 2), dq q * vv q w j ^ 2 :=
      Finset.sum_congr rfl inner
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at a3
    have hIcc : Icc 1 q = Ico 1 (q + 1) := by ext; simp
    have a4 : ∑ j ∈ range (q + 2), vv q w j ^ 2 = ∑ j ∈ Icc 1 q, vv q w j ^ 2 := by
      rw [Finset.sum_range_succ, hvq, hIcc, Finset.range_eq_Ico,
        Finset.sum_eq_sum_Ico_succ_bot (by omega), hv0]
      simp
    rw [a4, Finset.sum_congr rfl hsq] at a3
    rw [hB] at a1
    rw [hC] at a2
    linarith
  unfold dirichletEnergy pic
  have : ∀ i ∈ range (q + 1),
      (Real.sqrt (extWeights q w (i + 1)) - Real.sqrt (extWeights q w i)) ^ 2 =
      (vv q w i * u q (i + 1) - vv q w (i + 1) * u q i) ^ 2 / (u q i * u q (i + 1))
          + (B i + C (i + 1)) := edge
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, hsum1, add_comm]

theorem pic_nonneg (q : ℕ) (w : ℕ → ℝ) : 0 ≤ pic q w := by
  unfold pic
  apply Finset.sum_nonneg
  intro i hi
  have hi' : i ≤ q := by simpa [Nat.lt_succ_iff] using mem_range.mp hi
  exact div_nonneg (sq_nonneg _) (mul_nonneg (u_nonneg q i (by omega))
    (u_nonneg q (i + 1) (by omega)))

theorem sineWeight_eq (q j : ℕ) : sineWeight q j = 2 / ((q : ℝ) + 1) * u q j ^ 2 := by
  simp [sineWeight, u, th]

theorem sine_pos (q j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ q) : 0 < sineWeight q j := by
  rw [sineWeight_eq]
  have := u_pos q j h1 h2
  positivity

theorem sine_sum (q : ℕ) (hq : 1 ≤ q) : ∑ j ∈ Icc 1 q, sineWeight q j = 1 := by
  simp_rw [sineWeight_eq]
  rw [← Finset.mul_sum, sum_sq q hq]
  field_simp

theorem sine_energy (q : ℕ) (hq : 1 ≤ q) : dirichletEnergy q (sineWeight q) = dq q := by
  have hw : ∀ j ∈ Icc 1 q, 0 ≤ sineWeight q j := fun j hj =>
    (sine_pos q j (mem_Icc.mp hj).1 (mem_Icc.mp hj).2).le
  rw [energy_eq q hq _ hw, sine_sum q hq]
  have : pic q (sineWeight q) = 0 := by
    unfold pic
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : i ≤ q := by simpa [Nat.lt_succ_iff] using mem_range.mp hi
    have hv : ∀ j, j ≤ q + 1 → vv q (sineWeight q) j =
        Real.sqrt (2 / ((q : ℝ) + 1)) * u q j := by
      intro j hj
      have : extWeights q (sineWeight q) j = sineWeight q j := by
        unfold extWeights
        split_ifs with h
        · rfl
        · have : j = 0 ∨ j = q + 1 := by omega
          rcases this with rfl | rfl
          · simp [sineWeight_eq, u_zero]
          · simp [sineWeight_eq, u_last]
      unfold vv
      rw [this, sineWeight_eq, Real.sqrt_mul (by positivity), Real.sqrt_sq (u_nonneg q j hj)]
    rw [hv i (by omega), hv (i + 1) (by omega)]
    have : Real.sqrt (2 / ((q : ℝ) + 1)) * u q i * u q (i + 1) -
        Real.sqrt (2 / ((q : ℝ) + 1)) * u q (i + 1) * u q i = 0 := by ring
    rw [this]; simp
  rw [this]; ring

theorem lower (q : ℕ) (hq : 1 ≤ q) (w : ℕ → ℝ) (hw : ∀ j ∈ Icc 1 q, 0 ≤ w j)
    (h1 : ∑ j ∈ Icc 1 q, w j = 1) : dq q ≤ dirichletEnergy q w := by
  rw [energy_eq q hq w hw, h1]
  linarith [pic_nonneg q w]

theorem unique (q : ℕ) (hq : 1 ≤ q) (w : ℕ → ℝ) (hw : ∀ j ∈ Icc 1 q, 0 ≤ w j)
    (h1 : ∑ j ∈ Icc 1 q, w j = 1) (hE : dirichletEnergy q w = dq q) :
    ∀ j ∈ Icc 1 q, w j = sineWeight q j := by
  have hp : pic q w = 0 := by
    have := energy_eq q hq w hw
    rw [h1, hE] at this
    linarith
  have hsq : ∀ j ∈ Icc 1 q, vv q w j ^ 2 = w j := by
    intro j hj
    have h := mem_Icc.mp hj
    unfold vv extWeights
    rw [if_pos h, Real.sq_sqrt (hw j hj)]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => by
    have hi' : i ≤ q := by simpa [Nat.lt_succ_iff] using mem_range.mp hi
    exact div_nonneg (sq_nonneg _) (mul_nonneg (u_nonneg q i (by omega))
      (u_nonneg q (i + 1) (by omega))))).mp hp
  have step : ∀ i, 1 ≤ i → i + 1 ≤ q →
      vv q w i * u q (i + 1) = vv q w (i + 1) * u q i := by
    intro i hi1 hi2
    have := hz i (mem_range.mpr (by omega))
    have p1 := u_pos q i hi1 (by omega)
    have p2 := u_pos q (i + 1) (by omega) hi2
    rw [div_eq_zero_iff] at this
    rcases this with h | h
    · have := pow_eq_zero_iff (two_ne_zero) |>.mp h
      linarith
    · exact absurd h (mul_pos p1 p2).ne'
  have prop : ∀ j, 1 ≤ j → j ≤ q → vv q w j * u q 1 = vv q w 1 * u q j := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro _; rfl
    | succ j hj ih =>
      intro hjq
      have ih := ih (by omega)
      have s := step j hj hjq
      have p := u_pos q j hj (by omega)
      apply mul_right_cancel₀ p.ne'
      calc vv q w (j + 1) * u q 1 * u q j = (vv q w (j + 1) * u q j) * u q 1 := by ring
        _ = (vv q w j * u q (j + 1)) * u q 1 := by rw [s]
        _ = (vv q w j * u q 1) * u q (j + 1) := by ring
        _ = vv q w 1 * u q j * u q (j + 1) := by rw [ih]
        _ = vv q w 1 * u q (j + 1) * u q j := by ring
  have u1 := u_pos q 1 le_rfl hq
  set c := vv q w 1 / u q 1 with hc
  have hvc : ∀ j ∈ Icc 1 q, w j = c ^ 2 * u q j ^ 2 := by
    intro j hj
    have h := mem_Icc.mp hj
    have := prop j h.1 h.2
    have : vv q w j = c * u q j := by
      rw [hc]; field_simp; linarith
    rw [← hsq j hj, this]; ring
  have hsum : c ^ 2 * (((q : ℝ) + 1) / 2) = 1 := by
    rw [← sum_sq q hq, Finset.mul_sum, ← h1]
    exact (Finset.sum_congr rfl fun j hj => (hvc j hj).symm)
  intro j hj
  rw [hvc j hj, sineWeight_eq]
  have : c ^ 2 = 2 / ((q : ℝ) + 1) := by
    field_simp; field_simp at hsum; linarith
  rw [this]

end LocalLemmaHierarchy.Completeness.Dev.F3

namespace LocalLemmaHierarchy.Completeness

open Dev.F3 Finset

theorem chk_lemma_F_3 (q : ℕ) (hq : 1 ≤ q) :
    IsLeast {E : ℝ | ∃ w : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 ≤ w j) ∧
        ∑ j ∈ Finset.Icc 1 q, w j = 1 ∧ dirichletEnergy q w = E} (dq q) ∧
    (∀ w : ℕ → ℝ, (∀ j ∈ Finset.Icc 1 q, 0 ≤ w j) → ∑ j ∈ Finset.Icc 1 q, w j = 1 →
      dirichletEnergy q w = dq q → ∀ j ∈ Finset.Icc 1 q, w j = sineWeight q j) ∧
    dirichletEnergy q (sineWeight q) = dq q ∧
    (∀ j ∈ Finset.Icc 1 q, 0 < sineWeight q j) ∧
    ∑ j ∈ Finset.Icc 1 q, sineWeight q j = 1 := by
  refine ⟨⟨⟨sineWeight q, fun j hj => (sine_pos q j (mem_Icc.mp hj).1 (mem_Icc.mp hj).2).le,
    sine_sum q hq, sine_energy q hq⟩, ?_⟩, unique q hq, sine_energy q hq,
    fun j hj => sine_pos q j (mem_Icc.mp hj).1 (mem_Icc.mp hj).2, sine_sum q hq⟩
  rintro E ⟨w, hw, h1, rfl⟩
  exact lower q hq w hw h1

end LocalLemmaHierarchy.Completeness
end

theorem solution : type_of% @LocalLemmaHierarchy.Completeness.chk_lemma_F_3 := @LocalLemmaHierarchy.Completeness.chk_lemma_F_3
