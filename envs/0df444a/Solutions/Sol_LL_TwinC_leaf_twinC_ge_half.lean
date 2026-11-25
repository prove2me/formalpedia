-- Prove2me | solution 1 for LL_TwinC.leaf_twinC_ge_half
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T20:29:24.014841+00:00
-- url     : https://prove2.me/submissions/47eb8ae8-6568-49fa-b59d-7b507388f500

import Mathlib
import Definitions.Def_LL_TwinC_twinC

open LL_TwinC

abbrev TwP := {p : ℕ // p.Prime ∧ 2 < p}

lemma tw_one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i, 0 ≤ f i) (h1 : ∀ i, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hS : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg (fun i _ => h0 i)
    have ha0 := h0 a
    have ha1 := h1 a
    nlinarith [mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr ha1), mul_nonneg ha0 hS]

lemma tw_half (p : TwP) : ((p : ℕ) : ℝ) - 1 = 2 * (((p : ℕ) - 1) / 2 : ℕ) := by
  obtain ⟨hp, h2⟩ := p.2
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two (by omega)
  have : ((p : ℕ) - 1) / 2 = m := by omega
  rw [this, hm]; push_cast; ring

lemma tw_inj : Function.Injective (fun p : TwP => ((p : ℕ) - 1) / 2) := by
  intro p q h
  obtain ⟨hp, h2⟩ := p.2
  obtain ⟨hq, h2'⟩ := q.2
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two (by omega)
  obtain ⟨m', hm'⟩ := hq.odd_of_ne_two (by omega)
  apply Subtype.ext
  simp only at h
  omega

lemma tw_term (p : TwP) :
    1 / (((p : ℕ) : ℝ) - 1) ^ 2 = 1 / 4 * (1 / ((((p : ℕ) - 1) / 2 : ℕ) : ℝ) ^ 2) := by
  rw [tw_half p]; ring

lemma tw_sum_le (s : Finset TwP) : ∑ p ∈ s, 1 / (((p : ℕ) : ℝ) - 1) ^ 2 ≤ 1 / 2 := by
  have e : ∑ p ∈ s, 1 / (((p : ℕ) : ℝ) - 1) ^ 2 =
      1 / 4 * ∑ k ∈ s.image (fun p : TwP => ((p : ℕ) - 1) / 2), 1 / ((k : ℕ) : ℝ) ^ 2 := by
    rw [Finset.sum_image (fun x _ y _ hxy => tw_inj hxy), Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p _ => tw_term p)
  rw [e]
  have hle := sum_le_hasSum (s.image (fun p : TwP => ((p : ℕ) - 1) / 2))
    (fun i _ => by positivity) hasSum_zeta_two
  have hpi : Real.pi ^ 2 < 12 := by
    have := Real.pi_lt_d2
    have h0 := Real.pi_pos
    nlinarith
  nlinarith

lemma tw_prod_ge (s : Finset TwP) : 1 / 2 ≤ ∏ p ∈ s, (1 - 1 / (((p : ℕ) : ℝ) - 1) ^ 2) := by
  have h := tw_one_sub_sum_le_prod s (fun p : TwP => 1 / (((p : ℕ) : ℝ) - 1) ^ 2)
    (fun p => by positivity) (fun p => by
      rw [tw_term p]
      have : 1 / ((((p : ℕ) - 1) / 2 : ℕ) : ℝ) ^ 2 ≤ 1 := by
        have hk : (1 : ℝ) ≤ ((((p : ℕ) - 1) / 2 : ℕ) : ℝ) := by
          have := p.2.2
          have : 1 ≤ ((p : ℕ) - 1) / 2 := by omega
          exact_mod_cast this
        rw [div_le_one (by positivity)]
        nlinarith
      linarith)
  have := tw_sum_le s
  linarith

theorem solution : (1 : ℝ) / 2 ≤ twinC := by
  unfold twinC
  by_cases hm : Multipliable (fun p : {p : ℕ // p.Prime ∧ 2 < p} => (1 - 1 / ((p : ℝ) - 1) ^ 2))
  · exact le_hasProd_of_le_prod hm.hasProd (fun s => tw_prod_ge s)
  · rw [tprod_eq_one_of_not_multipliable hm]; norm_num

