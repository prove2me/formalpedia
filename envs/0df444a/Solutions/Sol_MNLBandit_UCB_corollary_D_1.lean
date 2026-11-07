-- Prove2me | solution 1 for MNLBandit.UCB.corollary_D_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T01:15:34.674757+00:00
-- url     : https://prove2.me/submissions/3eed62d3-3b0a-4912-9266-8b37ebcd6b0f

import Mathlib
import Theorems.Thm_MNLBandit_UCB_theorem_5

open MeasureTheory ProbabilityTheory

namespace MNLCorD1Aux

/-- Upper tail, from part 1 of Theorem 5 with `δ = t / μ`. -/
lemma upper (n : ℕ) (hn : 1 ≤ n) (p : unitInterval) (hp : p ≠ 0) (L t : ℝ) (hL : 1 / 4 ≤ L)
    (ht : 0 < t) (hμ0 : 0 < (1 - (p : ℝ)) / (p : ℝ)) (hμ1 : (1 - (p : ℝ)) / (p : ℝ) ≤ 1)
    (hc : 16 * (L - 1 / 4) * ((1 - (p : ℝ)) / (p : ℝ) + t) ≤ (n : ℝ) * t ^ 2) :
    Measure.pi (fun _ : Fin n => geometricMeasure p)
        {x | (∑ k, (x k : ℝ)) / (n : ℝ) > (1 - (p : ℝ)) / (p : ℝ) + t} ≤
      ENNReal.ofReal (Real.exp (1 / 2 - 2 * L)) := by
  set μ : ℝ := (1 - (p : ℝ)) / (p : ℝ) with hμdef
  set δ : ℝ := t / μ with hδdef
  have hδ : 0 < δ := div_pos ht hμ0
  have hδμ : δ * μ = t := by rw [hδdef]; field_simp
  obtain ⟨h1, -, -, -⟩ := MNLBandit.UCB.theorem_5 n hn p hp δ hδ
  have h1' := h1 hμ1
  have hset : {x : Fin n → ℕ | (∑ k, (x k : ℝ)) / (n : ℝ) > μ + t} =
      {x : Fin n → ℕ | (∑ k, (x k : ℝ)) / (n : ℝ) > (1 + δ) * μ} := by
    ext x; simp only [Set.mem_setOf_eq]; rw [add_mul, one_mul, hδμ]
  rw [hset]
  refine h1'.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD : 0 < 2 * (1 + δ) * (1 + μ) ^ 2 := by positivity
  rw [div_le_iff₀ hD]
  -- goal: (1/2 - 2L) * D ≤ -(n μ δ²)... rearranged
  have hμ2 : (1 + μ) ^ 2 ≤ 4 := by nlinarith
  have hK : 0 ≤ 2 * L - 1 / 2 := by linarith
  -- (2L - 1/2) * 2 (1+δ)(1+μ)^2 ≤ (2L-1/2) * 8 (1+δ)
  have e1 : (2 * L - 1 / 2) * (2 * (1 + δ) * (1 + μ) ^ 2) ≤ (2 * L - 1 / 2) * (8 * (1 + δ)) := by
    apply mul_le_mul_of_nonneg_left _ hK; nlinarith
  -- (2L - 1/2) * 8 (1+δ) * μ = 16 (L - 1/4) (μ + t) ≤ n t^2 = n μ δ^2 * μ
  have e2 : (2 * L - 1 / 2) * (8 * (1 + δ)) * μ ≤ (n : ℝ) * μ * δ ^ 2 * μ := by
    have : (2 * L - 1 / 2) * (8 * (1 + δ)) * μ = 16 * (L - 1 / 4) * (μ + t) := by
      rw [← hδμ]; ring
    have h2 : (n : ℝ) * μ * δ ^ 2 * μ = (n : ℝ) * t ^ 2 := by rw [← hδμ]; ring
    rw [this, h2]; exact hc
  have e3 : (2 * L - 1 / 2) * (8 * (1 + δ)) ≤ (n : ℝ) * μ * δ ^ 2 :=
    le_of_mul_le_mul_right e2 hμ0
  nlinarith

/-- Lower tail, from part 3 of Theorem 5 with `δ = t / μ`. -/
lemma lower (n : ℕ) (hn : 1 ≤ n) (p : unitInterval) (hp : p ≠ 0) (L t : ℝ) (hL : 1 / 4 ≤ L)
    (ht : 0 < t) (hμ0 : 0 < (1 - (p : ℝ)) / (p : ℝ)) (hμ1 : (1 - (p : ℝ)) / (p : ℝ) ≤ 1)
    (hc : 24 * (L - 1 / 4) * ((1 - (p : ℝ)) / (p : ℝ)) ≤ (n : ℝ) * t ^ 2) :
    Measure.pi (fun _ : Fin n => geometricMeasure p)
        {x | (∑ k, (x k : ℝ)) / (n : ℝ) < (1 - (p : ℝ)) / (p : ℝ) - t} ≤
      ENNReal.ofReal (Real.exp (1 / 2 - 2 * L)) := by
  set μ : ℝ := (1 - (p : ℝ)) / (p : ℝ) with hμdef
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases htμ : μ ≤ t
  · have : {x : Fin n → ℕ | (∑ k, (x k : ℝ)) / (n : ℝ) < μ - t} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have : 0 ≤ (∑ k, (x k : ℝ)) / (n : ℝ) := by positivity
      linarith
    rw [this, measure_empty]; exact bot_le
  push_neg at htμ
  set δ : ℝ := t / μ with hδdef
  have hδ : 0 < δ := div_pos ht hμ0
  have hδμ : δ * μ = t := by rw [hδdef]; field_simp
  obtain ⟨-, -, h3, -⟩ := MNLBandit.UCB.theorem_5 n hn p hp δ hδ
  have h3' := h3 hμ1
  have hset : {x : Fin n → ℕ | (∑ k, (x k : ℝ)) / (n : ℝ) < μ - t} =
      {x : Fin n → ℕ | (∑ k, (x k : ℝ)) / (n : ℝ) < (1 - δ) * μ} := by
    ext x; simp only [Set.mem_setOf_eq]; rw [sub_mul, one_mul, hδμ]
  rw [hset]
  refine h3'.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_))
  have hμ2 : (1 + μ) ^ 2 ≤ 4 := by nlinarith
  have hB : 2 ≤ 3 - 2 * δ * μ / (1 + μ) := by
    rw [mul_assoc, hδμ]
    have : t / (1 + μ) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have : 2 * t / (1 + μ) = 2 * (t / (1 + μ)) := by ring
    linarith
  have hA0 : 0 ≤ (n : ℝ) * δ ^ 2 * μ := by positivity
  have hA : (n : ℝ) * δ ^ 2 * μ / 24 ≤ (n : ℝ) * δ ^ 2 * μ / (6 * (1 + μ) ^ 2) := by
    apply div_le_div_of_nonneg_left hA0 (by positivity); linarith
  have hkey : 24 * (L - 1 / 4) ≤ (n : ℝ) * δ ^ 2 * μ := by
    have h2 : (n : ℝ) * δ ^ 2 * μ * μ = (n : ℝ) * t ^ 2 := by rw [← hδμ]; ring
    have : 24 * (L - 1 / 4) * μ ≤ (n : ℝ) * δ ^ 2 * μ * μ := by rw [h2]; exact hc
    exact le_of_mul_le_mul_right this hμ0
  have hA1 : 0 ≤ (n : ℝ) * δ ^ 2 * μ / (6 * (1 + μ) ^ 2) := by positivity
  nlinarith

lemma exp_bound (N ℓ : ℕ) (hN : 1 ≤ N) (hℓ : 1 ≤ ℓ) :
    Real.exp (1 / 2 - 2 * Real.log (Real.sqrt N * ℓ + 1)) ≤ 2 / (N * ℓ ^ 2) := by
  have hpos : 0 < Real.sqrt N * ℓ + 1 := by positivity
  rw [sub_eq_add_neg, Real.exp_add, ← Real.log_rpow hpos, Real.exp_neg,
    Real.exp_log (by positivity)]
  have he : Real.exp (1 / 2) ≤ 2 := by
    have h := Real.exp_one_lt_d9
    have : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hsq : (Real.sqrt N) ^ 2 = N := Real.sq_sqrt (by positivity)
  have hr : (Real.sqrt N * ℓ + 1) ^ (2 : ℝ) = (Real.sqrt N * ℓ + 1) ^ 2 := by
    exact_mod_cast Real.rpow_natCast _ 2
  rw [hr]
  have hge : (N : ℝ) * ℓ ^ 2 ≤ (Real.sqrt N * ℓ + 1) ^ 2 := by
    have : (N : ℝ) * ℓ ^ 2 = (Real.sqrt N * ℓ) ^ 2 := by rw [mul_pow, hsq]
    rw [this]; nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have hNl : 0 < (N : ℝ) * ℓ ^ 2 := by positivity
  rw [mul_inv_le_iff₀ (by positivity), div_mul_eq_mul_div, le_div_iff₀ hNl]
  nlinarith [Real.exp_pos (1 / 2)]

end MNLCorD1Aux

namespace MNLCorD1Aux

lemma null_case (n : ℕ) (p : unitInterval) (hp1 : (p : ℝ) = 1) :
    Measure.pi (fun _ : Fin n => geometricMeasure p)
      {x | (∑ k, (x k : ℝ)) / (n : ℝ) ≠ 0} = 0 := by
  have hp : p ≠ 0 := by
    intro h; rw [h] at hp1; simp at hp1
  have hk : ∀ k : Fin n, Measure.pi (fun _ : Fin n => geometricMeasure p)
      (Function.eval k ⁻¹' ({0}ᶜ : Set ℕ)) = 0 := by
    intro k
    apply Measure.pi_eval_preimage_null
    rw [prob_compl_eq_zero_iff (measurableSet_singleton 0), geometricMeasure_singleton hp,
      hp1]
    simp
  apply measure_mono_null _ (measure_iUnion_null hk)
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  simp only [Set.mem_iUnion, Set.mem_preimage, Function.eval, Set.mem_compl_iff,
    Set.mem_singleton_iff]
  by_contra hall
  push_neg at hall
  apply hx
  simp [hall]

end MNLCorD1Aux

namespace MNLCorD1Aux

lemma main (n : ℕ) (hn : 1 ≤ n) (N ℓ : ℕ) (hN : 1 ≤ N) (hℓ : 1 ≤ ℓ)
    (p : unitInterval) (hp : p ≠ 0) (hμ1 : (1 - (p : ℝ)) / (p : ℝ) ≤ 1) :
    Measure.pi (fun _ : Fin n => geometricMeasure p)
        {x | |(∑ k, (x k : ℝ)) / (n : ℝ) - (1 - (p : ℝ)) / (p : ℝ)| >
          Real.sqrt (48 * ((∑ k, (x k : ℝ)) / (n : ℝ)) * Real.log (Real.sqrt N * ℓ + 1) / n) +
            48 * Real.log (Real.sqrt N * ℓ + 1) / n} ≤
          ENNReal.ofReal (6 / (N * ℓ ^ 2)) ∧
    Measure.pi (fun _ : Fin n => geometricMeasure p)
        {x | |(∑ k, (x k : ℝ)) / (n : ℝ) - (1 - (p : ℝ)) / (p : ℝ)| ≥
          Real.sqrt (24 * ((1 - (p : ℝ)) / (p : ℝ)) * Real.log (Real.sqrt N * ℓ + 1) / n) +
            48 * Real.log (Real.sqrt N * ℓ + 1) / n} ≤
          ENNReal.ofReal (4 / (N * ℓ ^ 2)) ∧
    Measure.pi (fun _ : Fin n => geometricMeasure p)
        {x | (∑ k, (x k : ℝ)) / (n : ℝ) ≥ 3 * ((1 - (p : ℝ)) / (p : ℝ)) / 2 +
          48 * Real.log (Real.sqrt N * ℓ + 1) / n} ≤
          ENNReal.ofReal (3 / (N * ℓ ^ 2)) := by
  set μ : ℝ := (1 - (p : ℝ)) / (p : ℝ) with hμdef
  set L : ℝ := Real.log (Real.sqrt N * ℓ + 1) with hLdef
  set P : Measure (Fin n → ℕ) := Measure.pi (fun _ : Fin n => geometricMeasure p) with hPdef
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hℓ' : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hL : 0.69 < L := by
    have h2 : (2 : ℝ) ≤ Real.sqrt N * ℓ + 1 := by
      have : (1 : ℝ) ≤ Real.sqrt N := by rw [Real.one_le_sqrt]; exact hN'
      nlinarith
    have := Real.log_le_log (by norm_num) h2
    have := Real.log_two_gt_d9
    linarith
  have hL4 : 1 / 4 ≤ L := by linarith
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  have hμ0 : 0 ≤ μ := div_nonneg (by linarith) hp0
  have hNl : (0 : ℝ) < N * ℓ ^ 2 := by positivity
  have hE : ENNReal.ofReal (Real.exp (1 / 2 - 2 * L)) ≤ ENNReal.ofReal (2 / (N * ℓ ^ 2)) :=
    ENNReal.ofReal_le_ofReal (exp_bound N ℓ hN hℓ)
  have h22 : ENNReal.ofReal (2 / (N * ℓ ^ 2)) + ENNReal.ofReal (2 / (N * ℓ ^ 2)) =
      ENNReal.ofReal (4 / (N * ℓ ^ 2)) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  have h42 : ENNReal.ofReal (4 / (N * ℓ ^ 2)) + ENNReal.ofReal (2 / (N * ℓ ^ 2)) =
      ENNReal.ofReal (6 / (N * ℓ ^ 2)) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  have hXnn : ∀ x : Fin n → ℕ, 0 ≤ (∑ k, (x k : ℝ)) / (n : ℝ) := fun x => by positivity
  have hLn : 0 < 48 * L / n := by positivity
  -- the degenerate case `μ = 0`
  rcases hμ0.lt_or_eq with hμpos | hμz
  swap
  · have hp1' : (p : ℝ) = 1 := by
      have hpp : (0 : ℝ) < p := lt_of_le_of_ne hp0 (fun h => hp (Subtype.ext h.symm))
      have : 1 - (p : ℝ) = 0 := by
        have := hμz.symm; rw [hμdef, div_eq_zero_iff] at this
        rcases this with h | h
        · exact h
        · exact absurd h hpp.ne'
      linarith
    have hnull := null_case n p hp1'
    rw [← hμz]
    refine ⟨?_, ?_, ?_⟩
    · refine le_trans (le_of_eq (measure_mono_null ?_ hnull)) bot_le
      intro x hx; simp only [Set.mem_setOf_eq] at hx ⊢
      intro h0; rw [h0] at hx; simp at hx
      have : 0 ≤ Real.sqrt (48 * 0 * L / n) := Real.sqrt_nonneg _
      linarith
    · refine le_trans (le_of_eq (measure_mono_null ?_ hnull)) bot_le
      intro x hx; simp only [Set.mem_setOf_eq] at hx ⊢
      intro h0; rw [h0] at hx; simp at hx
      linarith
    · refine le_trans (le_of_eq (measure_mono_null ?_ hnull)) bot_le
      intro x hx; simp only [Set.mem_setOf_eq] at hx ⊢
      intro h0; rw [h0] at hx; simp at hx
      linarith
  -- main case `μ > 0`
  set s : ℝ := 48 * L - 1 with hsdef
  have hs : 0 < s := by linarith
  set u : ℝ := s / n with hudef
  have hu : 0 < u := div_pos hs hnpos
  have hnu : (n : ℝ) * u = s := by rw [hudef]; field_simp
  have hu48 : u < 48 * L / n := by
    rw [hudef]; apply div_lt_div_of_pos_right _ hnpos; linarith
  -- Part 2
  have part2 : P {x | |(∑ k, (x k : ℝ)) / (n : ℝ) - μ| ≥
      Real.sqrt (24 * μ * L / n) + 48 * L / n} ≤ ENNReal.ofReal (4 / (N * ℓ ^ 2)) := by
    set w : ℝ := Real.sqrt (24 * μ * L / n) with hwdef
    have hw0 : 0 ≤ w := Real.sqrt_nonneg _
    have hw2 : (n : ℝ) * w ^ 2 = 24 * μ * L := by
      rw [hwdef, Real.sq_sqrt (by positivity)]; field_simp
    set t : ℝ := w + u with htdef
    have ht : 0 < t := by linarith
    have hsub : {x : Fin n → ℕ | |(∑ k, (x k : ℝ)) / (n : ℝ) - μ| ≥ w + 48 * L / n} ⊆
        {x | (∑ k, (x k : ℝ)) / (n : ℝ) > μ + t} ∪ {x | (∑ k, (x k : ℝ)) / (n : ℝ) < μ - t} := by
      intro x hx
      simp only [Set.mem_setOf_eq, Set.mem_union] at hx ⊢
      rcases le_or_gt 0 ((∑ k, (x k : ℝ)) / (n : ℝ) - μ) with h | h
      · rw [abs_of_nonneg h] at hx; left; linarith
      · rw [abs_of_neg h] at hx; right; linarith
    have hntt : (n : ℝ) * t ^ 2 = 24 * μ * L + 2 * w * s + s * u := by
      have : (n : ℝ) * t ^ 2 = (n : ℝ) * w ^ 2 + 2 * w * ((n : ℝ) * u) + ((n : ℝ) * u) * u := by
        rw [htdef]; ring
      rw [this, hw2, hnu]
    have hcU : 16 * (L - 1 / 4) * (μ + t) ≤ (n : ℝ) * t ^ 2 := by
      rw [hntt, htdef]
      nlinarith [mul_nonneg hw0 (by linarith : (0:ℝ) ≤ 2 * s - 16 * (L - 1/4)),
        mul_nonneg hu.le (by linarith : (0:ℝ) ≤ s - 16 * (L - 1/4)),
        mul_nonneg hμ0 (by linarith : (0:ℝ) ≤ 24 * L - 16 * (L - 1/4))]
    have hcL : 24 * (L - 1 / 4) * μ ≤ (n : ℝ) * t ^ 2 := by
      rw [hntt]
      nlinarith [mul_nonneg hw0 hs.le, mul_nonneg hs.le hu.le]
    calc P _ ≤ P ({x | (∑ k, (x k : ℝ)) / (n : ℝ) > μ + t} ∪
            {x | (∑ k, (x k : ℝ)) / (n : ℝ) < μ - t}) := measure_mono hsub
      _ ≤ P {x | (∑ k, (x k : ℝ)) / (n : ℝ) > μ + t} +
            P {x | (∑ k, (x k : ℝ)) / (n : ℝ) < μ - t} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (2 / (N * ℓ ^ 2)) + ENNReal.ofReal (2 / (N * ℓ ^ 2)) :=
          add_le_add ((upper n hn p hp L t hL4 ht hμpos hμ1 hcU).trans hE)
            ((lower n hn p hp L t hL4 ht hμpos hμ1 hcL).trans hE)
      _ = _ := h22
  refine ⟨?_, part2, ?_⟩
  · -- Part 1
    by_cases hcase : 96 * (L - 1 / 4) ≤ (n : ℝ) * μ
    · have hsub : {x : Fin n → ℕ | |(∑ k, (x k : ℝ)) / (n : ℝ) - μ| >
          Real.sqrt (48 * ((∑ k, (x k : ℝ)) / (n : ℝ)) * L / n) + 48 * L / n} ⊆
          {x | |(∑ k, (x k : ℝ)) / (n : ℝ) - μ| ≥ Real.sqrt (24 * μ * L / n) + 48 * L / n} ∪
          {x | (∑ k, (x k : ℝ)) / (n : ℝ) < μ - μ / 2} := by
        intro x hx
        simp only [Set.mem_setOf_eq, Set.mem_union] at hx ⊢
        rcases le_or_gt (μ / 2) ((∑ k, (x k : ℝ)) / (n : ℝ)) with h | h
        · left
          have : Real.sqrt (24 * μ * L / n) ≤
              Real.sqrt (48 * ((∑ k, (x k : ℝ)) / (n : ℝ)) * L / n) := by
            apply Real.sqrt_le_sqrt
            apply div_le_div_of_nonneg_right _ hnpos.le
            nlinarith
          linarith
        · right; linarith
      have hcL : 24 * (L - 1 / 4) * μ ≤ (n : ℝ) * (μ / 2) ^ 2 := by nlinarith
      calc P _ ≤ P ({x | |(∑ k, (x k : ℝ)) / (n : ℝ) - μ| ≥
              Real.sqrt (24 * μ * L / n) + 48 * L / n} ∪
              {x | (∑ k, (x k : ℝ)) / (n : ℝ) < μ - μ / 2}) := measure_mono hsub
        _ ≤ P {x | |(∑ k, (x k : ℝ)) / (n : ℝ) - μ| ≥
              Real.sqrt (24 * μ * L / n) + 48 * L / n} +
              P {x | (∑ k, (x k : ℝ)) / (n : ℝ) < μ - μ / 2} := measure_union_le _ _
        _ ≤ ENNReal.ofReal (4 / (N * ℓ ^ 2)) + ENNReal.ofReal (2 / (N * ℓ ^ 2)) :=
            add_le_add part2
              ((lower n hn p hp L (μ / 2) hL4 (by linarith) hμpos hμ1 hcL).trans hE)
        _ = _ := h42
    · push_neg at hcase
      have hsub : {x : Fin n → ℕ | |(∑ k, (x k : ℝ)) / (n : ℝ) - μ| >
          Real.sqrt (48 * ((∑ k, (x k : ℝ)) / (n : ℝ)) * L / n) + 48 * L / n} ⊆
          {x | (∑ k, (x k : ℝ)) / (n : ℝ) > μ + u} ∪
          {x | (∑ k, (x k : ℝ)) / (n : ℝ) < μ - u} := by
        intro x hx
        simp only [Set.mem_setOf_eq, Set.mem_union] at hx ⊢
        have hsq := Real.sqrt_nonneg (48 * ((∑ k, (x k : ℝ)) / (n : ℝ)) * L / n)
        rcases le_or_gt 0 ((∑ k, (x k : ℝ)) / (n : ℝ) - μ) with h | h
        · rw [abs_of_nonneg h] at hx; left; linarith
        · rw [abs_of_neg h] at hx; right; linarith
      have hss : 16 * (L - 1 / 4) * ((n : ℝ) * μ + s) ≤ s * s := by
        rw [hsdef]; nlinarith
      have hcU : 16 * (L - 1 / 4) * (μ + u) ≤ (n : ℝ) * u ^ 2 := by
        have h1 : (n : ℝ) * (16 * (L - 1 / 4) * (μ + u)) ≤ (n : ℝ) * ((n : ℝ) * u ^ 2) := by
          have e1 : (n : ℝ) * (16 * (L - 1 / 4) * (μ + u)) =
              16 * (L - 1 / 4) * ((n : ℝ) * μ + (n : ℝ) * u) := by ring
          have e2 : (n : ℝ) * ((n : ℝ) * u ^ 2) = ((n : ℝ) * u) * ((n : ℝ) * u) := by ring
          rw [e1, e2, hnu]; exact hss
        exact le_of_mul_le_mul_left h1 hnpos
      have hcL : 24 * (L - 1 / 4) * μ ≤ (n : ℝ) * u ^ 2 := by
        have h1 : (n : ℝ) * (24 * (L - 1 / 4) * μ) ≤ (n : ℝ) * ((n : ℝ) * u ^ 2) := by
          have e1 : (n : ℝ) * (24 * (L - 1 / 4) * μ) = 24 * (L - 1 / 4) * ((n : ℝ) * μ) := by ring
          have e2 : (n : ℝ) * ((n : ℝ) * u ^ 2) = ((n : ℝ) * u) * ((n : ℝ) * u) := by ring
          rw [e1, e2, hnu, hsdef]
          nlinarith
        exact le_of_mul_le_mul_left h1 hnpos
      calc P _ ≤ P ({x | (∑ k, (x k : ℝ)) / (n : ℝ) > μ + u} ∪
              {x | (∑ k, (x k : ℝ)) / (n : ℝ) < μ - u}) := measure_mono hsub
        _ ≤ P {x | (∑ k, (x k : ℝ)) / (n : ℝ) > μ + u} +
              P {x | (∑ k, (x k : ℝ)) / (n : ℝ) < μ - u} := measure_union_le _ _
        _ ≤ ENNReal.ofReal (2 / (N * ℓ ^ 2)) + ENNReal.ofReal (2 / (N * ℓ ^ 2)) :=
            add_le_add ((upper n hn p hp L u hL4 hu hμpos hμ1 hcU).trans hE)
              ((lower n hn p hp L u hL4 hu hμpos hμ1 hcL).trans hE)
        _ = ENNReal.ofReal (4 / (N * ℓ ^ 2)) := h22
        _ ≤ _ := ENNReal.ofReal_le_ofReal (by
            apply div_le_div_of_nonneg_right _ hNl.le; norm_num)
  · -- Part 3
    set t : ℝ := μ / 2 + u with htdef
    have ht : 0 < t := by positivity
    have hsub : {x : Fin n → ℕ | (∑ k, (x k : ℝ)) / (n : ℝ) ≥ 3 * μ / 2 + 48 * L / n} ⊆
        {x | (∑ k, (x k : ℝ)) / (n : ℝ) > μ + t} := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      linarith
    have hcU : 16 * (L - 1 / 4) * (μ + t) ≤ (n : ℝ) * t ^ 2 := by
      have hnt : (n : ℝ) * t = (n : ℝ) * μ / 2 + s := by rw [htdef, mul_add, hnu]; ring
      have h1 : s * t ≤ (n : ℝ) * t ^ 2 := by
        have : (n : ℝ) * t ^ 2 = ((n : ℝ) * t) * t := by ring
        rw [this, hnt]; nlinarith [mul_nonneg hnpos.le hμ0]
      have h2 : μ + t ≤ 3 * t := by rw [htdef]; linarith
      have h3 : 16 * (L - 1 / 4) * (μ + t) ≤ 16 * (L - 1 / 4) * (3 * t) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
      have h4 : 16 * (L - 1 / 4) * (3 * t) = s * t - 11 * t := by rw [hsdef]; ring
      linarith
    calc P _ ≤ P {x | (∑ k, (x k : ℝ)) / (n : ℝ) > μ + t} := measure_mono hsub
      _ ≤ ENNReal.ofReal (2 / (N * ℓ ^ 2)) := (upper n hn p hp L t hL4 ht hμpos hμ1 hcU).trans hE
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by
            apply div_le_div_of_nonneg_right _ hNl.le; norm_num)

end MNLCorD1Aux

theorem solution (n : ℕ) (hn : 1 ≤ n) (N ℓ : ℕ) (hN : 1 ≤ N) (hℓ : 1 ≤ ℓ)
    (p : unitInterval) (hp : p ≠ 0) :
    let μ : ℝ := (1 - (p : ℝ)) / (p : ℝ)
    let P : Measure (Fin n → ℕ) := Measure.pi (fun _ : Fin n => geometricMeasure p)
    let Xbar : (Fin n → ℕ) → ℝ := fun x => (∑ k, (x k : ℝ)) / (n : ℝ)
    let lg : ℝ := Real.log (Real.sqrt N * ℓ + 1)
    μ ≤ 1 →
      P {x | |Xbar x - μ| > Real.sqrt (48 * Xbar x * lg / n) + 48 * lg / n} ≤
          ENNReal.ofReal (6 / (N * ℓ ^ 2)) ∧
      P {x | |Xbar x - μ| ≥ Real.sqrt (24 * μ * lg / n) + 48 * lg / n} ≤
          ENNReal.ofReal (4 / (N * ℓ ^ 2)) ∧
      P {x | Xbar x ≥ 3 * μ / 2 + 48 * lg / n} ≤ ENNReal.ofReal (3 / (N * ℓ ^ 2)) := by
  intro μ P Xbar lg hμ1
  exact MNLCorD1Aux.main n hn N ℓ hN hℓ p hp hμ1
