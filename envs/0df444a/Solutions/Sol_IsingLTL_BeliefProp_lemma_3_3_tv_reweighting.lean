-- Prove2me | solution 1 for IsingLTL.BeliefProp.lemma_3_3_tv_reweighting
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T20:35:30.355582+00:00
-- url     : https://prove2.me/submissions/3e24e89a-9241-4ea1-9c13-0ac5016e88fb

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist

namespace Aux_IsingLTL_BeliefProp_lemma_3_3_tv_reweighting

open IsingLTL.BeliefProp IsingLTL.FreeEntropy

lemma diff_le {X : Type*} [Fintype X] (f : X → ℝ) (fmax : ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ fmax) (ν ν' : X → ℝ)
    (hν : IsDistribution ν) (hν' : IsDistribution ν') :
    pairing ν f - pairing ν' f ≤ fmax / 2 * ∑ x, |ν x - ν' x| := by
  unfold pairing
  have h0 : ∑ x, (ν x - ν' x) = 0 := by
    rw [Finset.sum_sub_distrib, hν.2, hν'.2, sub_self]
  have e : ∑ x, f x * ν x - ∑ x, f x * ν' x = ∑ x, (f x - fmax / 2) * (ν x - ν' x) := by
    have : ∑ x, (f x - fmax / 2) * (ν x - ν' x) =
        ∑ x, f x * (ν x - ν' x) - fmax / 2 * ∑ x, (ν x - ν' x) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro x _; ring
    rw [this, h0, mul_zero, sub_zero, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro x _; ring
  rw [e, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have h1 : |f x - fmax / 2| ≤ fmax / 2 := by
    rw [abs_le]; constructor <;> linarith [(hf x).1, (hf x).2]
  calc (f x - fmax / 2) * (ν x - ν' x) ≤ |(f x - fmax / 2) * (ν x - ν' x)| := le_abs_self _
    _ = |f x - fmax / 2| * |ν x - ν' x| := abs_mul _ _
    _ ≤ fmax / 2 * |ν x - ν' x| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

lemma main {X : Type*} [Fintype X] (f : X → ℝ) (fmax : ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ fmax) (ν ν' : X → ℝ)
    (hν : IsDistribution ν) (hν' : IsDistribution ν')
    (hZ : 0 < pairing ν f) (hZ' : 0 < pairing ν' f) (hZZ : pairing ν' f ≤ pairing ν f) :
    ∑ x, |ν x * f x / pairing ν f - ν' x * f x / pairing ν' f| ≤
      3 * fmax / pairing ν f * tvDist ν ν' := by
  set Z := pairing ν f with hZdef
  set Z' := pairing ν' f with hZ'def
  set D := ∑ x, |ν x - ν' x| with hD
  have hpt : ∀ x, |ν x * f x / Z - ν' x * f x / Z'| ≤
      fmax * |ν x - ν' x| / Z + ν' x * f x * (1 / Z' - 1 / Z) := by
    intro x
    have hb : 0 ≤ ν' x * f x := mul_nonneg (hν'.1 x) (hf x).1
    have hinv : 0 ≤ 1 / Z' - 1 / Z := by
      rw [sub_nonneg]; exact one_div_le_one_div_of_le hZ' hZZ
    have e : ν x * f x / Z - ν' x * f x / Z' =
        (ν x - ν' x) * f x / Z - ν' x * f x * (1 / Z' - 1 / Z) := by
      field_simp
      ring
    rw [e]
    calc |(ν x - ν' x) * f x / Z - ν' x * f x * (1 / Z' - 1 / Z)|
        ≤ |(ν x - ν' x) * f x / Z| + |ν' x * f x * (1 / Z' - 1 / Z)| := abs_sub _ _
      _ = |ν x - ν' x| * f x / Z + ν' x * f x * (1 / Z' - 1 / Z) := by
          rw [abs_div, abs_mul, abs_of_nonneg (hf x).1, abs_of_pos hZ,
            abs_of_nonneg (mul_nonneg hb hinv)]
      _ ≤ fmax * |ν x - ν' x| / Z + ν' x * f x * (1 / Z' - 1 / Z) := by
          have : |ν x - ν' x| * f x ≤ fmax * |ν x - ν' x| := by
            rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hf x).2 (abs_nonneg _)
          have := div_le_div_of_nonneg_right this hZ.le
          linarith
  have hsum2 : ∑ x, ν' x * f x = Z' := by
    rw [hZ'def]; unfold pairing; apply Finset.sum_congr rfl; intro x _; ring
  have hdiff := diff_le f fmax hf ν ν' hν hν'
  calc ∑ x, |ν x * f x / Z - ν' x * f x / Z'|
      ≤ ∑ x, (fmax * |ν x - ν' x| / Z + ν' x * f x * (1 / Z' - 1 / Z)) :=
        Finset.sum_le_sum (fun x _ => hpt x)
    _ = fmax * D / Z + (Z - Z') / Z := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, ← Finset.sum_mul, hsum2,
          ← hD]
        field_simp
    _ ≤ fmax * D / Z + (fmax / 2 * D) / Z := by
        have := div_le_div_of_nonneg_right hdiff hZ.le
        linarith
    _ = 3 * fmax / Z * tvDist ν ν' := by
        unfold tvDist
        rw [← hD]
        field_simp
        ring

end Aux_IsingLTL_BeliefProp_lemma_3_3_tv_reweighting

open Aux_IsingLTL_BeliefProp_lemma_3_3_tv_reweighting in
open IsingLTL.BeliefProp in
theorem solution {X : Type*} [Fintype X] (f : X → ℝ) (fmax : ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ fmax) (ν ν' : X → ℝ)
    (hν : IsDistribution ν) (hν' : IsDistribution ν')
    (hνf : ∃ x, 0 < ν x ∧ 0 < f x) (hν'f : ∃ x, 0 < ν' x ∧ 0 < f x) :
    ∑ x, |ν x * f x / IsingLTL.FreeEntropy.pairing ν f - ν' x * f x / IsingLTL.FreeEntropy.pairing ν' f| ≤
        3 * fmax / max (IsingLTL.FreeEntropy.pairing ν f) (IsingLTL.FreeEntropy.pairing ν' f) * tvDist ν ν' ∧
      ∀ fmin : ℝ, 0 < fmin → (∀ x, fmin ≤ f x) →
        3 * fmax / max (IsingLTL.FreeEntropy.pairing ν f) (IsingLTL.FreeEntropy.pairing ν' f) * tvDist ν ν' ≤
          3 * fmax / fmin * tvDist ν ν' := by
  have hpos : ∀ μ : X → ℝ, IsDistribution μ → (∃ x, 0 < μ x ∧ 0 < f x) →
      0 < IsingLTL.FreeEntropy.pairing μ f := by
    rintro μ hμ ⟨x0, h1, h2⟩
    unfold IsingLTL.FreeEntropy.pairing
    calc 0 < f x0 * μ x0 := mul_pos h2 h1
      _ ≤ ∑ x, f x * μ x :=
        Finset.single_le_sum (f := fun x => f x * μ x)
          (fun x _ => mul_nonneg (hf x).1 (hμ.1 x)) (Finset.mem_univ x0)
  have hZ := hpos ν hν hνf
  have hZ' := hpos ν' hν' hν'f
  have htv0 : 0 ≤ tvDist ν ν' := by
    unfold tvDist; positivity
  have hfmax : 0 ≤ fmax := by
    obtain ⟨x0, _, _⟩ := hνf
    exact (hf x0).1.trans (hf x0).2
  constructor
  · rcases le_total (IsingLTL.FreeEntropy.pairing ν' f) (IsingLTL.FreeEntropy.pairing ν f) with h | h
    · rw [max_eq_left h]
      exact main f fmax hf ν ν' hν hν' hZ hZ' h
    · rw [max_eq_right h]
      have hsym := main f fmax hf ν' ν hν' hν hZ' hZ h
      have e1 : ∑ x, |ν x * f x / IsingLTL.FreeEntropy.pairing ν f -
          ν' x * f x / IsingLTL.FreeEntropy.pairing ν' f| =
          ∑ x, |ν' x * f x / IsingLTL.FreeEntropy.pairing ν' f -
            ν x * f x / IsingLTL.FreeEntropy.pairing ν f| := by
        apply Finset.sum_congr rfl; intro x _; exact abs_sub_comm _ _
      have e2 : tvDist ν ν' = tvDist ν' ν := by
        unfold tvDist
        congr 1
        apply Finset.sum_congr rfl; intro x _; exact abs_sub_comm _ _
      rw [e1, e2]
      exact hsym
  · intro fmin hfmin hfx
    have hZmin : fmin ≤ IsingLTL.FreeEntropy.pairing ν f := by
      unfold IsingLTL.FreeEntropy.pairing
      calc fmin = ∑ x, fmin * ν x := by rw [← Finset.mul_sum, hν.2, mul_one]
        _ ≤ ∑ x, f x * ν x :=
          Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_right (hfx x) (hν.1 x))
    have hmax : fmin ≤ max (IsingLTL.FreeEntropy.pairing ν f) (IsingLTL.FreeEntropy.pairing ν' f) :=
      hZmin.trans (le_max_left _ _)
    apply mul_le_mul_of_nonneg_right _ htv0
    exact div_le_div_of_nonneg_left (by linarith) hfmin hmax
