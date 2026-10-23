-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.strict_weighted_simplex_card_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:22:12.175763+00:00
-- url     : https://prove2.me/submissions/6e331dab-a1ad-4639-bf81-df424c2732a0

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_simplex_volume_bounds
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators Topology
open Filter

open OAI.PiExponent in
private lemma x8_mem_rws {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (H : ℝ) (a : Fin n → ℕ) :
    a ∈ realWeightedSimplex w H ↔ ∑ i, w i * (a i : ℝ) ≤ H := by
  classical
  unfold realWeightedSimplex
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun i => ?_, h⟩
    have hi : w i * (a i : ℝ) ≤ H :=
      le_trans (Finset.single_le_sum (f := fun j => w j * (a j : ℝ))
        (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)) h
    have h2 : (a i : ℝ) ≤ H / w i := by
      rw [le_div_iff₀ (hw i)]; linarith
    have := Nat.le_floor h2
    omega

/-- `((H + s) / H)^n → 1` as `H → ∞`. -/
private lemma x8_tendsto_real (n : ℕ) (s : ℝ) :
    Tendsto (fun H : ℝ => ((H + s) / H) ^ n) atTop (𝓝 1) := by
  have h1 : Tendsto (fun H : ℝ => (1 + s / H) ^ n) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).add
      ((tendsto_const_nhds (x := s)).div_atTop tendsto_id)
    simpa using this.pow n
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with H hH
  congr 1
  field_simp

theorem solution
    (n : ℕ) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    Tendsto
      (fun H : ℝ => ((OAI.PiExponent.strictWeightedSimplex w H).card : ℝ) / H ^ n)
      atTop
      (𝓝 (1 / ((Nat.factorial n : ℝ) * ∏ i, w i))) := by
  classical
  set D := (Nat.factorial n : ℝ) * ∏ i, w i with hD
  have hD0 : 0 < D := mul_pos (by exact_mod_cast Nat.factorial_pos n)
    (Finset.prod_pos fun i _ => hw i)
  have hlow := (x8_tendsto_real n (-1)).div_const D
  have hup := (x8_tendsto_real n (∑ i, w i)).div_const D
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with H hH
    have hH0 : (0 : ℝ) < H := by linarith
    have hb := (OAI.PiExponent.DeterminantContradiction.weighted_simplex_volume_bounds
      n w (H - 1) hw (by linarith)).1
    have hsub : OAI.PiExponent.realWeightedSimplex w (H - 1) ⊆
        OAI.PiExponent.strictWeightedSimplex w H := by
      intro a ha
      rw [x8_mem_rws w hw] at ha
      unfold OAI.PiExponent.strictWeightedSimplex
      rw [Finset.mem_filter, x8_mem_rws w hw]
      exact ⟨by linarith, by linarith⟩
    have hc : ((OAI.PiExponent.realWeightedSimplex w (H - 1)).card : ℝ) ≤
        ((OAI.PiExponent.strictWeightedSimplex w H).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hpow : (0 : ℝ) < H ^ n := pow_pos hH0 n
    rw [div_pow, div_div, le_div_iff₀ hpow]
    have e : (H + -1) ^ n / (H ^ n * D) * H ^ n = (H - 1) ^ n / D := by
      field_simp; ring
    rw [e]; exact le_trans hb hc
  · filter_upwards [eventually_ge_atTop 1] with H hH
    have hH0 : (0 : ℝ) < H := by linarith
    have hb := (OAI.PiExponent.DeterminantContradiction.weighted_simplex_volume_bounds
      n w H hw hH0.le).2
    have hc : ((OAI.PiExponent.strictWeightedSimplex w H).card : ℝ) ≤
        ((OAI.PiExponent.realWeightedSimplex w H).card : ℝ) := by
      unfold OAI.PiExponent.strictWeightedSimplex
      exact_mod_cast Finset.card_filter_le _ _
    have hpow : (0 : ℝ) < H ^ n := pow_pos hH0 n
    rw [div_pow, div_div, div_le_iff₀ hpow]
    have e : (H + ∑ i, w i) ^ n / (H ^ n * D) * H ^ n = (H + ∑ i, w i) ^ n / D := by
      field_simp
    rw [e]; exact le_trans hc hb
