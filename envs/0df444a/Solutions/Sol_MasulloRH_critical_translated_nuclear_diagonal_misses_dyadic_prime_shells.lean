-- Prove2me | solution 1 for MasulloRH.critical_translated_nuclear_diagonal_misses_dyadic_prime_shells
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T04:36:40.416592+00:00
-- url     : https://prove2.me/submissions/7b881100-48bf-4296-9bef-1e7e5008a44c

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Finset Filter MeasureTheory
open scoped ENNReal Topology

private theorem dyadic_obstruction (b : ℕ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (hcard : ∀ (S : Finset Nat.Primes) n, ((S.filter (fun (p : Nat.Primes) => (p : ℕ).log2 = n)).card : ℝ) ≤ b n) :
    ¬ Summable (fun n => b n / 2^n) := by
  classical
  intro hsum
  apply Nat.Primes.not_summable_one_div
  apply summable_of_sum_le (c := ∑' n, b n / 2^n) (fun p => by positivity)
  intro S
  let d (p : Nat.Primes) := (p : ℕ).log2
  rw [← Finset.sum_fiberwise_of_maps_to (t := S.image d) (g := d)
    (fun p hp => Finset.mem_image_of_mem _ hp) (fun p : Nat.Primes => (1 / (p:ℝ)))]
  apply (Finset.sum_le_sum ?_).trans (hsum.sum_le_tsum _ (fun n _ => div_nonneg (hb n) (by positivity)))
  intro n hn
  calc
    _ ≤ ∑ _p ∈ S.filter (fun p => d p = n), (1:ℝ)/2^n := by
      apply Finset.sum_le_sum
      intro p hp
      have hd := (Finset.mem_filter.mp hp).2
      have hg : (2:ℝ)^n ≤ (p:ℝ) := by
        rw [← hd]
        exact_mod_cast Nat.log2_self_le p.prop.ne_zero
      exact one_div_le_one_div_of_le (by positivity) hg
    _ ≤ b n / 2^n := by
      rw [Finset.sum_const, nsmul_eq_mul, ← mul_div_assoc, mul_one]
      exact div_le_div_of_nonneg_right (hcard S n) (by positivity)

private theorem series_diagonal_budget {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f g : ℕ → X → ℂ) (hf : ∀ j, Measurable (f j)) (hg : ∀ j, Measurable (g j))
    (m : Nat.Primes → X → ℂ) (hm : ∀ p, Measurable (m p))
    (hpart : ∀ x, ∑' p, ‖m p x‖ₑ ≤ 1) (S : Finset Nat.Primes) :
    ∑ p ∈ S, ‖∫ x, m p x * ∑' j, f j x * g j x ∂μ‖ₑ ≤
      ∑' j, eLpNorm (f j) 2 μ * eLpNorm (g j) 2 μ := by
  let Z (x : X) := ∑' j, ‖f j x * g j x‖ₑ
  have hZ : Measurable Z := Measurable.tsum (fun j => ((hf j).mul (hg j)).enorm)
  calc
    _ ≤ ∑ p ∈ S, ∫⁻ x, ‖m p x‖ₑ * Z x ∂μ := by
      apply Finset.sum_le_sum
      intro p _
      apply (enorm_integral_le_lintegral_enorm _).trans
      apply lintegral_mono
      intro x
      change ‖m p x * ∑' j, f j x * g j x‖ₑ ≤ ‖m p x‖ₑ * Z x
      rw [enorm_mul]
      exact mul_le_mul_of_nonneg_left enorm_tsum_le_tsum_enorm zero_le
    _ = ∫⁻ x, ∑ p ∈ S, ‖m p x‖ₑ * Z x ∂μ :=
      (lintegral_finsetSum S (fun p _ => (hm p).enorm.mul hZ)).symm
    _ ≤ ∫⁻ x, Z x ∂μ := by
      apply lintegral_mono
      intro x
      change (∑ p ∈ S, ‖m p x‖ₑ * Z x) ≤ Z x
      rw [← Finset.sum_mul]
      calc
        _ ≤ 1 * Z x := mul_le_mul_of_nonneg_right ((ENNReal.sum_le_tsum S).trans (hpart x)) zero_le
        _ = _ := one_mul _
    _ = ∑' j, ∫⁻ x, ‖f j x * g j x‖ₑ ∂μ :=
      lintegral_tsum (fun j => ((hf j).mul (hg j)).enorm.aemeasurable)
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro j
      have h := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
        (μ := μ) (hg j).aestronglyMeasurable (hf j).aestronglyMeasurable
      simpa [eLpNorm_one_eq_lintegral_enorm, Pi.smul_apply, smul_eq_mul] using h

private theorem dyadic_nuclear_no_go {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : ℕ → ℕ → X → ℂ) (hf : ∀ n j, Measurable (f n j)) (hg : ∀ n j, Measurable (g n j))
    (m : ℕ → Nat.Primes → X → ℂ) (hm : ∀ n p, Measurable (m n p))
    (hpart : ∀ n x, ∑' p, ‖m n p x‖ₑ ≤ 1)
    (N : ℕ) (hprime : ∀ (n : ℕ) (p : Nat.Primes), (p:ℕ).log2 = n → N ≤ n →
       1 ≤ ‖∫ x, m n p x * ∑' j, f n j x * g n j x ∂μ‖ₑ) :
    ∀ (C r : ℝ) (d : ℕ), 0 ≤ C → 0 < r → r < 2 →
      ¬ ∀ n : ℕ, ∑' j, eLpNorm (f n j) 2 μ * eLpNorm (g n j) 2 μ ≤
        ENNReal.ofReal (C * ((n:ℝ)+1)^d * r^n) := by
  intro C r d hC hr hr2 hbound
  let b (n : ℕ) := C * ((n:ℝ)+1)^d * r^n
  have hb (n : ℕ) : 0 ≤ b n := by dsimp [b]; positivity
  have hcard (S : Finset Nat.Primes) (n : ℕ) :
      ((S.filter (fun (p : Nat.Primes) => (p : ℕ).log2 = n)).card : ℝ) ≤ b n + 2 ^ N := by
    let P := S.filter (fun (p : Nat.Primes) => (p:ℕ).log2 = n)
    by_cases hN : N ≤ n
    · apply le_trans _ (le_add_of_nonneg_right (by positivity))
      have h : (P.card : ℝ≥0∞) ≤ ENNReal.ofReal (b n) := calc
        _ = ∑ _p ∈ P, (1:ℝ≥0∞) := by simp
        _ ≤ _ := Finset.sum_le_sum (fun p hp => hprime n p ((Finset.mem_filter.mp hp).2) hN)
        _ ≤ _ := series_diagonal_budget (μ := μ) (f n) (g n) (hf n) (hg n) (m n) (hm n) (hpart n) P
        _ ≤ _ := hbound n
      rw [← ENNReal.ofReal_natCast] at h
      exact (ENNReal.ofReal_le_ofReal_iff (hb n)).mp h
    · let e : Nat.Primes ↪ ℕ := ⟨Subtype.val, Subtype.val_injective⟩
      have hsub : P.map e ⊆ Finset.range (2^N) := by
        intro x hx
        rcases Finset.mem_map.mp hx with ⟨p,hp,rfl⟩
        apply Finset.mem_range.mpr
        apply (Nat.log2_lt p.prop.ne_zero).mp
        rw [(Finset.mem_filter.mp hp).2]
        omega
      have hc : P.card ≤ 2^N := by simpa using Finset.card_le_card hsub
      have hcr : (P.card : ℝ) ≤ 2^N := by exact_mod_cast hc
      exact le_trans hcr (le_add_of_nonneg_left (hb n))
  apply dyadic_obstruction (fun n => b n + 2^N) (fun n => add_nonneg (hb n) (by positivity)) hcard
  have hqpos : 0 < r / 2 := by positivity
  have hq : ‖r / 2‖ < 1 := by rw [Real.norm_of_nonneg hqpos.le]; linarith
  have hs := (summable_pow_mul_geometric_of_norm_lt_one d hq).comp_injective
    (i := fun n : ℕ => n+1) (fun _ _ e => Nat.add_right_cancel e)
  have ht := hs.mul_left (C / (r / 2))
  have hgeo := (summable_geometric_of_norm_lt_one (x := (1/2:ℝ)) (by norm_num [Real.norm_eq_abs])).mul_left ((2:ℝ)^N)
  apply (ht.add hgeo).congr
  intro n
  change C / (r / 2) * (((n+1:ℕ):ℝ)^d * (r/2)^(n+1)) + (2:ℝ)^N * (1/2)^n = (b n + 2^N) / 2^n
  rw [pow_succ, div_pow]
  dsimp [b]
  push_cast
  simp only [one_div, inv_pow]
  field_simp
  <;> ring

private noncomputable def halfDensity (x : ℝ) := Real.exp (|x| / 2) * (1+x^2)

private theorem halfDensity_translate (x : ℝ) (n : ℕ) :
    halfDensity x / halfDensity (x - (n:ℝ)*Real.log 2) ≤
      2 * ((n:ℝ)+1)^2 * (Real.exp (Real.log 2 / 2))^n := by
  let u : ℝ := n * Real.log 2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hu' : u ≤ (n:ℝ) := by
    dsimp [u]
    have hl := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    have hc : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
    nlinarith
  have hscale : 1+x^2 ≤ 2*((n:ℝ)+1)^2 * (1 + (x-u)^2) := by
    have h : 1+x^2 ≤ (2*(1+u^2))*(1+(x-u)^2) := by
      nlinarith [sq_nonneg ((x-u)-u), mul_nonneg (sq_nonneg u) (sq_nonneg (x-u))]
    have h' : 1+u^2 ≤ ((n:ℝ)+1)^2 := by nlinarith [sq_nonneg u, mul_nonneg (sub_nonneg.mpr hu') (add_nonneg (Nat.cast_nonneg n) hu), (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  have hab : |x| ≤ |x-u| + u := by
    calc
      |x| = |(x-u)+u| := by ring_nf
      _ ≤ |x-u|+|u| := abs_add_le _ _
      _ = _ := by rw [abs_of_nonneg hu]
  have hexp : Real.exp (|x|/2) ≤ Real.exp (|x-u|/2) * Real.exp (u/2) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    linarith
  have hp : Real.exp (u/2) = (Real.exp (Real.log 2/2))^n := by
    rw [← Real.exp_nat_mul]
    dsimp [u]; congr 1; ring
  have hden : 0 < halfDensity (x-u) := by dsimp [halfDensity]; positivity
  apply (div_le_iff₀ hden).mpr
  rw [← hp]
  unfold halfDensity
  calc
    _ ≤ (Real.exp (|x-u|/2) * Real.exp (u/2)) * (2*((n:ℝ)+1)^2 * (1+(x-u)^2)) :=
      mul_le_mul hexp hscale (by positivity) (by positivity)
    _ = _ := by ring
theorem solution (f g : ℕ → ℝ → ℂ) (hf : ∀ j, Measurable (f j)) (hg : ∀ j, Measurable (g j))
    (hcost : (∑' j, eLpNorm (f j) 2 volume * eLpNorm (g j) 2 volume) ≠ ∞)
    (m : ℕ → Nat.Primes → ℝ → ℂ) (hm : ∀ n p, Measurable (m n p))
    (hpart : ∀ n x, ∑' p, ‖m n p x‖ₑ ≤ 1) :
    let W := fun x : ℝ => Real.exp (|x| / 2) * (1+x^2)
    let u := fun n : ℕ => (n:ℝ)*Real.log 2
    ∀ N : ℕ, ∃ (n : ℕ) (p : Nat.Primes), (p:ℕ).log2 = n ∧ N ≤ n ∧
      ‖∫ x : ℝ, m n p x * ∑' j, ((W x / W (x-u n) : ℝ) : ℂ) * f j (x-u n) * g j x‖ₑ < 1 := by
  intro W u N
  let base : ℝ≥0∞ := ∑' j, eLpNorm (f j) 2 volume * eLpNorm (g j) 2 volume
  let r := Real.exp (Real.log 2/2)
  have hr : 0 < r := Real.exp_pos _
  have hr' : r < 2 := by
    rw [← Real.exp_log (by norm_num : (0:ℝ)<2)]
    apply Real.exp_lt_exp.mpr
    have := Real.log_pos (by norm_num : (1:ℝ)<2)
    linarith
  let B (n : ℕ) : ℝ := 2*((n:ℝ)+1)^2*r^n
  let F (n j : ℕ) (x : ℝ) : ℂ := ((W x / W (x-u n) : ℝ) : ℂ) * f j (x-u n)
  have hW : Measurable W := by
    dsimp [W]; fun_prop
  have hF (n j) : Measurable (F n j) := by
    dsimp [F]
    exact (Complex.continuous_ofReal.measurable.comp
      (hW.div (hW.comp (measurable_id.sub measurable_const)))).mul ((hf j).comp (measurable_id.sub measurable_const))
  have ha (n j : ℕ) : eLpNorm (F n j) 2 volume ≤ ENNReal.ofReal (B n) * eLpNorm (f j) 2 volume := by
    let v := fun x : ℝ => f j (x-u n)
    have hv : eLpNorm v 2 volume = eLpNorm (f j) 2 volume := by
      simpa only [v,sub_eq_add_neg, Function.comp_def] using
        eLpNorm_comp_measurePreserving (p := 2) (hf j).aestronglyMeasurable
          (measurePreserving_add_right (volume : Measure ℝ) (-(u n)))
    have hB : 0 ≤ B n := by dsimp [B]; positivity
    calc
      _ ≤ eLpNorm ((B n) • v) 2 volume := by
        apply eLpNorm_mono
        intro x
        change ‖((W x / W (x-u n) : ℝ) : ℂ) * f j (x-u n)‖ ≤ ‖(B n) • f j (x-u n)‖
        rw [norm_mul, Complex.norm_real, norm_smul, Real.norm_of_nonneg hB,
          Real.norm_of_nonneg (by dsimp [W]; positivity)]
        exact mul_le_mul_of_nonneg_right (halfDensity_translate x n) (norm_nonneg _)
      _ = _ := by rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg hB, hv]
  by_contra! hall
  apply dyadic_nuclear_no_go volume F (fun _ j => g j) hF (fun _ => hg) m hm hpart N
    (fun n p h hN => hall n p h hN) (2*base.toReal) r 2 (by positivity) hr hr'
  intro n
  calc
    _ ≤ ∑' j, (ENNReal.ofReal (B n) * eLpNorm (f j) 2 volume) * eLpNorm (g j) 2 volume :=
      ENNReal.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_right (ha n j) zero_le)
    _ = ENNReal.ofReal (B n) * base := by simp only [mul_assoc, ENNReal.tsum_mul_left, base]
    _ = _ := by
      rw [← ENNReal.ofReal_toReal (show base ≠ ∞ from hcost), ← ENNReal.ofReal_mul (by dsimp [B]; positivity)]
      rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
      congr 1
      dsimp [B]
      ring
