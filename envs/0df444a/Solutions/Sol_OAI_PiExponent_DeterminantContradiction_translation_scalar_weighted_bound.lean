-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.translation_scalar_weighted_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T06:30:01.068399+00:00
-- url     : https://prove2.me/submissions/429209e4-dc89-4730-98c8-9bb418db82c3

import Definitions.Def_OAI_PiExponent_MinorTranslationData
import Mathlib
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open Filter Topology
open scoped BigOperators

section
open PowerSeries
namespace S35K

theorem geom_aux (n : ℕ) : ∑ i ∈ Finset.range (n + 1), (if i = 0 then (0:ℝ) else 2 ^ (n - i)) ≤ 2 ^ n := by
  rw [Finset.sum_range_succ']
  simp only [if_pos, Nat.succ_ne_zero, if_false, add_zero]
  have : ∑ i ∈ Finset.range n, (2:ℝ) ^ (n - (i + 1)) = ∑ i ∈ Finset.range n, (2:ℝ) ^ i := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    congr 1; omega
  rw [this, geom_sum_eq (by norm_num : (2:ℝ) ≠ 1)]
  linarith [pow_pos (by norm_num : (0:ℝ) < 2) n]

theorem mul_step (f g : ℂ⟦X⟧) (T M : ℕ) (hT : 1 ≤ T) (hf : ∀ n, ‖coeff n f‖ ≤ 1)
    (hf0 : ∀ n < T, coeff n f = 0) (hg : ∀ n, ‖coeff n g‖ ≤ 2 ^ n)
    (hg0 : ∀ n < M, coeff n g = 0) :
    (∀ n, ‖coeff n (f * g)‖ ≤ 2 ^ n) ∧ ∀ n < M + T, coeff n (f * g) = 0 := by
  constructor
  · intro n
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => ?_).trans (geom_aux n))
    split_ifs with h
    · subst h; simp [hf0 0 (by omega)]
    · rw [norm_mul]
      calc ‖coeff i f‖ * ‖coeff (n - i) g‖ ≤ 1 * 2 ^ (n - i) :=
            mul_le_mul (hf i) (hg _) (norm_nonneg _) (by norm_num)
        _ = _ := one_mul _
  · intro n hn
    rw [coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    by_cases h1 : p.1 < T
    · simp [hf0 _ h1]
    · simp [hg0 p.2 (by omega)]

theorem pow_step (f g : ℂ⟦X⟧) (T M : ℕ) (hT : 1 ≤ T) (hf : ∀ n, ‖coeff n f‖ ≤ 1)
    (hf0 : ∀ n < T, coeff n f = 0) (hg : ∀ n, ‖coeff n g‖ ≤ 2 ^ n)
    (hg0 : ∀ n < M, coeff n g = 0) (e : ℕ) :
    (∀ n, ‖coeff n (f ^ e * g)‖ ≤ 2 ^ n) ∧ ∀ n < M + e * T, coeff n (f ^ e * g) = 0 := by
  induction e with
  | zero => simpa using ⟨hg, hg0⟩
  | succ e ih =>
    rw [pow_succ', mul_assoc]
    have := mul_step f (f ^ e * g) T (M + e * T) hT hf hf0 ih.1 ih.2
    refine ⟨this.1, fun n hn => this.2 n (by rw [Nat.succ_mul] at hn; omega)⟩

theorem prod_step {ι : Type} (s : Finset ι) (f : ι → ℂ⟦X⟧) (T e : ι → ℕ)
    (hT : ∀ i, 1 ≤ T i) (hf : ∀ i n, ‖coeff n (f i)‖ ≤ 1)
    (hf0 : ∀ i, ∀ n < T i, coeff n (f i) = 0) :
    (∀ n, ‖coeff n (∏ i ∈ s, f i ^ e i)‖ ≤ 2 ^ n) ∧
      ∀ n < ∑ i ∈ s, e i * T i, coeff n (∏ i ∈ s, f i ^ e i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨fun n => ?_, fun n hn => by simp at hn⟩
    rw [Finset.prod_empty, coeff_one]
    split_ifs <;> simp [one_le_pow₀]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have := pow_step (f a) _ (T a) _ (hT a) (hf a) (hf0 a) ih.1 ih.2 (e a)
    exact ⟨this.1, fun n hn => this.2 n (by omega)⟩

end S35K

theorem tail_coeff (T n : ℕ) : coeff n (tail T) = if n < T then 0 else -coeff n (PowerSeries.log ℂ) := by
  simp only [tail, map_sub, Polynomial.coeff_coe, coeff_trunc]
  split_ifs <;> simp

theorem tail_norm (T n : ℕ) : ‖coeff n (tail T)‖ ≤ 1 := by
  rw [tail_coeff]
  split_ifs with h
  · simp
  · rw [norm_neg, coeff_log]
    split_ifs with h0
    · simp
    · rw [show (algebraMap ℚ ℂ) ((-1) ^ (n + 1) / ↑n) = (((-1 : ℝ) ^ (n+1) / n : ℝ) : ℂ) by
        simp [Complex.ofReal_div]]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow, abs_neg, abs_one, one_pow,
        Nat.abs_cast]
      have : (1:ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
      rw [div_le_one (by linarith)]; exact this

theorem tail_zero (T n : ℕ) (hn : n < T) : coeff n (tail T) = 0 := by
  rw [tail_coeff, if_pos hn]

end

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (r : Row d H) (t : RowChoice d H r) (C : ℝ) (hC : 0 ≤ C)
    (hε : ∀ i : Fin d.m,
      ‖(r.1.val : ℂ) *
        (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i -
          period)‖ ≤ Real.exp (C - nu * fixedWeights d i))
    (hk : (t.2.2 : ℝ) ≤ H / (d.v0 : ℝ))
    (hT : ∀ i : Fin d.m,
      1 ≤ MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
    (hTw : ∀ i : Fin d.m,
      d.F0 * fixedWeights d i ≤
        (d.v0 : ℝ) *
          MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i) :
    ‖choiceScalar d r t‖ ≤
      Real.exp (-nu * (indexWeight d t.1 - rowWeight d r) +
        H * (nu / d.F0 + Real.log 2 / (d.v0 : ℝ) +
          (Real.log 4 + C) / d.wstar)) := by
  classical
  set a : Fin d.m →₀ ℕ := t.1.1 with ha_def
  set β : Fin d.m →₀ ℕ := beta d r with hβ_def
  set w : Fin d.m → ℝ := fixedWeights d with hw_def
  set T : Fin d.m → ℕ := MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 with hT_def
  set s : Fin d.m → ℕ := fun i => (t.2.1 i : ℕ) with hs_def
  set k : ℕ := (t.2.2 : ℕ) with hk_def
  set z : Fin d.m → ℂ := fun i => (r.1.val : ℂ) *
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i - period) with hz_def
  set G : PowerSeries ℂ := ∏ i, tail (T i) ^ s i with hG_def
  have hcs : choiceScalar d r t = ((∏ i, (a i).choose (β i) * (a i - β i).choose (s i) : ℕ) : ℂ) *
      (∏ i, z i ^ (a i - β i - s i)) * PowerSeries.coeff k G := rfl
  have hpos : 0 ≤ Real.exp (-nu * (indexWeight d t.1 - rowWeight d r) +
        H * (nu / d.F0 + Real.log 2 / (d.v0 : ℝ) + (Real.log 4 + C) / d.wstar)) := (Real.exp_pos _).le
  -- basic facts
  have hwstar : 0 < d.wstar := d.wstar_pos
  have hwl : ∀ i, d.wstar ≤ w i := by
    intro i
    have h1 := d.wstar_lower i
    rw [d.x_log i.val] at h1
    simpa [hw_def, fixedWeights, MatrixArithmetic.logWeights, finiteDenominators] using h1
  have hwpos : ∀ i, 0 < w i := fun i => lt_of_lt_of_le hwstar (hwl i)
  have haH : ∑ i, w i * (a i : ℝ) ≤ H := by
    have hmem := t.1.2
    simp only [transverseIndices, Finset.mem_map] at hmem
    obtain ⟨b, hb, hba⟩ := hmem
    simp only [realWeightedSimplex, Finset.mem_filter] at hb
    have : ∀ i, a i = b i := by
      intro i; rw [ha_def, ← hba]; rfl
    simpa [this] using hb.2
  have hF0 : 0 < d.F0 := d.F0_pos
  have hv0 : (0:ℝ) < d.v0 := d.v0_pos
  by_cases hβa : ∀ i, β i ≤ a i
  swap
  · push_neg at hβa
    obtain ⟨i, hi⟩ := hβa
    have : (∏ i, (a i).choose (β i) * (a i - β i).choose (s i) : ℕ) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by rw [Nat.choose_eq_zero_of_lt hi, zero_mul])
    rw [hcs, this]; simpa using hpos
  by_cases hc : PowerSeries.coeff k G = 0
  · rw [hcs, hc]; simpa using hpos
  have hG := S35K.prod_step Finset.univ (fun i => tail (T i)) T s hT
    (fun i n => tail_norm (T i) n) (fun i n hn => tail_zero (T i) n hn)
  have hkM : ∑ i, s i * T i ≤ k := by
    by_contra hlt; push_neg at hlt
    exact hc (hG.2 k hlt)
  have hGk : ‖PowerSeries.coeff k G‖ ≤ 2 ^ k := hG.1 k
  -- binomial bound
  have hB : ((∏ i, (a i).choose (β i) * (a i - β i).choose (s i) : ℕ) : ℝ) ≤ 4 ^ (∑ i, a i) := by
    have : (∏ i, (a i).choose (β i) * (a i - β i).choose (s i) : ℕ) ≤ ∏ i, 4 ^ (a i) := by
      apply Finset.prod_le_prod' ; intro i _
      calc (a i).choose (β i) * (a i - β i).choose (s i) ≤ 2 ^ (a i) * 2 ^ (a i) :=
            Nat.mul_le_mul (Nat.choose_le_two_pow _ _)
              ((Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)))
        _ = 4 ^ (a i) := by rw [← mul_pow]; norm_num
    rw [Finset.prod_pow_eq_pow_sum] at this
    exact_mod_cast this
  -- center bound
  have hZ : ‖∏ i, z i ^ (a i - β i - s i)‖ ≤ Real.exp (∑ i, ((a i - β i - s i : ℕ) : ℝ) * (C - nu * w i)) := by
    rw [norm_prod, Real.exp_sum]
    apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
    intro i _
    rw [norm_pow, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (hε i) _
  set Sa : ℕ := ∑ i, a i with hSa
  set E : ℝ := ∑ i, ((a i - β i - s i : ℕ) : ℝ) * (C - nu * w i) with hE
  have hnorm : ‖choiceScalar d r t‖ ≤ 4 ^ Sa * Real.exp E * 2 ^ k := by
    rw [hcs, norm_mul, norm_mul, Complex.norm_natCast]
    apply mul_le_mul _ hGk (norm_nonneg _) (by positivity)
    exact mul_le_mul hB hZ (norm_nonneg _) (by positivity)
  have h4 : (4:ℝ) ^ Sa = Real.exp (Sa * Real.log 4) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have h2 : (2:ℝ) ^ k = Real.exp (k * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [h4, h2, ← Real.exp_add, ← Real.exp_add] at hnorm
  refine hnorm.trans (Real.exp_le_exp.mpr ?_)
  -- real inequality
  have hsle : ∀ i, s i ≤ a i - β i := fun i => Nat.lt_succ_iff.mp (t.2.1 i).2
  have hecast : ∀ i, ((a i - β i - s i : ℕ) : ℝ) = (a i : ℝ) - β i - s i := by
    intro i
    rw [Nat.cast_sub (hsle i), Nat.cast_sub (hβa i)]
  have hEeq : E = C * ∑ i, ((a i : ℝ) - β i - s i) - nu * ((∑ i, w i * (a i : ℝ)) - (∑ i, w i * (β i : ℝ)))
      + nu * ∑ i, w i * (s i : ℝ) := by
    rw [hE]; simp only [hecast]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hidx : indexWeight d t.1 - rowWeight d r = (∑ i, w i * (a i : ℝ)) - (∑ i, w i * (β i : ℝ)) := rfl
  have hSaR : (Sa : ℝ) = ∑ i, (a i : ℝ) := by rw [hSa]; push_cast; rfl
  have he_le : ∑ i, ((a i : ℝ) - β i - s i) ≤ Sa := by
    rw [hSaR]; apply Finset.sum_le_sum; intro i _
    have : (0:ℝ) ≤ β i := by positivity
    have : (0:ℝ) ≤ s i := by positivity
    linarith
  have hSaH : (Sa : ℝ) ≤ H / d.wstar := by
    rw [le_div_iff₀ hwstar, hSaR, Finset.sum_mul]
    refine le_trans (Finset.sum_le_sum fun i _ => ?_) haH
    rw [mul_comm (a i : ℝ)]
    exact mul_le_mul_of_nonneg_right (hwl i) (by positivity)
  have hws : ∑ i, w i * (s i : ℝ) ≤ H / d.F0 := by
    have h1 : ∀ i, w i ≤ (d.v0 : ℝ) * T i / d.F0 := by
      intro i; rw [le_div_iff₀ hF0, mul_comm]; exact hTw i
    have h2 : ∑ i, w i * (s i : ℝ) ≤ ∑ i, (d.v0 : ℝ) / d.F0 * ((s i * T i : ℕ) : ℝ) := by
      apply Finset.sum_le_sum; intro i _
      have : w i * (s i : ℝ) ≤ (d.v0 : ℝ) * T i / d.F0 * s i :=
        mul_le_mul_of_nonneg_right (h1 i) (by positivity)
      push_cast
      have e : (d.v0 : ℝ) / d.F0 * ((s i : ℝ) * T i) = (d.v0 : ℝ) * T i / d.F0 * s i := by ring
      rw [e]; exact this
    rw [← Finset.mul_sum] at h2
    have h3 : ((∑ i, s i * T i : ℕ) : ℝ) ≤ k := by exact_mod_cast hkM
    push_cast at h2 h3
    have h4 : (d.v0 : ℝ) / d.F0 * ∑ i, (s i : ℝ) * T i ≤ (d.v0 : ℝ) / d.F0 * (H / d.v0) :=
      mul_le_mul_of_nonneg_left (h3.trans hk) (by positivity)
    have h5 : (d.v0 : ℝ) / d.F0 * (H / d.v0) = H / d.F0 := by field_simp
    linarith
  have hk2 : (k : ℝ) * Real.log 2 ≤ H * (Real.log 2 / d.v0) := by
    have := mul_le_mul_of_nonneg_right hk (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2))
    rw [mul_div_assoc', mul_comm H]; linarith [show H / (d.v0:ℝ) * Real.log 2 = Real.log 2 * H / d.v0 by ring]
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hA : (Sa : ℝ) * Real.log 4 + C * ∑ i, ((a i : ℝ) - β i - s i) ≤ H * ((Real.log 4 + C) / d.wstar) := by
    have := mul_le_mul_of_nonneg_left hSaH (add_nonneg hlog4 hC)
    have h' : C * ∑ i, ((a i : ℝ) - β i - s i) ≤ C * Sa := mul_le_mul_of_nonneg_left he_le hC
    have h'' : (Real.log 4 + C) * (H / d.wstar) = H * ((Real.log 4 + C) / d.wstar) := by ring
    linarith
  have hB2 : nu * ∑ i, w i * (s i : ℝ) ≤ H * (nu / d.F0) := by
    have := mul_le_mul_of_nonneg_left hws hnu
    have h' : nu * (H / d.F0) = H * (nu / d.F0) := by ring
    linarith
  rw [hEeq, hidx]
  have hsplit : H * (nu / d.F0 + Real.log 2 / (d.v0 : ℝ) + (Real.log 4 + C) / d.wstar) =
      H * (nu / d.F0) + H * (Real.log 2 / d.v0) + H * ((Real.log 4 + C) / d.wstar) := by ring
  rw [hsplit]
  linarith
