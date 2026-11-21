-- Prove2me | solution 1 for MultiInterm.Compete.lemma_C_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:11:29.782186+00:00
-- url     : https://prove2.me/submissions/fdb6350b-b2b2-40da-8420-a296090b15b5

import Mathlib
import Definitions.Def_MultiInterm_Compete_ValueDistribution

section
namespace MultiInterm.Dev.AlgC1

/-- the paper's H (App. C.7) -/
noncomputable def H (n : ℕ) (q : ℝ) : ℝ :=
  1 - q ^ n - n * (1 - q) * q ^ (n - 1) + n * (1 - q) * q ^ (2 * n - 2)


theorem Dle (m q a : ℝ) (hm : 2 ≤ m) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ha0 : 0 ≤ a)
    (ha : a * (1 + m * (1 - q)) ≤ 1) :
    -m * (1 - q) + a * (2 * m - (2 * m + 1) * q) ≤ 0 := by
  by_cases hc : 2 * m - (2 * m + 1) * q ≤ 0
  · nlinarith [mul_nonneg ha0 (neg_nonneg.mpr hc), mul_nonneg (by linarith : (0:ℝ) ≤ m) (by linarith : (0:ℝ) ≤ 1 - q)]
  · push_neg at hc
    have h1 := mul_le_mul_of_nonneg_left ha hc.le
    have key : (-m * (1 - q) + a * (2 * m - (2 * m + 1) * q)) * (1 + m * (1 - q)) ≤ 0 := by
      nlinarith [sq_nonneg (m * (1 - q) - 1), mul_nonneg (by linarith : (0:ℝ) ≤ m - 1) (by linarith : (0:ℝ) ≤ 1 - q)]
    by_contra hne
    push_neg at hne
    have : 0 < 1 + m * (1 - q) := by nlinarith
    nlinarith

theorem Dle_pow (k : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    -((k:ℝ) + 2) * (1 - q) + q ^ (k + 2) * (2 * ((k:ℝ) + 2) - (2 * ((k:ℝ) + 2) + 1) * q) ≤ 0 := by
  apply Dle _ q _ (by have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith) hq0 hq1 (pow_nonneg hq0 _)
  have hb := one_add_mul_le_pow (by linarith : (-2:ℝ) ≤ 1 - q) (k + 2)
  have hb2 : q ^ (k + 2) * (1 + (1 - q)) ^ (k + 2) ≤ 1 := by
    rw [← mul_pow]
    apply pow_le_one₀ (by nlinarith)
    nlinarith [sq_nonneg (1 - q)]
  have h3 : q ^ (k + 2) * (1 + ((k:ℝ) + 2) * (1 - q)) ≤ q ^ (k + 2) * (1 + (1 - q)) ^ (k + 2) := by
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq0 _)
    push_cast at hb
    linarith
  linarith

theorem amgm (s : ℝ) (hs : 0 ≤ s) (m : ℕ) :
    ((m:ℝ) + 1) * s ^ m ≤ ∑ i ∈ Finset.range (m + 1), (s ^ 2) ^ i := by
  have h2 : ∑ i ∈ Finset.range (m + 1), (s ^ 2) ^ i = ∑ i ∈ Finset.range (m + 1), (s ^ 2) ^ (m - i) := by
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro i hi
    have := Finset.mem_range.mp hi
    congr 2
  have h3 : ∑ i ∈ Finset.range (m + 1), (2 * s ^ m) ≤
      ∑ i ∈ Finset.range (m + 1), ((s ^ 2) ^ i + (s ^ 2) ^ (m - i)) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i ≤ m := by have := Finset.mem_range.mp hi; omega
    have e : s ^ i * s ^ (m - i) = s ^ m := by rw [← pow_add, Nat.add_sub_cancel' hi']
    have := sq_nonneg (s ^ i - s ^ (m - i))
    have e2 : (s ^ 2) ^ i = (s ^ i) ^ 2 := by ring
    have e3 : (s ^ 2) ^ (m - i) = (s ^ (m - i)) ^ 2 := by ring
    rw [e2, e3]
    nlinarith
  rw [Finset.sum_add_distrib, ← h2] at h3
  simp at h3
  nlinarith

theorem polyz (z : ℝ) (h0 : 0 < z) (h1 : z < 1) :
    z * (2 - 4 * (z ^ 2) ^ 2 / (1 + z ^ 2)) < 1 := by
  have e : z * (2 - 4 * (z ^ 2) ^ 2 / (1 + z ^ 2)) = z * (2 + 2 * z ^ 2 - 4 * z ^ 4) / (1 + z ^ 2) := by
    field_simp
  rw [e, div_lt_one (by positivity)]
  have h2 : 0 < 1 - z ^ 2 := by nlinarith
  nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 1 + z ^ 2) (sq_nonneg (z ^ 2 + z - 1)),
    mul_pos (mul_pos h2 (by positivity : 0 < z ^ 2)) (sq_pos_of_pos (by linarith : 0 < 1 - z))]

/-- H is decreasing on [0,1] for n ≥ 3 -/
theorem H_anti (n : ℕ) (hn : 3 ≤ n) (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) :
    H n q ≤ H n p := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have e1 : k + 3 - 1 = k + 2 := by omega
  have e2 : 2 * (k + 3) - 2 = 2 * k + 4 := by omega
  have hH : ∀ x, H (k + 3) x = 1 - x ^ (k + 3) - ((k:ℝ) + 3) * (1 - x) * x ^ (k + 2)
      + ((k:ℝ) + 3) * (1 - x) * x ^ (2 * k + 4) := by
    intro x; simp only [H, e1, e2]; push_cast; ring
  have hd : ∀ x : ℝ, HasDerivAt (fun x => 1 - x ^ (k + 3) - ((k:ℝ) + 3) * (1 - x) * x ^ (k + 2)
      + ((k:ℝ) + 3) * (1 - x) * x ^ (2 * k + 4))
      (((k:ℝ) + 3) * x ^ (k + 1) * (-((k:ℝ) + 2) * (1 - x)
        + x ^ (k + 2) * (2 * ((k:ℝ) + 2) - (2 * ((k:ℝ) + 2) + 1) * x))) x := by
    intro x
    have hA : HasDerivAt (fun q : ℝ => 1 - q) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (1:ℝ)
    have p1 := hasDerivAt_pow (k + 3) x
    have p2 := hasDerivAt_pow (k + 2) x
    have p3 := hasDerivAt_pow (2 * k + 4) x
    have := (((p1.const_sub 1).sub ((hA.const_mul ((k:ℝ) + 3)).mul p2))).add
      ((hA.const_mul ((k:ℝ) + 3)).mul p3)
    refine HasDerivAt.congr_deriv this ?_
    have a1 : k + 3 - 1 = k + 2 := by omega
    have a2 : k + 2 - 1 = k + 1 := by omega
    have a3 : 2 * k + 4 - 1 = 2 * k + 3 := by omega
    try simp only [a1, a2, a3]
    push_cast
    ring
  have hanti : AntitoneOn (fun x => 1 - x ^ (k + 3) - ((k:ℝ) + 3) * (1 - x) * x ^ (k + 2)
      + ((k:ℝ) + 3) * (1 - x) * x ^ (2 * k + 4)) (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun x _ => (hd x).continuousAt.continuousWithinAt
    · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x).deriv]
      have := Dle_pow k x hx.1.le hx.2.le
      have hp : 0 ≤ x ^ (k + 1) := pow_nonneg hx.1.le _
      have : 0 ≤ ((k:ℝ) + 3) * x ^ (k + 1) := by positivity
      nlinarith
  rw [hH, hH]
  exact hanti ⟨hp, hpq.trans hq⟩ ⟨hp.trans hpq, hq⟩ hpq


/-- strict positivity of Eq. (15)/τ (paper's XY < 1) -/
theorem eq15_pos (n : ℕ) (hn : 3 ≤ n) (q : ℝ) (h0 : 0 < q) (h1 : q < 1) :
    0 < 1 - q ^ n - 2 * n * (1 - q) * q ^ (n - 1)
      + 4 * n * (1 - q) * q ^ (3 * n - 3) / (1 + q ^ (n - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  obtain ⟨s, hs0, rfl⟩ : ∃ s, 0 < s ∧ q = s ^ 2 := ⟨Real.sqrt q, Real.sqrt_pos.mpr h0, (Real.sq_sqrt h0.le).symm⟩
  have hs1 : s < 1 := by nlinarith
  have e1 : k + 3 - 1 = k + 2 := by omega
  have e3 : 3 * (k + 3) - 3 = 3 * (k + 2) := by omega
  rw [e1, e3]
  set z := s ^ (k + 2) with hz
  have hz0 : 0 < z := pow_pos hs0 _
  have hz1 : z < 1 := pow_lt_one₀ hs0.le hs1 (by omega)
  have hw : (s ^ 2) ^ (k + 2) = z ^ 2 := by rw [hz]; ring
  have hw3 : (s ^ 2) ^ (3 * (k + 2)) = (z ^ 2) ^ 3 := by rw [hz]; ring
  rw [hw, hw3]
  have hP : 0 < 1 - (s ^ 2) ^ (k + 3) := by
    have : (s ^ 2) ^ (k + 3) < 1 := pow_lt_one₀ (by positivity) (by nlinarith) (by omega)
    linarith
  have hq1 : 0 < 1 - s ^ 2 := by nlinarith
  have hg := amgm s hs0.le (k + 2)
  have hgeo : (∑ i ∈ Finset.range (k + 2 + 1), (s ^ 2) ^ i) * (1 - s ^ 2) = 1 - (s ^ 2) ^ (k + 3) :=
    geom_sum_mul_neg (s ^ 2) (k + 3)
  have hAM : ((k:ℝ) + 3) * (1 - s ^ 2) * z ^ 2 ≤ z * (1 - (s ^ 2) ^ (k + 3)) := by
    rw [← hgeo]
    push_cast at hg
    have : ((k:ℝ) + 2 + 1) * z ≤ ∑ i ∈ Finset.range (k + 2 + 1), (s ^ 2) ^ i := hg
    nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg hz0.le hq1.le)]
  have hY : 0 ≤ 2 - 4 * (z ^ 2) ^ 2 / (1 + z ^ 2) := by
    have : 4 * (z ^ 2) ^ 2 / (1 + z ^ 2) ≤ 2 := by
      have hz2 : z ^ 2 < 1 := by nlinarith
      rw [div_le_iff₀ (by positivity)]; nlinarith [mul_nonneg (sq_nonneg z) (by linarith : (0:ℝ) ≤ 1 - z ^ 2)]
    linarith
  have hzY := polyz z hz0 hz1
  have eq : 2 * ((k + 3 : ℕ) : ℝ) * (1 - s ^ 2) * z ^ 2 = 0 + 2 * (((k:ℝ) + 3) * (1 - s ^ 2) * z ^ 2) := by
    push_cast; ring
  have key : 4 * ((k + 3 : ℕ) : ℝ) * (1 - s ^ 2) * (z ^ 2) ^ 3 / (1 + z ^ 2)
      = (((k:ℝ) + 3) * (1 - s ^ 2) * z ^ 2) * (4 * (z ^ 2) ^ 2 / (1 + z ^ 2)) := by
    push_cast; ring
  rw [eq, key]
  have h5 := mul_le_mul_of_nonneg_right hAM hY
  have h6 := mul_lt_mul_of_pos_right hzY hP
  nlinarith


end MultiInterm.Dev.AlgC1
end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open Set

namespace MultiInterm.Dev.T

lemma cdf_cont (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    Continuous (cdf ν) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hmono : Monotone (cdf ν) := (cdf ν).mono
  rw [hmono.continuousAt_iff_leftLim_eq_rightLim, StieltjesFunction.rightLim_eq]
  apply le_antisymm (hmono.leftLim_le le_rfl)
  have h := (cdf ν).measure_singleton x
  rw [measure_cdf, measure_singleton] at h
  have := ENNReal.ofReal_eq_zero.1 h.symm
  linarith

lemma pre_Iic (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν] (t : ℝ) (ht1 : t < 1)
    (hne : ∃ x, cdf ν x ≤ t) :
    ∃ s, {x | cdf ν x ≤ t} = Iic s ∧ cdf ν s = t := by
  have hG := cdf_cont ν
  have hmono : Monotone (cdf ν) := (cdf ν).mono
  set S := {x | cdf ν x ≤ t} with hS
  have hclosed : IsClosed S := isClosed_le hG continuous_const
  have hbdd : BddAbove S := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
      ((tendsto_cdf_atTop ν).eventually (lt_mem_nhds ht1))
    refine ⟨N, fun x hx => ?_⟩
    by_contra h
    push Not at h
    exact absurd (hN x h.le) (not_lt.2 hx)
  have hne' : S.Nonempty := hne
  have hmem := hclosed.csSup_mem hne' hbdd
  have hset : S = Iic (sSup S) := by
    ext x
    constructor
    · intro hx; exact le_csSup hbdd hx
    · intro hx; exact le_trans (hmono hx) hmem
  refine ⟨sSup S, hset, le_antisymm hmem ?_⟩
  by_contra h
  push Not at h
  obtain ⟨b, hb, hbt⟩ := (hG.continuousAt.eventually (gt_mem_nhds h)).exists_gt
  exact absurd (le_csSup hbdd (show b ∈ S from hbt.le)) (not_le.2 hb)


lemma ν_Iic (ν : Measure ℝ) [IsProbabilityMeasure ν] (x : ℝ) :
    ν (Iic x) = ENNReal.ofReal (cdf ν x) := by
  rw [cdf_eq_real, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma map_cdf (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    ν.map (cdf ν) = volume.restrict (Icc (0:ℝ) 1) := by
  have hG := cdf_cont ν
  have : IsProbabilityMeasure (ν.map (cdf ν)) :=
    Measure.isProbabilityMeasure_map hG.measurable.aemeasurable
  have : IsFiniteMeasure (ν.map (cdf ν)) := inferInstance
  refine Measure.ext_of_Iic _ _ (fun t => ?_)
  rw [Measure.map_apply hG.measurable measurableSet_Iic,
    Measure.restrict_apply measurableSet_Iic]
  have hpre : (cdf ν ⁻¹' Iic t) = {x | cdf ν x ≤ t} := rfl
  rw [hpre]
  rcases lt_or_ge t 0 with h0 | h0
  · have : {x | cdf ν x ≤ t} = ∅ := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le h0 (cdf_nonneg ν x)
    rw [this]
    have : Iic t ∩ Icc (0:ℝ) 1 = ∅ := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
      intro ⟨h1, h2, _⟩; linarith
    simp [this]
  rcases lt_or_ge t 1 with h1 | h1
  · have hIcc : Iic t ∩ Icc (0:ℝ) 1 = Icc 0 t := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨a, b, _⟩; exact ⟨b, a⟩
      · rintro ⟨a, b⟩; exact ⟨b, a, by linarith⟩
    rw [hIcc, Real.volume_Icc, sub_zero]
    by_cases hne : ∃ x, cdf ν x ≤ t
    · obtain ⟨s, hs, hst⟩ := pre_Iic ν t h1 hne
      rw [hs, ν_Iic, hst]
    · push Not at hne
      have : {x | cdf ν x ≤ t} = ∅ := by
        ext x; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]; exact hne x
      rw [this, measure_empty]
      have : t = 0 := by
        by_contra hne0
        have htp : 0 < t := lt_of_le_of_ne h0 (Ne.symm hne0)
        obtain ⟨x, hx⟩ := (((tendsto_cdf_atBot ν).eventually (ge_mem_nhds htp)).exists)
        exact absurd (hne x) (not_lt.2 hx)
      subst this; simp
  · have : {x | cdf ν x ≤ t} = univ := by
      ext x; simp only [mem_setOf_eq, mem_univ, iff_true]
      exact le_trans (cdf_le_one ν x) h1
    rw [this, measure_univ]
    have : Iic t ∩ Icc (0:ℝ) 1 = Icc 0 1 := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨_, b⟩; exact b
      · rintro ⟨a, b⟩; exact ⟨by linarith, a, b⟩
    rw [this, Real.volume_Icc]; simp


lemma H_Iic (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν] (k : ℕ) (c : ℝ) :
    ((k : ℝ≥0∞) + 1) * ∫⁻ y in Iic c, ENNReal.ofReal (cdf ν y) ^ k ∂ν
      = ENNReal.ofReal (cdf ν c) ^ (k + 1) := by
  have hG := cdf_cont ν
  have hP := map_cdf ν
  have h0 := cdf_nonneg ν c
  have h1 := cdf_le_one ν c
  set S' : Set ℝ := cdf ν ⁻¹' Iic (cdf ν c) with hS'
  have hsub : Iic c ⊆ S' := fun x hx => (cdf ν).mono hx
  have hmeasS' : MeasurableSet S' := hG.measurable measurableSet_Iic
  have hνS' : ν S' = ν (Iic c) := by
    have : ν S' = ν.map (cdf ν) (Iic (cdf ν c)) := by
      rw [Measure.map_apply hG.measurable measurableSet_Iic]
    rw [this, hP, Measure.restrict_apply measurableSet_Iic, ν_Iic]
    have : Iic (cdf ν c) ∩ Icc (0:ℝ) 1 = Icc 0 (cdf ν c) := by
      ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨a, b, _⟩; exact ⟨b, a⟩
      · rintro ⟨a, b⟩; exact ⟨b, a, by linarith⟩
    rw [this, Real.volume_Icc, sub_zero]
  have hae : Iic c =ᵐ[ν] S' :=
    ae_eq_of_subset_of_measure_ge hsub hνS'.le measurableSet_Iic.nullMeasurableSet (measure_ne_top _ _)
  have step1 : ∫⁻ y in Iic c, ENNReal.ofReal (cdf ν y) ^ k ∂ν
      = ∫⁻ y in S', ENNReal.ofReal (cdf ν y) ^ k ∂ν := setLIntegral_congr hae
  have step2 : ∫⁻ y in S', ENNReal.ofReal (cdf ν y) ^ k ∂ν
      = ∫⁻ u in Iic (cdf ν c), ENNReal.ofReal u ^ k ∂(ν.map (cdf ν)) := by
    rw [setLIntegral_map measurableSet_Iic (by fun_prop) hG.measurable]
  rw [step1, step2, hP, Measure.restrict_restrict measurableSet_Iic]
  have hIcc : Iic (cdf ν c) ∩ Icc (0:ℝ) 1 = Icc 0 (cdf ν c) := by
    ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨a, b, _⟩; exact ⟨b, a⟩
    · rintro ⟨a, b⟩; exact ⟨b, a, by linarith⟩
  rw [hIcc]
  have hint : ∫⁻ u in Icc 0 (cdf ν c), ENNReal.ofReal u ^ k
      = ENNReal.ofReal (cdf ν c ^ (k+1) / (k+1)) := by
    have hcongr : ∫⁻ u in Icc 0 (cdf ν c), ENNReal.ofReal u ^ k
        = ∫⁻ u in Icc 0 (cdf ν c), ENNReal.ofReal (u ^ k) := by
      refine setLIntegral_congr_fun measurableSet_Icc (fun u hu => ?_)
      rw [ENNReal.ofReal_pow hu.1]
    rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h0, integral_pow]
      simp
    · exact (continuous_pow k).integrableOn_Icc
    · exact (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall
        (fun u hu => pow_nonneg hu.1 k))
  rw [hint, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by positivity)
    zero_le_one, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow h0]
  congr 1
  push_cast
  field_simp


lemma Ioc_real (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν] (k : ℕ)
    (a b : ℝ) (hab : a ≤ b) :
    ((k : ℝ≥0∞) + 1) * ∫⁻ y in Ioc a b, ENNReal.ofReal (cdf ν y) ^ k ∂ν
      = ENNReal.ofReal (cdf ν b) ^ (k + 1) - ENNReal.ofReal (cdf ν a) ^ (k + 1) := by
  have hu : ∫⁻ y in Iic b, ENNReal.ofReal (cdf ν y) ^ k ∂ν
      = ∫⁻ y in Iic a, ENNReal.ofReal (cdf ν y) ^ k ∂ν
        + ∫⁻ y in Ioc a b, ENNReal.ofReal (cdf ν y) ^ k ∂ν := by
    rw [← lintegral_union measurableSet_Ioc (Set.disjoint_left.2 (fun x hx hx' => by
      exact absurd hx (not_le.2 hx'.1))), Set.Iic_union_Ioc_eq_Iic hab]
  have hb := H_Iic ν k b
  have ha := H_Iic ν k a
  rw [hu, mul_add, ha] at hb
  have hfin : ENNReal.ofReal (cdf ν a) ^ (k + 1) ≠ ∞ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  exact ENNReal.eq_sub_of_add_eq hfin (by rw [add_comm]; exact hb)

/-- probability-integral-transform identity for the atomless law -/
theorem lintegral_F_pow (D : MultiInterm.Compete.ValueDistribution) (hD : D.zeroMass = 0)
    (k : ℕ) (a b : ℝ≥0) (hab : a ≤ b) :
    ((k : ℝ≥0∞) + 1) * ∫⁻ v in Set.Ioc a b, (D.F v : ℝ≥0∞) ^ k ∂D.law
      = (D.F b : ℝ≥0∞) ^ (k + 1) - (D.F a : ℝ≥0∞) ^ (k + 1) := by
  have hμ : D.law = D.continuousLaw := by
    simp [MultiInterm.Compete.ValueDistribution.law, hD]
  set μ := D.continuousLaw with hμdef
  set ν : Measure ℝ := μ.map (fun x : ℝ≥0 => (x : ℝ)) with hν
  have hmeas : Measurable (fun x : ℝ≥0 => (x : ℝ)) := measurable_coe_nnreal_real
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hmeas.aemeasurable
  have : NullSingletonClass ν := by
    refine ⟨fun y => ?_⟩
    rw [hν, Measure.map_apply hmeas (measurableSet_singleton y)]
    refine measure_mono_null (t := {y.toNNReal}) (fun x hx => ?_) (D.atomless _)
    simp only [mem_preimage, mem_singleton_iff] at hx ⊢
    rw [← hx]; simp
  have hF : ∀ v : ℝ≥0, (D.F v : ℝ≥0∞) = ENNReal.ofReal (cdf ν (v : ℝ)) := by
    intro v
    rw [← ν_Iic, hν, Measure.map_apply hmeas measurableSet_Iic]
    have : (fun x : ℝ≥0 => (x : ℝ)) ⁻¹' Iic (v : ℝ) = Iic v := by
      ext x; simp
    rw [this, MultiInterm.Compete.ValueDistribution.F, hμ, ENNReal.coe_toNNReal (measure_ne_top _ _)]
  simp_rw [hF]
  rw [hμ]
  have key := Ioc_real ν k a b (by exact_mod_cast hab)
  rw [← key]
  congr 1
  rw [hν, setLIntegral_map measurableSet_Ioc ((((cdf_cont ν).measurable.ennreal_ofReal).pow_const k)) hmeas]
  have : (fun x : ℝ≥0 => (x : ℝ)) ⁻¹' Ioc (a : ℝ) b = Ioc a b := by
    ext x; simp
  rw [this]

end MultiInterm.Dev.T
end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MultiInterm.Dev.Tail

section Core

variable (ν : Measure ℝ) [IsProbabilityMeasure ν] (f : ℝ → ℝ≥0∞) (I : Set ℝ)
  (hν : ν = volume.withDensity f) (hI : I.OrdConnected)
  (hpos : ∀ x ∈ I, 0 < f x ∧ f x < ⊤)
  (hmono : MonotoneOn (fun v : ℝ => v - (1 - cdf ν v) / (f v).toReal) I)
  (v0 : ℝ) (hv0 : v0 ∈ I) (c : ℝ) (hc : c = v0 - (1 - cdf ν v0) / (f v0).toReal)
  (hcv : c < v0)

include hν hI hpos hmono hv0 hc hcv

theorem step_ineq (s t : ℝ) (hs : v0 ≤ s) (hst : s < t) (hsI : s ∈ I) (htI : t ∈ I) :
    (t - c) * (1 - cdf ν t) - (s - c) * (1 - cdf ν s) ≤ (t - s) ^ 2 / (v0 - c) := by
  have hg0 : 0 ≤ 1 - cdf ν t := by have := cdf_le_one ν t; linarith
  have hg1 : 1 - cdf ν t ≤ 1 := by have := cdf_nonneg ν t; linarith
  have htc : 0 < t - c := by linarith
  have hd : 0 < v0 - c := by linarith
  obtain ⟨m, hm⟩ : ∃ m, m = (1 - cdf ν t) / (t - c) := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := by rw [hm]; exact div_nonneg hg0 htc.le
  have hgm : 1 - cdf ν t = m * (t - c) := by rw [hm]; field_simp
  have hpt : ∀ v ∈ Set.Ioc s t, ENNReal.ofReal m ≤ f v := by
    intro v hv
    have hvI : v ∈ I := hI.out hsI htI ⟨hv.1.le, hv.2⟩
    obtain ⟨hf0, hftop⟩ := hpos v hvI
    have hq : 0 < (f v).toReal := ENNReal.toReal_pos hf0.ne' hftop.ne
    have h1 : c ≤ v - (1 - cdf ν v) / (f v).toReal := by
      rw [hc]; exact hmono hv0 hvI (by linarith [hv.1])
    have h3 : 1 - cdf ν v ≤ (v - c) * (f v).toReal := by
      rw [← div_le_iff₀ hq]; linarith
    have h4 := monotone_cdf ν hv.2
    have h5 : m ≤ (f v).toReal := by
      rw [hm, div_le_iff₀ htc]
      nlinarith [hv.2]
    calc ENNReal.ofReal m ≤ ENNReal.ofReal (f v).toReal := ENNReal.ofReal_le_ofReal h5
      _ = f v := ENNReal.ofReal_toReal hftop.ne
  have hmeas : ν (Set.Ioc s t) = ENNReal.ofReal (cdf ν t - cdf ν s) := by
    have := (cdf ν).measure_Ioc s t
    rw [measure_cdf] at this
    exact this
  have hlow : ENNReal.ofReal m * ENNReal.ofReal (t - s) ≤ ν (Set.Ioc s t) := by
    rw [hν, withDensity_apply _ measurableSet_Ioc]
    calc ENNReal.ofReal m * ENNReal.ofReal (t - s)
        = ∫⁻ _ in Set.Ioc s t, ENNReal.ofReal m := by
          rw [setLIntegral_const, Real.volume_Ioc]
      _ ≤ _ := setLIntegral_mono' measurableSet_Ioc hpt
  have hreal : m * (t - s) ≤ cdf ν t - cdf ν s := by
    rw [hmeas, ← ENNReal.ofReal_mul hm0] at hlow
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith [monotone_cdf ν hst.le])).1 hlow
  have hmK : m ≤ 1 / (v0 - c) := by
    rw [hm, div_le_div_iff₀ htc hd]
    nlinarith
  have key : (t - c) * (1 - cdf ν t) - (s - c) * (1 - cdf ν s) ≤ m * (t - s) ^ 2 := by
    have h3 := mul_nonneg (show 0 ≤ s - c by linarith)
      (show 0 ≤ (1 - cdf ν s) - (1 - cdf ν t) - m * (t - s) by linarith)
    have e : (t - s) * (1 - cdf ν t) = (t - s) * (m * (t - c)) := by rw [← hgm]
    nlinarith [h3, e]
  calc _ ≤ m * (t - s) ^ 2 := key
    _ ≤ 1 / (v0 - c) * (t - s) ^ 2 :=
        mul_le_mul_of_nonneg_right hmK (sq_nonneg _)
    _ = (t - s) ^ 2 / (v0 - c) := by ring

theorem H_antitone (a b : ℝ) (ha : v0 ≤ a) (hab : a ≤ b) (haI : a ∈ I) (hbI : b ∈ I) :
    (b - c) * (1 - cdf ν b) ≤ (a - c) * (1 - cdf ν a) := by
  rcases hab.eq_or_lt with rfl | hab
  · exact le_rfl
  by_contra hlt
  push Not at hlt
  have hd : 0 < v0 - c := by linarith
  obtain ⟨ε, hε⟩ : ∃ ε, ε = (b - c) * (1 - cdf ν b) - (a - c) * (1 - cdf ν a) :=
    ⟨_, rfl⟩
  have hε0 : 0 < ε := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) ^ 2 / (ε * (v0 - c)))
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  have hN0 : 0 < N := by exact_mod_cast hNpos
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℝ, t = fun i : ℕ => a + (i : ℝ) * (b - a) / N := ⟨_, rfl⟩
  have htm : ∀ i : ℕ, i ≤ N → a ≤ t i ∧ t i ≤ b := by
    intro i hi
    have hi' : (i : ℝ) ≤ N := by exact_mod_cast hi
    rw [ht]
    constructor
    · have : 0 ≤ (i : ℝ) * (b - a) / N := by
        apply div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) hNpos.le
      simp only; linarith
    · have : (i : ℝ) * (b - a) / N ≤ b - a := by
        rw [div_le_iff₀ hNpos]; nlinarith
      simp only; linarith
  have htI : ∀ i : ℕ, i ≤ N → t i ∈ I := fun i hi =>
    hI.out haI hbI ⟨(htm i hi).1, (htm i hi).2⟩
  have hdiff : ∀ i : ℕ, t (i + 1) - t i = (b - a) / N := by
    intro i; rw [ht]; simp only; push_cast; field_simp; ring
  have hstep : ∀ i ∈ Finset.range N,
      (t (i + 1) - c) * (1 - cdf ν (t (i + 1))) - (t i - c) * (1 - cdf ν (t i))
        ≤ ((b - a) / N) ^ 2 / (v0 - c) := by
    intro i hi
    have hi' : i + 1 ≤ N := Finset.mem_range.1 hi
    have hlt' : t i < t (i + 1) := by
      have := hdiff i
      have : 0 < (b - a) / N := div_pos (by linarith) hNpos
      linarith
    have := step_ineq ν f I hν hI hpos hmono v0 hv0 c hc hcv (t i) (t (i + 1))
      (by linarith [(htm i (by omega)).1]) hlt' (htI i (by omega)) (htI (i + 1) hi')
    rw [hdiff i] at this
    exact this
  have hsum := Finset.sum_range_sub
    (fun i => (t i - c) * (1 - cdf ν (t i))) N
  have hle := Finset.sum_le_card_nsmul (Finset.range N) _ _ hstep
  rw [hsum, Finset.card_range, nsmul_eq_mul] at hle
  have htN : t N = b := by rw [ht]; simp only; field_simp; ring
  have ht0 : t 0 = a := by rw [ht]; simp
  simp only [htN, ht0] at hle
  have h1 : (N : ℝ) * (((b - a) / N) ^ 2 / (v0 - c)) = (b - a) ^ 2 / (N * (v0 - c)) := by
    field_simp
  have h2 : (b - a) ^ 2 / (N * (v0 - c)) < ε := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hN
    nlinarith
  linarith

end Core

theorem core_bound (ν : Measure ℝ) [IsProbabilityMeasure ν] (f : ℝ → ℝ≥0∞) (I : Set ℝ)
    (hν : ν = volume.withDensity f) (hI : I.OrdConnected)
    (hpos : ∀ x ∈ I, 0 < f x ∧ f x < ⊤)
    (hmono : MonotoneOn (fun v : ℝ => v - (1 - cdf ν v) / (f v).toReal) I)
    (hne : I.Nonempty) :
    ∃ B : ℝ, ∀ x ∈ I, x * (1 - cdf ν x) ≤ B := by
  obtain ⟨v0, hv0⟩ := hne
  obtain ⟨hf0, hftop⟩ := hpos v0 hv0
  have hq : 0 < (f v0).toReal := ENNReal.toReal_pos hf0.ne' hftop.ne
  have hG0 : 0 ≤ 1 - cdf ν v0 := by have := cdf_le_one ν v0; linarith
  obtain ⟨c, hc⟩ : ∃ c, c = v0 - (1 - cdf ν v0) / (f v0).toReal := ⟨_, rfl⟩
  refine ⟨|v0| + |c| + |v0 - c|, fun x hx => ?_⟩
  have hx0 := cdf_nonneg ν x
  have hx1 := cdf_le_one ν x
  have hv := le_abs_self v0
  have hcab := le_abs_self c
  have hvc := le_abs_self (v0 - c)
  have a1 := abs_nonneg v0
  have a2 := abs_nonneg c
  have a3 := abs_nonneg (v0 - c)
  by_cases hxv : x < v0
  · rcases le_or_gt 0 x with h | h
    · nlinarith [mul_nonneg h hx0]
    · nlinarith [mul_nonneg (neg_nonneg.2 h.le) (show 0 ≤ 1 - cdf ν x by linarith)]
  · push Not at hxv
    have hGx : 1 - cdf ν x ≤ 1 - cdf ν v0 := by linarith [monotone_cdf ν hxv]
    rcases hG0.eq_or_lt with h0 | h0
    · have : 1 - cdf ν x = 0 := by linarith
      rw [this]; simp; linarith
    · have hcv : c < v0 := by
        have : 0 < (1 - cdf ν v0) / (f v0).toReal := div_pos h0 hq
        linarith
      have hH := H_antitone ν f I hν hI hpos hmono v0 hv0 c hc hcv v0 x le_rfl hxv hv0 hx
      have hG1 : 1 - cdf ν v0 ≤ 1 := by linarith [cdf_nonneg ν v0]
      have : (v0 - c) * (1 - cdf ν v0) ≤ v0 - c := by nlinarith
      have hcG : c * (1 - cdf ν x) ≤ |c| := by
        have := mul_le_mul_of_nonneg_right hcab (show 0 ≤ 1 - cdf ν x by linarith)
        nlinarith [abs_nonneg c]
      nlinarith

/-- regular laws have v(1-F(v)) bounded (revenue curve is bounded) -/
theorem mul_one_sub_F_bounded (D : MultiInterm.Compete.ValueDistribution) (hD : D.zeroMass = 0) :
    ∃ C : ℝ≥0, ∀ᵐ (v : ℝ≥0) ∂D.law, (v : ℝ≥0∞) * (1 - (D.F v : ℝ≥0∞)) ≤ C := by
  obtain ⟨_, f, I, hfm, hmap, hI, hIoc, hpos, hmono⟩ := D.regular
  have hcoe : Measurable (fun x : ℝ≥0 => (x : ℝ)) := by fun_prop
  have : IsProbabilityMeasure (D.continuousLaw.map (fun x : ℝ≥0 => (x : ℝ))) :=
    Measure.isProbabilityMeasure_map hcoe.aemeasurable
  have hne : I.Nonempty := by
    rcases Set.eq_empty_or_nonempty I with h | h
    · exfalso
      rw [h, Set.compl_empty, measure_univ] at hIoc
      exact one_ne_zero hIoc
    · exact h
  obtain ⟨B, hB⟩ := core_bound _ f I hmap hI hpos hmono hne
  have hae : ∀ᵐ x : ℝ≥0 ∂D.continuousLaw, (x : ℝ) ∈ I := by
    rw [ae_iff]
    rw [Measure.map_apply hcoe hI.measurableSet.compl] at hIoc
    exact hIoc
  have hpt : ∀ x : ℝ≥0, (x : ℝ) ∈ I →
      (x : ℝ≥0∞) * (1 - (D.F x : ℝ≥0∞)) ≤ ((max B 0).toNNReal : ℝ≥0∞) := by
    intro x hx
    have hmeasIic : D.continuousLaw (Set.Iic x : Set ℝ≥0) ≠ ⊤ := measure_ne_top _ _
    have hcdf : cdf (D.continuousLaw.map (fun x : ℝ≥0 => (x : ℝ))) x
        = (D.continuousLaw (Set.Iic x : Set ℝ≥0)).toReal := by
      rw [cdf_eq_real, Measure.real, Measure.map_apply hcoe measurableSet_Iic]
      congr 2
    have hlaw : D.law (Set.Iic x : Set ℝ≥0) = (D.zeroMass : ℝ≥0∞) +
        ((1 - D.zeroMass : ℝ≥0) : ℝ≥0∞) * D.continuousLaw (Set.Iic x : Set ℝ≥0) := by
      simp [MultiInterm.Compete.ValueDistribution.law, Measure.dirac_apply' _ measurableSet_Iic]
    have hFreal : (D.F x : ℝ) = D.zeroMass + (1 - (D.zeroMass : ℝ)) *
        (D.continuousLaw (Set.Iic x : Set ℝ≥0)).toReal := by
      have hlt := D.zeroMass_lt_one
      have hle : D.zeroMass ≤ 1 := hlt.le
      unfold MultiInterm.Compete.ValueDistribution.F
      rw [ENNReal.coe_toNNReal_eq_toReal, hlaw, ENNReal.toReal_add (by simp)
        (ENNReal.mul_ne_top (by simp) hmeasIic), ENNReal.toReal_mul]
      simp only [ENNReal.coe_toReal, NNReal.coe_sub hle, NNReal.coe_one]
    have hF1 : D.F x ≤ 1 := by
      unfold MultiInterm.Compete.ValueDistribution.F
      have : D.law (Set.Iic x : Set ℝ≥0) ≤ 1 := prob_le_one
      simpa using ENNReal.toNNReal_mono (by simp) this
    have hBx := hB x hx
    rw [hcdf] at hBx
    have hp0 := ENNReal.toReal_nonneg (a := D.continuousLaw (Set.Iic x : Set ℝ≥0))
    have hp1 : (D.continuousLaw (Set.Iic x : Set ℝ≥0)).toReal ≤ 1 := by
      have := cdf_le_one (D.continuousLaw.map (fun x : ℝ≥0 => (x : ℝ))) x
      rwa [hcdf] at this
    have hz0 : (0 : ℝ) ≤ D.zeroMass := D.zeroMass.2
    have hz1 : (D.zeroMass : ℝ) < 1 := by exact_mod_cast D.zeroMass_lt_one
    have hx0 : (0 : ℝ) ≤ x := x.2
    rw [← ENNReal.coe_one, ← ENNReal.coe_sub, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_sub hF1, hFreal]
    simp only [NNReal.coe_one, Real.coe_toNNReal', ]
    have h1 : (x : ℝ) * (1 - (D.zeroMass + (1 - (D.zeroMass : ℝ)) *
        (D.continuousLaw (Set.Iic x : Set ℝ≥0)).toReal))
        ≤ x * (1 - (D.continuousLaw (Set.Iic x : Set ℝ≥0)).toReal) := by
      apply mul_le_mul_of_nonneg_left _ hx0
      nlinarith
    exact h1.trans (hBx.trans (le_max_of_le_left (le_max_left _ _)))
  refine ⟨(max B 0).toNNReal, ?_⟩
  unfold MultiInterm.Compete.ValueDistribution.law
  rw [ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    rw [ae_dirac_eq]
    simp
  · apply Measure.ae_smul_measure
    filter_upwards [hae] with x hx using hpt x hx

end MultiInterm.Dev.Tail
end

section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MultiInterm.Dev.C1

open MultiInterm.Compete

noncomputable def Phi (m : ℕ) (t : ℝ) : ℝ := ((m:ℝ)+3) * t^(m+2) - ((m:ℝ)+2) * t^(m+3)

noncomputable def Wf (D : ValueDistribution) (m : ℕ) (v : ℝ≥0) : ℝ≥0∞ :=
  (1 - (D.F v : ℝ≥0∞)) * (D.F v : ℝ≥0∞)^(m+1)

noncomputable def Iint (D : ValueDistribution) (m : ℕ) (c : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ v in Set.Ioi c, (v : ℝ≥0∞) * Wf D m v ∂D.law

variable (D : ValueDistribution)

lemma F_le_one (v : ℝ≥0) : D.F v ≤ 1 := by
  unfold ValueDistribution.F
  have : D.law (Set.Iic v) ≤ 1 := prob_le_one
  simpa using ENNReal.toNNReal_mono (by simp) this

lemma F_mono : Monotone D.F := by
  intro a b hab
  unfold ValueDistribution.F
  exact ENNReal.toNNReal_mono (measure_ne_top _ _) (measure_mono (Set.Iic_subset_Iic.2 hab))

lemma F_meas : Measurable D.F := (F_mono D).measurable

lemma Fe_meas : Measurable fun v => (D.F v : ℝ≥0∞) := (F_meas D).coe_nnreal_ennreal

lemma Wf_meas (m : ℕ) : Measurable (Wf D m) :=
  (measurable_const.sub (Fe_meas D)).mul ((Fe_meas D).pow_const _)

lemma R_eq (m : ℕ) (c : ℝ≥0) :
    R D (m+3) c = ((m:ℝ≥0∞)+3) * c * (1 - (D.F c : ℝ≥0∞)) * (D.F c : ℝ≥0∞)^(m+2)
      + (((m:ℝ≥0∞)+3) * ((m:ℝ≥0∞)+2)) * Iint D m c := by
  unfold R Iint Wf
  have e1 : m+3-1 = m+2 := by omega
  have e2 : m+3-2 = m+1 := by omega
  rw [e1, e2]
  push_cast
  simp only [mul_assoc]

lemma Wint (hD : D.zeroMass = 0) (m : ℕ) (a b : ℝ≥0) (hab : a ≤ b) :
    (((m:ℝ≥0∞)+3) * ((m:ℝ≥0∞)+2)) * ∫⁻ v in Set.Ioc a b, Wf D m v ∂D.law
      = ENNReal.ofReal (Phi m (D.F b) - Phi m (D.F a)) := by
  have h1 := MultiInterm.Dev.T.lintegral_F_pow D hD (m+1) a b hab
  have h2 := MultiInterm.Dev.T.lintegral_F_pow D hD (m+2) a b hab
  have hFab : (D.F a : ℝ≥0∞) ≤ D.F b := by exact_mod_cast F_mono D hab
  have hLK : ∫⁻ v in Set.Ioc a b, Wf D m v ∂D.law
      + ∫⁻ v in Set.Ioc a b, (D.F v : ℝ≥0∞)^(m+2) ∂D.law
      = ∫⁻ v in Set.Ioc a b, (D.F v : ℝ≥0∞)^(m+1) ∂D.law := by
    rw [← lintegral_add_left (Wf_meas D m)]
    refine lintegral_congr (fun v => ?_)
    have hle : (D.F v : ℝ≥0∞) ≤ 1 := by exact_mod_cast F_le_one D v
    have e : (D.F v : ℝ≥0∞)^(m+2) = (D.F v : ℝ≥0∞) * (D.F v : ℝ≥0∞)^(m+1) := by ring
    calc _ = ((1 - (D.F v:ℝ≥0∞)) + D.F v) * (D.F v:ℝ≥0∞)^(m+1) := by
          rw [add_mul, e]; rfl
      _ = _ := by rw [tsub_add_cancel_of_le hle, one_mul]
  set L := ∫⁻ v in Set.Ioc a b, Wf D m v ∂D.law with hL
  set J := ∫⁻ v in Set.Ioc a b, (D.F v : ℝ≥0∞)^(m+1) ∂D.law with hJ
  set K := ∫⁻ v in Set.Ioc a b, (D.F v : ℝ≥0∞)^(m+2) ∂D.law with hK
  have hJt : J ≠ ⊤ := by
    intro h; rw [h, ENNReal.mul_top (by simp)] at h1
    exact ENNReal.sub_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) h1.symm
  have hKt : K ≠ ⊤ := by
    intro h; rw [h, ENNReal.mul_top (by simp)] at h2
    exact ENNReal.sub_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top) h2.symm
  have hLt : L ≠ ⊤ := ne_top_of_le_ne_top hJt (by rw [← hLK]; exact le_self_add)
  have e1 : ((m:ℝ)+2) * J.toReal = (D.F b:ℝ)^(m+2) - (D.F a:ℝ)^(m+2) := by
    have := congrArg ENNReal.toReal h1
    have c1 : (((m+1:ℕ):ℝ≥0∞)+1).toReal = (m:ℝ)+2 := by
      rw [ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_natCast]; simp; ring
    rw [ENNReal.toReal_mul, c1, ENNReal.toReal_sub_of_le (by gcongr) (ENNReal.pow_ne_top ENNReal.coe_ne_top),
      ENNReal.toReal_pow, ENNReal.toReal_pow] at this
    simpa using this
  have e2 : ((m:ℝ)+3) * K.toReal = (D.F b:ℝ)^(m+3) - (D.F a:ℝ)^(m+3) := by
    have := congrArg ENNReal.toReal h2
    have c1 : (((m+2:ℕ):ℝ≥0∞)+1).toReal = (m:ℝ)+3 := by
      rw [ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_natCast]; simp; ring
    rw [ENNReal.toReal_mul, c1, ENNReal.toReal_sub_of_le (by gcongr) (ENNReal.pow_ne_top ENNReal.coe_ne_top),
      ENNReal.toReal_pow, ENNReal.toReal_pow] at this
    simpa using this
  have e3 : L.toReal + K.toReal = J.toReal := by
    rw [← ENNReal.toReal_add hLt hKt, hLK]
  have hfin : (((m:ℝ≥0∞)+3) * ((m:ℝ≥0∞)+2)) * L ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) hLt
  rw [← ENNReal.ofReal_toReal hfin]
  congr 1
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp only [ENNReal.toReal_add, ENNReal.toReal_natCast, ENNReal.toReal_ofNat, ENNReal.natCast_ne_top,
    ne_eq, not_false_eq_true, ENNReal.ofNat_ne_top]
  unfold Phi
  have : L.toReal = J.toReal - K.toReal := by linarith
  rw [this]
  linear_combination ((m:ℝ)+3) * e1 - ((m:ℝ)+2) * e2

lemma hFlim : Tendsto (fun k : ℕ => ((D.F (k:ℝ≥0) : ℝ≥0) : ℝ)) atTop (nhds 1) := by
  have h1 : Tendsto (fun x : ℝ≥0 => D.law (Set.Iic x)) atTop (nhds (D.law Set.univ)) :=
    tendsto_measure_Iic_atTop _
  rw [measure_univ] at h1
  have h2 := h1.comp tendsto_natCast_atTop_atTop
  have h3 := (ENNReal.tendsto_toNNReal ENNReal.one_ne_top).comp h2
  simpa [ValueDistribution.F, Function.comp_def] using (NNReal.tendsto_coe.2 h3)

lemma Iinf (hD : D.zeroMass = 0) (m : ℕ) (τ : ℝ≥0) :
    ENNReal.ofReal (1 - Phi m (D.F τ)) ≤
      (((m:ℝ≥0∞)+3) * ((m:ℝ≥0∞)+2)) * ∫⁻ v in Set.Ioi τ, Wf D m v ∂D.law := by
  have hT : Tendsto (fun k : ℕ => ENNReal.ofReal (Phi m (D.F (k:ℝ≥0)) - Phi m (D.F τ))) atTop
      (𝓝 (ENNReal.ofReal (1 - Phi m (D.F τ)))) := by
    apply ENNReal.tendsto_ofReal
    apply Tendsto.sub_const
    have hPhi : Continuous (Phi m) := by unfold Phi; fun_prop
    have := (hPhi.tendsto 1).comp (hFlim D)
    have e : Phi m 1 = 1 := by unfold Phi; simp; ring
    rw [e] at this
    exact this
  refine le_of_tendsto hT ?_
  filter_upwards [eventually_ge_atTop ⌈τ⌉₊] with k hk
  have hτk : τ ≤ (k:ℝ≥0) := (Nat.le_ceil τ).trans (by exact_mod_cast hk)
  rw [← Wint D hD m τ k hτk]
  gcongr
  exact Set.Ioc_subset_Ioi_self

lemma real_ineq (m : ℕ) (x p q s : ℝ) (hx : 0 ≤ x) (hs0 : 0 ≤ s) (hsp : s ≤ p) (hp0 : 0 ≤ p)
    (hpq : p ≤ q) (hq : q ≤ 1) :
    x * (((m:ℝ)+3) * (1-q) * q^(2*m+4)) ≤
      ((m:ℝ)+3) * (x * p^(m+2)) * (1 - s) * s^(m+2)
      + (x * p^(m+2)) * (Phi m p - Phi m s) + x * (Phi m q - Phi m p) := by
  have hH := MultiInterm.Dev.AlgC1.H_anti (m+3) (by omega) p q hp0 hpq hq
  have hHe : ∀ t : ℝ, MultiInterm.Dev.AlgC1.H (m+3) t
      = 1 - Phi m t + ((m:ℝ)+3) * (1-t) * t^(2*m+4) := by
    intro t
    have e1 : m+3-1 = m+2 := by omega
    have e2 : 2*(m+3)-2 = 2*m+4 := by omega
    simp only [MultiInterm.Dev.AlgC1.H, e1, e2, Phi]; push_cast; ring
  rw [hHe, hHe] at hH
  have hpow : s^(m+3) ≤ p^(m+3) := pow_le_pow_left₀ hs0 hsp _
  have hc : 0 ≤ x * p^(m+2) := by positivity
  have k1 : (x*p^(m+2)) * (Phi m p - p^(m+3)) ≤ (x*p^(m+2)) * (Phi m p - s^(m+3)) :=
    mul_le_mul_of_nonneg_left (by linarith) hc
  have k2 : x * (((m:ℝ)+3) * (1-q) * q^(2*m+4)) ≤
      x * (((m:ℝ)+3) * (1-p) * p^(2*m+4) + Phi m q - Phi m p) :=
    mul_le_mul_of_nonneg_left (by linarith) hx
  have eq1 : ((m:ℝ)+3) * (x * p^(m+2)) * (1 - s) * s^(m+2)
      + (x * p^(m+2)) * (Phi m p - Phi m s) + x * (Phi m q - Phi m p)
      = (x*p^(m+2)) * (Phi m p - s^(m+3)) + x * (Phi m q - Phi m p) := by
    unfold Phi; ring
  have eq2 : (x*p^(m+2)) * (Phi m p - p^(m+3)) = x * (((m:ℝ)+3) * (1-p) * p^(2*m+4)) := by
    unfold Phi; ring
  rw [eq1]
  nlinarith [k1, k2, eq2]

lemma Iint_ge (m : ℕ) (c x τ : ℝ≥0) (hcx : c ≤ x) (hxτ : x ≤ τ) :
    (c:ℝ≥0∞) * ∫⁻ v in Set.Ioc c x, Wf D m v ∂D.law
      + (x:ℝ≥0∞) * ∫⁻ v in Set.Ioc x τ, Wf D m v ∂D.law + Iint D m τ ≤ Iint D m c := by
  have hdis : ∀ a b : ℝ≥0, Disjoint (Set.Ioc a b) (Set.Ioi b) := fun a b =>
    Set.disjoint_left.2 fun v h1 h2 => absurd h1.2 (not_le.2 h2)
  have hsplit : Iint D m c = ∫⁻ v in Set.Ioc c x, (v:ℝ≥0∞) * Wf D m v ∂D.law
      + (∫⁻ v in Set.Ioc x τ, (v:ℝ≥0∞) * Wf D m v ∂D.law + Iint D m τ) := by
    unfold Iint
    rw [← lintegral_union measurableSet_Ioi (hdis x τ), Set.Ioc_union_Ioi_eq_Ioi hxτ,
      ← lintegral_union measurableSet_Ioi (hdis c x), Set.Ioc_union_Ioi_eq_Ioi hcx]
  have b : ∀ a b : ℝ≥0, a ≤ b → ∀ S : Set ℝ≥0, MeasurableSet S → (∀ v ∈ S, a ≤ v) →
      (a:ℝ≥0∞) * ∫⁻ v in S, Wf D m v ∂D.law ≤ ∫⁻ v in S, (v:ℝ≥0∞) * Wf D m v ∂D.law := by
    intro a b _ S hS hav
    rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    refine setLIntegral_mono' hS (fun v hv => ?_)
    gcongr
    exact_mod_cast hav v hv
  have b1 := b c x hcx (Set.Ioc c x) measurableSet_Ioc (fun v hv => hv.1.le)
  have b2 := b x τ hxτ (Set.Ioc x τ) measurableSet_Ioc (fun v hv => hv.1.le)
  rw [hsplit, add_assoc]
  exact add_le_add b1 (add_le_add b2 le_rfl)

lemma Iint_tau (m : ℕ) (τ : ℝ≥0) :
    (τ:ℝ≥0∞) * ∫⁻ v in Set.Ioi τ, Wf D m v ∂D.law ≤ Iint D m τ := by
  unfold Iint
  rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine setLIntegral_mono' measurableSet_Ioi (fun v hv => ?_)
  gcongr
  exact_mod_cast hv.le

lemma Ifin (hD : D.zeroMass = 0) (m : ℕ) (τ : ℝ≥0) : Iint D m τ ≠ ⊤ := by
  obtain ⟨C, hC⟩ := MultiInterm.Dev.Tail.mul_one_sub_F_bounded D hD
  have : Iint D m τ ≤ ∫⁻ v in Set.Ioi τ, (C:ℝ≥0∞) ∂D.law := by
    unfold Iint
    refine lintegral_mono_ae (ae_restrict_of_ae (hC.mono fun v hv => ?_))
    have hle : (D.F v : ℝ≥0∞) ^ (m+1) ≤ 1 :=
      pow_le_one₀ zero_le (by exact_mod_cast F_le_one D v)
    calc (v:ℝ≥0∞) * Wf D m v = ((v:ℝ≥0∞) * (1 - (D.F v : ℝ≥0∞))) * (D.F v:ℝ≥0∞)^(m+1) := by
          unfold Wf; ring
      _ ≤ C * 1 := mul_le_mul' hv hle
      _ = C := mul_one _
  refine ne_top_of_le_ne_top ?_ this
  rw [setLIntegral_const]
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _)

lemma law_eq (hD : D.zeroMass = 0) : D.law = D.continuousLaw := by
  simp [ValueDistribution.law, hD]

lemma F_pos (hD : D.zeroMass = 0) (τ : ℝ≥0) (hτ : 0 < τ) : 0 < (D.F τ : ℝ) := by
  have h := D.full_support 0 τ hτ (by simpa using D.upper_pos)
  rw [← law_eq D hD] at h
  have h2 : 0 < D.law (Set.Iic τ) := lt_of_lt_of_le h (measure_mono (fun v hv => le_of_lt hv.2))
  have : 0 < D.F τ := ENNReal.toNNReal_pos h2.ne' (measure_ne_top _ _)
  exact_mod_cast this

lemma F_lt_one (hD : D.zeroMass = 0) (τ : ℝ≥0) (hτv : (τ:ℝ≥0∞) < D.upper) : (D.F τ : ℝ) < 1 := by
  have h := D.full_support τ (τ+1) (by simp) hτv
  rw [← law_eq D hD] at h
  have hcompl := measure_add_measure_compl (μ := D.law) (measurableSet_Iic (a := τ))
  rw [Set.compl_Iic, measure_univ] at hcompl
  have h2 : 0 < D.law (Set.Ioi τ) := lt_of_lt_of_le h (measure_mono (fun v hv => hv.1))
  have h3 := congrArg ENNReal.toReal hcompl
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h3
  have hp : 0 < (D.law (Set.Ioi τ)).toReal := ENNReal.toReal_pos h2.ne' (measure_ne_top _ _)
  have h4 : (D.F τ : ℝ) = (D.law (Set.Iic τ)).toReal := by
    exact ENNReal.coe_toNNReal_eq_toReal _
  simp at h3
  linarith

lemma R_ge (hD : D.zeroMass = 0) (m : ℕ) (τ x : ℝ≥0) (hxτ : x ≤ τ) :
    ENNReal.ofReal ((x:ℝ) * (((m:ℝ)+3) * (1 - (D.F τ:ℝ)) * (D.F τ:ℝ)^(2*m+4))) +
      (((m:ℝ≥0∞)+3) * ((m:ℝ≥0∞)+2)) * Iint D m τ ≤ R D (m+3) (g D (m+3) x) := by
  set c : ℝ≥0 := g D (m+3) x with hc
  have hcdef : c = x * D.F x ^ (m+2) := by
    have e1 : m+3-1 = m+2 := by omega
    simp only [hc, g, e1]
  have hFx1 := F_le_one D x
  have hcx : c ≤ x := by
    rw [hcdef]; exact mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le hFx1)
  have hFc := F_mono D hcx
  have hFxτ := F_mono D hxτ
  have hFτ1 := F_le_one D τ
  rw [R_eq]
  have hI := Iint_ge D m c x τ hcx hxτ
  have hW1 := Wint D hD m c x hcx
  have hW2 := Wint D hD m x τ hxτ
  have hcreal : (c:ℝ) = x * (D.F x : ℝ)^(m+2) := by rw [hcdef]; push_cast; ring
  have hE := real_ineq m x (D.F x) (D.F τ) (D.F c) x.2 (D.F c).2 (by exact_mod_cast hFc)
    (D.F x).2 (by exact_mod_cast hFxτ) (by exact_mod_cast hFτ1)
  rw [← hcreal] at hE
  have hs1 : (0:ℝ) ≤ 1 - (D.F c : ℝ) := by
    have : (D.F c : ℝ) ≤ 1 := by exact_mod_cast F_le_one D c
    linarith
  have t1 : ENNReal.ofReal (((m:ℝ)+3) * c * (1 - (D.F c:ℝ)) * (D.F c:ℝ)^(m+2))
      = ((m:ℝ≥0∞)+3) * c * (1 - (D.F c:ℝ≥0∞)) * (D.F c:ℝ≥0∞)^(m+2) := by
    have hc0 : (0:ℝ) ≤ c := c.coe_nonneg
    have hm3 : (0:ℝ) ≤ (m:ℝ)+3 := by positivity
    rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hm3 hc0) hs1),
      ENNReal.ofReal_mul (mul_nonneg hm3 hc0), ENNReal.ofReal_mul hm3,
      ENNReal.ofReal_pow (D.F c).coe_nonneg, ENNReal.ofReal_sub _ (D.F c).coe_nonneg]
    simp [ENNReal.ofReal_add]
  have t2 : ENNReal.ofReal ((c:ℝ) * (Phi m (D.F x) - Phi m (D.F c)))
      = (c:ℝ≥0∞) * ((((m:ℝ≥0∞)+3) * ((m:ℝ≥0∞)+2)) * ∫⁻ v in Set.Ioc c x, Wf D m v ∂D.law) := by
    rw [hW1, ENNReal.ofReal_mul c.coe_nonneg]; simp
  have t3 : ENNReal.ofReal ((x:ℝ) * (Phi m (D.F τ) - Phi m (D.F x)))
      = (x:ℝ≥0∞) * ((((m:ℝ≥0∞)+3) * ((m:ℝ≥0∞)+2)) * ∫⁻ v in Set.Ioc x τ, Wf D m v ∂D.law) := by
    rw [hW2, ENNReal.ofReal_mul x.coe_nonneg]; simp
  have hsum : ENNReal.ofReal ((x:ℝ) * (((m:ℝ)+3) * (1 - (D.F τ:ℝ)) * (D.F τ:ℝ)^(2*m+4)))
      ≤ ((m:ℝ≥0∞)+3) * c * (1 - (D.F c:ℝ≥0∞)) * (D.F c:ℝ≥0∞)^(m+2)
        + (c:ℝ≥0∞) * ((((m:ℝ≥0∞)+3) * ((m:ℝ≥0∞)+2)) * ∫⁻ v in Set.Ioc c x, Wf D m v ∂D.law)
        + (x:ℝ≥0∞) * ((((m:ℝ≥0∞)+3) * ((m:ℝ≥0∞)+2)) * ∫⁻ v in Set.Ioc x τ, Wf D m v ∂D.law) := by
    rw [← t1, ← t2, ← t3]
    refine (ENNReal.ofReal_le_ofReal hE).trans ?_
    exact ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)
  calc _ ≤ (((m:ℝ≥0∞)+3) * c * (1 - (D.F c:ℝ≥0∞)) * (D.F c:ℝ≥0∞)^(m+2)
        + (c:ℝ≥0∞) * ((((m:ℝ≥0∞)+3) * ((m:ℝ≥0∞)+2)) * ∫⁻ v in Set.Ioc c x, Wf D m v ∂D.law)
        + (x:ℝ≥0∞) * ((((m:ℝ≥0∞)+3) * ((m:ℝ≥0∞)+2)) * ∫⁻ v in Set.Ioc x τ, Wf D m v ∂D.law))
        + (((m:ℝ≥0∞)+3) * ((m:ℝ≥0∞)+2)) * Iint D m τ := by gcongr
    _ = ((m:ℝ≥0∞)+3) * c * (1 - (D.F c:ℝ≥0∞)) * (D.F c:ℝ≥0∞)^(m+2)
        + (((m:ℝ≥0∞)+3) * ((m:ℝ≥0∞)+2)) *
          ((c:ℝ≥0∞) * ∫⁻ v in Set.Ioc c x, Wf D m v ∂D.law
            + (x:ℝ≥0∞) * ∫⁻ v in Set.Ioc x τ, Wf D m v ∂D.law + Iint D m τ) := by ring
    _ ≤ _ := by gcongr


lemma ofReal_first (m : ℕ) (c s : ℝ≥0) (hs : s ≤ 1) :
    ENNReal.ofReal (((m:ℝ)+3) * c * (1 - (s:ℝ)) * (s:ℝ)^(m+2))
      = ((m:ℝ≥0∞)+3) * c * (1 - (s:ℝ≥0∞)) * (s:ℝ≥0∞)^(m+2) := by
  have hs1 : (0:ℝ) ≤ 1 - (s : ℝ) := by
    have : (s : ℝ) ≤ 1 := by exact_mod_cast hs
    linarith
  have hc0 : (0:ℝ) ≤ c := c.coe_nonneg
  have hm3 : (0:ℝ) ≤ (m:ℝ)+3 := by positivity
  rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hm3 hc0) hs1),
    ENNReal.ofReal_mul (mul_nonneg hm3 hc0), ENNReal.ofReal_mul hm3,
    ENNReal.ofReal_pow s.coe_nonneg, ENNReal.ofReal_sub _ s.coe_nonneg]
  simp [ENNReal.ofReal_add]

lemma final_ineq (m : ℕ) (τ x y q a : ℝ) (hτ : 0 < τ) (hq0 : 0 < q) (hq1 : q < 1)
    (hxy : 4 * τ * q^(m+2) / (1 + q^(m+2)) ≤ x + y) (ha : τ * (1 - Phi m q) ≤ a) :
    τ * (((m:ℝ)+3) * (1 - q) * q^(m+2)) <
      x * (((m:ℝ)+3) * (1 - q) * q^(2*m+4)) + y * (((m:ℝ)+3) * (1 - q) * q^(2*m+4)) + a := by
  have key := MultiInterm.Dev.AlgC1.eq15_pos (m+3) (by omega) q hq0 hq1
  have e1 : m+3-1 = m+2 := by omega
  have e3 : 3*(m+3)-3 = 3*(m+2) := by omega
  rw [e1, e3] at key
  push_cast at key
  have p1 : q^(m+3) = q * q^(m+2) := by ring
  have p2 : q^(3*(m+2)) = (q^(m+2))^3 := by ring
  have p3 : q^(2*m+4) = (q^(m+2))^2 := by ring
  rw [p1, p2] at key
  unfold Phi at ha
  rw [p1] at ha
  rw [p3]
  have hz : 0 < q^(m+2) := pow_pos hq0 _
  generalize q^(m+2) = z at *
  have hq' : 0 ≤ 1 - q := by linarith
  have hlow : 4 * τ * z / (1 + z) * (((m:ℝ)+3) * (1 - q) * z^2)
      ≤ (x + y) * (((m:ℝ)+3) * (1 - q) * z^2) :=
    mul_le_mul_of_nonneg_right hxy (by positivity)
  have heq : 4 * τ * z / (1 + z) * (((m:ℝ)+3) * (1 - q) * z^2)
      = τ * (4 * ((m:ℝ)+3) * (1 - q) * z^3 / (1 + z)) := by
    field_simp
  have hk := mul_pos hτ key
  nlinarith [hlow, heq, hk, ha]

end MultiInterm.Dev.C1

namespace MultiInterm.Compete

open MultiInterm.Dev.C1 in
theorem chk_lemma_C_1 (D : ValueDistribution) (hD : D.zeroMass = 0) (n : ℕ) (hn : 3 ≤ n)
    (τ x y : ℝ≥0) (hτ : 0 < τ) (hτv : (τ : ℝ≥0∞) < D.upper)
    (hx : 0 < x ∧ x ≤ τ) (hy : 0 < y ∧ y ≤ τ)
    (hxy : 4 * τ * D.F τ ^ (n - 1) / (1 + D.F τ ^ (n - 1)) ≤ x + y) :
    R D n τ < R D n (g D n x) + R D n (g D n y) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e1 : m+3-1 = m+2 := by omega
  rw [e1] at hxy
  have hq0 := F_pos D hD τ hτ
  have hq1 := F_lt_one D hD τ hτv
  have hX := R_ge D hD m τ x hx.2
  have hY := R_ge D hD m τ y hy.2
  have hNt : (((m:ℝ≥0∞)+3) * ((m:ℝ≥0∞)+2)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (by simp)
  have hAfin := ENNReal.mul_ne_top hNt (Ifin D hD m τ)
  obtain ⟨a, ha0, hA⟩ : ∃ a : ℝ, 0 ≤ a ∧
      (((m:ℝ≥0∞)+3) * ((m:ℝ≥0∞)+2)) * Iint D m τ = ENNReal.ofReal a :=
    ⟨_, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hAfin).symm⟩
  rw [hA] at hX hY
  have ha : (τ:ℝ) * (1 - Phi m (D.F τ)) ≤ a := by
    have h1 := Iinf D hD m τ
    have h2 := Iint_tau D m τ
    have h3 : ENNReal.ofReal ((τ:ℝ) * (1 - Phi m (D.F τ))) ≤ ENNReal.ofReal a := by
      rw [← hA, ENNReal.ofReal_mul τ.coe_nonneg]
      simp only [ENNReal.ofReal_coe_nnreal]
      calc (τ:ℝ≥0∞) * ENNReal.ofReal (1 - Phi m (D.F τ))
          ≤ (τ:ℝ≥0∞) * ((((m:ℝ≥0∞)+3) * ((m:ℝ≥0∞)+2)) * ∫⁻ v in Set.Ioi τ, Wf D m v ∂D.law) := by
            gcongr
        _ = (((m:ℝ≥0∞)+3) * ((m:ℝ≥0∞)+2)) * ((τ:ℝ≥0∞) * ∫⁻ v in Set.Ioi τ, Wf D m v ∂D.law) := by
            ring
        _ ≤ _ := by gcongr
    exact (ENNReal.ofReal_le_ofReal_iff ha0).1 h3
  have hqn : (0:ℝ) ≤ 1 - (D.F τ:ℝ) := by linarith
  have hm3 : (0:ℝ) ≤ (m:ℝ)+3 := by positivity
  have hRτ : R D (m+3) τ = ENNReal.ofReal ((τ:ℝ) * (((m:ℝ)+3) * (1 - (D.F τ:ℝ)) * (D.F τ:ℝ)^(m+2)))
      + ENNReal.ofReal a := by
    rw [R_eq, hA]
    congr 1
    have : (τ:ℝ) * (((m:ℝ)+3) * (1 - (D.F τ:ℝ)) * (D.F τ:ℝ)^(m+2))
        = ((m:ℝ)+3) * τ * (1 - (D.F τ:ℝ)) * (D.F τ:ℝ)^(m+2) := by ring
    rw [this, ofReal_first m τ (D.F τ) (F_le_one D τ)]
  have hxy' : 4 * (τ:ℝ) * (D.F τ:ℝ)^(m+2) / (1 + (D.F τ:ℝ)^(m+2)) ≤ x + y := by
    have := NNReal.coe_le_coe.2 hxy
    push_cast at this
    exact this
  have hfin := final_ineq m τ x y (D.F τ) a (by exact_mod_cast hτ) hq0 hq1 hxy' ha
  have hB : 0 ≤ ((m:ℝ)+3) * (1 - (D.F τ:ℝ)) * (D.F τ:ℝ)^(2*m+4) :=
    mul_nonneg (mul_nonneg hm3 hqn) (pow_nonneg (D.F τ).coe_nonneg _)
  have hr : 0 ≤ (τ:ℝ) * (((m:ℝ)+3) * (1 - (D.F τ:ℝ)) * (D.F τ:ℝ)^(m+2)) :=
    mul_nonneg τ.coe_nonneg (mul_nonneg (mul_nonneg hm3 hqn) (pow_nonneg (D.F τ).coe_nonneg _))
  have htx := mul_nonneg x.coe_nonneg hB
  have hty := mul_nonneg y.coe_nonneg hB
  rw [hRτ]
  calc _ = ENNReal.ofReal ((τ:ℝ) * (((m:ℝ)+3) * (1 - (D.F τ:ℝ)) * (D.F τ:ℝ)^(m+2)) + a) :=
        (ENNReal.ofReal_add hr ha0).symm
    _ < ENNReal.ofReal (((x:ℝ) * (((m:ℝ)+3) * (1 - (D.F τ:ℝ)) * (D.F τ:ℝ)^(2*m+4)) + a)
          + ((y:ℝ) * (((m:ℝ)+3) * (1 - (D.F τ:ℝ)) * (D.F τ:ℝ)^(2*m+4)) + a)) := by
        rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)]
        linarith
    _ = (ENNReal.ofReal ((x:ℝ) * (((m:ℝ)+3) * (1 - (D.F τ:ℝ)) * (D.F τ:ℝ)^(2*m+4))) + ENNReal.ofReal a)
          + (ENNReal.ofReal ((y:ℝ) * (((m:ℝ)+3) * (1 - (D.F τ:ℝ)) * (D.F τ:ℝ)^(2*m+4))) + ENNReal.ofReal a) := by
        rw [ENNReal.ofReal_add (by linarith) (by linarith), ENNReal.ofReal_add htx ha0,
          ENNReal.ofReal_add hty ha0]
    _ ≤ _ := add_le_add hX hY

end MultiInterm.Compete
end

theorem solution : type_of% @MultiInterm.Compete.chk_lemma_C_1 := @MultiInterm.Compete.chk_lemma_C_1
