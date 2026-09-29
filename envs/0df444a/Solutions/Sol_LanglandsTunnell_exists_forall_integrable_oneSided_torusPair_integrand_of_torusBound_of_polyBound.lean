-- Prove2me | solution 1 for LanglandsTunnell.exists_forall_integrable_oneSided_torusPair_integrand_of_torusBound_of_polyBound
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/e772cae7-b650-5d97-b015-aa100fdeaddc

import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_forall_integrable_oneSided_torusPair_integrand_of_torusBound_of_polyBound

set_option autoImplicit false

open MeasureTheory Set

namespace FbInt4

lemma one_add_pow_mul_gauss_le (N : ℕ) (z : ℝ) :
    (1 + |z|) ^ N * Real.exp (-(Real.pi * z ^ 2))
      ≤ Real.exp ((N : ℝ) ^ 2 / (2 * Real.pi)) * Real.exp (-(Real.pi / 2) * z ^ 2) := by
  have hpi := Real.pi_pos
  have h1 : (1 + |z|) ^ N ≤ Real.exp ((N : ℝ) * |z|) := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + |z|)
      (by linarith [Real.add_one_le_exp |z|] : 1 + |z| ≤ Real.exp |z|) N
    rwa [← Real.exp_nat_mul] at h
  have h2 : (N : ℝ) * |z| + -(Real.pi * z ^ 2) ≤ (N : ℝ) ^ 2 / (2 * Real.pi) + -(Real.pi / 2) * z ^ 2 := by
    have hsq : |z| ^ 2 = z ^ 2 := sq_abs z
    have key' : 2 * Real.pi * ((N : ℝ) * |z|) - Real.pi ^ 2 * z ^ 2 ≤ (N : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (Real.pi * |z| - N), hsq]
    have key : (N : ℝ) * |z| - Real.pi * z ^ 2 / 2 ≤ (N : ℝ) ^ 2 / (2 * Real.pi) := by
      have e : (N : ℝ) * |z| - Real.pi * z ^ 2 / 2
          = (2 * Real.pi * ((N : ℝ) * |z|) - Real.pi ^ 2 * z ^ 2) / (2 * Real.pi) := by
        rw [eq_div_iff (by positivity)]; ring
      rw [e]
      exact div_le_div_of_nonneg_right key' (by positivity)
    linarith
  calc (1 + |z|) ^ N * Real.exp (-(Real.pi * z ^ 2))
      ≤ Real.exp ((N : ℝ) * |z|) * Real.exp (-(Real.pi * z ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp ((N : ℝ) * |z| + -(Real.pi * z ^ 2)) := by rw [Real.exp_add]
    _ ≤ Real.exp ((N : ℝ) ^ 2 / (2 * Real.pi) + -(Real.pi / 2) * z ^ 2) := Real.exp_le_exp.mpr h2
    _ = Real.exp ((N : ℝ) ^ 2 / (2 * Real.pi)) * Real.exp (-(Real.pi / 2) * z ^ 2) := by
        rw [Real.exp_add]

lemma integrable_z (N : ℕ) :
    Integrable (fun z : ℝ => (1 + |z|) ^ N * Real.exp (-(Real.pi * z ^ 2))) := by
  have hpi := Real.pi_pos
  have hmaj : Integrable (fun z : ℝ => Real.exp ((N : ℝ) ^ 2 / (2 * Real.pi)) *
      Real.exp (-(Real.pi / 2) * z ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < Real.pi / 2)).const_mul _
  refine hmaj.mono' (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ ?_)
  intro z
  have h0 : 0 ≤ (1 + |z|) ^ N * Real.exp (-(Real.pi * z ^ 2)) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact one_add_pow_mul_gauss_le N z

lemma gauss_poly_integrableOn (p : ℝ) (hp : -1 < p) (N : ℕ) :
    IntegrableOn (fun u : ℝ => u ^ p * (1 + u) ^ N * Real.exp (-(Real.pi * u ^ 2))) (Ioi 0) := by
  have hpi := Real.pi_pos
  have hmaj : IntegrableOn (fun u : ℝ => Real.exp ((N : ℝ) ^ 2 / (2 * Real.pi)) *
      (u ^ p * Real.exp (-(Real.pi / 2) * u ^ 2))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_sq (by positivity : (0 : ℝ) < Real.pi / 2) hp).const_mul _
  have hcont : ContinuousOn (fun u : ℝ => u ^ p * (1 + u) ^ N * Real.exp (-(Real.pi * u ^ 2))) (Ioi 0) :=
    ((continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx))).mul
      (Continuous.continuousOn (by fun_prop))).mul (Continuous.continuousOn (by fun_prop))
  refine hmaj.mono' (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono ?_
  intro u hu
  have hu0 : 0 < u := hu
  have h0 : 0 ≤ u ^ p * (1 + u) ^ N * Real.exp (-(Real.pi * u ^ 2)) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  have h := one_add_pow_mul_gauss_le N u
  rw [abs_of_pos hu0] at h
  calc u ^ p * (1 + u) ^ N * Real.exp (-(Real.pi * u ^ 2))
      = u ^ p * ((1 + u) ^ N * Real.exp (-(Real.pi * u ^ 2))) := by ring
    _ ≤ u ^ p * (Real.exp ((N : ℝ) ^ 2 / (2 * Real.pi)) * Real.exp (-(Real.pi / 2) * u ^ 2)) :=
        mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hu0.le p)
    _ = _ := by ring

lemma rpow_mul_exp_neg_div_sq_le (β c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, ∀ w : ℝ, 0 < w → w ≤ 1 → w ^ β * Real.exp (-(c / w ^ 2)) ≤ C := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, -β ≤ 2 * (N : ℝ) := ⟨Nat.ceil |β|, by
    have h1 : |β| ≤ (Nat.ceil |β| : ℝ) := Nat.le_ceil _
    have h2 : -β ≤ |β| := neg_le_abs β
    have h3 : (0 : ℝ) ≤ (Nat.ceil |β| : ℝ) := Nat.cast_nonneg _
    linarith⟩
  refine ⟨(N.factorial : ℝ) / c ^ N, ?_⟩
  intro w hw hw1
  have hw2 : 0 < w ^ 2 := by positivity
  have s1 : w ^ β ≤ (w ^ (2 * N))⁻¹ := by
    have h := Real.rpow_le_rpow_of_exponent_ge hw hw1 (show -(2 * (N : ℝ)) ≤ β by linarith)
    have e : w ^ (-(2 * (N : ℝ))) = (w ^ (2 * N))⁻¹ := by
      rw [Real.rpow_neg hw.le, show (2 * (N : ℝ)) = ((2 * N : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    rw [e] at h
    exact h
  have s2 : Real.exp (-(c / w ^ 2)) ≤ (N.factorial : ℝ) / (c / w ^ 2) ^ N := by
    have h := Real.pow_div_factorial_le_exp (x := c / w ^ 2) (le_of_lt (div_pos hc hw2)) N
    have hpos : 0 < (c / w ^ 2) ^ N / (N.factorial : ℝ) := by positivity
    have h' := inv_anti₀ hpos h
    rw [inv_div] at h'
    rw [Real.exp_neg]
    exact h'
  calc w ^ β * Real.exp (-(c / w ^ 2)) ≤ (w ^ (2 * N))⁻¹ * ((N.factorial : ℝ) / (c / w ^ 2) ^ N) :=
        mul_le_mul s1 s2 (Real.exp_pos _).le (by positivity)
    _ = (N.factorial : ℝ) / c ^ N := by
        rw [div_pow, pow_mul]
        field_simp

lemma k_bound (b : ℝ) (N : ℕ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ s : ℝ, 0 < s →
      s ^ b * (1 + s⁻¹) ^ N * Real.exp (-(Real.pi * (s ^ 2)⁻¹)) ≤ C₀ * (1 + s ^ (max b 0)) := by
  obtain ⟨C, hC⟩ := rpow_mul_exp_neg_div_sq_le (b - N) Real.pi Real.pi_pos
  have hC0 : 0 ≤ C := by
    have := hC 1 one_pos le_rfl
    have : 0 ≤ (1 : ℝ) ^ (b - N) * Real.exp (-(Real.pi / 1 ^ 2)) := by positivity
    linarith
  refine ⟨2 ^ N * (C + 1), by positivity, ?_⟩
  intro s hs
  rcases le_or_gt s 1 with hs1 | hs1
  ·
    have h1 : (1 + s⁻¹) ^ N ≤ (2 * s⁻¹) ^ N := by
      apply pow_le_pow_left₀ (by positivity)
      have : 1 ≤ s⁻¹ := one_le_inv_iff₀.mpr ⟨hs, hs1⟩
      linarith
    have h2 : s ^ b * (s⁻¹) ^ N = s ^ (b - N) := by
      rw [Real.rpow_sub hs, ← Real.rpow_natCast, Real.inv_rpow hs.le, div_eq_mul_inv]
    have h3 : s ^ (b - N) * Real.exp (-(Real.pi * (s ^ 2)⁻¹)) ≤ C := by
      have := hC s hs hs1
      rwa [div_eq_mul_inv] at this
    calc s ^ b * (1 + s⁻¹) ^ N * Real.exp (-(Real.pi * (s ^ 2)⁻¹))
        ≤ s ^ b * (2 * s⁻¹) ^ N * Real.exp (-(Real.pi * (s ^ 2)⁻¹)) := by
          gcongr
      _ = 2 ^ N * (s ^ (b - N) * Real.exp (-(Real.pi * (s ^ 2)⁻¹))) := by
          rw [mul_pow, ← h2]; ring
      _ ≤ 2 ^ N * C := by gcongr
      _ ≤ 2 ^ N * (C + 1) * (1 + s ^ (max b 0)) := by
          have : 0 ≤ s ^ (max b 0) := Real.rpow_nonneg hs.le _
          have h4 : 0 ≤ (2:ℝ) ^ N * (C + 1) * s ^ (max b 0) := by positivity
          have h5 : (0:ℝ) ≤ 2 ^ N := by positivity
          linarith
  ·
    have h1 : (1 + s⁻¹) ^ N ≤ 2 ^ N := by
      apply pow_le_pow_left₀ (by positivity)
      have : s⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hs1.le
      linarith
    have h2 : s ^ b ≤ s ^ (max b 0) := Real.rpow_le_rpow_of_exponent_le hs1.le (le_max_left _ _)
    have h3 : Real.exp (-(Real.pi * (s ^ 2)⁻¹)) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_nonpos]; positivity
    calc s ^ b * (1 + s⁻¹) ^ N * Real.exp (-(Real.pi * (s ^ 2)⁻¹))
        ≤ s ^ (max b 0) * 2 ^ N * 1 := by
          gcongr
      _ ≤ 2 ^ N * (C + 1) * (1 + s ^ (max b 0)) := by
          have : 0 ≤ s ^ (max b 0) := Real.rpow_nonneg hs.le _
          have h6 : 0 ≤ (2:ℝ) ^ N * (C + 1) := by positivity
          have h7 : 0 ≤ (2:ℝ) ^ N * C * s ^ (max b 0) := by positivity
          linarith

lemma integrableOn_y2 (c : ℝ) (hc : c < -1) (N : ℕ) :
    IntegrableOn (fun y : ℝ => y ^ c * (1 + y⁻¹) ^ N * Real.exp (-(Real.pi * (y ^ 2)⁻¹))) (Ioi 0) := by
  obtain ⟨C₀, hC0, hk⟩ := k_bound c N
  have hcont : ContinuousOn
      (fun y : ℝ => y ^ c * (1 + y⁻¹) ^ N * Real.exp (-(Real.pi * (y ^ 2)⁻¹))) (Ioi 0) := by
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · exact continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx))
    · exact ((continuousOn_const.add (continuousOn_inv₀.mono (fun x hx => ne_of_gt hx))).pow N)
    · refine Real.continuous_exp.comp_continuousOn (ContinuousOn.neg (continuousOn_const.mul ?_))
      exact (continuous_pow 2).continuousOn.inv₀ (fun x hx => pow_ne_zero 2 (ne_of_gt hx))
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · have hconst : IntegrableOn (fun _ : ℝ => C₀ * 2) (Ioc (0 : ℝ) 1) :=
      integrableOn_const (hs := measure_Ioc_lt_top.ne)
    refine Integrable.mono' hconst ?_ ?_
    · exact (hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
    · refine (ae_restrict_mem measurableSet_Ioc).mono ?_
      intro y hy
      have hy0 : 0 < y := hy.1
      have hnn : 0 ≤ y ^ c * (1 + y⁻¹) ^ N * Real.exp (-(Real.pi * (y ^ 2)⁻¹)) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      refine (hk y hy0).trans ?_
      have : y ^ (max c 0) ≤ 1 := Real.rpow_le_one hy0.le hy.2 (le_max_right _ _)
      nlinarith
  · have hmaj : IntegrableOn (fun y : ℝ => 2 ^ N * y ^ c) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt hc zero_lt_one).const_mul _
    refine Integrable.mono' hmaj ?_ ?_
    · exact (hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_mem measurableSet_Ioi).mono ?_
      intro y hy
      have hy1 : 1 < y := hy
      have hy0 : 0 < y := zero_lt_one.trans hy1
      have hnn : 0 ≤ y ^ c * (1 + y⁻¹) ^ N * Real.exp (-(Real.pi * (y ^ 2)⁻¹)) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have h1 : (1 + y⁻¹) ^ N ≤ 2 ^ N := by
        apply pow_le_pow_left₀ (by positivity)
        have : y⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hy1.le
        linarith
      have h3 : Real.exp (-(Real.pi * (y ^ 2)⁻¹)) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_nonpos]; positivity
      calc y ^ c * (1 + y⁻¹) ^ N * Real.exp (-(Real.pi * (y ^ 2)⁻¹)) ≤ y ^ c * 2 ^ N * 1 := by
            gcongr
        _ = 2 ^ N * y ^ c := by ring

lemma integrable_ts (a b : ℝ) (N : ℕ) (ha : max b 0 < a) :
    Integrable (fun p : ℝ × ℝ =>
        p.1 ^ a * Real.exp (-(2 * Real.pi * p.1)) *
          (p.2 ^ b * (1 + p.2⁻¹) ^ N * Real.exp (-(Real.pi * (p.2 ^ 2)⁻¹)) *
            Real.exp (-(Real.pi * (p.1 ^ 2 * p.2 ^ 2))) * (1 + p.1 * p.2) ^ N))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hpi := Real.pi_pos
  set b' : ℝ := max b 0 with hb'
  have hb'0 : 0 ≤ b' := le_max_right _ _
  have ha0 : 0 < a := lt_of_le_of_lt hb'0 ha
  obtain ⟨C₀, hC0, hk⟩ := k_bound b N
  have hI0i := gauss_poly_integrableOn 0 (by norm_num) N
  have hI1i := gauss_poly_integrableOn b' (by linarith) N
  set I0 : ℝ := ∫ u in Ioi (0 : ℝ), u ^ (0 : ℝ) * (1 + u) ^ N * Real.exp (-(Real.pi * u ^ 2)) with hI0
  set I1 : ℝ := ∫ u in Ioi (0 : ℝ), u ^ b' * (1 + u) ^ N * Real.exp (-(Real.pi * u ^ 2)) with hI1
  set μ0 : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ0
  set F : ℝ × ℝ → ℝ := fun p : ℝ × ℝ =>
        p.1 ^ a * Real.exp (-(2 * Real.pi * p.1)) *
          (p.2 ^ b * (1 + p.2⁻¹) ^ N * Real.exp (-(Real.pi * (p.2 ^ 2)⁻¹)) *
            Real.exp (-(Real.pi * (p.1 ^ 2 * p.2 ^ 2))) * (1 + p.1 * p.2) ^ N) with hF
  have hFm : Measurable F := by
    rw [hF]
    have m1 : Measurable fun p : ℝ × ℝ => p.1 := measurable_fst
    have m2 : Measurable fun p : ℝ × ℝ => p.2 := measurable_snd
    refine ((m1.pow_const a).mul (by fun_prop)).mul ?_
    refine (((((m2.pow_const b).mul ((measurable_const.add m2.inv).pow_const N)).mul
      (by fun_prop)).mul (by fun_prop)).mul ((measurable_const.add (m1.mul m2)).pow_const N))
  have hFnn : ∀ t s : ℝ, 0 < t → 0 < s → 0 ≤ F (t, s) := by
    intro t s ht hs; simp only [hF]; positivity

  set n : ℝ → ℝ → ℝ := fun t u => (1 + (u / t) ^ b') * (1 + u) ^ N * Real.exp (-(Real.pi * u ^ 2)) with hn
  have hbd : ∀ t s : ℝ, 0 < t → 0 < s →
      F (t, s) ≤ C₀ * (t ^ a * Real.exp (-(2 * Real.pi * t))) * n t (t * s) := by
    intro t s ht hs
    have hk' := hk s hs
    have e1 : t * s / t = s := by field_simp
    have e2 : Real.exp (-(Real.pi * (t ^ 2 * s ^ 2))) = Real.exp (-(Real.pi * (t * s) ^ 2)) := by
      congr 1; ring
    simp only [hF, hn]
    rw [e1, e2]
    have hA : 0 ≤ t ^ a * Real.exp (-(2 * Real.pi * t)) := by positivity
    have hB : 0 ≤ Real.exp (-(Real.pi * (t * s) ^ 2)) * (1 + t * s) ^ N := by positivity
    calc t ^ a * Real.exp (-(2 * Real.pi * t)) *
          (s ^ b * (1 + s⁻¹) ^ N * Real.exp (-(Real.pi * (s ^ 2)⁻¹)) *
            Real.exp (-(Real.pi * (t * s) ^ 2)) * (1 + t * s) ^ N)
        = (t ^ a * Real.exp (-(2 * Real.pi * t))) *
            ((s ^ b * (1 + s⁻¹) ^ N * Real.exp (-(Real.pi * (s ^ 2)⁻¹))) *
              (Real.exp (-(Real.pi * (t * s) ^ 2)) * (1 + t * s) ^ N)) := by ring
      _ ≤ (t ^ a * Real.exp (-(2 * Real.pi * t))) *
            ((C₀ * (1 + s ^ b')) * (Real.exp (-(Real.pi * (t * s) ^ 2)) * (1 + t * s) ^ N)) := by
          gcongr
      _ = C₀ * (t ^ a * Real.exp (-(2 * Real.pi * t))) *
            ((1 + s ^ b') * (1 + t * s) ^ N * Real.exp (-(Real.pi * (t * s) ^ 2))) := by ring

  have hn_int : ∀ t : ℝ, 0 < t → IntegrableOn (n t) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), n t u = I0 + (t ^ b')⁻¹ * I1 := by
    intro t ht
    have hsum : IntegrableOn (fun u : ℝ => u ^ (0 : ℝ) * (1 + u) ^ N * Real.exp (-(Real.pi * u ^ 2))
        + (t ^ b')⁻¹ * (u ^ b' * (1 + u) ^ N * Real.exp (-(Real.pi * u ^ 2)))) (Ioi 0) :=
      hI0i.add (hI1i.const_mul _)
    have heq : ∀ u ∈ Ioi (0 : ℝ), n t u = u ^ (0 : ℝ) * (1 + u) ^ N * Real.exp (-(Real.pi * u ^ 2))
        + (t ^ b')⁻¹ * (u ^ b' * (1 + u) ^ N * Real.exp (-(Real.pi * u ^ 2))) := by
      intro u hu
      have hu0 : 0 ≤ u := le_of_lt hu
      simp only [hn]
      rw [Real.rpow_zero, Real.div_rpow hu0 ht.le, div_eq_mul_inv]
      ring
    refine ⟨hsum.congr_fun (fun u hu => (heq u hu).symm) measurableSet_Ioi, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_add hI0i (hI1i.const_mul _),
      integral_const_mul]

  have hsec : ∀ t : ℝ, 0 < t → Integrable (fun s : ℝ => F (t, s)) μ0 := by
    intro t ht
    obtain ⟨hni, -⟩ := hn_int t ht
    have hsc : IntegrableOn (fun s : ℝ => n t (t * s)) (Ioi 0) := by
      rw [integrableOn_Ioi_comp_mul_left_iff (n t) 0 ht, mul_zero]
      exact hni
    have hmaj : Integrable (fun s : ℝ => C₀ * (t ^ a * Real.exp (-(2 * Real.pi * t))) * n t (t * s)) μ0 :=
      hsc.const_mul _
    refine hmaj.mono' ((hFm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable) ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (hFnn t s ht hs)]
    exact hbd t s ht hs

  have hJ : ∀ t : ℝ, 0 < t → ∫ s, ‖F (t, s)‖ ∂μ0
      ≤ C₀ * (t ^ a * Real.exp (-(2 * Real.pi * t))) * (t⁻¹ * (I0 + (t ^ b')⁻¹ * I1)) := by
    intro t ht
    obtain ⟨hni, hnv⟩ := hn_int t ht
    have hsc : IntegrableOn (fun s : ℝ => n t (t * s)) (Ioi 0) := by
      rw [integrableOn_Ioi_comp_mul_left_iff (n t) 0 ht, mul_zero]
      exact hni
    have hval : ∫ s in Ioi (0 : ℝ), n t (t * s) = t⁻¹ * (I0 + (t ^ b')⁻¹ * I1) := by
      rw [integral_comp_mul_left_Ioi (n t) 0 ht, mul_zero, smul_eq_mul, hnv]
    calc ∫ s, ‖F (t, s)‖ ∂μ0
        ≤ ∫ s, C₀ * (t ^ a * Real.exp (-(2 * Real.pi * t))) * n t (t * s) ∂μ0 := by
          refine integral_mono_ae (hsec t ht).norm (hsc.const_mul _) ?_
          refine (ae_restrict_mem measurableSet_Ioi).mono ?_
          intro s hs
          beta_reduce
          rw [Real.norm_eq_abs, abs_of_nonneg (hFnn t s ht hs)]
          exact hbd t s ht hs
      _ = C₀ * (t ^ a * Real.exp (-(2 * Real.pi * t))) * (t⁻¹ * (I0 + (t ^ b')⁻¹ * I1)) := by
          rw [integral_const_mul]
          simp only [hμ0]
          rw [hval]

  have hgam : ∀ s : ℝ, -1 < s → IntegrableOn (fun t : ℝ => t ^ s * Real.exp (-(2 * Real.pi * t))) (Ioi 0) := by
    intro s hs
    have := integrableOn_rpow_mul_exp_neg_mul_rpow hs (zero_lt_one' ℝ) (by positivity : (0:ℝ) < 2 * Real.pi)
    refine this.congr_fun ?_ measurableSet_Ioi
    intro t ht
    simp only [Real.rpow_one, neg_mul]
  have hg_int : IntegrableOn (fun t : ℝ =>
      C₀ * (t ^ a * Real.exp (-(2 * Real.pi * t))) * (t⁻¹ * (I0 + (t ^ b')⁻¹ * I1))) (Ioi 0) := by
    have h1 := (hgam (a - 1) (by linarith)).const_mul (C₀ * I0)
    have h2 := (hgam (a - 1 - b') (by linarith)).const_mul (C₀ * I1)
    have h12 : IntegrableOn (fun t : ℝ => C₀ * I0 * (t ^ (a - 1) * Real.exp (-(2 * Real.pi * t)))
        + C₀ * I1 * (t ^ (a - 1 - b') * Real.exp (-(2 * Real.pi * t)))) (Ioi 0) := h1.add h2
    refine IntegrableOn.congr_fun h12 ?_ measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := ht
    have e1 : t ^ (a - 1) = t ^ a * t⁻¹ := by
      rw [Real.rpow_sub_one ht0.ne']; ring
    have e2 : t ^ (a - 1 - b') = t ^ a * t⁻¹ * (t ^ b')⁻¹ := by
      rw [Real.rpow_sub ht0, Real.rpow_sub_one ht0.ne']; ring
    beta_reduce
    rw [e1, e2]
    ring

  have hprod := (integrable_prod_iff (μ := μ0) (ν := μ0) hFm.aestronglyMeasurable).mpr
  refine hprod ⟨?_, ?_⟩
  · exact (ae_restrict_mem measurableSet_Ioi).mono (fun t ht => hsec t ht)
  · refine Integrable.mono' hg_int hFm.aestronglyMeasurable.norm.integral_prod_right' ?_
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro t ht
    have hnn : 0 ≤ ∫ s, ‖F (t, s)‖ ∂μ0 := integral_nonneg (fun _ => norm_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    exact hJ t ht

lemma integrable_ty (a b : ℝ) (N : ℕ) (ha : max b 0 < a) :
    Integrable (fun p : ℝ × ℝ =>
        p.1 ^ a * Real.exp (-(2 * Real.pi * p.1)) *
          (|p.2| ^ b * (1 + |p.2|⁻¹) ^ N * Real.exp (-(Real.pi * (p.2 ^ 2)⁻¹)) *
            Real.exp (-(Real.pi * (p.1 ^ 2 * p.2 ^ 2))) * (1 + p.1 * |p.2|) ^ N))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Iio (0 : ℝ)))) := by

  have hneg : MeasurePreserving (fun y : ℝ => -y) (volume.restrict (Ioi (0 : ℝ)))
      (volume.restrict (Iio (0 : ℝ))) := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
      (measurableSet_Iio (a := (0 : ℝ)))
    have e : (fun y : ℝ => -y) ⁻¹' Iio (0 : ℝ) = Ioi 0 := by
      ext y; simp
    rwa [e] at h
  have hmp := (MeasurePreserving.id (volume.restrict (Ioi (0 : ℝ)))).prod hneg
  set Φ : ℝ × ℝ → ℝ := fun p : ℝ × ℝ =>
        p.1 ^ a * Real.exp (-(2 * Real.pi * p.1)) *
          (|p.2| ^ b * (1 + |p.2|⁻¹) ^ N * Real.exp (-(Real.pi * (p.2 ^ 2)⁻¹)) *
            Real.exp (-(Real.pi * (p.1 ^ 2 * p.2 ^ 2))) * (1 + p.1 * |p.2|) ^ N) with hΦ
  have hΦm : Measurable Φ := by
    rw [hΦ]
    have m1 : Measurable fun p : ℝ × ℝ => p.1 := measurable_fst
    have m2 : Measurable fun p : ℝ × ℝ => |p.2| := continuous_abs.measurable.comp measurable_snd
    refine ((m1.pow_const a).mul (by fun_prop)).mul ?_
    refine (((((m2.pow_const b).mul ((measurable_const.add m2.inv).pow_const N)).mul
      (by fun_prop)).mul (by fun_prop)).mul ((measurable_const.add (m1.mul m2)).pow_const N))
  rw [← hmp.integrable_comp hΦm.aestronglyMeasurable]
  have hts := integrable_ts a b N ha
  have hae : ∀ᵐ p ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))),
      p.2 ∈ Ioi (0 : ℝ) :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)
  refine hts.congr (hae.mono ?_)
  intro p hp
  have hp0 : 0 < p.2 := hp
  simp only [hΦ, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, abs_neg, abs_of_pos hp0, neg_sq]

end FbInt4

theorem solution
    (β : ℂ) (g : ℝ → ℂ) (hg : Measurable g) (Cg σg : ℝ) (hσg : 0 ≤ σg)
    (hgb : ∀ τ : ℝ, τ ≠ 0 → ‖g τ‖ ≤ Cg * (1 + |τ| ^ (-σg)))
    (B : ℝ → ℝ → ℝ → ℝ → ℂ) (hB : Measurable fun x : ℝ × ℝ × ℝ × ℝ => B x.1 x.2.1 x.2.2.1 x.2.2.2)
    (CB : ℝ) (N : ℕ)
    (hBb : ∀ p q r z : ℝ, ‖B p q r z‖ ≤ CB * (1 + |p|) ^ N * (1 + |q|) ^ N * (1 + |r|) ^ N * (1 + |z|) ^ N) :
    ∃ σ₀ : ℝ, ∀ α γ : ℂ, σ₀ < α.re → γ.re < -σ₀ →
      Integrable (fun x : ℝ × ℝ × ℝ × ℝ =>
        ((x.1 : ℝ) : ℂ) ^ α * (Real.exp (-(2 * Real.pi * x.1)) : ℂ) *
          ((|x.2.1| : ℝ) : ℂ) ^ β * ((x.2.2.1 : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi * ((x.2.1 ^ 2)⁻¹ + x.1 ^ 2 * x.2.1 ^ 2 + (x.2.2.1 ^ 2)⁻¹))) : ℂ) *
          g (x.1 * |x.2.1| / x.2.2.1) *
          (B (x.2.1⁻¹) (x.2.2.1⁻¹) (x.1 * x.2.1) x.2.2.2 * (Real.exp (-(Real.pi * x.2.2.2 ^ 2)) : ℂ)))
        ((volume.restrict (Ioi (0 : ℝ))).prod ((volume.restrict (Iio (0 : ℝ))).prod
          ((volume.restrict (Ioi (0 : ℝ))).prod volume))) := by
  classical

  set b : ℝ := β.re with hb
  refine ⟨max b 0 + σg + 1, ?_⟩
  intro α γ hα hγ
  set a : ℝ := α.re with ha
  set c : ℝ := γ.re with hc
  have hσ0 : 0 ≤ max b 0 := le_max_right _ _
  have ha0 : max b 0 < a := by linarith
  have hm : max (b - σg) 0 ≤ max b 0 := max_le_max (by linarith) le_rfl
  have ha1 : max (b - σg) 0 < a - σg := by linarith
  have hc0 : c < -1 := by linarith
  have hc1 : c + σg < -1 := by linarith

  set μt : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμt
  set μ1 : Measure ℝ := volume.restrict (Iio (0 : ℝ)) with hμ1
  set μ2 : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ2

  set Z : ℝ → ℝ := fun z => (1 + |z|) ^ N * Real.exp (-(Real.pi * z ^ 2)) with hZ
  set Ψ : ℝ → ℝ → ℝ := fun c' y => y ^ c' * (1 + y⁻¹) ^ N * Real.exp (-(Real.pi * (y ^ 2)⁻¹)) with hΨ
  set Φ : ℝ → ℝ → ℝ × ℝ → ℝ := fun a' b' p =>
      p.1 ^ a' * Real.exp (-(2 * Real.pi * p.1)) *
        (|p.2| ^ b' * (1 + |p.2|⁻¹) ^ N * Real.exp (-(Real.pi * (p.2 ^ 2)⁻¹)) *
          Real.exp (-(Real.pi * (p.1 ^ 2 * p.2 ^ 2))) * (1 + p.1 * |p.2|) ^ N) with hΦ
  have hZi : Integrable Z := FbInt4.integrable_z N
  have hΨ0 : Integrable (Ψ c) μ2 := FbInt4.integrableOn_y2 c hc0 N
  have hΨ1 : Integrable (Ψ (c + σg)) μ2 := FbInt4.integrableOn_y2 (c + σg) hc1 N
  have hΦ0 : Integrable (Φ a b) (μt.prod μ1) := FbInt4.integrable_ty a b N ha0
  have hΦ1 : Integrable (Φ (a - σg) (b - σg)) (μt.prod μ1) := FbInt4.integrable_ty (a - σg) (b - σg) N ha1

  set G' : (ℝ × ℝ) × (ℝ × ℝ) → ℝ := fun q =>
      Φ a b q.1 * (Ψ c q.2.1 * Z q.2.2) + Φ (a - σg) (b - σg) q.1 * (Ψ (c + σg) q.2.1 * Z q.2.2) with hG'
  have hG'i : Integrable G' ((μt.prod μ1).prod (μ2.prod (volume : Measure ℝ))) :=
    (hΦ0.mul_prod (hΨ0.mul_prod hZi)).add (hΦ1.mul_prod (hΨ1.mul_prod hZi))

  set G : ℝ × ℝ × ℝ × ℝ → ℝ := fun x => G' ((x.1, x.2.1), (x.2.2.1, x.2.2.2)) with hG
  have hGi : Integrable G (μt.prod (μ1.prod (μ2.prod (volume : Measure ℝ)))) := by
    have e : (μt.prod (μ1.prod (μ2.prod volume)))
        = Measure.map MeasurableEquiv.prodAssoc ((μt.prod μ1).prod (μ2.prod (volume : Measure ℝ))) :=
      (Measure.prodAssoc_prod).symm
    rw [e, integrable_map_equiv]
    refine hG'i.congr (ae_of_all _ ?_)
    intro q
    simp only [hG, Function.comp, MeasurableEquiv.prodAssoc, MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply]

  have hCg : 0 ≤ Cg := by
    have h := hgb 1 one_ne_zero
    have h2 : (0 : ℝ) < 1 + |(1:ℝ)| ^ (-σg) := by positivity
    nlinarith [norm_nonneg (g 1)]
  have hCB : 0 ≤ CB := by
    have h := hBb 0 0 0 0
    simp at h
    exact (norm_nonneg _).trans h

  have hmeas : Measurable (fun x : ℝ × ℝ × ℝ × ℝ =>
        ((x.1 : ℝ) : ℂ) ^ α * (Real.exp (-(2 * Real.pi * x.1)) : ℂ) *
          ((|x.2.1| : ℝ) : ℂ) ^ β * ((x.2.2.1 : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi * ((x.2.1 ^ 2)⁻¹ + x.1 ^ 2 * x.2.1 ^ 2 + (x.2.2.1 ^ 2)⁻¹))) : ℂ) *
          g (x.1 * |x.2.1| / x.2.2.1) *
          (B (x.2.1⁻¹) (x.2.2.1⁻¹) (x.1 * x.2.1) x.2.2.2 * (Real.exp (-(Real.pi * x.2.2.2 ^ 2)) : ℂ))) := by
    have m1 : Measurable fun x : ℝ × ℝ × ℝ × ℝ => x.1 := measurable_fst
    have m2 : Measurable fun x : ℝ × ℝ × ℝ × ℝ => x.2.1 := measurable_fst.comp measurable_snd
    have m3 : Measurable fun x : ℝ × ℝ × ℝ × ℝ => x.2.2.1 :=
      measurable_fst.comp (measurable_snd.comp measurable_snd)
    have m4 : Measurable fun x : ℝ × ℝ × ℝ × ℝ => x.2.2.2 :=
      measurable_snd.comp (measurable_snd.comp measurable_snd)
    have hgm : Measurable fun x : ℝ × ℝ × ℝ × ℝ => g (x.1 * |x.2.1| / x.2.2.1) :=
      hg.comp ((m1.mul (continuous_abs.measurable.comp m2)).div m3)
    have hBm : Measurable fun x : ℝ × ℝ × ℝ × ℝ => B (x.2.1⁻¹) (x.2.2.1⁻¹) (x.1 * x.2.1) x.2.2.2 :=
      hB.comp (m2.inv.prodMk (m3.inv.prodMk ((m1.mul m2).prodMk m4)))
    have hc1 : Measurable fun x : ℝ × ℝ × ℝ × ℝ => ((x.1 : ℝ) : ℂ) ^ α :=
      (Complex.measurable_ofReal.comp m1).pow_const α
    have hc2 : Measurable fun x : ℝ × ℝ × ℝ × ℝ => ((|x.2.1| : ℝ) : ℂ) ^ β :=
      (Complex.measurable_ofReal.comp (continuous_abs.measurable.comp m2)).pow_const β
    have hc3 : Measurable fun x : ℝ × ℝ × ℝ × ℝ => ((x.2.2.1 : ℝ) : ℂ) ^ γ :=
      (Complex.measurable_ofReal.comp m3).pow_const γ
    have he1 : Measurable fun x : ℝ × ℝ × ℝ × ℝ => (Real.exp (-(2 * Real.pi * x.1)) : ℂ) :=
      Complex.measurable_ofReal.comp (by fun_prop)
    have he2 : Measurable fun x : ℝ × ℝ × ℝ × ℝ =>
        (Real.exp (-(Real.pi * ((x.2.1 ^ 2)⁻¹ + x.1 ^ 2 * x.2.1 ^ 2 + (x.2.2.1 ^ 2)⁻¹))) : ℂ) :=
      Complex.measurable_ofReal.comp (by fun_prop)
    have he3 : Measurable fun x : ℝ × ℝ × ℝ × ℝ => (Real.exp (-(Real.pi * x.2.2.2 ^ 2)) : ℂ) :=
      Complex.measurable_ofReal.comp (by fun_prop)
    exact (((((hc1.mul he1).mul hc2).mul hc3).mul he2).mul hgm).mul (hBm.mul he3)

  have hbound : ∀ x : ℝ × ℝ × ℝ × ℝ, 0 < x.1 → x.2.1 < 0 → 0 < x.2.2.1 →
      ‖((x.1 : ℝ) : ℂ) ^ α * (Real.exp (-(2 * Real.pi * x.1)) : ℂ) *
          ((|x.2.1| : ℝ) : ℂ) ^ β * ((x.2.2.1 : ℝ) : ℂ) ^ γ *
          (Real.exp (-(Real.pi * ((x.2.1 ^ 2)⁻¹ + x.1 ^ 2 * x.2.1 ^ 2 + (x.2.2.1 ^ 2)⁻¹))) : ℂ) *
          g (x.1 * |x.2.1| / x.2.2.1) *
          (B (x.2.1⁻¹) (x.2.2.1⁻¹) (x.1 * x.2.1) x.2.2.2 * (Real.exp (-(Real.pi * x.2.2.2 ^ 2)) : ℂ))‖
        ≤ (Cg * CB) * G x := by
    rintro ⟨t, y, w, z⟩ ht hy hw
    simp only at ht hy hw
    have hs : 0 < |y| := abs_pos.mpr hy.ne
    have hτ : 0 < t * |y| / w := by positivity

    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_cpow_eq_rpow_re_of_pos hs,
      Complex.norm_cpow_eq_rpow_re_of_pos hw, Complex.norm_real, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, Real.abs_exp, Real.abs_exp, Real.abs_exp]

    have hgτ : ‖g (t * |y| / w)‖ ≤ Cg * (1 + (t * |y| / w) ^ (-σg)) := by
      have h := hgb (t * |y| / w) hτ.ne'
      rwa [abs_of_pos hτ] at h
    have hBx : ‖B y⁻¹ w⁻¹ (t * y) z‖ ≤ CB * (1 + |y|⁻¹) ^ N * (1 + w⁻¹) ^ N * (1 + t * |y|) ^ N * (1 + |z|) ^ N := by
      have h := hBb y⁻¹ w⁻¹ (t * y) z
      rwa [abs_inv, abs_inv, abs_of_pos hw, abs_mul, abs_of_pos ht] at h

    have r1 : (t * |y| / w) ^ (-σg) = t ^ (-σg) * |y| ^ (-σg) * w ^ σg := by
      rw [Real.div_rpow (by positivity) hw.le, Real.mul_rpow ht.le hs.le, Real.rpow_neg hw.le, div_inv_eq_mul]
    have r2 : t ^ (a - σg) = t ^ a * t ^ (-σg) := by rw [sub_eq_add_neg, Real.rpow_add ht]
    have r3 : |y| ^ (b - σg) = |y| ^ b * |y| ^ (-σg) := by rw [sub_eq_add_neg, Real.rpow_add hs]
    have r4 : w ^ (c + σg) = w ^ c * w ^ σg := by rw [Real.rpow_add hw]
    have r5 : Real.exp (-(Real.pi * ((y ^ 2)⁻¹ + t ^ 2 * y ^ 2 + (w ^ 2)⁻¹)))
        = Real.exp (-(Real.pi * (y ^ 2)⁻¹)) * Real.exp (-(Real.pi * (t ^ 2 * y ^ 2))) *
          Real.exp (-(Real.pi * (w ^ 2)⁻¹)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

    have hG : (Cg * CB) * G (t, y, w, z) =
        t ^ a * Real.exp (-(2 * Real.pi * t)) * |y| ^ b * w ^ c *
          (Real.exp (-(Real.pi * (y ^ 2)⁻¹)) * Real.exp (-(Real.pi * (t ^ 2 * y ^ 2))) *
            Real.exp (-(Real.pi * (w ^ 2)⁻¹))) *
          (Cg * (1 + t ^ (-σg) * |y| ^ (-σg) * w ^ σg)) *
          (CB * (1 + |y|⁻¹) ^ N * (1 + w⁻¹) ^ N * (1 + t * |y|) ^ N * (1 + |z|) ^ N *
            Real.exp (-(Real.pi * z ^ 2))) := by
      simp only [hG, hG', hΦ, hΨ, hZ, ha, hb, hc]
      rw [r2, r3, r4]
      ring
    rw [hG, r5, ← r1]
    have hE : 0 ≤ t ^ a * Real.exp (-(2 * Real.pi * t)) * |y| ^ b * w ^ c *
        (Real.exp (-(Real.pi * (y ^ 2)⁻¹)) * Real.exp (-(Real.pi * (t ^ 2 * y ^ 2))) *
          Real.exp (-(Real.pi * (w ^ 2)⁻¹))) := by positivity
    calc _ = (t ^ a * Real.exp (-(2 * Real.pi * t)) * |y| ^ b * w ^ c *
          (Real.exp (-(Real.pi * (y ^ 2)⁻¹)) * Real.exp (-(Real.pi * (t ^ 2 * y ^ 2))) *
            Real.exp (-(Real.pi * (w ^ 2)⁻¹)))) *
          ‖g (t * |y| / w)‖ * (‖B y⁻¹ w⁻¹ (t * y) z‖ * Real.exp (-(Real.pi * z ^ 2))) := by ring
      _ ≤ (t ^ a * Real.exp (-(2 * Real.pi * t)) * |y| ^ b * w ^ c *
          (Real.exp (-(Real.pi * (y ^ 2)⁻¹)) * Real.exp (-(Real.pi * (t ^ 2 * y ^ 2))) *
            Real.exp (-(Real.pi * (w ^ 2)⁻¹)))) *
          (Cg * (1 + (t * |y| / w) ^ (-σg))) *
          ((CB * (1 + |y|⁻¹) ^ N * (1 + w⁻¹) ^ N * (1 + t * |y|) ^ N * (1 + |z|) ^ N) *
            Real.exp (-(Real.pi * z ^ 2))) := by
        gcongr
      _ = _ := by ring

  have q1 : Measure.QuasiMeasurePreserving (fun x : ℝ × ℝ × ℝ × ℝ => x.1)
      (μt.prod (μ1.prod (μ2.prod (volume : Measure ℝ)))) μt := Measure.quasiMeasurePreserving_fst
  have q2 : Measure.QuasiMeasurePreserving (fun x : ℝ × ℝ × ℝ × ℝ => x.2.1)
      (μt.prod (μ1.prod (μ2.prod (volume : Measure ℝ)))) μ1 :=
    Measure.quasiMeasurePreserving_fst.comp Measure.quasiMeasurePreserving_snd
  have q3 : Measure.QuasiMeasurePreserving (fun x : ℝ × ℝ × ℝ × ℝ => x.2.2.1)
      (μt.prod (μ1.prod (μ2.prod (volume : Measure ℝ)))) μ2 :=
    Measure.quasiMeasurePreserving_fst.comp
      (Measure.quasiMeasurePreserving_snd.comp Measure.quasiMeasurePreserving_snd)
  have a1 : ∀ᵐ x ∂(μt.prod (μ1.prod (μ2.prod (volume : Measure ℝ)))), x.1 ∈ Ioi (0 : ℝ) :=
    q1.ae (ae_restrict_mem measurableSet_Ioi)
  have a2 : ∀ᵐ x ∂(μt.prod (μ1.prod (μ2.prod (volume : Measure ℝ)))), x.2.1 ∈ Iio (0 : ℝ) :=
    q2.ae (ae_restrict_mem measurableSet_Iio)
  have a3 : ∀ᵐ x ∂(μt.prod (μ1.prod (μ2.prod (volume : Measure ℝ)))), x.2.2.1 ∈ Ioi (0 : ℝ) :=
    q3.ae (ae_restrict_mem measurableSet_Ioi)
  refine Integrable.mono' (hGi.const_mul (Cg * CB)) hmeas.aestronglyMeasurable ?_
  filter_upwards [a1, a2, a3] with x h1 h2 h3
  exact hbound x h1 h2 h3

end S_LanglandsTunnell_exists_forall_integrable_oneSided_torusPair_integrand_of_torusBound_of_polyBound
end P2MW
export P2MW.S_LanglandsTunnell_exists_forall_integrable_oneSided_torusPair_integrand_of_torusBound_of_polyBound (solution)
