-- Prove2me | solution 1 for LSeries.abscissaOfAbsConv_lt_of_differentiableOn_ball
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/eaa6d88a-b372-5166-b2e7-30ae9cca762f

import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.NumberTheory.LSeries.Positivity
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.DiscreteSubset
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Linearity
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball

set_option autoImplicit false

section P2M_CharacterSum

open Finset Filter Asymptotics

namespace LandauSiegel

lemma sum_range_eq_sum_zmod (q : ℕ) [NeZero q] (f : ZMod q → ℂ) :
    ∑ k ∈ range q, f k = ∑ a, f a := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_neZero q)).symm⟩
  rw [Finset.sum_range]
  exact Fintype.sum_congr _ _ (fun i => congrArg f (ZMod.natCast_zmod_val (n := n+1) i))

lemma sum_range_of_periodic {q : ℕ} (f : ℕ → ℂ) (hf : Function.Periodic f q)
    (h0 : ∑ k ∈ range q, f k = 0) (n : ℕ) :
    ∑ k ∈ range n, f k = ∑ k ∈ range (n % q), f k := by
  conv_lhs => rw [← Nat.div_add_mod n q]
  rw [Finset.sum_range_add]
  have h1 : ∀ m, ∑ k ∈ range (q * m), f k = 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, zero_add, ← h0]
      exact Finset.sum_congr rfl fun k _ => by
        rw [add_comm, mul_comm]; exact hf.nat_mul m k
  rw [h1, zero_add]
  exact Finset.sum_congr rfl fun k _ => by
    calc f (q * (n / q) + k) = f (k + (n / q) * q) := by ring_nf
      _ = f k := hf.nat_mul (n / q) k

lemma norm_sum_range_le_of_periodic {q : ℕ} (f : ℕ → ℂ) (hf : Function.Periodic f q)
    (hq : 0 < q) (h0 : ∑ k ∈ range q, f k = 0) (hb : ∀ k, ‖f k‖ ≤ 1) (n : ℕ) :
    ‖∑ k ∈ range n, f k‖ ≤ q := by
  rw [sum_range_of_periodic f hf h0 n]
  calc ‖∑ k ∈ range (n % q), f k‖ ≤ ∑ k ∈ range (n % q), ‖f k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ range (n % q), (1 : ℝ) := Finset.sum_le_sum fun _ _ => hb _
    _ = (n % q : ℕ) := by simp
    _ ≤ q := by exact_mod_cast (Nat.mod_lt n hq).le

end LandauSiegel

namespace DirichletCharacter
p2m_export "DirichletCharacter" "LFunction zetaMul LFunction_eq_LSeries isMultiplicative_zetaMul norm_LFunction_product_ge_one LSeries_twist_vonMangoldt_eq mul norm_le_one LSeriesSummable_twist_vonMangoldt LFunction_changeLevel LFunction_ne_zero_of_one_le_re level_one zetaMul_nonneg changeLevel differentiable_LFunction changeLevel_eq_cast_of_dvd LSeriesSummable_mul LSeriesSummable_zetaMul isMultiplicative_toArithmeticFunction unit_norm_eq_one apply_eq_toArithmeticFunction_apply LSeriesSummable_of_one_lt_re LFunctionTrivChar"
p2m_open "DirichletCharacter"

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

omit [NeZero q] in
lemma periodic_natCast : Function.Periodic (fun k : ℕ ↦ χ k) q := by
  intro k; simp

lemma level_ne_one_of_ne_one (hχ : χ ≠ 1) : q ≠ 1 := by
  rintro rfl
  exact hχ (level_one χ)

lemma apply_natCast_zero_of_ne_one (hχ : χ ≠ 1) : χ ((0 : ℕ) : ZMod q) = 0 := by
  have : Fact (1 < q) := ⟨lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
    (level_ne_one_of_ne_one χ hχ).symm⟩
  rw [Nat.cast_zero, MulChar.map_zero]

lemma sum_range_level_eq_zero (hχ : χ ≠ 1) : ∑ k ∈ range q, χ k = 0 := by
  rw [LandauSiegel.sum_range_eq_sum_zmod q (fun a ↦ χ a)]
  exact MulChar.sum_eq_zero_of_ne_one hχ

theorem norm_sum_range_le (hχ : χ ≠ 1) (n : ℕ) : ‖∑ k ∈ range n, χ k‖ ≤ q :=
  LandauSiegel.norm_sum_range_le_of_periodic _ (periodic_natCast χ) (Nat.pos_of_neZero q)
    (sum_range_level_eq_zero χ hχ) (fun _ ↦ χ.norm_le_one _) n

theorem norm_sum_Icc_le (hχ : χ ≠ 1) (n : ℕ) : ‖∑ k ∈ Icc 1 n, χ k‖ ≤ q := by
  have : ∑ k ∈ Icc 1 n, χ k = ∑ k ∈ range (n + 1), χ k := by
    rw [Nat.range_succ_eq_Icc_zero, ← Finset.insert_Icc_succ_left_eq_Icc (Nat.zero_le n),
      Finset.sum_insert (by simp), Order.succ_eq_add_one, zero_add,
      apply_natCast_zero_of_ne_one χ hχ, zero_add]
  rw [this]
  exact norm_sum_range_le χ hχ (n + 1)

omit [NeZero q] in

theorem norm_sum_Icc_le_self (n : ℕ) : ‖∑ k ∈ Icc 1 n, χ k‖ ≤ n := by
  calc ‖∑ k ∈ Icc 1 n, χ k‖ ≤ ∑ k ∈ Icc 1 n, ‖χ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Icc 1 n, (1 : ℝ) := Finset.sum_le_sum fun k _ ↦ χ.norm_le_one _
    _ = n := by simp

theorem isBigO_sum_Icc (hχ : χ ≠ 1) :
    (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, χ k) =O[atTop] fun n ↦ (n : ℝ) ^ (0 : ℝ) := by
  refine Asymptotics.IsBigO.of_bound q ?_
  filter_upwards with n
  simpa using norm_sum_Icc_le χ hχ n

end DirichletCharacter

end P2M_CharacterSum

section P2M_LFunctionIntegral

open Complex Filter Topology Set MeasureTheory Asymptotics

namespace LandauSiegel

noncomputable def summatory (f : ℕ → ℂ) (t : ℝ) : ℂ := ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k

lemma summatory_apply (f : ℕ → ℂ) (t : ℝ) : summatory f t = ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, f k := rfl

lemma measurable_summatory (f : ℕ → ℂ) : Measurable (summatory f) :=
  (measurable_from_nat (f := fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, f k)).comp Nat.measurable_floor

lemma norm_summatory_le {f : ℕ → ℂ} {C : ℝ} (h : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C) (t : ℝ) :
    ‖summatory f t‖ ≤ C := h _

noncomputable def mellinSummatory (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  mellin ((Ioi 1).indicator (summatory f)) (-s)

lemma mellinSummatory_eq_integral (f : ℕ → ℂ) (s : ℂ) :
    mellinSummatory f s = ∫ t in Ioi (1:ℝ), summatory f t * (t : ℂ) ^ (-(s + 1)) := by
  have hI : Ioi (0:ℝ) ∩ Ioi 1 = Ioi 1 := by
    rw [Set.Ioi_inter_Ioi, max_eq_right zero_le_one]
  rw [mellinSummatory, mellin]
  conv_rhs => rw [← hI, ← setIntegral_indicator measurableSet_Ioi]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  by_cases ht : t ∈ Ioi (1:ℝ)
  · simp only [ht, Set.indicator_of_mem, smul_eq_mul, neg_add']
    ring
  · simp only [ht, Set.indicator_of_notMem, not_false_eq_true, smul_zero]

variable {f : ℕ → ℂ} {C : ℝ}

lemma locallyIntegrableOn_indicator_summatory (h : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C) :
    LocallyIntegrableOn ((Ioi 1).indicator (summatory f)) (Ioi 0) := by
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro k _ hk
  refine Measure.integrableOn_of_bounded (M := C) hk.measure_lt_top.ne ?_ ?_
  · exact ((measurable_summatory f).indicator measurableSet_Ioi).aestronglyMeasurable
  · have hC : 0 ≤ C := (norm_nonneg _).trans (h 0)
    filter_upwards with t
    rw [norm_indicator_eq_indicator_norm]
    exact Set.indicator_apply_le' (fun _ ↦ norm_summatory_le h t) (fun _ ↦ hC)

lemma indicator_summatory_isBigO_top (h : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C) :
    (Ioi 1).indicator (summatory f) =O[atTop] fun t : ℝ ↦ t ^ (-(0:ℝ)) := by
  refine IsBigO.of_bound |C| ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [neg_zero, Real.rpow_zero, Real.norm_eq_abs, abs_one, mul_one,
    norm_indicator_eq_indicator_norm]
  exact Set.indicator_apply_le' (fun _ ↦ (norm_summatory_le h t).trans (le_abs_self C))
    (fun _ ↦ abs_nonneg C)

lemma indicator_summatory_isBigO_zero (b : ℝ) :
    (Ioi 1).indicator (summatory f) =O[𝓝[>] 0] fun t : ℝ ↦ t ^ (-b) := by
  refine IsBigO.of_bound 0 ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with t ht
  rw [Set.indicator_of_notMem (notMem_Ioi.mpr ht.2.le), norm_zero, zero_mul]

theorem differentiableAt_mellinSummatory (h : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C) {s : ℂ}
    (hs : 0 < s.re) : DifferentiableAt ℂ (mellinSummatory f) s := by
  have : DifferentiableAt ℂ (mellin ((Ioi 1).indicator (summatory f))) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1)
      (locallyIntegrableOn_indicator_summatory h) (indicator_summatory_isBigO_top h)
      (by simpa using hs) (indicator_summatory_isBigO_zero _) (by simp)
  exact this.comp s (differentiable_id.neg).differentiableAt

theorem differentiableOn_mellinSummatory (h : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C) :
    DifferentiableOn ℂ (mellinSummatory f) {s | 0 < s.re} :=
  fun _ hs ↦ (differentiableAt_mellinSummatory h hs).differentiableWithinAt

theorem norm_mellinSummatory_le (h : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C) {s : ℂ}
    (hs : 0 < s.re) : ‖mellinSummatory f s‖ ≤ C / s.re := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (h 0)
  rw [mellinSummatory_eq_integral]
  have hint : IntegrableOn (fun t : ℝ ↦ C * t ^ (-(s.re + 1))) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul C
  calc ‖∫ t in Ioi (1:ℝ), summatory f t * (t : ℂ) ^ (-(s + 1))‖
      ≤ ∫ t in Ioi (1:ℝ), ‖summatory f t * (t : ℂ) ^ (-(s + 1))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (1:ℝ), C * t ^ (-(s.re + 1)) := by
        have hle : ∀ t ∈ Ioi (1:ℝ),
            ‖summatory f t * (t : ℂ) ^ (-(s + 1))‖ ≤ C * t ^ (-(s.re + 1)) := fun t ht ↦ by
          rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht), neg_re, add_re,
            one_re]
          exact mul_le_mul_of_nonneg_right (norm_summatory_le h t) (Real.rpow_nonneg
            (zero_lt_one.trans ht).le _)
        refine setIntegral_mono_on ?_ hint measurableSet_Ioi hle
        refine hint.mono' ?_ ?_
        · exact ((measurable_summatory f).mul
            (measurable_ofReal.pow_const _)).norm.aestronglyMeasurable
        · rw [ae_restrict_iff' measurableSet_Ioi]
          filter_upwards with t ht
          rw [norm_norm]
          exact hle t ht
    _ = C / s.re := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) zero_lt_one]
        rw [Real.one_rpow, show -(s.re + 1) + 1 = -s.re by ring, neg_div_neg_eq, one_div,
          div_eq_mul_inv]

theorem LSeries_eq_mul_mellinSummatory (h : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C)
    (hf : ∀ n, ‖f n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    LSeries f s = s * mellinSummatory f s := by
  rw [mellinSummatory_eq_integral]
  refine LSeries_eq_mul_integral f le_rfl (zero_lt_one.trans hs) ?_ ?_
  · refine LSeriesSummable_of_sum_norm_bigO (r := 1) ?_ zero_le_one hs
    refine IsBigO.of_bound 1 ?_
    filter_upwards with n
    rw [one_mul, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _),
      Real.rpow_one, Real.norm_natCast]
    calc ∑ k ∈ Finset.Icc 1 n, ‖f k‖ ≤ ∑ k ∈ Finset.Icc 1 n, (1:ℝ) :=
          Finset.sum_le_sum fun k _ ↦ hf k
      _ = n := by simp
  · exact IsBigO.of_bound |C| (by
      filter_upwards [eventually_ge_atTop 1] with n hn
      simpa using (h n).trans (le_abs_self C))

theorem norm_mellinSummatory_one_le (h : ∀ n, ‖∑ k ∈ Finset.Icc 1 n, f k‖ ≤ C) (hC : 1 ≤ C)
    (hf : ∀ n, ‖f n‖ ≤ 1) : ‖mellinSummatory f 1‖ ≤ Real.log C + 1 := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  rw [mellinSummatory_eq_integral]

  let g : ℝ → ℝ := fun t ↦ if t ≤ C then t⁻¹ else C * t ^ (-2:ℝ)
  have hg1 : IntegrableOn g (Ioc 1 C) :=
    ((continuousOn_inv₀.mono (by intro t ht; exact (zero_lt_one.trans_le ht.1).ne' :
      Icc (1:ℝ) C ⊆ {t | t ≠ 0})).integrableOn_Icc.mono_set Ioc_subset_Icc_self).congr_fun
      (fun t ht ↦ by simp [g, ht.2]) measurableSet_Ioc
  have hg2 : IntegrableOn g (Ioi C) := by
    have : IntegrableOn (fun t : ℝ ↦ C * t ^ (-2:ℝ)) (Ioi C) :=
      (integrableOn_Ioi_rpow_of_lt (show (-2:ℝ) < -1 by norm_num) hC0).const_mul C
    exact this.congr_fun (fun t ht ↦ by simp [g, not_le.mpr (mem_Ioi.mp ht)]) measurableSet_Ioi
  have hg : IntegrableOn g (Ioi 1) := by
    rw [← Ioc_union_Ioi_eq_Ioi hC]; exact hg1.union hg2
  have hint : ∫ t in Ioi 1, g t = Real.log C + 1 := by
    rw [← Ioc_union_Ioi_eq_Ioi hC, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      hg1 hg2]
    congr 1
    · rw [setIntegral_congr_fun measurableSet_Ioc (g := fun t : ℝ ↦ t⁻¹)
        (fun t ht ↦ by simp [g, ht.2]), ← intervalIntegral.integral_of_le hC,
        integral_inv_of_pos zero_lt_one hC0, div_one]
    · rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t : ℝ ↦ C * t ^ (-2:ℝ))
        (fun t ht ↦ by simp [g, not_le.mpr (mem_Ioi.mp ht)]), integral_const_mul,
        integral_Ioi_rpow_of_lt (show (-2:ℝ) < -1 by norm_num) hC0]
      rw [show (-2:ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
      field_simp

  have hle : ∀ t ∈ Ioi (1:ℝ), ‖summatory f t * (t : ℂ) ^ (-((1:ℂ) + 1))‖ ≤ g t := by
    intro t ht
    have ht0 : 0 < t := zero_lt_one.trans ht
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, show (-((1:ℂ) + 1)).re = -2 by norm_num]
    by_cases htC : t ≤ C
    · simp only [g, htC, ↓reduceIte]
      calc ‖summatory f t‖ * t ^ (-2:ℝ) ≤ t * t ^ (-2:ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg ht0.le _)
            calc ‖summatory f t‖ ≤ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖f k‖ := norm_sum_le _ _
              _ ≤ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (1:ℝ) := Finset.sum_le_sum fun k _ ↦ hf k
              _ = ⌊t⌋₊ := by simp
              _ ≤ t := Nat.floor_le ht0.le
        _ = t⁻¹ := by
            rw [show (-2:ℝ) = -1 + -1 by norm_num, Real.rpow_add ht0, Real.rpow_neg_one,
              ← mul_assoc, mul_inv_cancel₀ ht0.ne', one_mul]
    · simp only [g, htC, ↓reduceIte]
      exact mul_le_mul_of_nonneg_right (norm_summatory_le h t) (Real.rpow_nonneg ht0.le _)
  calc ‖∫ t in Ioi (1:ℝ), summatory f t * (t : ℂ) ^ (-((1:ℂ) + 1))‖
      ≤ ∫ t in Ioi (1:ℝ), ‖summatory f t * (t : ℂ) ^ (-((1:ℂ) + 1))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (1:ℝ), g t := by
        refine setIntegral_mono_on ?_ hg measurableSet_Ioi hle
        refine hg.mono' ?_ ?_
        · exact ((measurable_summatory f).mul
            (measurable_ofReal.pow_const _)).norm.aestronglyMeasurable
        · rw [ae_restrict_iff' measurableSet_Ioi]
          filter_upwards with t ht
          rw [norm_norm]
          exact hle t ht
    _ = Real.log C + 1 := hint

theorem conj_mellinSummatory (hf : ∀ n, starRingEnd ℂ (f n) = f n) (s : ℂ) :
    starRingEnd ℂ (mellinSummatory f s) = mellinSummatory f (starRingEnd ℂ s) := by
  rw [mellinSummatory_eq_integral, mellinSummatory_eq_integral]
  refine (integral_conj (f := fun t : ℝ ↦ summatory f t * (t : ℂ) ^ (-(s + 1)))).symm.trans ?_
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
  have ht0 : 0 < t := zero_lt_one.trans ht
  rw [map_mul, summatory_apply, map_sum]
  congr 1
  · exact Finset.sum_congr rfl fun n _ ↦ hf n
  · have harg : (t : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg ht0.le]; exact Real.pi_ne_zero.symm
    calc starRingEnd ℂ ((t : ℂ) ^ (-(s + 1)))
        = starRingEnd ℂ ((t : ℂ) ^ (starRingEnd ℂ (starRingEnd ℂ (-(s + 1))))) := by
          rw [Complex.conj_conj]
      _ = (starRingEnd ℂ (t : ℂ)) ^ (starRingEnd ℂ (-(s + 1))) :=
          (Complex.conj_cpow _ _ harg).symm
      _ = (t : ℂ) ^ (-(starRingEnd ℂ s + 1)) := by
          rw [Complex.conj_ofReal, map_neg, map_add, map_one]

theorem im_mellinSummatory_ofReal (hf : ∀ n, starRingEnd ℂ (f n) = f n) (σ : ℝ) :
    (mellinSummatory f σ).im = 0 := by
  have := conj_mellinSummatory hf σ
  rw [Complex.conj_ofReal] at this
  exact Complex.conj_eq_iff_im.mp this

end LandauSiegel

namespace DirichletCharacter
p2m_export "DirichletCharacter" "LFunction zetaMul LFunction_eq_LSeries isMultiplicative_zetaMul norm_LFunction_product_ge_one LSeries_twist_vonMangoldt_eq mul norm_le_one LSeriesSummable_twist_vonMangoldt LFunction_changeLevel LFunction_ne_zero_of_one_le_re level_one zetaMul_nonneg changeLevel differentiable_LFunction changeLevel_eq_cast_of_dvd LSeriesSummable_mul LSeriesSummable_zetaMul isMultiplicative_toArithmeticFunction unit_norm_eq_one apply_eq_toArithmeticFunction_apply LSeriesSummable_of_one_lt_re LFunctionTrivChar"
p2m_open "DirichletCharacter"

open LandauSiegel

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

theorem LFunction_eq_mul_mellinSummatory (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    LFunction χ s = s * mellinSummatory (χ ·) s := by
  set U : Set ℂ := {s : ℂ | 0 < s.re} with hUdef
  have hU : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hO : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have h := norm_sum_Icc_le χ hχ
  have hg : AnalyticOnNhd ℂ (fun s ↦ s * mellinSummatory (χ ·) s) U :=
    (differentiableOn_id.mul (differentiableOn_mellinSummatory h)).analyticOnNhd hO
  have hf : AnalyticOnNhd ℂ (LFunction χ) U :=
    (differentiable_LFunction hχ).differentiableOn.analyticOnNhd hO
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg hU (z₀ := 2) (by simp [hUdef]) ?_ hs
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (by simp : (1:ℝ) < (2:ℂ).re)] with s hs'
  rw [LFunction_eq_LSeries χ hs']
  exact LSeries_eq_mul_mellinSummatory h (fun n ↦ χ.norm_le_one _) hs'

theorem norm_LFunction_le (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ‖LFunction χ s‖ ≤ q * ‖s‖ / s.re := by
  rw [LFunction_eq_mul_mellinSummatory χ hχ hs, norm_mul]
  calc ‖s‖ * ‖mellinSummatory (χ ·) s‖ ≤ ‖s‖ * (q / s.re) :=
        mul_le_mul_of_nonneg_left (norm_mellinSummatory_le (norm_sum_Icc_le χ hχ) hs)
          (norm_nonneg _)
    _ = q * ‖s‖ / s.re := by ring

theorem norm_LFunction_one_le (hχ : χ ≠ 1) : ‖LFunction χ 1‖ ≤ Real.log q + 1 := by
  rw [LFunction_eq_mul_mellinSummatory χ hχ (by simp), one_mul]
  exact norm_mellinSummatory_one_le (norm_sum_Icc_le χ hχ)
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)) (fun n ↦ χ.norm_le_one _)

theorem conj_LFunction (hχ : χ ≠ 1) (hreal : ∀ a, starRingEnd ℂ (χ a) = χ a) {s : ℂ}
    (hs : 0 < s.re) : starRingEnd ℂ (LFunction χ s) = LFunction χ (starRingEnd ℂ s) := by
  rw [LFunction_eq_mul_mellinSummatory χ hχ hs, LFunction_eq_mul_mellinSummatory χ hχ
    (by simpa using hs), map_mul, conj_mellinSummatory (fun n ↦ hreal _)]

private theorem _root_.DirichletCharacter.im_LFunction_ofReal (hχ : χ ≠ 1) (hreal : ∀ a, starRingEnd ℂ (χ a) = χ a) {σ : ℝ}
    (hσ : 0 < σ) : (LFunction χ σ).im = 0 := by
  have := conj_LFunction χ hχ hreal (s := σ) (by simpa using hσ)
  rw [Complex.conj_ofReal] at this
  exact Complex.conj_eq_iff_im.mp this

p2m_export "DirichletCharacter" "im_LFunction_ofReal"
end DirichletCharacter

end P2M_LFunctionIntegral

section P2M_Coefficients

open scoped ComplexOrder
open ArithmeticFunction PowerSeries Finset

namespace LandauSiegel

noncomputable def localSeries (f : ArithmeticFunction ℂ) (p : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun k ↦ f (p ^ k)

@[scoped simp] lemma coeff_localSeries (f : ArithmeticFunction ℂ) (p k : ℕ) :
    coeff k (localSeries f p) = f (p ^ k) := coeff_mk _ _

lemma localSeries_mul (f g : ArithmeticFunction ℂ) {p : ℕ} (hp : p.Prime) :
    localSeries (f * g) p = localSeries f p * localSeries g p := by
  ext k
  rw [coeff_localSeries, coeff_mul, mul_apply, Nat.sum_divisorsAntidiagonal
    (f := fun x y ↦ f x * g y), Nat.sum_divisors_prime_pow hp,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [coeff_localSeries, coeff_localSeries, Nat.pow_div (Nat.lt_succ_iff.mp (mem_range.mp hi))
    hp.pos]

noncomputable def geom (x : ℂ) : PowerSeries ℂ := PowerSeries.mk fun k ↦ x ^ k

@[scoped simp] lemma coeff_geom (x : ℂ) (k : ℕ) : coeff k (geom x) = x ^ k := coeff_mk _ _

lemma geom_zero : geom 0 = 1 := by
  ext k; cases k <;> simp [coeff_one]

lemma localSeries_zeta {p : ℕ} (hp : p.Prime) :
    localSeries (ArithmeticFunction.zeta : ArithmeticFunction ℂ) p = geom 1 := by
  ext k; simp [natCoe_apply, zeta_apply, hp.ne_zero]

lemma localSeries_toArithmeticFunction {N : ℕ} (χ : DirichletCharacter ℂ N) {p : ℕ}
    (hp : p.Prime) : localSeries (toArithmeticFunction (χ ·)) p = geom (χ p) := by
  ext k; simp [toArithmeticFunction, hp.ne_zero]

lemma localSeries_pmul_toArithmeticFunction {N₁ N₂ : ℕ} (χ₁ : DirichletCharacter ℂ N₁)
    (χ₂ : DirichletCharacter ℂ N₂) {p : ℕ} (hp : p.Prime) :
    localSeries ((toArithmeticFunction (χ₁ ·)).pmul (toArithmeticFunction (χ₂ ·))) p
      = geom (χ₁ p * χ₂ p) := by
  ext k; simp [toArithmeticFunction, hp.ne_zero, mul_pow]

def CoeffNonneg (A : PowerSeries ℂ) : Prop := ∀ k, 0 ≤ coeff k A

lemma CoeffNonneg.mul {A B : PowerSeries ℂ} (hA : CoeffNonneg A) (hB : CoeffNonneg B) :
    CoeffNonneg (A * B) := fun k ↦ by
  rw [coeff_mul]; exact Finset.sum_nonneg fun x _ ↦ mul_nonneg (hA _) (hB _)

lemma coeffNonneg_one : CoeffNonneg 1 := fun k ↦ by
  rw [coeff_one]; split_ifs <;> simp

lemma coeffNonneg_geom_one : CoeffNonneg (geom 1) := fun k ↦ by simp

lemma coeffNonneg_geom_one_mul_geom_neg_one : CoeffNonneg (geom 1 * geom (-1)) := fun k ↦ by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ coeff i (geom 1) *
    coeff j (geom (-1))) k]
  simp only [coeff_geom, one_pow, one_mul]
  rw [← Finset.sum_range_reflect (fun j ↦ (-1:ℂ) ^ (k - j)) (k + 1)]
  simp only [add_tsub_cancel_right]
  rw [Finset.sum_congr rfl (g := fun j ↦ (-1:ℂ) ^ j) fun j hj ↦ by
    rw [Nat.sub_sub_self (Nat.lt_succ_iff.mp (mem_range.mp hj))], neg_one_geom_sum]
  split_ifs <;> simp

lemma coeffNonneg_local (ε₁ ε₂ : ℂ) (h₁ : ε₁ = 0 ∨ ε₁ = 1 ∨ ε₁ = -1)
    (h₂ : ε₂ = 0 ∨ ε₂ = 1 ∨ ε₂ = -1) :
    CoeffNonneg ((geom 1 * geom ε₁) * (geom ε₂ * geom (ε₁ * ε₂))) := by
  have A := coeffNonneg_geom_one
  have B := coeffNonneg_geom_one_mul_geom_neg_one
  rcases h₁ with rfl | rfl | rfl <;> rcases h₂ with rfl | rfl | rfl <;>
    simp only [mul_zero, zero_mul, mul_one, one_mul, neg_mul, neg_neg, geom_zero]
  · exact A
  · exact A.mul A
  · exact B
  · exact A.mul A
  · exact (A.mul A).mul (A.mul A)
  · rw [show geom 1 * geom 1 * (geom (-1) * geom (-1)) = (geom 1 * geom (-1)) * (geom 1 * geom (-1))
      by ring]
    exact B.mul B
  · exact B
  · exact B.mul B
  · rw [show geom 1 * geom (-1) * (geom (-1) * geom 1) = (geom 1 * geom (-1)) * (geom 1 * geom (-1))
      by ring]
    exact B.mul B

variable {N₁ N₂ : ℕ} (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂)

noncomputable def siegelCoeff : ArithmeticFunction ℂ :=
  χ₁.zetaMul *
    (toArithmeticFunction (χ₂ ·) *
      (toArithmeticFunction (χ₁ ·)).pmul (toArithmeticFunction (χ₂ ·)))

lemma isMultiplicative_siegelCoeff : (siegelCoeff χ₁ χ₂).IsMultiplicative := by
  have h₁ : (toArithmeticFunction (χ₁ ·) : ArithmeticFunction ℂ).IsMultiplicative :=
    DirichletCharacter.isMultiplicative_toArithmeticFunction χ₁
  have h₂ : (toArithmeticFunction (χ₂ ·) : ArithmeticFunction ℂ).IsMultiplicative :=
    DirichletCharacter.isMultiplicative_toArithmeticFunction χ₂
  exact (DirichletCharacter.isMultiplicative_zetaMul χ₁).mul (h₂.mul (h₁.pmul h₂))

lemma localSeries_siegelCoeff {p : ℕ} (hp : p.Prime) :
    localSeries (siegelCoeff χ₁ χ₂) p
      = (geom 1 * geom (χ₁ p)) * (geom (χ₂ p) * geom (χ₁ p * χ₂ p)) := by
  rw [siegelCoeff, DirichletCharacter.zetaMul, localSeries_mul _ _ hp, localSeries_mul _ _ hp,
    localSeries_mul _ _ hp, localSeries_zeta hp, localSeries_toArithmeticFunction _ hp,
    localSeries_toArithmeticFunction _ hp, localSeries_pmul_toArithmeticFunction _ _ hp]

lemma values_of_sq_eq_one {N : ℕ} {χ : DirichletCharacter ℂ N} (hχ : χ ^ 2 = 1) (a : ZMod N) :
    χ a = 0 ∨ χ a = 1 ∨ χ a = -1 :=
  MulChar.isQuadratic_iff_sq_eq_one.mpr hχ a

theorem siegelCoeff_prime_pow_nonneg (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1) {p : ℕ} (hp : p.Prime)
    (k : ℕ) : 0 ≤ siegelCoeff χ₁ χ₂ (p ^ k) := by
  rw [← coeff_localSeries, localSeries_siegelCoeff _ _ hp]
  exact coeffNonneg_local _ _ (values_of_sq_eq_one h₁ _) (values_of_sq_eq_one h₂ _) k

theorem siegelCoeff_nonneg (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1) (n : ℕ) :
    0 ≤ siegelCoeff χ₁ χ₂ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, le_refl]
  · simp only [(isMultiplicative_siegelCoeff χ₁ χ₂).multiplicative_factorization _ hn]
    exact Finset.prod_nonneg fun p hp ↦
        siegelCoeff_prime_pow_nonneg χ₁ χ₂ h₁ h₂ (Nat.prime_of_mem_primeFactors hp) _

theorem siegelCoeff_one : siegelCoeff χ₁ χ₂ 1 = 1 := (isMultiplicative_siegelCoeff χ₁ χ₂).map_one

theorem siegelCoeff_zero : siegelCoeff χ₁ χ₂ 0 = 0 := ArithmeticFunction.map_zero

end LandauSiegel
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

end P2M_Coefficients
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

section P2M_ProductCharacter

p2m_open "ArithmeticFunction DirichletCharacter P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.DirichletCharacter"

namespace LandauSiegel

variable {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂]
  (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂)

noncomputable def productChar : DirichletCharacter ℂ (N₁ * N₂) :=
  changeLevel (dvd_mul_right N₁ N₂) χ₁ * changeLevel (dvd_mul_left N₂ N₁) χ₂

lemma changeLevel_apply_natCast {N M : ℕ} [NeZero M] (h : N ∣ M) (χ : DirichletCharacter ℂ N)
    (n : ℕ) (hn : IsUnit (n : ZMod M)) : changeLevel h χ (n : ZMod M) = χ (n : ZMod N) := by
  obtain ⟨u, hu⟩ := hn
  rw [← hu, changeLevel_eq_cast_of_dvd χ h u, hu, ZMod.cast_natCast h]

theorem productChar_apply_natCast (n : ℕ) : productChar χ₁ χ₂ n = χ₁ n * χ₂ n := by
  rw [productChar, MulChar.mul_apply]
  by_cases hn : IsUnit (n : ZMod (N₁ * N₂))
  · rw [changeLevel_apply_natCast _ _ _ hn, changeLevel_apply_natCast _ _ _ hn]
  · rw [MulChar.map_nonunit _ hn, zero_mul]
    rw [ZMod.isUnit_iff_coprime] at hn
    rcases (not_and_or.mp (mt (fun h ↦ Nat.Coprime.mul_right h.1 h.2) hn)) with h | h
    · rw [MulChar.map_nonunit _ (mt (ZMod.isUnit_iff_coprime _ _).mp h), zero_mul]
    · rw [MulChar.map_nonunit _ (mt (ZMod.isUnit_iff_coprime _ _).mp h), mul_zero]

omit [NeZero N₁] [NeZero N₂] in
theorem productChar_sq_eq_one (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1) :
    productChar χ₁ χ₂ ^ 2 = 1 := by
  rw [productChar, mul_pow, ← map_pow, ← map_pow, h₁, h₂, map_one, map_one, one_mul]

section LSeriesIdentity

variable {s : ℂ}

lemma LSeriesSummable_toArithmeticFunction {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hs : 1 < s.re) : LSeriesSummable (toArithmeticFunction (χ ·)) s :=
  (LSeriesSummable_congr _ fun h ↦ (χ.apply_eq_toArithmeticFunction_apply h).symm).mpr
      <| ZMod.LSeriesSummable_of_one_lt_re χ hs

lemma LSeries_toArithmeticFunction {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hs : 1 < s.re) : LSeries (toArithmeticFunction (χ ·)) s = LFunction χ s := by
  rw [LFunction_eq_LSeries χ hs]
  exact (LSeries_congr χ.apply_eq_toArithmeticFunction_apply s).symm

lemma pmul_toArithmeticFunction_eq :
    (toArithmeticFunction (χ₁ ·)).pmul (toArithmeticFunction (χ₂ ·))
      = (toArithmeticFunction (productChar χ₁ χ₂ ·) : ArithmeticFunction ℂ) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [toArithmeticFunction]
  · simp [pmul_apply, toArithmeticFunction, hn, productChar_apply_natCast]

lemma LSeriesSummable_siegelCoeff (hs : 1 < s.re) :
    LSeriesSummable (siegelCoeff χ₁ χ₂) s := by
  rw [siegelCoeff, pmul_toArithmeticFunction_eq]
  exact ArithmeticFunction.LSeriesSummable_mul (LSeriesSummable_zetaMul χ₁ hs)
    (ArithmeticFunction.LSeriesSummable_mul (LSeriesSummable_toArithmeticFunction χ₂ hs)
      (LSeriesSummable_toArithmeticFunction _ hs))

theorem LSeries_siegelCoeff (hs : 1 < s.re) :
    LSeries (siegelCoeff χ₁ χ₂) s =
      riemannZeta s * LFunction χ₁ s * (LFunction χ₂ s * LFunction (productChar χ₁ χ₂) s) := by
  have h₁ := LSeriesSummable_toArithmeticFunction χ₁ hs
  have h₂ := LSeriesSummable_toArithmeticFunction χ₂ hs
  have h₃ := LSeriesSummable_toArithmeticFunction (productChar χ₁ χ₂) hs
  have hζ : LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s :=
    LSeriesSummable_zeta_iff.mpr hs
  rw [siegelCoeff, pmul_toArithmeticFunction_eq, zetaMul, ← coe_mul, ← coe_mul, ← coe_mul,
    LSeries_convolution' (hζ.convolution h₁) (h₂.convolution h₃),
    LSeries_convolution' hζ h₁, LSeries_convolution' h₂ h₃,
    LSeries_toArithmeticFunction χ₁ hs,
    LSeries_toArithmeticFunction χ₂ hs, LSeries_toArithmeticFunction _ hs,
    ← LSeries_zeta_eq_riemannZeta hs]
  simp_rw [← natCoe_apply]

end LSeriesIdentity
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

end LandauSiegel
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

end P2M_ProductCharacter
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

section P2M_Estermann

open scoped ComplexOrder
p2m_open "Complex Filter Topology Set Metric Finset Set.Finset"

namespace LandauSiegel

namespace Estermann

variable {a : ℕ → ℂ} {G : ℂ → ℂ} {lam M β : ℝ}

noncomputable def c (G : ℂ → ℂ) (m : ℕ) : ℂ := (m.factorial : ℂ)⁻¹ * iteratedDeriv m G 2

lemma hasSum_c (hG : Differentiable ℂ G) (z : ℂ) :
    HasSum (fun m ↦ c G m * (z - 2) ^ m) (G z) := by
  have := Complex.hasSum_taylorSeries_of_entire hG 2 z
  convert this using 1
  all_goals first | rfl | skip
  ext m
  simp only [c, smul_eq_mul]
  ring

lemma norm_c_le (hG : Differentiable ℂ G) (hM : ∀ s ∈ sphere (2:ℂ) (3/2), ‖G s‖ ≤ M) (m : ℕ) :
    ‖c G m‖ ≤ M * (2/3) ^ m := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m (by norm_num : (0:ℝ) < 3/2)
    hG.diffContOnCl hM
  rw [c, norm_mul, norm_inv, Complex.norm_natCast]
  have hf : (0:ℝ) < m.factorial := by exact_mod_cast m.factorial_pos
  calc (m.factorial : ℝ)⁻¹ * ‖iteratedDeriv m G 2‖
      ≤ (m.factorial : ℝ)⁻¹ * (m.factorial * M / (3/2) ^ m) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hf.le)
    _ = M * (2/3) ^ m := by
        rw [div_eq_mul_inv, ← inv_pow, show ((3:ℝ)/2)⁻¹ = 2/3 by norm_num]
        field_simp

lemma iteratedDeriv_inv_sub_one (m : ℕ) :
    iteratedDeriv m (fun s : ℂ ↦ (s - 1)⁻¹) 2 = (-1) ^ m * m.factorial := by
  have : (fun s : ℂ ↦ (s - 1)⁻¹) = fun s ↦ (1 * s - 1)⁻¹ := by simp
  rw [this, iteratedDeriv_eq_iterate, iter_deriv_inv_linear_sub]
  norm_num

lemma contDiffAt_inv_sub_one (m : ℕ) : ContDiffAt ℂ m (fun s : ℂ ↦ (s - 1)⁻¹) 2 :=
  ((contDiffAt_id.sub contDiffAt_const).inv (by norm_num))

lemma c_alternating (ha : 0 ≤ a)
    (hsum : ∀ y : ℝ, 1 < y → LSeriesSummable a y)
    (hG2 : ∀ s : ℂ, 1 < s.re → G s = LSeries a s - lam / (s - 1)) (m : ℕ) :
    0 ≤ (-1) ^ m * c G m + lam := by
  have habs : LSeries.abscissaOfAbsConv a < ((2:ℝ):ℂ).re := by
    simp only [ofReal_ofNat, re_ofNat]
    exact (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable hsum).trans_lt
      (by exact_mod_cast one_lt_two)

  have hev : G =ᶠ[𝓝 2] (LSeries a - fun s ↦ (lam : ℂ) * (s - 1)⁻¹) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by simp : (1:ℝ) < (2:ℂ).re)] with s hs
    rw [Pi.sub_apply, hG2 s hs, div_eq_mul_inv]
  have hL : ContDiffAt ℂ m (LSeries a) 2 :=
    (LSeries_analyticOnNhd a 2 (by simpa using habs)).contDiffAt
  have hR : ContDiffAt ℂ m (fun s : ℂ ↦ lam * (s - 1)⁻¹) 2 :=
    contDiffAt_const.mul (contDiffAt_inv_sub_one m)
  have hderiv : iteratedDeriv m G 2
      = iteratedDeriv m (LSeries a) 2 - lam * ((-1) ^ m * m.factorial) := by
    rw [hev.iteratedDeriv_eq, iteratedDeriv_sub hL hR, iteratedDeriv_const_mul _
      (contDiffAt_inv_sub_one m), iteratedDeriv_inv_sub_one]
  have hpos := LSeries.iteratedDeriv_alternating ha habs m
  rw [ofReal_ofNat] at hpos
  have hf : (0:ℂ) < (m.factorial : ℂ)⁻¹ := by
    rw [inv_pos]; exact_mod_cast m.factorial_pos
  have key : (-1) ^ m * c G m + lam = (m.factorial : ℂ)⁻¹ *
      ((-1) ^ m * iteratedDeriv m (LSeries a) 2) := by
    rw [c, hderiv]
    have h1 : ((-1:ℂ) ^ m) * (-1) ^ m = 1 := by
      rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    have h2 : (m.factorial : ℂ)⁻¹ * m.factorial = 1 :=
      inv_mul_cancel₀ (by exact_mod_cast m.factorial_ne_zero)
    linear_combination (-(lam:ℂ) * ((m.factorial:ℂ)⁻¹ * m.factorial)) * h1 + (-(lam:ℂ)) * h2
  rw [key]
  exact mul_nonneg hf.le hpos

lemma one_sub_lam_le_c_zero (ha : 0 ≤ a) (ha1 : a 1 = 1)
    (hsum : ∀ y : ℝ, 1 < y → LSeriesSummable a y)
    (hG2 : ∀ s : ℂ, 1 < s.re → G s = LSeries a s - lam / (s - 1)) :
    1 - lam ≤ (c G 0).re := by
  have h2 := hsum 2 one_lt_two
  have hL : (1:ℂ) ≤ LSeries a (2:ℝ) := by
    calc (1:ℂ) = LSeries.term a (2:ℝ) 1 := by simp [ha1]
      _ ≤ LSeries a (2:ℝ) := h2.le_tsum 1 fun n _ ↦ ?_
    rw [LSeries.term_def]
    split_ifs with h0
    · exact le_rfl
    · rw [div_eq_mul_inv]; exact mul_nonneg (ha n) (inv_natCast_cpow_ofReal_pos h0 2).le
  have hc : c G 0 = LSeries a (2:ℝ) - lam := by
    simp only [c, Nat.factorial_zero, Nat.cast_one, inv_one, iteratedDeriv_zero, one_mul]
    rw [hG2 2 (by simp), ofReal_ofNat]
    norm_num
  rw [hc, sub_re, ofReal_re]
  exact sub_le_sub_right (Complex.le_def.mp hL).1 _

lemma tail_const_le (hM : 0 ≤ M) :
    6 * M * (5/6:ℝ) ^ ⌈Real.log (12 * (M + 1)) / Real.log (6/5)⌉₊ ≤ 1/2 := by
  set L := Real.log (12 * (M + 1)) / Real.log (6/5) with hL
  set K := ⌈L⌉₊ with hK
  have hlog : 0 < Real.log (6/5:ℝ) := Real.log_pos (by norm_num)
  have h12 : (1:ℝ) ≤ 12 * (M + 1) := by linarith
  have hL0 : 0 ≤ L := div_nonneg (Real.log_nonneg h12) hlog.le

  have hpow : 12 * (M + 1) ≤ (6/5:ℝ) ^ K := by
    have h1 : (6/5:ℝ) ^ (L:ℝ) = 12 * (M + 1) := by
      rw [Real.rpow_def_of_pos (by norm_num), hL, mul_div_cancel₀ _ hlog.ne',
        Real.exp_log (by linarith)]
    rw [← h1, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil L)
  have hpos : (0:ℝ) < (6/5:ℝ) ^ K := by positivity
  have : (5/6:ℝ) ^ K = ((6/5:ℝ) ^ K)⁻¹ := by
    rw [← inv_pow]; norm_num
  rw [this]
  rw [show 6 * M * ((6/5:ℝ) ^ K)⁻¹ = 6 * M / (6/5:ℝ) ^ K by ring]
  rw [div_le_iff₀ hpos]
  nlinarith

theorem main (hG : Differentiable ℂ G) (ha : 0 ≤ a) (ha1 : a 1 = 1)
    (hsum : ∀ y : ℝ, 1 < y → LSeriesSummable a y)
    (hlam : 0 ≤ lam) (hM : 0 ≤ M)
    (hG2 : ∀ s : ℂ, 1 < s.re → G s = LSeries a s - lam / (s - 1))
    (hbound : ∀ s ∈ sphere (2:ℂ) (3/2), ‖G s‖ ≤ M)
    (hβ : 3/4 ≤ β) (hβ1 : β < 1) (hGβ : (G β).re ≤ lam / (1 - β)) :
    (1 - β) / 2 * Real.exp (-((1 - β) * (Real.log (12 * (M + 1)) / Real.log (6/5) + 1))) ≤ lam := by
  set L := Real.log (12 * (M + 1)) / Real.log (6/5) with hL
  set K := ⌈L⌉₊ with hK
  set x : ℝ := 2 - β with hx
  have hx1 : 1 < x := by rw [hx]; linarith
  have hx54 : x ≤ 5/4 := by rw [hx]; linarith
  have hx0 : 0 ≤ x := by linarith
  have hlog : 0 < Real.log (6/5:ℝ) := Real.log_pos (by norm_num)
  have hL0 : 0 ≤ L := div_nonneg (Real.log_nonneg (by linarith)) hlog.le
  have hKL : (K:ℝ) < L + 1 := Nat.ceil_lt_add_one hL0
  have hK1 : 1 ≤ K := by
    refine Nat.one_le_iff_ne_zero.mpr fun h ↦ ?_
    have : L ≤ 0 := by
      have := Nat.le_ceil L
      rwa [← hK, h, Nat.cast_zero] at this
    have hL1 : 0 < L := by
      refine div_pos (Real.log_pos ?_) hlog
      linarith
    linarith

  let f : ℕ → ℂ := fun m ↦ c G m * ((β:ℂ) - 2) ^ m
  have hf : HasSum f (G β) := hasSum_c hG β
  have hsplit : (∑ m ∈ range K, f m) + ∑' m, f (m + K) = G β :=
    (hf.summable.sum_add_tsum_nat_add K).trans hf.tsum_eq

  have hfm : ∀ m, ‖f m‖ ≤ M * (5/6:ℝ) ^ m := by
    intro m
    rw [norm_mul, norm_pow, show ((β:ℂ) - 2) = ((β - 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, show |β - 2| = x by rw [abs_sub_comm, abs_of_pos (by linarith), hx]]
    calc ‖c G m‖ * x ^ m ≤ M * (2/3:ℝ) ^ m * x ^ m :=
          mul_le_mul_of_nonneg_right (norm_c_le hG hbound m) (pow_nonneg hx0 m)
      _ = M * ((2/3:ℝ) * x) ^ m := by rw [mul_pow]; ring
      _ ≤ M * (5/6:ℝ) ^ m := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) m) hM
  have htail : ‖∑' m, f (m + K)‖ ≤ 6 * M * (5/6:ℝ) ^ K := by
    have hg : HasSum (fun m : ℕ ↦ M * (5/6:ℝ) ^ K * (5/6:ℝ) ^ m) (M * (5/6:ℝ) ^ K * (1 - 5/6)⁻¹) :=
      (hasSum_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    have := tsum_of_norm_bounded hg fun m ↦ (by
      calc ‖f (m + K)‖ ≤ M * (5/6:ℝ) ^ (m + K) := hfm _
        _ = M * (5/6:ℝ) ^ K * (5/6:ℝ) ^ m := by rw [pow_add]; ring)
    calc ‖∑' m, f (m + K)‖ ≤ M * (5/6:ℝ) ^ K * (1 - 5/6)⁻¹ := this
      _ = 6 * M * (5/6:ℝ) ^ K := by norm_num; ring
  have htail' : -(1/2:ℝ) ≤ (∑' m, f (m + K)).re := by
    have h1 := tail_const_le hM
    have h2 : |(∑' m, f (m + K)).re| ≤ ‖∑' m, f (m + K)‖ := Complex.abs_re_le_norm _
    rw [← hL, ← hK] at h1
    have := neg_le_of_abs_le h2
    linarith

  have hre : ∀ m, (f m).re = (c G m).re * (β - 2) ^ m := by
    intro m
    simp only [f]
    rw [show ((β:ℂ) - 2) ^ m = (((β - 2) ^ m : ℝ) : ℂ) by push_cast; ring, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hterm : ∀ m, -lam * x ^ m ≤ (f m).re := by
    intro m
    rw [hre, show (β - 2) ^ m = (-1) ^ m * x ^ m by rw [← mul_pow]; congr 1; rw [hx]; ring,
      ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hx0 m)
    have h := c_alternating ha hsum hG2 m
    have h' := (Complex.le_def.mp h).1
    simp only [Complex.zero_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re] at h'
    have hi : ((-1:ℂ) ^ m).im = 0 := by
      rw [show (-1:ℂ) = ((-1:ℝ):ℂ) by norm_num, ← Complex.ofReal_pow, Complex.ofReal_im]
    have hr : ((-1:ℂ) ^ m).re = (-1) ^ m := by
      rw [show (-1:ℂ) = ((-1:ℝ):ℂ) by norm_num, ← Complex.ofReal_pow, Complex.ofReal_re]
    rw [hi, hr] at h'
    linarith
  have hhead : 1 - lam * ((x ^ K - 1) / (x - 1)) ≤ (∑ m ∈ range K, f m).re := by
    rw [Complex.re_sum, ← geom_sum_eq hx1.ne' K]
    obtain ⟨K', hK'⟩ : ∃ K', K = K' + 1 := ⟨K - 1, (Nat.sub_add_cancel hK1).symm⟩
    rw [hK', Finset.sum_range_succ', Finset.sum_range_succ', pow_zero]
    have h0 : 1 - lam ≤ (f 0).re := by
      rw [hre, pow_zero, mul_one]; exact one_sub_lam_le_c_zero ha ha1 hsum hG2
    have h1 : ∑ m ∈ range K', -(lam * x ^ (m + 1)) ≤ ∑ m ∈ range K', (f (m + 1)).re :=
      Finset.sum_le_sum fun m _ ↦ by have := hterm (m + 1); linarith
    have h2 : ∑ m ∈ range K', -(lam * x ^ (m + 1)) = -∑ m ∈ range K', lam * x ^ (m + 1) :=
      Finset.sum_neg_distrib ..
    have h3 : ∑ m ∈ range K', lam * x ^ (m + 1) = lam * ∑ m ∈ range K', x ^ (m + 1) :=
      (Finset.mul_sum ..).symm
    linarith

  have hGβ' : (G β).re = (∑ m ∈ range K, f m).re + (∑' m, f (m + K)).re := by
    rw [← hsplit, Complex.add_re]
  have hβ0 : 0 < 1 - β := by linarith
  have hxK : 1 ≤ x ^ K := one_le_pow₀ hx1.le
  have key : 1/2 ≤ lam * x ^ K / (1 - β) := by
    have e1 : (x ^ K - 1) / (x - 1) = (x ^ K - 1) / (1 - β) := by rw [hx]; ring_nf
    rw [e1] at hhead
    have : lam / (1 - β) + lam * ((x ^ K - 1) / (1 - β)) = lam * x ^ K / (1 - β) := by
      field_simp; ring
    linarith
  have key2 : (1 - β) / 2 ≤ lam * x ^ K := by
    rw [le_div_iff₀ hβ0] at key
    linarith

  have hxexp : x ^ K ≤ Real.exp ((1 - β) * (L + 1)) := by
    calc x ^ K ≤ Real.exp (1 - β) ^ K := by
          refine pow_le_pow_left₀ hx0 ?_ K
          rw [hx]; have := Real.add_one_le_exp (1 - β); linarith
      _ = Real.exp ((1 - β) * K) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp ((1 - β) * (L + 1)) := by
          refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hKL.le hβ0.le)
  have hexp0 : 0 < Real.exp ((1 - β) * (L + 1)) := Real.exp_pos _
  rw [Real.exp_neg]
  calc (1 - β) / 2 * (Real.exp ((1 - β) * (L + 1)))⁻¹
      ≤ lam * x ^ K * (Real.exp ((1 - β) * (L + 1)))⁻¹ :=
        mul_le_mul_of_nonneg_right key2 (inv_nonneg.mpr hexp0.le)
    _ ≤ lam * Real.exp ((1 - β) * (L + 1)) * (Real.exp ((1 - β) * (L + 1)))⁻¹ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxexp hlam)
          (inv_nonneg.mpr hexp0.le)
    _ = lam := by field_simp

end Estermann
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

end LandauSiegel
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

end P2M_Estermann
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

section P2M_SiegelFunction

p2m_open "Complex Filter Topology Set Metric DirichletCharacter P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.DirichletCharacter"

namespace LandauSiegel

noncomputable def zeta0 (s : ℂ) : ℂ :=
  (riemannZeta s - 1 / (s - 1) / Gammaℝ s) + dslope (fun s ↦ (Gammaℝ s)⁻¹) 1 s

lemma zeta0_apply_of_ne_one {s : ℂ} (hs : s ≠ 1) : zeta0 s = riemannZeta s - 1 / (s - 1) := by
  rw [zeta0, dslope_of_ne _ hs, slope, vsub_eq_sub, Gammaℝ_one, inv_one, smul_eq_mul]
  have : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp
  ring

lemma differentiable_dslope_of_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a : ℂ) :
    Differentiable ℂ (dslope f a) := by
  intro b
  rcases eq_or_ne b a with rfl | h
  · obtain ⟨p, hp⟩ := hf.analyticAt b
    exact hp.has_fpower_series_dslope_fslope.analyticAt.differentiableAt
  · exact (differentiableAt_dslope_of_ne h).mpr (hf b)

lemma differentiable_zeta0 : Differentiable ℂ zeta0 := by
  refine Differentiable.add ?_ (differentiable_dslope_of_differentiable differentiable_Gammaℝ_inv 1)
  intro s
  rcases eq_or_ne s 1 with rfl | hs
  · exact HurwitzZeta.differentiableAt_hurwitzZetaEven_sub_one_div 0
  · have : (fun s : ℂ ↦ riemannZeta s - 1 / (s - 1) / Gammaℝ s)
        = fun s ↦ riemannZeta s - 1 / (s - 1) * (Gammaℝ s)⁻¹ := by
      ext; rw [div_eq_mul_inv]
    rw [this]
    have hd : DifferentiableAt ℂ (fun s : ℂ ↦ 1 / (s - 1)) s :=
      DifferentiableAt.div (c := fun _ : ℂ ↦ (1:ℂ)) (d := fun s : ℂ ↦ s - 1)
        (differentiableAt_const 1) (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs)
    exact (differentiableAt_riemannZeta hs).sub (hd.mul (differentiable_Gammaℝ_inv s))

lemma exists_bound_zeta0_sphere : ∃ Z : ℝ, 0 ≤ Z ∧ ∀ s ∈ sphere (2:ℂ) (3/2), ‖zeta0 s‖ ≤ Z := by
  obtain ⟨Z, hZ⟩ := (isCompact_sphere (2:ℂ) (3/2)).exists_bound_of_continuousOn
    differentiable_zeta0.continuous.continuousOn
  exact ⟨max Z 0, le_max_right _ _, fun s hs ↦ (hZ s hs).trans (le_max_left _ _)⟩

noncomputable def zeta0Bound : ℝ := exists_bound_zeta0_sphere.choose

lemma zeta0Bound_nonneg : 0 ≤ zeta0Bound := exists_bound_zeta0_sphere.choose_spec.1

lemma norm_zeta0_le {s : ℂ} (hs : s ∈ sphere (2:ℂ) (3/2)) : ‖zeta0 s‖ ≤ zeta0Bound :=
  exists_bound_zeta0_sphere.choose_spec.2 s hs

variable {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂]
  (χ₁ : DirichletCharacter ℂ N₁) (χ₂ : DirichletCharacter ℂ N₂)

noncomputable def P (s : ℂ) : ℂ :=
  LFunction χ₁ s * (LFunction χ₂ s * LFunction (productChar χ₁ χ₂) s)

noncomputable def siegelG (s : ℂ) : ℂ := zeta0 s * P χ₁ χ₂ s + dslope (P χ₁ χ₂) 1 s

variable {χ₁ χ₂}

lemma differentiable_P (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1) (hψ : productChar χ₁ χ₂ ≠ 1) :
    Differentiable ℂ (P χ₁ χ₂) :=
  (differentiable_LFunction h₁).mul ((differentiable_LFunction h₂).mul (differentiable_LFunction hψ))

lemma differentiable_siegelG (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1) (hψ : productChar χ₁ χ₂ ≠ 1) :
    Differentiable ℂ (siegelG χ₁ χ₂) :=
  (differentiable_zeta0.mul (differentiable_P h₁ h₂ hψ)).add
    (differentiable_dslope_of_differentiable (differentiable_P h₁ h₂ hψ) 1)

lemma siegelG_apply_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    siegelG χ₁ χ₂ s = riemannZeta s * P χ₁ χ₂ s - P χ₁ χ₂ 1 / (s - 1) := by
  rw [siegelG, zeta0_apply_of_ne_one hs, dslope_of_ne _ hs, slope, vsub_eq_sub, smul_eq_mul]
  have : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  field_simp
  ring

lemma siegelG_eq_LSeries {s : ℂ} (hs : 1 < s.re) :
    siegelG χ₁ χ₂ s = LSeries (siegelCoeff χ₁ χ₂) s - P χ₁ χ₂ 1 / (s - 1) := by
  have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hs
  rw [siegelG_apply_of_ne_one hs1, LSeries_siegelCoeff χ₁ χ₂ hs, P, mul_assoc]

lemma re_ge_of_mem_sphere {s : ℂ} (hs : s ∈ sphere (2:ℂ) (3/2)) : 1/2 ≤ s.re := by
  have h : ‖s - 2‖ = 3/2 := by simpa [dist_eq_norm] using hs
  have := abs_re_le_norm (s - 2)
  rw [h, sub_re, re_ofNat] at this
  have := neg_le_of_abs_le this
  linarith

lemma norm_le_of_mem_sphere {s : ℂ} (hs : s ∈ sphere (2:ℂ) (3/2)) : ‖s‖ ≤ 7/2 := by
  have h : ‖s - 2‖ = 3/2 := by simpa [dist_eq_norm] using hs
  calc ‖s‖ = ‖(s - 2) + 2‖ := by ring_nf
    _ ≤ ‖s - 2‖ + ‖(2:ℂ)‖ := norm_add_le _ _
    _ = 7/2 := by rw [h, Complex.norm_ofNat]; norm_num

lemma half_le_norm_sub_one_of_mem_sphere {s : ℂ} (hs : s ∈ sphere (2:ℂ) (3/2)) :
    1/2 ≤ ‖s - 1‖ := by
  have h : ‖s - 2‖ = 3/2 := by simpa [dist_eq_norm] using hs
  have : ‖s - 2‖ ≤ ‖s - 1‖ + ‖(1:ℂ)‖ := by
    calc ‖s - 2‖ = ‖(s - 1) - 1‖ := by ring_nf
      _ ≤ ‖s - 1‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
  rw [h, norm_one] at this
  linarith

lemma norm_LFunction_le_of_mem_sphere {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {s : ℂ} (hs : s ∈ sphere (2:ℂ) (3/2)) : ‖LFunction χ s‖ ≤ 7 * q := by
  have hre := re_ge_of_mem_sphere hs
  have h := norm_LFunction_le χ hχ (by linarith : 0 < s.re)
  calc ‖LFunction χ s‖ ≤ q * ‖s‖ / s.re := h
    _ ≤ q * (7/2) / (1/2) := by
        gcongr
        · exact norm_le_of_mem_sphere hs
    _ = 7 * q := by ring

lemma norm_LFunction_one_le' {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    ‖LFunction χ 1‖ ≤ q := by
  have h := norm_LFunction_le χ hχ (s := 1) (by simp)
  simpa using h

lemma norm_P_le_of_mem_sphere (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1) (hψ : productChar χ₁ χ₂ ≠ 1)
    {s : ℂ} (hs : s ∈ sphere (2:ℂ) (3/2)) :
    ‖P χ₁ χ₂ s‖ ≤ 343 * ((N₁:ℝ) * N₂) ^ 2 := by
  rw [P, norm_mul, norm_mul]
  have e1 := norm_LFunction_le_of_mem_sphere h₁ hs
  have e2 := norm_LFunction_le_of_mem_sphere h₂ hs
  have e3 := norm_LFunction_le_of_mem_sphere hψ hs
  rw [Nat.cast_mul] at e3
  calc ‖LFunction χ₁ s‖ * (‖LFunction χ₂ s‖ * ‖LFunction (productChar χ₁ χ₂) s‖)
      ≤ (7 * N₁) * ((7 * N₂) * (7 * (N₁ * N₂))) := by
        gcongr
    _ = 343 * ((N₁:ℝ) * N₂) ^ 2 := by ring

lemma norm_P_one_le (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1) (hψ : productChar χ₁ χ₂ ≠ 1) :
    ‖P χ₁ χ₂ 1‖ ≤ ((N₁:ℝ) * N₂) ^ 2 := by
  rw [P, norm_mul, norm_mul]
  have e1 := norm_LFunction_one_le' h₁
  have e2 := norm_LFunction_one_le' h₂
  have e3 := norm_LFunction_one_le' hψ
  rw [Nat.cast_mul] at e3
  calc ‖LFunction χ₁ 1‖ * (‖LFunction χ₂ 1‖ * ‖LFunction (productChar χ₁ χ₂) 1‖)
      ≤ N₁ * (N₂ * (N₁ * N₂)) := by gcongr
    _ = ((N₁:ℝ) * N₂) ^ 2 := by ring

noncomputable def siegelGConst : ℝ := 343 * zeta0Bound + 688

lemma siegelGConst_pos : 0 < siegelGConst := by
  have := zeta0Bound_nonneg; unfold siegelGConst; positivity

theorem norm_siegelG_le_of_mem_sphere (h₁ : χ₁ ≠ 1) (h₂ : χ₂ ≠ 1) (hψ : productChar χ₁ χ₂ ≠ 1)
    {s : ℂ} (hs : s ∈ sphere (2:ℂ) (3/2)) :
    ‖siegelG χ₁ χ₂ s‖ ≤ siegelGConst * ((N₁:ℝ) * N₂) ^ 2 := by
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hs; norm_num [dist_eq_norm] at hs
  have hP := norm_P_le_of_mem_sphere h₁ h₂ hψ hs
  have hP1 := norm_P_one_le h₁ h₂ hψ
  have hZ := norm_zeta0_le hs
  have hd := half_le_norm_sub_one_of_mem_sphere hs
  have hQ : 0 ≤ ((N₁:ℝ) * N₂) ^ 2 := by positivity
  rw [siegelG, dslope_of_ne _ hs1, slope, vsub_eq_sub, smul_eq_mul]
  calc ‖zeta0 s * P χ₁ χ₂ s + (s - 1)⁻¹ * (P χ₁ χ₂ s - P χ₁ χ₂ 1)‖
      ≤ ‖zeta0 s‖ * ‖P χ₁ χ₂ s‖ + ‖s - 1‖⁻¹ * (‖P χ₁ χ₂ s‖ + ‖P χ₁ χ₂ 1‖) := by
        refine (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) ?_)
        rw [norm_mul, norm_inv]
        exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr (norm_nonneg _))
    _ ≤ zeta0Bound * (343 * ((N₁:ℝ) * N₂) ^ 2) + 2 * (343 * ((N₁:ℝ) * N₂) ^ 2 + ((N₁:ℝ) * N₂) ^ 2) := by
        gcongr
        · exact zeta0Bound_nonneg
        · rw [show (2:ℝ) = (1/2)⁻¹ by norm_num]
          exact inv_anti₀ (by norm_num) hd
    _ = siegelGConst * ((N₁:ℝ) * N₂) ^ 2 := by unfold siegelGConst; ring

end LandauSiegel
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

end P2M_SiegelFunction
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

section P2M_RealValues

open scoped ComplexOrder
p2m_open "Complex Filter Topology Set DirichletCharacter P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.DirichletCharacter ArithmeticFunction"

namespace LandauSiegel

lemma pos_of_forall_ne_zero {g : ℝ → ℝ} {u v : ℝ} (huv : u ≤ v) (hg : ContinuousOn g (Icc u v))
    (hne : ∀ x ∈ Icc u v, g x ≠ 0) (hv : 0 < g v) : 0 < g u := by
  by_contra h
  push Not at h
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc huv hg ⟨h, hv.le⟩
  exact hne c hc hc0

lemma riemannZeta_ofReal_pos {σ : ℝ} (hσ : 1 < σ) : 0 < riemannZeta σ := by
  rw [← LSeries_one_eq_riemannZeta (by simpa using hσ)]
  refine LSeries.positive (fun _ ↦ zero_le_one) (by simp) ?_
  rw [show (fun _ : ℕ ↦ (1:ℂ)) = 1 from rfl, LSeries.abscissaOfAbsConv_one]; exact_mod_cast hσ

lemma exists_re_riemannZeta_neg {η : ℝ} (hη : 0 < η) :
    ∃ β : ℝ, 3/4 ≤ β ∧ 1 - η < β ∧ β < 1 ∧ (riemannZeta β).re < 0 := by

  have ht := tendsto_riemannZeta_sub_one_div
  have hb : ∀ᶠ s in 𝓝[≠] (1:ℂ), ‖riemannZeta s - 1 / (s - 1) - Real.eulerMascheroniConstant‖ < 1 :=
    by simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp ht) 1 one_pos
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hb
  obtain ⟨δ, hδ, hball⟩ := hb
  set B : ℝ := |Real.eulerMascheroniConstant| + 1 with hB

  obtain ⟨t, ht0, ht1, ht2, ht3, ht4⟩ : ∃ t : ℝ, 0 < t ∧ t < δ ∧ t < η ∧ t ≤ 1/4 ∧ t < 1 / (B + 1) := by
    refine ⟨min (min (δ/2) (η/2)) (min (1/4) (1 / (2 * (B + 1)))), ?_, ?_, ?_, ?_, ?_⟩
    · have : 0 < B + 1 := by positivity
      positivity
    · exact (min_le_left _ _).trans_lt ((min_le_left _ _).trans_lt (by linarith))
    · exact (min_le_left _ _).trans_lt ((min_le_right _ _).trans_lt (by linarith))
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · refine (min_le_right _ _).trans_lt ((min_le_right _ _).trans_lt ?_)
      have : 0 < B + 1 := by positivity
      rw [div_lt_div_iff₀ (by positivity) this]
      linarith
  refine ⟨1 - t, by linarith, by linarith, by linarith, ?_⟩
  have hne : ((1 - t : ℝ) : ℂ) ≠ 1 := by
    intro h; apply_fun Complex.re at h; simp at h; linarith
  have hdist : dist ((1 - t : ℝ) : ℂ) 1 < δ := by
    rw [dist_eq_norm, show ((1 - t : ℝ) : ℂ) - 1 = ((-t : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos ht0]
    exact ht1
  have h := hball hdist hne

  have hre : (riemannZeta ((1 - t : ℝ) : ℂ)).re
      = (riemannZeta ((1 - t : ℝ) : ℂ) - 1 / (((1 - t : ℝ) : ℂ) - 1) - Real.eulerMascheroniConstant).re
        + Real.eulerMascheroniConstant - 1 / t := by
    simp only [sub_re, ofReal_re]
    rw [show ((1 - t : ℝ) : ℂ) - 1 = ((-t : ℝ) : ℂ) by push_cast; ring, one_div,
      ← ofReal_inv, ofReal_re]
    field_simp
    ring
  rw [hre]
  have h1 := (abs_re_le_norm _).trans_lt h
  have h2 := le_abs_self Real.eulerMascheroniConstant
  have h3 : B + 1 < 1 / t := by
    rw [lt_div_iff₀ ht0]
    have : 0 < B + 1 := by positivity
    calc (B + 1) * t < (B + 1) * (1 / (B + 1)) := mul_lt_mul_of_pos_left ht4 this
      _ = 1 := by field_simp
  have h4 := (abs_lt.mp h1).2
  linarith

namespace Quadratic

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

omit [NeZero q] in
lemma conj_apply (hχ : χ ^ 2 = 1) (a : ZMod q) : starRingEnd ℂ (χ a) = χ a := by
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ a with h | h | h <;> simp [h]

private lemma _root_.LandauSiegel.Quadratic.im_LFunction_ofReal (hχ : χ ^ 2 = 1) (h1 : χ ≠ 1) {σ : ℝ} (hσ : 0 < σ) :
    (LFunction χ σ).im = 0 :=
  DirichletCharacter.im_LFunction_ofReal χ h1 (conj_apply hχ) hσ

p2m_export "LandauSiegel.Quadratic" "im_LFunction_ofReal"
lemma continuous_re_LFunction_ofReal (h1 : χ ≠ 1) :
    Continuous fun σ : ℝ ↦ (LFunction χ σ).re :=
  Complex.continuous_re.comp ((differentiable_LFunction h1).continuous.comp continuous_ofReal)

lemma riemannZeta_mul_LFunction_eq_LSeries_zetaMul {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * LFunction χ s = LSeries χ.zetaMul s := by
  have hζ : LSeriesSummable (ArithmeticFunction.zeta : ArithmeticFunction ℂ) s :=
    LSeriesSummable_zeta_iff.mpr hs
  rw [zetaMul, ← coe_mul, LSeries_convolution' hζ (LSeriesSummable_toArithmeticFunction χ hs),
    LSeries_toArithmeticFunction χ hs, ← LSeries_zeta_eq_riemannZeta hs]
  simp_rw [← natCoe_apply]

lemma re_LFunction_ofReal_pos_of_one_lt (hχ : χ ^ 2 = 1) {σ : ℝ} (hσ : 1 < σ) :
    0 < (LFunction χ σ).re := by
  have hσ' : (1:ℝ) < (σ:ℂ).re := by simpa using hσ
  have hprod : 0 < LSeries χ.zetaMul σ := by
    refine LSeries.positive (zetaMul_nonneg hχ) ?_ ?_
    · rw [(isMultiplicative_zetaMul χ).map_one]; exact zero_lt_one
    · refine (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦ ?_).trans_lt
        (by exact_mod_cast hσ : ((1:ℝ) : EReal) < σ)
      exact LSeriesSummable_zetaMul χ (by simpa using hy)
  rw [← riemannZeta_mul_LFunction_eq_LSeries_zetaMul hσ'] at hprod
  have hζ := riemannZeta_ofReal_pos hσ
  obtain ⟨hζre, hζim⟩ := Complex.pos_iff.mp hζ
  obtain ⟨hpre, hpim⟩ := Complex.pos_iff.mp hprod
  rw [mul_re, ← hζim, zero_mul, sub_zero] at hpre
  exact (mul_pos_iff_of_pos_left hζre).mp hpre

theorem re_LFunction_ofReal_pos_of_forall_ne_zero (hχ : χ ^ 2 = 1) (h1 : χ ≠ 1) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (h : ∀ σ : ℝ, σ ∈ Icc β 1 → LFunction χ σ ≠ 0) :
    0 < (LFunction χ β).re := by
  refine pos_of_forall_ne_zero (g := fun σ : ℝ ↦ (LFunction χ σ).re) (u := β) (v := 2) (by linarith)
    (continuous_re_LFunction_ofReal h1).continuousOn
    (fun σ hσ hz ↦ ?_) (re_LFunction_ofReal_pos_of_one_lt hχ one_lt_two)
  have hσ0 : 0 < σ := hβ0.trans_le hσ.1
  have hL : LFunction χ σ = 0 := by
    apply Complex.ext
    · simpa using hz
    · simpa using im_LFunction_ofReal hχ h1 hσ0
  rcases le_or_gt σ 1 with hσ1 | hσ1
  · exact h σ ⟨hσ.1, hσ1⟩ hL
  · exact LFunction_ne_zero_of_one_le_re χ (.inl h1) (by simp [hσ1.le]) hL

theorem re_LFunction_one_pos (hχ : χ ^ 2 = 1) (h1 : χ ≠ 1) : 0 < (LFunction χ 1).re := by
  have := re_LFunction_ofReal_pos_of_forall_ne_zero hχ h1 zero_lt_one le_rfl fun σ hσ ↦
    LFunction_ne_zero_of_one_le_re χ (.inl h1) (by simp [le_antisymm hσ.2 hσ.1])
  simpa using this

theorem im_LFunction_one (hχ : χ ^ 2 = 1) (h1 : χ ≠ 1) : (LFunction χ 1).im = 0 := by
  simpa using im_LFunction_ofReal hχ h1 zero_lt_one

theorem LFunction_one_eq_ofReal_re (hχ : χ ^ 2 = 1) (h1 : χ ≠ 1) :
    LFunction χ 1 = ((LFunction χ 1).re : ℂ) :=
  Complex.ext (by simp) (by simp [im_LFunction_one hχ h1])

theorem LFunction_one_pos (hχ : χ ^ 2 = 1) (h1 : χ ≠ 1) : 0 < LFunction χ 1 := by
  rw [LFunction_one_eq_ofReal_re hχ h1]
  exact_mod_cast re_LFunction_one_pos hχ h1

end Quadratic
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

end LandauSiegel
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

end P2M_RealValues
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

section P2M_SiegelBound

open scoped ComplexOrder
p2m_open "Complex Filter Topology Set Metric DirichletCharacter P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.DirichletCharacter"

namespace LandauSiegel

variable {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂]
  {χ₁ : DirichletCharacter ℂ N₁} {χ₂ : DirichletCharacter ℂ N₂}

lemma mul_re_of_im_eq_zero {z w : ℂ} (hz : z.im = 0) (hw : w.im = 0) :
    (z * w).re = z.re * w.re ∧ (z * w).im = 0 := by
  simp [mul_re, mul_im, hz, hw]

lemma P_one_re_pos (h₁ : χ₁ ^ 2 = 1) (h₁' : χ₁ ≠ 1) (h₂ : χ₂ ^ 2 = 1) (h₂' : χ₂ ≠ 1)
    (hψ : productChar χ₁ χ₂ ≠ 1) :
    0 < (P χ₁ χ₂ 1).re ∧ (P χ₁ χ₂ 1).im = 0 ∧
      (P χ₁ χ₂ 1).re = (LFunction χ₁ 1).re * ((LFunction χ₂ 1).re *
        (LFunction (productChar χ₁ χ₂) 1).re) := by
  have hψ2 := productChar_sq_eq_one χ₁ χ₂ h₁ h₂
  have a := Quadratic.re_LFunction_one_pos h₁ h₁'
  have b := Quadratic.re_LFunction_one_pos h₂ h₂'
  have c := Quadratic.re_LFunction_one_pos hψ2 hψ
  have a' := Quadratic.im_LFunction_one h₁ h₁'
  have b' := Quadratic.im_LFunction_one h₂ h₂'
  have c' := Quadratic.im_LFunction_one hψ2 hψ
  obtain ⟨e1, e1'⟩ := mul_re_of_im_eq_zero b' c'
  obtain ⟨e2, e2'⟩ := mul_re_of_im_eq_zero a' e1'
  refine ⟨?_, ?_, ?_⟩
  · rw [P, e2, e1]; positivity
  · rw [P, e2']
  · rw [P, e2, e1]

theorem key_inequality (h₁ : χ₁ ^ 2 = 1) (h₁' : χ₁ ≠ 1) (h₂ : χ₂ ^ 2 = 1) (h₂' : χ₂ ≠ 1)
    (hψ : productChar χ₁ χ₂ ≠ 1) {β : ℝ} (hβ : 3/4 ≤ β) (hβ1 : β < 1)
    (hFβ : (riemannZeta β * P χ₁ χ₂ β).re ≤ 0) :
    (1 - β) / 2 * Real.exp (-((1 - β) *
      (Real.log (12 * (siegelGConst * ((N₁:ℝ) * N₂) ^ 2 + 1)) / Real.log (6/5) + 1)))
      ≤ (P χ₁ χ₂ 1).re := by
  obtain ⟨hlam, hlam_im, -⟩ := P_one_re_pos h₁ h₁' h₂ h₂' hψ
  have hlamC : ((P χ₁ χ₂ 1).re : ℂ) = P χ₁ χ₂ 1 := by
    apply Complex.ext <;> simp [hlam_im]
  have hβ1' : (β:ℂ) ≠ 1 := by
    intro h; apply_fun Complex.re at h; simp at h; linarith
  refine Estermann.main (a := ⇑(siegelCoeff χ₁ χ₂)) (G := siegelG χ₁ χ₂)
    (differentiable_siegelG h₁' h₂' hψ) (fun n ↦ siegelCoeff_nonneg χ₁ χ₂ h₁ h₂ n)
    (siegelCoeff_one χ₁ χ₂) (fun y hy ↦ LSeriesSummable_siegelCoeff χ₁ χ₂ (by simpa using hy))
    hlam.le (by have := siegelGConst_pos; positivity) (fun s hs ↦ ?_)
    (fun s hs ↦ norm_siegelG_le_of_mem_sphere h₁' h₂' hψ hs) hβ hβ1 ?_
  · rw [siegelG_eq_LSeries hs, hlamC]
  · rw [siegelG_apply_of_ne_one hβ1', sub_re,
      show (β:ℂ) - 1 = ((β - 1 : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_re]
    have : (P χ₁ χ₂ 1).re / (β - 1) = -((P χ₁ χ₂ 1).re / (1 - β)) := by
      rw [← div_neg, neg_sub]
    rw [this]
    linarith

end LandauSiegel
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

end P2M_SiegelBound
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

section P2M_Exceptional

open scoped ComplexOrder
p2m_open "Complex Finset DirichletCharacter P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.DirichletCharacter"

namespace LandauSiegel

lemma one_div_card_succ_le_prod (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    1 / ((S.card : ℝ) + 1) ≤ ∏ p ∈ S, (1 - 1 / (p:ℝ)) := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have hs : ∀ p ∈ s, 2 ≤ p := fun p hp ↦ hS p (mem_insert_of_mem hp)
    have ha2 : 2 ≤ a := hS a (mem_insert_self a s)
    have hnot : a ∉ s := fun h ↦ lt_irrefl a (ha a h)

    have hcard : s.card + 2 ≤ a := by
      have hsub : s ⊆ Finset.Ico 2 a := fun p hp ↦ Finset.mem_Ico.mpr ⟨hs p hp, ha p hp⟩
      have := Finset.card_le_card hsub
      rw [Nat.card_Ico] at this
      omega
    rw [Finset.prod_insert hnot, Finset.card_insert_of_notMem hnot]
    have ha0 : (0:ℝ) < a := by exact_mod_cast (by omega : 0 < a)
    have hcard' : (s.card : ℝ) + 2 ≤ a := by exact_mod_cast hcard
    have ih' := ih hs
    have h1 : 1 - 1 / ((s.card : ℝ) + 2) ≤ 1 - 1 / (a:ℝ) := by
      gcongr
    have hpos : (0:ℝ) ≤ 1 - 1 / (a:ℝ) := by
      rw [sub_nonneg, div_le_one ha0]; exact_mod_cast (by omega : 1 ≤ a)
    calc 1 / (((s.card + 1 : ℕ) : ℝ) + 1) = (1 - 1 / ((s.card : ℝ) + 2)) * (1 / ((s.card : ℝ) + 1)) := by
          push_cast; field_simp; ring
      _ ≤ (1 - 1 / (a:ℝ)) * ∏ p ∈ s, (1 - 1 / (p:ℝ)) := by
          gcongr

lemma two_pow_card_primeFactors_le {n : ℕ} (hn : n ≠ 0) : 2 ^ n.primeFactors.card ≤ n := by
  calc 2 ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, 2 := by simp
    _ ≤ ∏ p ∈ n.primeFactors, p := Finset.prod_le_prod' fun p hp ↦
        (Nat.prime_of_mem_primeFactors hp).two_le
    _ ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)

lemma card_primeFactors_le_logb {n : ℕ} (hn : n ≠ 0) :
    (n.primeFactors.card : ℝ) ≤ Real.logb 2 n := by
  have h := two_pow_card_primeFactors_le hn
  have : (2:ℝ) ^ (n.primeFactors.card : ℝ) ≤ n := by
    rw [Real.rpow_natCast]; exact_mod_cast h
  exact (Real.le_logb_iff_rpow_le one_lt_two (by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr this

section EulerFactor

variable {N : ℕ} {χ : DirichletCharacter ℂ N}

noncomputable def eulerFactorRe (χ : DirichletCharacter ℂ N) (p : ℕ) : ℝ := 1 - (χ p).re / p

lemma eulerFactor_eq_ofReal (hχ : χ ^ 2 = 1) (p : ℕ) :
    (1 - χ p * (p:ℂ) ^ (-(1:ℂ))) = (eulerFactorRe χ p : ℂ) := by
  rw [eulerFactorRe, cpow_neg_one, ofReal_sub, ofReal_one, ofReal_div, ofReal_natCast]
  congr 1
  rw [div_eq_mul_inv]
  congr 1
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p with h | h | h <;> simp [h]

lemma eulerFactorRe_pos (hχ : χ ^ 2 = 1) {p : ℕ} (hp : p.Prime) : 0 < eulerFactorRe χ p := by
  rw [eulerFactorRe, sub_pos, div_lt_one (by exact_mod_cast hp.pos)]
  have h2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p with h | h | h <;> simp [h] <;>
    first | exact_mod_cast hp.pos | exact_mod_cast hp.one_lt | linarith

lemma one_sub_inv_le_eulerFactorRe (p : ℕ) :
    1 - 1 / (p:ℝ) ≤ eulerFactorRe χ p := by
  rw [eulerFactorRe]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  have : (χ p).re ≤ 1 := (re_le_norm _).trans (χ.norm_le_one _)
  gcongr

lemma eulerFactorRe_le_two (p : ℕ) : eulerFactorRe χ p ≤ 2 := by
  rw [eulerFactorRe]
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  have : -1 ≤ (χ p).re := (abs_le.mp ((abs_re_le_norm _).trans (χ.norm_le_one _))).1
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp
  have : -1 ≤ (χ p).re / p := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  linarith

lemma eulerFactorRe_of_dvd {p : ℕ} (hpp : p.Prime) (hp : p ∣ N) : eulerFactorRe χ p = 1 := by
  rw [eulerFactorRe]
  have : ¬ IsUnit (p : ZMod N) := by
    rw [ZMod.isUnit_iff_coprime]
    intro hc
    exact hpp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc hp)
  rw [MulChar.map_nonunit _ this]; simp

lemma LFunction_changeLevel_one [NeZero N] (hχ : χ ^ 2 = 1) (h1 : χ ≠ 1) {M : ℕ} [NeZero M]
    (hNM : N ∣ M) :
    LFunction (changeLevel hNM χ) 1
      = LFunction χ 1 * ((∏ p ∈ M.primeFactors, eulerFactorRe χ p : ℝ) : ℂ) := by
  rw [LFunction_changeLevel hNM χ (.inl h1), ofReal_prod]
  congr 1
  exact Finset.prod_congr rfl fun p _ ↦ by rw [← eulerFactor_eq_ofReal hχ]

end EulerFactor
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

variable {N₁ N : ℕ} [NeZero N₁] [NeZero N]
  {χ₁ : DirichletCharacter ℂ N₁} {χ : DirichletCharacter ℂ N}

omit [NeZero N₁] [NeZero N] in
lemma changeLevel_eq_of_productChar_eq_one (h₁ : χ₁ ^ 2 = 1) (hψ : productChar χ₁ χ = 1) :
    changeLevel (dvd_mul_left N N₁) χ = changeLevel (dvd_mul_right N₁ N) χ₁ := by
  rw [productChar] at hψ
  have hinv : χ₁⁻¹ = χ₁ := by
    rw [inv_eq_iff_eq_inv, eq_comm, inv_eq_of_mul_eq_one_right]
    rw [← sq, h₁]
  calc changeLevel (dvd_mul_left N N₁) χ
      = (changeLevel (dvd_mul_right N₁ N) χ₁)⁻¹ := (eq_inv_of_mul_eq_one_right hψ)
    _ = changeLevel (dvd_mul_right N₁ N) χ₁⁻¹ := (map_inv _ _).symm
    _ = changeLevel (dvd_mul_right N₁ N) χ₁ := by rw [hinv]

theorem exceptional_bound (h₁ : χ₁ ^ 2 = 1) (h₁' : χ₁ ≠ 1) (h : χ ^ 2 = 1) (h' : χ ≠ 1)
    (hψ : productChar χ₁ χ = 1) :
    (LFunction χ₁ 1).re / (Real.logb 2 (N₁ * N) + 1)
      ≤ (LFunction χ 1).re * 2 ^ N₁.primeFactors.card := by
  have hM0 : N₁ * N ≠ 0 := mul_ne_zero (NeZero.ne N₁) (NeZero.ne N)
  set M := N₁ * N with hM
  set E := ∏ p ∈ M.primeFactors, eulerFactorRe χ p with hE
  set E₁ := ∏ p ∈ M.primeFactors, eulerFactorRe χ₁ p with hE₁

  have hrel : LFunction χ 1 * (E:ℂ) = LFunction χ₁ 1 * (E₁:ℂ) := by
    rw [hE, hE₁, ← LFunction_changeLevel_one h h' (dvd_mul_left N N₁),
      ← LFunction_changeLevel_one h₁ h₁' (dvd_mul_right N₁ N),
      changeLevel_eq_of_productChar_eq_one h₁ hψ]
  have hrel' : (LFunction χ 1).re * E = (LFunction χ₁ 1).re * E₁ := by
    have := congrArg Complex.re hrel
    simpa [mul_re, Quadratic.im_LFunction_one h h', Quadratic.im_LFunction_one h₁ h₁'] using this

  have hprime : ∀ p ∈ M.primeFactors, p.Prime := fun p hp ↦ Nat.prime_of_mem_primeFactors hp
  have hE₁pos : 1 / (Real.logb 2 M + 1) ≤ E₁ := by
    calc 1 / (Real.logb 2 M + 1) ≤ 1 / ((M.primeFactors.card : ℝ) + 1) := by
          gcongr
          exact card_primeFactors_le_logb hM0
      _ ≤ ∏ p ∈ M.primeFactors, (1 - 1 / (p:ℝ)) :=
          one_div_card_succ_le_prod _ fun p hp ↦ (hprime p hp).two_le
      _ ≤ E₁ := Finset.prod_le_prod (fun p hp ↦ by
            rw [sub_nonneg, div_le_one (by exact_mod_cast (hprime p hp).pos)]
            exact_mod_cast (hprime p hp).one_lt.le)
          fun p _ ↦ one_sub_inv_le_eulerFactorRe p
  have hEle : E ≤ 2 ^ N₁.primeFactors.card := by
    calc E ≤ ∏ p ∈ M.primeFactors, (if p ∣ N then (1:ℝ) else 2) :=
          Finset.prod_le_prod (fun p hp ↦ (eulerFactorRe_pos h (hprime p hp)).le) fun p hp ↦ by
            split_ifs with hd
            · exact (eulerFactorRe_of_dvd (hprime p hp) hd).le
            · exact eulerFactorRe_le_two p
      _ = 2 ^ (M.primeFactors.filter (fun p ↦ ¬ p ∣ N)).card := by
          rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
      _ ≤ 2 ^ N₁.primeFactors.card := by
          refine pow_le_pow_right₀ one_le_two (Finset.card_le_card fun p hp ↦ ?_)
          rw [Finset.mem_filter, Nat.mem_primeFactors] at hp
          obtain ⟨⟨hpp, hpM, -⟩, hpN⟩ := hp
          rw [Nat.mem_primeFactors]
          exact ⟨hpp, (Or.resolve_right ((Nat.Prime.dvd_mul hpp).mp hpM) hpN), NeZero.ne N₁⟩
  have hLpos := Quadratic.re_LFunction_one_pos h h'
  have hL₁pos := Quadratic.re_LFunction_one_pos h₁ h₁'
  have hlog : 0 < Real.logb 2 M + 1 := by
    have : 0 ≤ Real.logb 2 M := Real.logb_nonneg one_lt_two (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hM0)
    linarith
  calc (LFunction χ₁ 1).re / (Real.logb 2 (N₁ * N) + 1)
      = (LFunction χ₁ 1).re * (1 / (Real.logb 2 M + 1)) := by rw [hM]; push_cast; ring
    _ ≤ (LFunction χ₁ 1).re * E₁ := mul_le_mul_of_nonneg_left hE₁pos hL₁pos.le
    _ = (LFunction χ 1).re * E := hrel'.symm
    _ ≤ (LFunction χ 1).re * 2 ^ N₁.primeFactors.card := mul_le_mul_of_nonneg_left hEle hLpos.le

end LandauSiegel
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

end P2M_Exceptional
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

section P2M_Siegel

open scoped ComplexOrder
p2m_open "Complex Set DirichletCharacter P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.DirichletCharacter"

namespace LandauSiegel

noncomputable def chi4 : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

lemma chi4_ne_one : chi4 ≠ 1 := by
  rw [chi4, Ne, MulChar.ringHomComp_eq_one_iff Int.cast_injective]
  intro h
  have h3 : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
  have hu : IsUnit (3 : ZMod 4) := by decide
  rw [h, MulChar.one_apply hu] at h3
  norm_num at h3

lemma chi4_sq : chi4 ^ 2 = 1 :=
  (ZMod.isQuadratic_χ₄.comp _).sq_eq_one

lemma log_le_rpow_mul {x δ : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ) : Real.log x ≤ (1/δ) * x ^ δ := by
  have := Real.log_le_rpow_div (zero_le_one.trans hx) hδ
  rw [one_div_mul_eq_div]; exact this

lemma one_le_rpow_nat {N : ℕ} [NeZero N] {δ : ℝ} (hδ : 0 ≤ δ) : (1:ℝ) ≤ (N:ℝ) ^ δ :=
  Real.one_le_rpow (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)) hδ

lemma add_log_le {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) {N : ℕ} [NeZero N] :
    a + Real.log N ≤ (a + 1/δ) * (N:ℝ) ^ δ := by
  have hN : (1:ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have h1 := log_le_rpow_mul hN hδ
  have h2 := one_le_rpow_nat (N := N) hδ.le
  nlinarith

section Config

variable {ε : ℝ} {N₁ : ℕ} [NeZero N₁] {χ₁ : DirichletCharacter ℂ N₁} {β : ℝ}

theorem siegel_of_config (hε : 0 < ε) (h₁ : χ₁ ^ 2 = 1) (h₁' : χ₁ ≠ 1) (hβ : 3/4 ≤ β)
    (hβ1 : β < 1) (hβε : (1 - β) * (2 / Real.log (6/5)) ≤ ε / 2)
    (Hyp : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ^ 2 = 1 → χ ≠ 1 →
      productChar χ₁ χ ≠ 1 → (riemannZeta β * P χ₁ χ β).re ≤ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ^ 2 = 1 → χ ≠ 1 →
      C * (N:ℝ) ^ (-ε) ≤ (LFunction χ 1).re := by

  have hlog65 : 0 < Real.log (6/5:ℝ) := Real.log_pos (by norm_num)
  set A : ℝ := 1 / Real.log (6/5) with hA
  have hA0 : 0 < A := by positivity
  set D₁ : ℝ := 12 * (siegelGConst * (N₁:ℝ) ^ 2 + 1) with hD₁
  have hCG := siegelGConst_pos
  have hD₁0 : 0 < D₁ := by positivity
  set K₁ : ℝ := (1 - β) / 2 * Real.exp (-((1 - β) * (A * Real.log D₁ + 1))) with hK₁
  have hK₁0 : 0 < K₁ := by have : 0 < 1 - β := by linarith
                           positivity
  have hLN₁ : 0 ≤ Real.log N₁ := Real.log_natCast_nonneg _
  set K₂ : ℝ := K₁ / ((Real.log N₁ + 1) * (Real.log N₁ + 1 + 1 / (ε/2))) with hK₂
  have hK₂0 : 0 < K₂ := by positivity
  have hL₁ := Quadratic.re_LFunction_one_pos h₁ h₁'
  have hlb : 0 ≤ Real.logb 2 (N₁:ℝ) := Real.logb_nonneg one_lt_two (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N₁))
  set K₃ : ℝ := (LFunction χ₁ 1).re / 2 ^ N₁.primeFactors.card /
    (Real.logb 2 N₁ + 1 + 1 / (ε * Real.log 2)) with hK₃
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hK₃0 : 0 < K₃ := by positivity
  refine ⟨min K₂ K₃, lt_min hK₂0 hK₃0, fun N _ χ hχ hχ' ↦ ?_⟩
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hN0 : (0:ℝ) < N := by linarith
  have hNε : 0 < (N:ℝ) ^ (-ε) := Real.rpow_pos_of_pos hN0 _
  by_cases hψ : productChar χ₁ χ = 1
  ·
    have hex := exceptional_bound h₁ h₁' hχ hχ' hψ
    have hden : Real.logb 2 ((N₁:ℝ) * N) + 1
        ≤ (Real.logb 2 N₁ + 1 + 1 / (ε * Real.log 2)) * (N:ℝ) ^ ε := by
      rw [Real.logb_mul (by exact_mod_cast NeZero.ne N₁) (by exact_mod_cast NeZero.ne N)]
      have h := add_log_le (a := (Real.logb 2 N₁ + 1) * Real.log 2) (by positivity) hε (N := N)
      rw [Real.logb, Real.logb] at *
      have hNε' : 0 < (N:ℝ) ^ ε := Real.rpow_pos_of_pos hN0 _
      rw [show Real.log N₁ / Real.log 2 + Real.log N / Real.log 2 + 1
          = ((Real.log N₁ / Real.log 2 + 1) * Real.log 2 + Real.log N) / Real.log 2 by
            field_simp; ring]
      rw [div_le_iff₀ hlog2]
      calc (Real.log ↑N₁ / Real.log 2 + 1) * Real.log 2 + Real.log ↑N
          ≤ ((Real.log ↑N₁ / Real.log 2 + 1) * Real.log 2 + 1 / ε) * (N:ℝ) ^ ε := h
        _ = (Real.log ↑N₁ / Real.log 2 + 1 + 1 / (ε * Real.log 2)) * (N:ℝ) ^ ε * Real.log 2 := by
            field_simp
    have hden0 : 0 < Real.logb 2 ((N₁:ℝ) * N) + 1 := by
      have hN₁1 : (1:ℝ) ≤ N₁ := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N₁)
      have : 0 ≤ Real.logb 2 ((N₁:ℝ) * N) :=
        Real.logb_nonneg one_lt_two (one_le_mul_of_one_le_of_one_le hN₁1 hN1)
      linarith
    have hLχ := Quadratic.re_LFunction_one_pos hχ hχ'
    calc min K₂ K₃ * (N:ℝ) ^ (-ε) ≤ K₃ * (N:ℝ) ^ (-ε) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hNε.le
      _ ≤ (LFunction χ₁ 1).re / 2 ^ N₁.primeFactors.card / (Real.logb 2 ((N₁:ℝ) * N) + 1) := by
          rw [hK₃, Real.rpow_neg hN0.le, ← div_eq_mul_inv, div_div]
          gcongr
      _ ≤ (LFunction χ 1).re := by
          rw [div_div, div_le_iff₀ (by positivity)]
          calc (LFunction χ₁ 1).re = (LFunction χ₁ 1).re / (Real.logb 2 (↑N₁ * ↑N) + 1)
                * (Real.logb 2 (↑N₁ * ↑N) + 1) := by field_simp
            _ ≤ (LFunction χ 1).re * 2 ^ N₁.primeFactors.card * (Real.logb 2 (↑N₁ * ↑N) + 1) := by
                gcongr
            _ = (LFunction χ 1).re * (2 ^ N₁.primeFactors.card * (Real.logb 2 (↑N₁ * ↑N) + 1)) := by
                ring
  ·
    have hkey := key_inequality h₁ h₁' hχ hχ' hψ hβ hβ1 (Hyp N χ hχ hχ' hψ)
    obtain ⟨-, -, hP⟩ := P_one_re_pos h₁ h₁' hχ hχ' hψ
    rw [hP] at hkey
    have hψ2 := productChar_sq_eq_one χ₁ χ h₁ hχ
    have hLχ := Quadratic.re_LFunction_one_pos hχ hχ'
    have hLψ := Quadratic.re_LFunction_one_pos hψ2 hψ

    have hU₁ : (LFunction χ₁ 1).re ≤ Real.log N₁ + 1 :=
      (re_le_norm _).trans (norm_LFunction_one_le χ₁ h₁')
    have hUψ : (LFunction (productChar χ₁ χ) 1).re
        ≤ (Real.log N₁ + 1 + 1 / (ε/2)) * (N:ℝ) ^ (ε/2) := by
      refine (re_le_norm _).trans ((norm_LFunction_one_le _ hψ).trans ?_)
      rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast NeZero.ne N₁) (by exact_mod_cast NeZero.ne N),
        show Real.log N₁ + Real.log N + 1 = (Real.log N₁ + 1) + Real.log N by ring]
      exact add_log_le (by positivity) (half_pos hε)

    have hLB : K₁ * (N:ℝ) ^ (-(ε/2)) ≤ (1 - β) / 2 * Real.exp (-((1 - β) *
        (Real.log (12 * (siegelGConst * ((N₁:ℝ) * N) ^ 2 + 1)) / Real.log (6/5) + 1))) := by
      rw [hK₁, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      rw [Real.rpow_def_of_pos hN0, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hlogle : Real.log (12 * (siegelGConst * ((N₁:ℝ) * N) ^ 2 + 1))
          ≤ Real.log D₁ + 2 * Real.log N := by
        rw [show 2 * Real.log N = Real.log ((N:ℝ) ^ 2) by rw [Real.log_pow]; norm_num,
          ← Real.log_mul hD₁0.ne' (by positivity)]
        refine Real.log_le_log (by positivity) ?_
        rw [hD₁]
        have : (1:ℝ) ≤ (N:ℝ) ^ 2 := by nlinarith
        nlinarith [hCG.le, sq_nonneg (N₁:ℝ)]
      have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN1
      have hb0 : 0 ≤ 1 - β := by linarith
      have e1 : (1 - β) * (Real.log (12 * (siegelGConst * ((N₁:ℝ) * N) ^ 2 + 1)) / Real.log (6/5) + 1)
          ≤ (1 - β) * (A * Real.log D₁ + 1) + (ε/2) * Real.log N := by
        calc (1 - β) * (Real.log (12 * (siegelGConst * ((N₁:ℝ) * N) ^ 2 + 1)) / Real.log (6/5) + 1)
            ≤ (1 - β) * ((Real.log D₁ + 2 * Real.log N) / Real.log (6/5) + 1) := by gcongr
          _ = (1 - β) * (A * Real.log D₁ + 1) + ((1 - β) * (2 / Real.log (6/5))) * Real.log N := by
              rw [hA]; field_simp; ring
          _ ≤ (1 - β) * (A * Real.log D₁ + 1) + (ε/2) * Real.log N := by gcongr
      linarith

    have hmain : K₁ * (N:ℝ) ^ (-(ε/2)) ≤ (Real.log N₁ + 1) * ((LFunction χ 1).re *
        ((Real.log N₁ + 1 + 1 / (ε/2)) * (N:ℝ) ^ (ε/2))) := by
      refine hLB.trans (hkey.trans ?_)
      have : 0 ≤ (LFunction χ 1).re * (LFunction (productChar χ₁ χ) 1).re := by positivity
      gcongr
    have hden : 0 < (Real.log N₁ + 1) * (Real.log N₁ + 1 + 1 / (ε/2)) := by positivity
    have hNN : (N:ℝ) ^ (ε/2) * (N:ℝ) ^ (-(ε/2)) = 1 := by
      rw [← Real.rpow_add hN0, add_neg_cancel, Real.rpow_zero]
    have hsplit : (N:ℝ) ^ (-ε) = (N:ℝ) ^ (-(ε/2)) * (N:ℝ) ^ (-(ε/2)) := by
      rw [← Real.rpow_add hN0]; ring_nf
    calc min K₂ K₃ * (N:ℝ) ^ (-ε) ≤ K₂ * (N:ℝ) ^ (-ε) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hNε.le
      _ = (K₁ * (N:ℝ) ^ (-(ε/2))) * ((N:ℝ) ^ (-(ε/2)) / ((Real.log N₁ + 1) * (Real.log N₁ + 1 + 1 / (ε/2)))) := by
          rw [hsplit, hK₂]; ring
      _ ≤ ((Real.log N₁ + 1) * ((LFunction χ 1).re * ((Real.log N₁ + 1 + 1 / (ε/2)) * (N:ℝ) ^ (ε/2))))
            * ((N:ℝ) ^ (-(ε/2)) / ((Real.log N₁ + 1) * (Real.log N₁ + 1 + 1 / (ε/2)))) :=
          mul_le_mul_of_nonneg_right hmain (by positivity)
      _ = (LFunction χ 1).re * ((N:ℝ) ^ (ε/2) * (N:ℝ) ^ (-(ε/2)))
            * (((Real.log N₁ + 1) * (Real.log N₁ + 1 + 1 / (ε/2)))
              / ((Real.log N₁ + 1) * (Real.log N₁ + 1 + 1 / (ε/2)))) := by ring
      _ = (LFunction χ 1).re := by rw [hNN, div_self hden.ne', mul_one, mul_one]

end Config
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

theorem siegel {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ^ 2 = 1 → χ ≠ 1 →
      C * (N:ℝ) ^ (-ε) ≤ (LFunction χ 1).re := by
  have hlog65 : 0 < Real.log (6/5:ℝ) := Real.log_pos (by norm_num)
  set η : ℝ := min (1/4) (ε * Real.log (6/5) / 4) with hη
  have hη0 : 0 < η := by positivity
  have hη4 : η ≤ 1/4 := min_le_left _ _
  have hηε : ∀ β : ℝ, 1 - η < β → (1 - β) * (2 / Real.log (6/5)) ≤ ε / 2 := by
    intro β hβ
    have h1 : 1 - β < ε * Real.log (6/5) / 4 := by
      linarith [min_le_right (1/4:ℝ) (ε * Real.log (6/5) / 4)]
    rw [mul_div_assoc', div_le_iff₀ hlog65]
    nlinarith
  by_cases hA : ∃ (N₁ : ℕ) (_ : NeZero N₁) (χ₁ : DirichletCharacter ℂ N₁) (β : ℝ),
      χ₁ ^ 2 = 1 ∧ χ₁ ≠ 1 ∧ 1 - η < β ∧ β < 1 ∧ LFunction χ₁ β = 0
  ·
    obtain ⟨N₁, _, χ₁, β, h₁, h₁', hβη, hβ1, hzero⟩ := hA
    refine siegel_of_config hε h₁ h₁' (by linarith) hβ1 (hηε β hβη) fun N _ χ hχ hχ' hψ ↦ ?_
    rw [P, hzero, zero_mul, mul_zero, Complex.zero_re]
  ·
    push Not at hA
    obtain ⟨β, hβ34, hβη, hβ1, hζ⟩ := exists_re_riemannZeta_neg hη0
    refine siegel_of_config (χ₁ := chi4) hε chi4_sq chi4_ne_one hβ34 hβ1 (hηε β hβη)
      fun N _ χ hχ hχ' hψ ↦ ?_
    have hpos : ∀ {M : ℕ} [NeZero M] (φ : DirichletCharacter ℂ M), φ ^ 2 = 1 → φ ≠ 1 →
        0 < (LFunction φ β).re ∧ (LFunction φ β).im = 0 := by
      intro M _ φ hφ hφ'
      refine ⟨Quadratic.re_LFunction_ofReal_pos_of_forall_ne_zero hφ hφ' (by linarith) hβ1.le
        fun σ hσ ↦ ?_, Quadratic.im_LFunction_ofReal hφ hφ' (by linarith)⟩
      rcases eq_or_lt_of_le hσ.2 with rfl | hσ1
      · exact LFunction_ne_zero_of_one_le_re φ (.inl hφ') (by simp)
      · exact hA M inferInstance φ σ hφ hφ' (by linarith [hσ.1]) hσ1
    obtain ⟨a, a'⟩ := hpos chi4 chi4_sq chi4_ne_one
    obtain ⟨b, b'⟩ := hpos χ hχ hχ'
    obtain ⟨c, c'⟩ := hpos (productChar chi4 χ) (productChar_sq_eq_one _ _ chi4_sq hχ) hψ
    obtain ⟨e1, e1'⟩ := mul_re_of_im_eq_zero b' c'
    obtain ⟨e2, e2'⟩ := mul_re_of_im_eq_zero a' e1'
    have hPre : 0 < (P chi4 χ β).re := by rw [P, e2, e1]; positivity
    have hPim : (P chi4 χ β).im = 0 := by rw [P, e2']
    rw [mul_re, hPim, mul_zero, sub_zero]
    exact (mul_neg_of_neg_of_pos hζ hPre).le

theorem siegel_norm {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ^ 2 = 1 → χ ≠ 1 →
      C * (N:ℝ) ^ (-ε) ≤ ‖LFunction χ 1‖ := by
  obtain ⟨C, hC, h⟩ := siegel hε
  exact ⟨C, hC, fun N _ χ hχ hχ' ↦ (h N χ hχ hχ').trans (re_le_norm _)⟩

theorem siegel_complexOrder {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ^ 2 = 1 → χ ≠ 1 →
      ((C * (N:ℝ) ^ (-ε) : ℝ) : ℂ) ≤ LFunction χ 1 := by
  obtain ⟨C, hC, h⟩ := siegel hε
  refine ⟨C, hC, fun N _ χ hχ hχ' ↦ ?_⟩
  rw [Quadratic.LFunction_one_eq_ofReal_re hχ hχ']
  exact_mod_cast h N χ hχ hχ'

end LandauSiegel
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

end P2M_Siegel
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

section P2M_Landau

open scoped ComplexOrder
p2m_open "Complex Filter Topology Set Metric Finset Set.Finset LSeries P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LSeries"

namespace LSeries
p2m_export "LSeries" "positive abscissaOfAbsConv_one convolution abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable logMul iteratedDeriv_alternating term_of_ne_zero abscissaOfAbsConv norm_term_eq positive_of_differentiable_of_eqOn absicssaOfAbsConv_logPowMul term_def term_nonneg term"
p2m_open "LSeries"

variable {a : ℕ → ℂ}

lemma re_term_logMul_pow (m : ℕ) (x : ℝ) (n : ℕ) :
    (term (logMul^[m] a) x n).re
      = if n = 0 then 0 else (Real.log n) ^ m * ((a n).re * (n:ℝ) ^ (-x)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [hn, ↓reduceIte, term_of_ne_zero hn]
  have hlog : (logMul^[m] a) n = (Real.log n : ℂ) ^ m * a n := by
    induction m with
    | zero => simp
    | succ m ih => rw [Function.iterate_succ_apply', logMul, ih, pow_succ, ← natCast_log]; ring
  rw [hlog, show (n:ℂ) ^ (x:ℂ) = (((n:ℝ) ^ x : ℝ) : ℂ) by
      rw [ofReal_cpow (Nat.cast_nonneg n)]; norm_cast,
    ← ofReal_pow, div_eq_mul_inv, ← ofReal_inv, mul_assoc, mul_comm (a n), ← mul_assoc,
    ← ofReal_mul, re_ofReal_mul, mul_assoc]
  congr 1
  rw [Real.rpow_neg (Nat.cast_nonneg n), mul_comm]

theorem abscissaOfAbsConv_lt_of_differentiableOn_ball' (ha : 0 ≤ a) {x : ℝ}
    (hx : abscissaOfAbsConv a ≤ x) {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball (x:ℂ) r))
    (hfa : ∀ s ∈ ball (x:ℂ) r, x < s.re → f s = LSeries a s) :
    abscissaOfAbsConv a < x := by

  set x₁ : ℝ := x + r/4 with hx₁
  set δ : ℝ := 3 * r / 8 with hδ
  set x₂ : ℝ := x₁ - δ with hx₂
  have hδ0 : 0 < δ := by positivity
  have hx₂x : x₂ < x := by rw [hx₂, hx₁, hδ]; linarith
  have habs₁ : abscissaOfAbsConv a < (x₁:ℂ).re := by
    rw [ofReal_re]; exact hx.trans_lt (by exact_mod_cast (by rw [hx₁]; linarith : x < x₁))

  have hsub : ball (x₁:ℂ) (r/2) ⊆ ball (x:ℂ) r := by
    intro s hs
    rw [mem_ball, dist_eq_norm] at hs ⊢
    have hx₁x : ‖(x₁:ℂ) - x‖ = r/4 := by
      rw [← ofReal_sub, norm_real, Real.norm_eq_abs, hx₁, add_sub_cancel_left, abs_of_pos]
      positivity
    calc ‖s - x‖ = ‖(s - x₁) + ((x₁:ℂ) - x)‖ := by ring_nf
      _ ≤ ‖s - x₁‖ + ‖(x₁:ℂ) - x‖ := norm_add_le _ _
      _ < r/2 + r/4 := by rw [hx₁x]; linarith
      _ ≤ r := by linarith
  have hf₁ : DifferentiableOn ℂ f (ball (x₁:ℂ) (r/2)) := hf.mono hsub
  have hx₂mem : (x₂:ℂ) ∈ ball (x₁:ℂ) (r/2) := by
    rw [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs, hx₂, sub_sub_cancel_left,
      abs_neg, abs_of_pos hδ0, hδ]
    linarith

  have hT := Complex.hasSum_taylorSeries_on_ball hf₁ hx₂mem

  have hev : f =ᶠ[𝓝 (x₁:ℂ)] LSeries a := by
    have ho : IsOpen (ball (x:ℂ) r ∩ {s : ℂ | x < s.re}) :=
      isOpen_ball.inter (isOpen_lt continuous_const continuous_re)
    have hmem : (x₁:ℂ) ∈ ball (x:ℂ) r ∩ {s : ℂ | x < s.re} := by
      refine ⟨?_, by simp [hx₁, hr]⟩
      rw [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs, hx₁, add_sub_cancel_left,
        abs_of_pos (by positivity)]
      linarith
    filter_upwards [ho.mem_nhds hmem] with s hs using hfa s hs.1 hs.2
  have hderiv : ∀ m, iteratedDeriv m f x₁ = (-1) ^ m * LSeries (logMul^[m] a) x₁ := fun m ↦ by
    rw [hev.iteratedDeriv_eq, LSeries_iteratedDeriv m habs₁]

  let T : ℕ → ℕ → ℝ := fun n m ↦
    if n = 0 then 0 else (Real.log n) ^ m * δ ^ m / m.factorial * ((a n).re * (n:ℝ) ^ (-x₁))
  have ha_re : ∀ n, 0 ≤ (a n).re := fun n ↦ (Complex.le_def.mp (ha n)).1
  have hT0 : ∀ n m, 0 ≤ T n m := by
    intro n m
    simp only [T]
    split_ifs with hn
    · exact le_rfl
    · have : 0 ≤ Real.log n := Real.log_natCast_nonneg n
      exact mul_nonneg (div_nonneg (mul_nonneg (pow_nonneg this m) (pow_nonneg hδ0.le m))
        (Nat.cast_nonneg _)) (mul_nonneg (ha_re n) (Real.rpow_nonneg (Nat.cast_nonneg n) _))

  have hrow : ∀ m, HasSum (fun n ↦ T n m)
      (((m.factorial : ℂ)⁻¹ • ((x₂:ℂ) - x₁) ^ m • iteratedDeriv m f x₁).re) := by
    intro m
    have hs : LSeriesSummable (logMul^[m] a) x₁ :=
      LSeriesSummable_of_abscissaOfAbsConv_lt_re (by rwa [absicssaOfAbsConv_logPowMul])
    have hval : ((m.factorial : ℂ)⁻¹ • ((x₂:ℂ) - x₁) ^ m • iteratedDeriv m f x₁).re
        = δ ^ m / m.factorial * (LSeries (logMul^[m] a) x₁).re := by
      have hxd : (x₂:ℂ) - x₁ = -(δ:ℂ) := by rw [hx₂]; push_cast; ring
      rw [hderiv, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_assoc, hxd,
        mul_assoc ((m.factorial:ℂ)⁻¹), ← mul_pow, show -(δ:ℂ) * -1 = δ by ring,
        show (m.factorial : ℂ)⁻¹ * (δ:ℂ) ^ m = ((δ ^ m / m.factorial : ℝ) : ℂ) by push_cast; ring,
        re_ofReal_mul]
    rw [hval]
    have h2 := (Complex.hasSum_re hs.hasSum).mul_left (δ ^ m / m.factorial)
    convert h2 using 1
    all_goals first | rfl | skip
    ext n
    rw [re_term_logMul_pow]
    simp only [T]
    split_ifs with hn
    · simp
    · ring

  have hcol : HasSum (fun m ↦ ((m.factorial : ℂ)⁻¹ • ((x₂:ℂ) - x₁) ^ m • iteratedDeriv m f x₁).re)
      (f x₂).re := Complex.hasSum_re hT

  have hexp : ∀ n, n ≠ 0 → HasSum (fun m ↦ T n m) ((a n).re * (n:ℝ) ^ (-x₂)) := by
    intro n hn
    have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have he := (NormedSpace.expSeries_div_hasSum_exp (δ * Real.log n)).mul_right
      ((a n).re * (n:ℝ) ^ (-x₁))
    convert he using 1
    all_goals first | rfl | skip
    · ext m
      simp only [T, hn, ↓reduceIte, mul_pow]
      ring
    · rw [show NormedSpace.exp (δ * Real.log n) = Real.exp (δ * Real.log n) from
          (congrFun Real.exp_eq_exp_ℝ _).symm, mul_comm δ, ← Real.rpow_def_of_pos hnpos, hx₂,
        show -(x₁ - δ) = δ + (-x₁) by ring, Real.rpow_add hnpos]
      ring

  let g : ℕ → ℝ := fun n ↦ if n = 0 then 0 else (a n).re * (n:ℝ) ^ (-x₂)
  have hg0 : ∀ n, 0 ≤ g n := fun n ↦ by
    simp only [g]; split_ifs
    · exact le_rfl
    · exact mul_nonneg (ha_re n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hgT : ∀ n, HasSum (fun m ↦ T n m) (g n) := fun n ↦ by
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [g, T, ↓reduceIte]; exact hasSum_zero
    · simp only [g, hn, ↓reduceIte]; exact hexp n hn

  have hbound : ∀ N, ∑ n ∈ range N, g n ≤ (f x₂).re := by
    intro N
    calc ∑ n ∈ range N, g n = ∑ n ∈ range N, ∑' m, T n m :=
          sum_congr rfl fun n _ ↦ (hgT n).tsum_eq.symm
      _ = ∑' m, ∑ n ∈ range N, T n m :=
          (Summable.tsum_finsetSum fun n _ ↦ (hgT n).summable).symm
      _ ≤ ∑' m, ((m.factorial : ℂ)⁻¹ • ((x₂:ℂ) - x₁) ^ m • iteratedDeriv m f x₁).re :=
          Summable.tsum_le_tsum (fun m ↦ ((hrow m).summable.sum_le_tsum (range N)
            (fun n _ ↦ hT0 n m)).trans_eq (hrow m).tsum_eq)
            (summable_sum fun n _ ↦ (hgT n).summable) hcol.summable
      _ = (f x₂).re := hcol.tsum_eq
  have hsum : Summable g := summable_of_sum_range_le hg0 hbound

  have hL : LSeriesSummable a x₂ := by
    refine Summable.of_norm ?_
    convert hsum using 1
    ext n
    rw [norm_term_eq]
    simp only [g, ofReal_re]
    split_ifs with hn
    · rfl
    · obtain ⟨hre, him⟩ := Complex.le_def.mp (ha n)
      have : a n = ((a n).re : ℂ) := Complex.ext (by simp) (by simpa using him.symm)
      rw [this, norm_real, Real.norm_eq_abs, abs_of_nonneg (ha_re n), ofReal_re,
        Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  exact hL.abscissaOfAbsConv_le.trans_lt (by simpa using hx₂x)

theorem not_exists_extension_of_abscissaOfAbsConv_eq (ha : 0 ≤ a) {x : ℝ}
    (hx : abscissaOfAbsConv a = x) {r : ℝ} (hr : 0 < r) :
    ¬ ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (ball (x:ℂ) r) ∧
        ∀ s ∈ ball (x:ℂ) r, x < s.re → f s = LSeries a s := by
  rintro ⟨f, hf, hfa⟩
  have := abscissaOfAbsConv_lt_of_differentiableOn_ball' ha hx.le hr hf hfa
  rw [hx] at this
  exact lt_irrefl _ this

theorem not_differentiableOn_ball_abscissaOfAbsConv (ha : 0 ≤ a) {x : ℝ}
    (hx : abscissaOfAbsConv a = x) {r : ℝ} (hr : 0 < r) :
    ¬ DifferentiableOn ℂ (LSeries a) (ball (x:ℂ) r) := fun h ↦
  not_exists_extension_of_abscissaOfAbsConv_eq ha hx hr ⟨LSeries a, h, fun _ _ _ ↦ rfl⟩

end LSeries
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

end P2M_Landau
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

section P2M_ZeroFactorization

open Complex Filter Topology Set Metric

namespace LandauSiegel

lemma finite_zeros_of_isCompact {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f ≠ 0) {K : Set ℂ}
    (hK : IsCompact K) : {z ∈ K | f z = 0}.Finite := by
  have han : AnalyticOnNhd ℂ f univ := hf.differentiableOn.analyticOnNhd isOpen_univ
  refine (hK.of_isClosed_subset ?_ (fun z hz ↦ hz.1)).finite ?_
  · exact hK.isClosed.inter (isClosed_eq hf.continuous continuous_const)
  · refine IsDiscrete.of_nhdsWithin fun z hz ↦ ?_
    rcases (han z trivial).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      apply hf0
      have := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ trivial h
      exact funext fun w ↦ this trivial
    · rw [Filter.le_pure_iff]
      rw [eventually_nhdsWithin_iff] at h
      rw [mem_nhdsWithin_iff_eventually]
      filter_upwards [h] with w hw hws
      by_contra hne
      exact hw hne hws.2

theorem exists_multiset_factorization {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f ≠ 0)
    (c : ℂ) (r : ℝ) :
    ∃ (Z : Multiset ℂ) (g : ℂ → ℂ), Differentiable ℂ g ∧ (∀ z ∈ closedBall c r, g z ≠ 0) ∧
      (∀ ρ ∈ Z, ρ ∈ closedBall c r ∧ f ρ = 0) ∧ ∀ z, f z = (Z.map (fun ρ ↦ z - ρ)).prod * g z := by

  suffices H : ∀ (n : ℕ) (f : ℂ → ℂ), Differentiable ℂ f → f ≠ 0 →
      {z ∈ closedBall c r | f z = 0}.ncard ≤ n →
      ∃ (Z : Multiset ℂ) (g : ℂ → ℂ), Differentiable ℂ g ∧ (∀ z ∈ closedBall c r, g z ≠ 0) ∧
        (∀ ρ ∈ Z, ρ ∈ closedBall c r ∧ f ρ = 0) ∧ ∀ z, f z = (Z.map (fun ρ ↦ z - ρ)).prod * g z from
    H _ f hf hf0 le_rfl
  intro n
  induction n with
  | zero =>
    intro f hf hf0 hcard
    have hfin := finite_zeros_of_isCompact hf hf0 (isCompact_closedBall c r)
    have hempty : {z ∈ closedBall c r | f z = 0} = ∅ :=
      (Set.ncard_eq_zero hfin).mp (Nat.le_zero.mp hcard)
    refine ⟨0, f, hf, fun z hz hfz ↦ ?_, by simp, fun z ↦ by simp⟩
    have : z ∈ {z ∈ closedBall c r | f z = 0} := ⟨hz, hfz⟩
    rw [hempty] at this
    exact this
  | succ n ih =>
    intro f hf hf0 hcard
    have hfin := finite_zeros_of_isCompact hf hf0 (isCompact_closedBall c r)
    by_cases hex : ∃ ρ ∈ closedBall c r, f ρ = 0
    · obtain ⟨ρ, hρK, hρ0⟩ := hex

      have han : AnalyticAt ℂ f ρ := hf.analyticAt ρ
      have hne' : ¬ ∀ᶠ z in 𝓝 ρ, f z = 0 := by
        intro h
        apply hf0
        have := (hf.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
          isPreconnected_univ (mem_univ ρ) h
        exact funext fun w ↦ this (mem_univ w)
      have hne : analyticOrderAt f ρ ≠ ⊤ := by rwa [ne_eq, analyticOrderAt_eq_top]
      set m := analyticOrderNatAt f ρ with hm
      obtain ⟨h, hh_an, hh_ne, hfh⟩ := han.analyticOrderAt_ne_top.mp hne
      have hm1 : 1 ≤ m := by
        by_contra hlt
        push Not at hlt
        have h0 : analyticOrderNatAt f ρ = 0 := by omega
        have h2 := Nat.cast_analyticOrderNatAt hne
        rw [h0, Nat.cast_zero] at h2
        exact (han.analyticOrderAt_eq_zero.mp h2.symm) hρ0

      let f₁ : ℂ → ℂ := Function.update (fun z ↦ f z / (z - ρ) ^ m) ρ (h ρ)
      have hf₁ρ : f₁ =ᶠ[𝓝 ρ] h := by
        filter_upwards [hfh] with z hz
        rcases eq_or_ne z ρ with rfl | hzρ
        · simp [f₁]
        · simp only [f₁, Function.update_of_ne hzρ, smul_eq_mul] at hz ⊢
          rw [hz, ← hm]
          field_simp [pow_ne_zero m (sub_ne_zero.mpr hzρ)]
      have hf₁_diff : Differentiable ℂ f₁ := by
        intro z
        rcases eq_or_ne z ρ with rfl | hzρ
        · exact hh_an.differentiableAt.congr_of_eventuallyEq hf₁ρ
        · have : f₁ =ᶠ[𝓝 z] fun z ↦ f z / (z - ρ) ^ m := by
            filter_upwards [eventually_ne_nhds hzρ] with w hw
            simp [f₁, Function.update_of_ne hw]
          refine DifferentiableAt.congr_of_eventuallyEq ?_ this
          exact (hf z).div ((differentiableAt_id.sub_const ρ).pow m)
            (pow_ne_zero m (sub_ne_zero.mpr hzρ))
      have hff₁ : ∀ z, f z = (z - ρ) ^ m * f₁ z := by
        intro z
        rcases eq_or_ne z ρ with rfl | hzρ
        · rw [hρ0, sub_self, zero_pow (by omega), zero_mul]
        · simp only [f₁, Function.update_of_ne hzρ]
          field_simp [pow_ne_zero m (sub_ne_zero.mpr hzρ)]
      have hf₁0 : f₁ ≠ 0 := by
        intro h0
        apply hf0
        funext z
        rw [hff₁ z, h0, Pi.zero_apply, mul_zero]
      have hf₁ρ_ne : f₁ ρ ≠ 0 := by simpa [f₁] using hh_ne

      have hzeros : {z ∈ closedBall c r | f₁ z = 0} = {z ∈ closedBall c r | f z = 0} \ {ρ} := by
        ext z
        simp only [mem_setOf_eq, mem_diff, mem_singleton_iff]
        constructor
        · rintro ⟨hzK, hz0⟩
          have hzρ : z ≠ ρ := fun h ↦ hf₁ρ_ne (h ▸ hz0)
          exact ⟨⟨hzK, by rw [hff₁ z, hz0, mul_zero]⟩, hzρ⟩
        · rintro ⟨⟨hzK, hz0⟩, hzρ⟩
          refine ⟨hzK, ?_⟩
          have := hff₁ z
          rw [hz0] at this
          exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero m (sub_ne_zero.mpr hzρ))
      have hcard₁ : {z ∈ closedBall c r | f₁ z = 0}.ncard ≤ n := by
        rw [hzeros, Set.ncard_diff_singleton_of_mem (show ρ ∈ {z ∈ closedBall c r | f z = 0} from ⟨hρK, hρ0⟩)]
        omega
      obtain ⟨Z₁, g, hg, hgK, hZ₁, hfac⟩ := ih f₁ hf₁_diff hf₁0 hcard₁
      refine ⟨Multiset.replicate m ρ + Z₁, g, hg, hgK, fun ρ' hρ' ↦ ?_, fun z ↦ ?_⟩
      · rcases Multiset.mem_add.mp hρ' with h1 | h1
        · rw [Multiset.eq_of_mem_replicate h1]; exact ⟨hρK, hρ0⟩
        · obtain ⟨hK', h0'⟩ := hZ₁ ρ' h1
          exact ⟨hK', by rw [hff₁ ρ', h0', mul_zero]⟩
      · rw [Multiset.map_add, Multiset.prod_add, Multiset.map_replicate, Multiset.prod_replicate,
          hff₁ z, hfac z, mul_assoc]
    · push Not at hex
      exact ⟨0, f, hf, fun z hz ↦ hex z hz, by simp, fun z ↦ by simp⟩

end LandauSiegel
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

end P2M_ZeroFactorization
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

section P2M_LogDerivBound

open Complex Filter Topology Set Metric

namespace LandauSiegel

theorem exists_log_of_forall_ne_zero {g : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hg : DifferentiableOn ℂ g (ball 0 r)) (hg0 : ∀ z ∈ ball (0:ℂ) r, g z ≠ 0) :
    ∃ ℓ : ℂ → ℂ, (∀ z ∈ ball (0:ℂ) r, HasDerivAt ℓ (deriv g z / g z) z) ∧ ℓ 0 = 0 ∧
      ∀ z ∈ ball (0:ℂ) r, Complex.exp (ℓ z) = g z / g 0 := by
  have hq : DifferentiableOn ℂ (fun z ↦ deriv g z / g z) (ball 0 r) :=
    (hg.analyticOnNhd isOpen_ball).deriv.differentiableOn.div hg hg0
  obtain ⟨ℓ, hℓ0, hℓ⟩ := (hq.isExactOn_ball).with_val_at 0 0
  refine ⟨ℓ, hℓ, hℓ0, fun z hz ↦ ?_⟩

  let φ : ℂ → ℂ := fun w ↦ g w * Complex.exp (-ℓ w)
  have hφd : ∀ w ∈ ball (0:ℂ) r, HasDerivAt φ 0 w := by
    intro w hw
    have h1 : HasDerivAt g (deriv g w) w :=
      (hg.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
    have h2 : HasDerivAt (fun w ↦ Complex.exp (-ℓ w)) (Complex.exp (-ℓ w) * -(deriv g w / g w)) w :=
      (hℓ w hw).neg.cexp
    convert h1.mul h2 using 1
    · rfl
    · rfl
    · rfl
    field_simp [hg0 w hw]
    ring
  have hconst : φ z = φ 0 := by
    have := (convex_ball (0:ℂ) r).norm_image_sub_le_of_norm_deriv_le (C := 0)
      (fun w hw ↦ (hφd w hw).differentiableAt) (fun w hw ↦ by rw [(hφd w hw).deriv, norm_zero])
      (mem_ball_self hr) hz
    rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at this
    exact this
  simp only [φ, hℓ0, neg_zero, Complex.exp_zero, mul_one] at hconst
  rw [eq_div_iff (hg0 0 (mem_ball_self hr)), ← hconst, mul_left_comm, ← Complex.exp_add,
    add_neg_cancel, Complex.exp_zero, mul_one]

lemma differentiable_multiset_prod_sub (Z : Multiset ℂ) :
    Differentiable ℂ (fun w ↦ (Z.map (fun ρ ↦ w - ρ)).prod) := by
  induction Z using Multiset.induction with
  | empty => simp
  | cons ρ Z ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (differentiable_id.sub_const ρ).mul ih

lemma multiset_prod_sub_ne_zero {Z : Multiset ℂ} {z : ℂ} (hz : ∀ ρ ∈ Z, z ≠ ρ) :
    (Z.map (fun ρ ↦ z - ρ)).prod ≠ 0 := by
  refine Multiset.prod_ne_zero fun h ↦ ?_
  obtain ⟨ρ', hρ', h0⟩ := Multiset.mem_map.mp h
  exact hz ρ' hρ' (sub_eq_zero.mp h0)

lemma logDeriv_multiset_prod_sub (Z : Multiset ℂ) (z : ℂ) (hz : ∀ ρ ∈ Z, z ≠ ρ) :
    logDeriv (fun w ↦ (Z.map (fun ρ ↦ w - ρ)).prod) z = (Z.map fun ρ ↦ (z - ρ)⁻¹).sum := by
  induction Z using Multiset.induction with
  | empty => simp [logDeriv_apply]
  | cons ρ Z ih =>
    have hz' : ∀ ρ' ∈ Z, z ≠ ρ' := fun ρ' h ↦ hz ρ' (Multiset.mem_cons_of_mem h)
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    rw [logDeriv_mul (f := fun w ↦ w - ρ) (g := fun w ↦ (Z.map (fun ρ ↦ w - ρ)).prod) z
      (sub_ne_zero.mpr (hz ρ (Multiset.mem_cons_self ρ Z))) (multiset_prod_sub_ne_zero hz')
      (differentiableAt_id.sub_const ρ) (differentiable_multiset_prod_sub Z z), ih hz']
    congr 1
    rw [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]

noncomputable def bFactor (R : ℝ) (ρ : ℂ) (w : ℂ) : ℂ := ((R:ℂ) ^ 2 - (starRingEnd ℂ) ρ * w) / R

lemma differentiable_bFactor (R : ℝ) (ρ : ℂ) : Differentiable ℂ (bFactor R ρ) :=
  ((differentiable_const _).sub ((differentiable_const _).mul differentiable_id)).div_const _

lemma bFactor_zero (R : ℝ) (ρ : ℂ) (hR : R ≠ 0) : bFactor R ρ 0 = R := by
  simp [bFactor, sq, hR]

lemma deriv_bFactor (R : ℝ) (ρ w : ℂ) : deriv (bFactor R ρ) w = -(starRingEnd ℂ) ρ / R := by
  unfold bFactor
  rw [deriv_div_const, deriv_const_sub, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]

lemma norm_bFactor_of_mem_sphere {R : ℝ} (hR : 0 < R) (ρ : ℂ) {w : ℂ} (hw : ‖w‖ = R) :
    ‖bFactor R ρ w‖ = ‖w - ρ‖ := by
  have hwc : (R:ℂ) ^ 2 = w * (starRingEnd ℂ) w := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]; push_cast; ring
  rw [bFactor, hwc, show w * (starRingEnd ℂ) w - (starRingEnd ℂ) ρ * w
      = w * (starRingEnd ℂ) (w - ρ) by rw [map_sub]; ring, norm_div, norm_mul,
    Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, hw]
  field_simp

lemma bFactor_ne_zero {R : ℝ} (hR : 0 < R) {ρ w : ℂ} (h : ‖ρ‖ * ‖w‖ < R ^ 2) :
    bFactor R ρ w ≠ 0 := by
  rw [bFactor, div_ne_zero_iff]
  refine ⟨fun h0 ↦ ?_, by exact_mod_cast hR.ne'⟩
  have : ‖(R:ℂ) ^ 2‖ = ‖(starRingEnd ℂ) ρ * w‖ := by rw [sub_eq_zero.mp h0]
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, norm_mul, Complex.norm_conj] at this
  linarith

lemma differentiable_multiset_prod_bFactor (R : ℝ) (Z : Multiset ℂ) :
    Differentiable ℂ (fun w ↦ (Z.map (fun ρ ↦ bFactor R ρ w)).prod) := by
  induction Z using Multiset.induction with
  | empty => simp
  | cons ρ Z ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (differentiable_bFactor R ρ).mul ih

lemma logDeriv_multiset_prod_bFactor_zero {R : ℝ} (hR : 0 < R) (Z : Multiset ℂ) :
    logDeriv (fun w ↦ (Z.map (fun ρ ↦ bFactor R ρ w)).prod) 0
      = (Z.map fun ρ ↦ -(starRingEnd ℂ) ρ / R ^ 2).sum := by
  induction Z using Multiset.induction with
  | empty => simp [logDeriv_apply]
  | cons ρ Z ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    have h0 : ∀ ρ', bFactor R ρ' 0 ≠ 0 := fun ρ' ↦ by
      rw [bFactor_zero R ρ' hR.ne']; exact_mod_cast hR.ne'
    rw [logDeriv_mul (f := bFactor R ρ) (g := fun w ↦ (Z.map (fun ρ ↦ bFactor R ρ w)).prod) 0
      (h0 ρ) (Multiset.prod_ne_zero fun h ↦ ?_) (differentiable_bFactor R ρ 0)
      (differentiable_multiset_prod_bFactor R Z 0), ih]
    · congr 1
      rw [logDeriv_apply, deriv_bFactor, bFactor_zero R ρ hR.ne']
      field_simp
    · obtain ⟨ρ', _, h0'⟩ := Multiset.mem_map.mp h
      exact h0 ρ' h0'

lemma norm_multiset_prod (Z : Multiset ℂ) (F : ℂ → ℂ) :
    ‖(Z.map F).prod‖ = (Z.map fun ρ ↦ ‖F ρ‖).prod := by
  induction Z using Multiset.induction with
  | empty => simp
  | cons ρ Z ih => simp [ih]

lemma re_multiset_sum (Z : Multiset ℂ) (F : ℂ → ℂ) :
    ((Z.map F).sum).re = (Z.map fun ρ ↦ (F ρ).re).sum := by
  induction Z using Multiset.induction with
  | empty => simp
  | cons ρ Z ih => simp [ih]

lemma multiset_prod_le_pow_card {Z : Multiset ℂ} {F : ℂ → ℝ} {C : ℝ} (h0 : ∀ ρ ∈ Z, 0 ≤ F ρ)
    (hC : ∀ ρ ∈ Z, F ρ ≤ C) : (Z.map F).prod ≤ C ^ Multiset.card Z := by
  induction Z using Multiset.induction with
  | empty => simp
  | cons ρ Z ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ]
    have h0' : ∀ ρ' ∈ Z, 0 ≤ F ρ' := fun ρ' h ↦ h0 ρ' (Multiset.mem_cons_of_mem h)
    have hC' : ∀ ρ' ∈ Z, F ρ' ≤ C := fun ρ' h ↦ hC ρ' (Multiset.mem_cons_of_mem h)
    rw [mul_comm]
    exact mul_le_mul (ih h0' hC') (hC ρ (Multiset.mem_cons_self _ _)) (h0 ρ (Multiset.mem_cons_self _ _))
      (le_trans (Multiset.prod_nonneg fun x hx ↦ by
        obtain ⟨ρ', hρ', rfl⟩ := Multiset.mem_map.mp hx; exact h0' ρ' hρ') (ih h0' hC') |>.trans' le_rfl |> fun h ↦
        (pow_nonneg ((h0 ρ (Multiset.mem_cons_self _ _)).trans (hC ρ (Multiset.mem_cons_self _ _))) _))

theorem neg_re_logDeriv_le {f g : ℂ → ℂ} {r R M : ℝ} (hr : 0 < r) (hrR : r < R) (Z : Multiset ℂ)
    (hg : Differentiable ℂ g) (hgK : ∀ z ∈ closedBall (0:ℂ) r, g z ≠ 0)
    (hZ : ∀ ρ ∈ Z, ρ ∈ closedBall (0:ℂ) r) (hfac : ∀ z, f z = (Z.map (fun ρ ↦ z - ρ)).prod * g z)
    (h0 : f 0 ≠ 0) (hM : ∀ z ∈ closedBall (0:ℂ) R, ‖f z‖ ≤ M * ‖f 0‖) :
    -(logDeriv f 0).re
      ≤ 4 * (Real.log M + 1) / r + (Z.map fun ρ ↦ ρ.re * (1 / ‖ρ‖ ^ 2 - 1 / R ^ 2)).sum := by
  have hR : 0 < R := hr.trans hrR
  have hfeq : f = fun z ↦ (Z.map (fun ρ ↦ z - ρ)).prod * g z := funext hfac
  have hZ' : ∀ ρ ∈ Z, ‖ρ‖ ≤ r := fun ρ h ↦ mem_closedBall_zero_iff.mp (hZ ρ h)
  have hρ0 : ∀ ρ ∈ Z, (0:ℂ) ≠ ρ := by
    intro ρ hρ h
    apply h0
    rw [hfac 0, Multiset.prod_eq_zero, zero_mul]
    exact Multiset.mem_map.mpr ⟨ρ, hρ, by rw [← h, sub_self]⟩
  have hf0pos : 0 < ‖f 0‖ := norm_pos_iff.mpr h0
  have hM1 : 1 ≤ M := by
    have := hM 0 (mem_closedBall_self hR.le)
    nlinarith
  set L : ℝ := Real.log M + 1 with hL
  have hL0 : 0 < L := by have := Real.log_nonneg hM1; linarith

  set G : ℂ → ℂ := fun w ↦ g w * (Z.map (fun ρ ↦ bFactor R ρ w)).prod with hGdef
  have hGd : Differentiable ℂ G := hg.mul (differentiable_multiset_prod_bFactor R Z)
  have hGsphere : ∀ w ∈ sphere (0:ℂ) R, ‖G w‖ = ‖f w‖ := by
    intro w hw
    rw [mem_sphere_zero_iff_norm] at hw
    rw [hGdef, hfac w, norm_mul, norm_mul, norm_multiset_prod, norm_multiset_prod, mul_comm]
    congr 2
    exact Multiset.map_congr rfl fun ρ _ ↦ norm_bFactor_of_mem_sphere hR ρ hw
  have hGbound : ∀ z ∈ closedBall (0:ℂ) R, ‖G z‖ ≤ M * ‖f 0‖ := by
    intro z hz
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hGd.diffContOnCl
      (fun w hw ↦ ?_) (by rwa [closure_ball 0 hR.ne'])
    rw [frontier_ball 0 hR.ne'] at hw
    rw [hGsphere w hw]
    exact hM w (sphere_subset_closedBall hw)
  have hG0 : G 0 = g 0 * R ^ Multiset.card Z := by
    rw [hGdef]
    simp only
    rw [Multiset.map_congr rfl fun ρ _ ↦ bFactor_zero R ρ hR.ne', Multiset.map_const',
      Multiset.prod_replicate]
  have hfG0 : ‖f 0‖ ≤ ‖G 0‖ := by
    rw [hfac 0, hG0, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR, norm_multiset_prod, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact multiset_prod_le_pow_card (fun _ _ ↦ norm_nonneg _)
      fun ρ hρ ↦ by rw [zero_sub, norm_neg]; exact (hZ' ρ hρ).trans hrR.le
  have hG0pos : 0 < ‖G 0‖ := hf0pos.trans_le hfG0
  have hGne : ∀ z ∈ ball (0:ℂ) r, G z ≠ 0 := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    refine mul_ne_zero (hgK z (mem_closedBall_zero_iff.mpr hz.le)) (Multiset.prod_ne_zero fun h ↦ ?_)
    obtain ⟨ρ, hρ, hb⟩ := Multiset.mem_map.mp h
    refine bFactor_ne_zero hR ?_ hb
    calc ‖ρ‖ * ‖z‖ ≤ r * r := mul_le_mul (hZ' ρ hρ) hz.le (norm_nonneg _) hr.le
      _ < R ^ 2 := by rw [sq]; exact mul_lt_mul'' hrR hrR hr.le hr.le

  obtain ⟨ℓ, hℓ, hℓ0, hℓexp⟩ := exists_log_of_forall_ne_zero hr hGd.differentiableOn hGne
  have hℓd : DifferentiableOn ℂ ℓ (ball 0 r) := fun z hz ↦ (hℓ z hz).differentiableAt.differentiableWithinAt
  have hℓre : ∀ z ∈ ball (0:ℂ) r, (ℓ z).re ≤ L := by
    intro z hz
    have hGz : 0 < ‖G z‖ := norm_pos_iff.mpr (hGne z hz)
    have h1 : Real.exp (ℓ z).re = ‖G z‖ / ‖G 0‖ := by
      rw [← Complex.norm_exp, hℓexp z hz, norm_div]
    have h2 : (ℓ z).re = Real.log (‖G z‖ / ‖G 0‖) := by rw [← h1, Real.log_exp]
    rw [h2, hL]
    have hzR : z ∈ closedBall (0:ℂ) R :=
      mem_closedBall_zero_iff.mpr ((mem_ball_zero_iff.mp hz).le.trans hrR.le)
    calc Real.log (‖G z‖ / ‖G 0‖) ≤ Real.log (M * ‖f 0‖ / ‖G 0‖) := by
          gcongr; exact hGbound z hzR
      _ ≤ Real.log M := by
          refine Real.log_le_log (by positivity) ?_
          rw [div_le_iff₀ hG0pos]
          exact mul_le_mul_of_nonneg_left hfG0 (by linarith)
      _ ≤ Real.log M + 1 := by linarith

  have hBC : ∀ z ∈ ball (0:ℂ) r, ‖ℓ z‖ ≤ 2 * L * ‖z‖ / (r - ‖z‖) := fun z hz ↦
    Complex.borelCaratheodory_zero hL0 hℓd (fun w hw ↦ hℓre w hw) hr hz hℓ0
  have hsph : ∀ z ∈ sphere (0:ℂ) (r/2), ‖ℓ z‖ ≤ 2 * L := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    have hzb : z ∈ ball (0:ℂ) r := mem_ball_zero_iff.mpr (by linarith)
    have := hBC z hzb
    rw [hz, show r - r/2 = r/2 by ring] at this
    calc ‖ℓ z‖ ≤ 2 * L * (r/2) / (r/2) := this
      _ = 2 * L := by field_simp
  have hdcl : DiffContOnCl ℂ ℓ (ball 0 (r/2)) := by
    refine (hℓd.mono ?_).diffContOnCl
    rw [closure_ball 0 (by positivity : r/2 ≠ 0)]
    exact closedBall_subset_ball (by linarith)
  have hCauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < r/2)
    hdcl hsph
  have hdℓ : ‖deriv ℓ 0‖ ≤ 4 * L / r := by
    calc ‖deriv ℓ 0‖ ≤ 2 * L / (r/2) := hCauchy
      _ = 4 * L / r := by field_simp; ring

  have hℓ' : deriv ℓ 0 = logDeriv G 0 := (hℓ 0 (mem_ball_self hr)).deriv
  have hbprod0 : (Z.map (fun ρ ↦ bFactor R ρ 0)).prod ≠ 0 := by
    refine Multiset.prod_ne_zero fun h ↦ ?_
    obtain ⟨ρ, _, hb⟩ := Multiset.mem_map.mp h
    rw [bFactor_zero R ρ hR.ne'] at hb
    exact hR.ne' (by exact_mod_cast hb)
  have hg0 : g 0 ≠ 0 := hgK 0 (mem_closedBall_self hr.le)
  have hlogG : logDeriv G 0 = logDeriv g 0 + (Z.map fun ρ ↦ -(starRingEnd ℂ) ρ / R ^ 2).sum := by
    rw [hGdef, logDeriv_mul (f := g) (g := fun w ↦ (Z.map (fun ρ ↦ bFactor R ρ w)).prod) 0 hg0
      hbprod0 (hg 0) (differentiable_multiset_prod_bFactor R Z 0),
      logDeriv_multiset_prod_bFactor_zero hR]
  have hlogf : logDeriv f 0 = (Z.map fun ρ ↦ ((0:ℂ) - ρ)⁻¹).sum + logDeriv g 0 := by
    rw [hfeq, logDeriv_mul (f := fun z ↦ (Z.map (fun ρ ↦ z - ρ)).prod) (g := g) 0
      (multiset_prod_sub_ne_zero hρ0) hg0 (differentiable_multiset_prod_sub Z 0) (hg 0),
      logDeriv_multiset_prod_sub Z 0 hρ0]

  have hsum : ((Z.map fun ρ ↦ -(starRingEnd ℂ) ρ / R ^ 2).sum).re
      - ((Z.map fun ρ ↦ ((0:ℂ) - ρ)⁻¹).sum).re
      = (Z.map fun ρ ↦ ρ.re * (1 / ‖ρ‖ ^ 2 - 1 / R ^ 2)).sum := by
    rw [re_multiset_sum, re_multiset_sum, ← Multiset.sum_map_sub]
    refine congrArg _ (Multiset.map_congr rfl fun ρ _ ↦ ?_)
    rw [zero_sub, inv_neg, Complex.neg_re, Complex.inv_re, Complex.normSq_eq_norm_sq,
      show ((R:ℂ) ^ 2) = ((R ^ 2 : ℝ) : ℂ) by push_cast; rfl, Complex.div_ofReal_re, Complex.neg_re,
      Complex.conj_re]
    ring
  have key : (logDeriv f 0).re = (deriv ℓ 0).re
      - (Z.map fun ρ ↦ ρ.re * (1 / ‖ρ‖ ^ 2 - 1 / R ^ 2)).sum := by
    rw [← hsum, hlogf, hℓ', hlogG]
    simp only [add_re]
    ring
  rw [key]
  have := (abs_re_le_norm (deriv ℓ 0)).trans hdℓ
  have := neg_le_of_abs_le this
  rw [hL] at this ⊢
  linarith

end LandauSiegel
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

end P2M_LogDerivBound
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

section P2M_LFunctionLogDeriv

open scoped ComplexOrder
p2m_open "Complex Filter Topology Set Metric DirichletCharacter P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.DirichletCharacter"

namespace LandauSiegel

lemma norm_LFunction_le_riemannZeta {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) {σ : ℝ}
    (hσ : 1 < σ) : ‖LFunction ψ σ‖ ≤ ‖riemannZeta σ‖ := by
  have hσ' : 1 < (σ:ℂ).re := by simpa using hσ
  have hs1 : LSeriesSummable 1 σ := by
    rw [LSeriesSummable_one_iff]; simpa using hσ
  have hsψ : LSeriesSummable (ψ ·) σ := (ZMod.LSeriesSummable_of_one_lt_re ψ hσ')
  rw [LFunction_eq_LSeries ψ hσ', ← LSeries_one_eq_riemannZeta hσ', LSeries, LSeries]
  have hpos : 0 ≤ ∑' n, LSeries.term 1 (σ:ℂ) n :=
    tsum_nonneg fun n ↦ LSeries.term_nonneg (by simp) _
  obtain ⟨hre, him⟩ := Complex.le_def.mp hpos
  have hreal : ∑' n, LSeries.term 1 (σ:ℂ) n = ((∑' n, LSeries.term 1 (σ:ℂ) n).re : ℂ) :=
    Complex.ext (by simp) (by simp [← him])
  rw [hreal, Complex.norm_real, Real.norm_of_nonneg (by simpa using hre), Complex.re_tsum hs1]
  refine (norm_tsum_le_tsum_norm hsψ.norm).trans (Summable.tsum_le_tsum (fun n ↦ ?_) hsψ.norm
    (Complex.hasSum_re hs1.hasSum).summable)
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [hn, ↓reduceIte, LSeries.term_of_ne_zero hn, Pi.one_apply, ofReal_re]
    rw [show (1:ℂ) / (n:ℂ) ^ (σ:ℂ) = (((1:ℝ) / (n:ℝ) ^ σ : ℝ) : ℂ) by
      rw [ofReal_div, ofReal_one, ofReal_cpow (Nat.cast_nonneg n)]; norm_cast, ofReal_re]
    gcongr
    exact ψ.norm_le_one _

lemma inv_norm_riemannZeta_le_norm_LFunction {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {σ : ℝ} (hσ : 1 < σ) : ‖riemannZeta σ‖⁻¹ ≤ ‖LFunction χ σ‖ := by
  have hζ : 0 < ‖riemannZeta σ‖ := norm_pos_iff.mpr (riemannZeta_ofReal_pos hσ).ne'
  have h := norm_LFunction_product_ge_one χ (x := σ - 1) (by linarith) 0
  simp only [ofReal_zero, mul_zero, add_zero, ofReal_sub, ofReal_one, add_sub_cancel] at h
  rw [norm_mul, norm_mul, norm_pow, norm_pow] at h
  have h0 : ‖LFunctionTrivChar N σ‖ ≤ ‖riemannZeta σ‖ := norm_LFunction_le_riemannZeta 1 hσ
  have h2 : ‖LFunction (χ ^ 2) σ‖ ≤ ‖riemannZeta σ‖ := norm_LFunction_le_riemannZeta _ hσ
  have h4 : 1 ≤ (‖riemannZeta σ‖ * ‖LFunction χ σ‖) ^ 4 := by
    calc (1:ℝ) ≤ ‖LFunctionTrivChar N σ‖ ^ 3 * ‖LFunction χ σ‖ ^ 4 * ‖LFunction (χ ^ 2) σ‖ := h
      _ ≤ ‖riemannZeta σ‖ ^ 3 * ‖LFunction χ σ‖ ^ 4 * ‖riemannZeta σ‖ := by gcongr
      _ = (‖riemannZeta σ‖ * ‖LFunction χ σ‖) ^ 4 := by ring
  have h5 : 1 ≤ ‖riemannZeta σ‖ * ‖LFunction χ σ‖ := by
    by_contra hlt
    push Not at hlt
    have := pow_lt_one₀ (by positivity) hlt (by norm_num : 4 ≠ 0)
    linarith
  rw [inv_le_iff_one_le_mul₀ hζ, mul_comm]
  exact h5

lemma exists_riemannZeta_le : ∃ A : ℝ, 0 ≤ A ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
    ‖riemannZeta σ‖ ≤ 1 / (σ - 1) + A := by
  obtain ⟨A, hA⟩ := (isCompact_Icc (a := (1:ℝ)) (b := 2)).exists_bound_of_continuousOn
    ((differentiable_zeta0.continuous.comp continuous_ofReal).continuousOn)
  refine ⟨max A 0, le_max_right _ _, fun σ h1 h2 ↦ ?_⟩
  have hσ1 : (σ:ℂ) ≠ 1 := by
    intro h; apply_fun Complex.re at h; simp at h; linarith
  have := zeta0_apply_of_ne_one hσ1
  have hb := hA σ ⟨h1.le, h2⟩
  simp only [Function.comp_apply] at hb
  calc ‖riemannZeta σ‖ = ‖zeta0 σ + 1 / ((σ:ℂ) - 1)‖ := by rw [this]; ring_nf
    _ ≤ ‖zeta0 σ‖ + ‖1 / ((σ:ℂ) - 1)‖ := norm_add_le _ _
    _ ≤ A + 1 / (σ - 1) := by
        gcongr
        rw [show (σ:ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) by push_cast; ring, ← ofReal_one, ← ofReal_div,
          Complex.norm_real, Real.norm_of_nonneg (le_of_lt (by
            have : 0 < σ - 1 := by linarith
            positivity))]
    _ ≤ 1 / (σ - 1) + max A 0 := by linarith [le_max_left A 0]

section Main

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

noncomputable def zeroTerm (ρ : ℂ) : ℝ := ρ.re * (1 / ‖ρ‖ ^ 2 - 4)

lemma zeroTerm_nonpos {ρ : ℂ} (h1 : ‖ρ‖ ≤ 1/4) (h2 : ρ.re ≤ 0) : zeroTerm ρ ≤ 0 := by
  rw [zeroTerm]
  rcases eq_or_ne ρ 0 with rfl | hρ
  · simp
  have hn : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ
  have : 4 ≤ 1 / ‖ρ‖ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  exact mul_nonpos_of_nonpos_of_nonneg h2 (by linarith)

lemma zeroTerm_real_le {d : ℝ} (hd : 0 < d) (hd4 : d ≤ 1/4) :
    zeroTerm ((-d : ℝ) : ℂ) ≤ -1 / d + 1 := by
  rw [zeroTerm, ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hd]
  have : (-d) * (1 / d ^ 2 - 4) = -1 / d + 4 * d := by field_simp; ring
  rw [this]
  linarith

theorem neg_re_logDeriv_LFunction_le (hχ : χ ≠ 1) {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 3/2) :
    ∃ Z : Multiset ℂ,
      (∀ ρ ∈ Z, ‖ρ‖ ≤ 1/4 ∧ LFunction χ (σ + ρ) = 0 ∧ ρ.re < 0) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1/4 → LFunction χ (σ + z) = 0 → z ∈ Z) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1/4 → LFunction χ (σ + z) = 0 → deriv (LFunction χ) (σ + z) = 0 →
        z ∈ Z.erase z) ∧
      -(deriv (LFunction χ) σ / LFunction χ σ).re
        ≤ 16 * (Real.log (4 * q * ‖riemannZeta σ‖) + 1) + (Z.map zeroTerm).sum := by
  set f : ℂ → ℂ := fun z ↦ LFunction χ (σ + z) with hfdef
  have hfd : Differentiable ℂ f := (differentiable_LFunction hχ).comp
    ((differentiable_const _).add differentiable_id)
  have hderiv : ∀ z, deriv f z = deriv (LFunction χ) (σ + z) := fun z ↦ by
    rw [hfdef]; exact deriv_comp_const_add _ _ _
  have hf0 : f 0 ≠ 0 := by
    simp only [f, add_zero]
    exact LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simp [hσ.le])
  have hfne : f ≠ 0 := fun h ↦ hf0 (by rw [h]; rfl)
  obtain ⟨Z, g, hg, hgK, hZ, hfac⟩ := exists_multiset_factorization hfd hfne 0 (1/4)

  have hζ : 0 < ‖riemannZeta σ‖ := norm_pos_iff.mpr (riemannZeta_ofReal_pos hσ).ne'
  have hLσ : ‖riemannZeta σ‖⁻¹ ≤ ‖f 0‖ := by
    simp only [f, add_zero]; exact inv_norm_riemannZeta_le_norm_LFunction χ hσ
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hM : ∀ z ∈ closedBall (0:ℂ) (1/2), ‖f z‖ ≤ (4 * q * ‖riemannZeta σ‖) * ‖f 0‖ := by
    intro z hz
    rw [mem_closedBall_zero_iff] at hz
    have hre : 1/2 ≤ (σ + z : ℂ).re := by
      simp only [add_re, ofReal_re]
      have := (abs_re_le_norm z).trans hz
      have := neg_le_of_abs_le this
      linarith
    have h1 : ‖f z‖ ≤ 4 * q := by
      have hn2 : ‖(σ:ℂ) + z‖ ≤ 2 := by
        calc ‖(σ:ℂ) + z‖ ≤ ‖(σ:ℂ)‖ + ‖z‖ := norm_add_le _ _
          _ ≤ 3/2 + 1/2 := by
              rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; exact add_le_add hσ2 hz
          _ = 2 := by norm_num
      calc ‖f z‖ ≤ q * ‖(σ:ℂ) + z‖ / (σ + z : ℂ).re := norm_LFunction_le χ hχ (by linarith)
        _ ≤ q * 2 / (1/2) :=
            div_le_div₀ (by positivity) (by gcongr) (by norm_num) hre
        _ = 4 * q := by ring
    calc ‖f z‖ ≤ 4 * q := h1
      _ = (4 * q * ‖riemannZeta σ‖) * ‖riemannZeta σ‖⁻¹ := by field_simp
      _ ≤ (4 * q * ‖riemannZeta σ‖) * ‖f 0‖ := by gcongr
  have hmain := neg_re_logDeriv_le (f := f) (r := 1/4) (R := 1/2) (by norm_num) (by norm_num) Z hg hgK
    (fun ρ h ↦ (hZ ρ h).1) hfac hf0 hM

  refine ⟨Z, fun ρ hρ ↦ ?_, fun z hz hz0 ↦ ?_, fun z hz hz0 hz1 ↦ ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hZ ρ hρ
    refine ⟨mem_closedBall_zero_iff.mp h1, h2, ?_⟩
    by_contra hre
    push Not at hre
    exact LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simp; linarith) h2
  · have : (Z.map (fun ρ ↦ z - ρ)).prod = 0 := by
      have h := hfac z
      rw [show f z = 0 from hz0] at h
      exact (mul_eq_zero.mp h.symm).resolve_right (hgK z (mem_closedBall_zero_iff.mpr hz))
    obtain ⟨ρ, hρ, h0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp this)
    rwa [← sub_eq_zero.mp h0] at hρ
  ·
    have hzZ : z ∈ Z := by
      have : (Z.map (fun ρ ↦ z - ρ)).prod = 0 := by
        have h := hfac z
        rw [show f z = 0 from hz0] at h
        exact (mul_eq_zero.mp h.symm).resolve_right (hgK z (mem_closedBall_zero_iff.mpr hz))
      obtain ⟨ρ, hρ, h0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp this)
      rwa [← sub_eq_zero.mp h0] at hρ
    by_contra hnot

    set Z' := Z.erase z with hZ'
    have hcons : Z = z ::ₘ Z' := (Multiset.cons_erase hzZ).symm
    let h : ℂ → ℂ := fun w ↦ (Z'.map (fun ρ ↦ w - ρ)).prod * g w
    have hfh : f = fun w ↦ (w - z) * h w := by
      funext w; rw [hfac w, hcons, Multiset.map_cons, Multiset.prod_cons, mul_assoc]
    have hhz : h z ≠ 0 :=
      mul_ne_zero (multiset_prod_sub_ne_zero fun ρ hρ heq ↦ hnot (heq ▸ hρ))
        (hgK z (mem_closedBall_zero_iff.mpr hz))
    have hhd : DifferentiableAt ℂ h z :=
      ((differentiable_multiset_prod_sub Z').mul hg) z
    have hd : deriv f z = h z := by
      rw [hfh, deriv_fun_mul (differentiableAt_fun_id.sub_const z) hhd, deriv_sub_const, deriv_id'']
      simp
    rw [hderiv z, hz1] at hd
    exact hhz hd.symm
  · have hld : deriv (LFunction χ) σ / LFunction χ σ = logDeriv f 0 := by
      rw [logDeriv_apply, hderiv 0]; simp [f]
    rw [hld]
    convert hmain using 2
    · ring
    · simp only [zeroTerm]
      congr 1
      refine Multiset.map_congr rfl fun ρ _ ↦ ?_
      norm_num

end Main
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

lemma multiset_sum_le_of_nonpos {Z : Multiset ℂ} {t : ℂ → ℝ} (ht : ∀ ρ ∈ Z, t ρ ≤ 0) :
    (Z.map t).sum ≤ 0 := by
  induction Z using Multiset.induction with
  | empty => simp
  | cons ρ Z ih =>
    rw [Multiset.map_cons, Multiset.sum_cons]
    have h1 := ht ρ (Multiset.mem_cons_self _ _)
    have h2 := ih fun ρ' h ↦ ht ρ' (Multiset.mem_cons_of_mem h)
    linarith

lemma multiset_sum_le_one_term {Z : Multiset ℂ} {t : ℂ → ℝ} (ht : ∀ ρ ∈ Z, t ρ ≤ 0) {ρ₁ : ℂ}
    (h1 : ρ₁ ∈ Z) : (Z.map t).sum ≤ t ρ₁ := by
  rw [← Multiset.cons_erase h1, Multiset.map_cons, Multiset.sum_cons]
  have := multiset_sum_le_of_nonpos (Z := Z.erase ρ₁) (t := t)
    fun ρ hρ ↦ ht ρ (Multiset.mem_of_mem_erase hρ)
  linarith

lemma multiset_sum_le_two_terms {Z : Multiset ℂ} {t : ℂ → ℝ} (ht : ∀ ρ ∈ Z, t ρ ≤ 0) {ρ₁ ρ₂ : ℂ}
    (h1 : ρ₁ ∈ Z) (h2 : ρ₂ ∈ Z.erase ρ₁) : (Z.map t).sum ≤ t ρ₁ + t ρ₂ := by
  rw [← Multiset.cons_erase h1, Multiset.map_cons, Multiset.sum_cons]
  have := multiset_sum_le_one_term (Z := Z.erase ρ₁) (t := t)
    (fun ρ hρ ↦ ht ρ (Multiset.mem_of_mem_erase hρ)) h2
  linarith

end LandauSiegel
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

end P2M_LFunctionLogDeriv
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

section P2M_MangoldtPositivity

open scoped LSeries.notation
p2m_open "Complex Filter Topology Set LSeries P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LSeries DirichletCharacter P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.DirichletCharacter"
open ArithmeticFunction (vonMangoldt)

local notation "Λ" => vonMangoldt

namespace LandauSiegel

variable {q : ℕ}

lemma re_three_four_one_nonneg {z : ℂ} (hz : z = 0 ∨ ‖z‖ = 1) : 0 ≤ (3 + 4 * z + z ^ 2).re := by
  rcases hz with rfl | h
  · simp
  · have h2 : z.re ^ 2 + z.im ^ 2 = 1 := by
      have := Complex.sq_norm_sub_sq_re z
      rw [h] at this; linarith
    have : (3 + 4 * z + z ^ 2).re = 2 * (1 + z.re) ^ 2 := by
      simp only [add_re, mul_re, sq, re_ofNat, im_ofNat]
      nlinarith
    rw [this]; positivity

lemma apply_eq_zero_or_norm_eq_one (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    χ a = 0 ∨ ‖χ a‖ = 1 := by
  by_cases ha : IsUnit a
  · exact .inr (χ.unit_norm_eq_one ha.unit)
  · exact .inl (MulChar.map_nonunit χ ha)

lemma re_term_mul_vonMangoldt (f : ℕ → ℂ) (σ : ℝ) (n : ℕ) :
    (term (fun n ↦ f n * Λ n) σ n).re
      = (if n = 0 then 0 else Λ n * ((n:ℝ) ^ σ)⁻¹) * (f n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [term_of_ne_zero hn, hn, ↓reduceIte]
    rw [show (n:ℂ) ^ (σ:ℂ) = (((n:ℝ) ^ σ : ℝ) : ℂ) by rw [ofReal_cpow (Nat.cast_nonneg n)]; norm_cast,
      div_eq_mul_inv, ← ofReal_inv, mul_comm (f n), mul_assoc, mul_comm (f n), ← mul_assoc,
      ← ofReal_mul, re_ofReal_mul]

lemma vonMangoldt_weight_nonneg (σ : ℝ) (n : ℕ) :
    0 ≤ (if n = 0 then 0 else Λ n * ((n:ℝ) ^ σ)⁻¹) := by
  split_ifs
  · exact le_rfl
  · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (inv_nonneg.mpr (by positivity))

lemma re_LSeries_mul_vonMangoldt_nonneg {F : ℕ → ℂ} {σ : ℝ} (hF : ∀ n, 0 ≤ (F n).re)
    (hs : LSeriesSummable (fun n ↦ F n * Λ n) σ) :
    0 ≤ (LSeries (fun n ↦ F n * Λ n) σ).re := by
  rw [LSeries, Complex.re_tsum hs]
  refine tsum_nonneg fun n ↦ ?_
  rw [re_term_mul_vonMangoldt]
  exact mul_nonneg (vonMangoldt_weight_nonneg σ n) (hF n)

section ThreeFourOne

variable (χ : DirichletCharacter ℂ q)

theorem re_three_four_one_LSeries_nonneg {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ (3 * LSeries ↗Λ σ + 4 * LSeries (↗χ * ↗Λ) σ + LSeries (↗(χ ^ 2 :) * ↗Λ) σ).re := by
  have hσ' : 1 < (σ:ℂ).re := by simpa using hσ
  have h0 : LSeriesSummable ↗Λ σ := ArithmeticFunction.LSeriesSummable_vonMangoldt hσ'
  have h1 : LSeriesSummable (↗χ * ↗Λ) σ := LSeriesSummable_twist_vonMangoldt χ hσ'
  have h2 : LSeriesSummable (↗(χ ^ 2 :) * ↗Λ) σ := LSeriesSummable_twist_vonMangoldt _ hσ'

  set F : ℕ → ℂ := fun n ↦ 3 + 4 * χ n + (χ n) ^ 2 with hF
  have hsum : 3 * LSeries ↗Λ σ + 4 * LSeries (↗χ * ↗Λ) σ + LSeries (↗(χ ^ 2 :) * ↗Λ) σ
      = LSeries (fun n ↦ F n * Λ n) σ := by
    have hfun : (((3:ℂ) • ↗Λ + (4:ℂ) • (↗χ * ↗Λ) + ↗(χ ^ 2 :) * ↗Λ : ℕ → ℂ))
        = fun n ↦ F n * Λ n := by
      ext n
      simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, hF,
        MulChar.pow_apply' χ two_ne_zero]
      ring
    rw [← LSeries_smul, ← LSeries_smul, ← LSeries_add (h0.smul (3:ℂ)) (h1.smul (4:ℂ)),
      ← LSeries_add ((h0.smul (3:ℂ)).add (h1.smul (4:ℂ))) h2, hfun]
  rw [hsum]
  refine re_LSeries_mul_vonMangoldt_nonneg (fun n ↦ re_three_four_one_nonneg
    (apply_eq_zero_or_norm_eq_one χ n)) ?_
  rw [← show (((3:ℂ) • ↗Λ + (4:ℂ) • (↗χ * ↗Λ) + ↗(χ ^ 2 :) * ↗Λ : ℕ → ℂ)) = fun n ↦ F n * Λ n by
    ext n
    simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, hF, MulChar.pow_apply' χ two_ne_zero]
    ring]
  exact ((h0.smul (3:ℂ)).add (h1.smul (4:ℂ))).add h2

end ThreeFourOne
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

section TwoReal

variable (χ₁ χ₂ : DirichletCharacter ℂ q)

theorem re_two_real_LSeries_nonneg (h₁ : χ₁ ^ 2 = 1) (h₂ : χ₂ ^ 2 = 1) {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ (LSeries ↗Λ σ + LSeries (↗χ₁ * ↗Λ) σ + LSeries (↗χ₂ * ↗Λ) σ
      + LSeries (↗(χ₁ * χ₂) * ↗Λ) σ).re := by
  have hσ' : 1 < (σ:ℂ).re := by simpa using hσ
  have h0 : LSeriesSummable ↗Λ σ := ArithmeticFunction.LSeriesSummable_vonMangoldt hσ'
  have hs1 : LSeriesSummable (↗χ₁ * ↗Λ) σ := LSeriesSummable_twist_vonMangoldt χ₁ hσ'
  have hs2 : LSeriesSummable (↗χ₂ * ↗Λ) σ := LSeriesSummable_twist_vonMangoldt χ₂ hσ'
  have hs3 : LSeriesSummable (↗(χ₁ * χ₂) * ↗Λ) σ := LSeriesSummable_twist_vonMangoldt _ hσ'
  set F : ℕ → ℂ := fun n ↦ (1 + χ₁ n) * (1 + χ₂ n) with hF
  have hfun : (↗Λ + ↗χ₁ * ↗Λ + ↗χ₂ * ↗Λ + ↗(χ₁ * χ₂) * ↗Λ : ℕ → ℂ) = fun n ↦ F n * Λ n := by
    ext n
    simp only [Pi.add_apply, Pi.mul_apply, hF, MulChar.mul_apply]
    ring
  have hsum : LSeries ↗Λ σ + LSeries (↗χ₁ * ↗Λ) σ + LSeries (↗χ₂ * ↗Λ) σ
      + LSeries (↗(χ₁ * χ₂) * ↗Λ) σ = LSeries (fun n ↦ F n * Λ n) σ := by
    rw [← LSeries_add h0 hs1, ← LSeries_add (h0.add hs1) hs2, ← LSeries_add ((h0.add hs1).add hs2) hs3,
      hfun]
  rw [hsum]
  refine re_LSeries_mul_vonMangoldt_nonneg (fun n ↦ ?_) (hfun ▸ ((h0.add hs1).add hs2).add hs3)
  simp only [hF]
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr h₁ (n : ZMod q) with h | h | h <;>
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr h₂ (n : ZMod q) with h' | h' | h' <;>
    simp [h, h']

end TwoReal
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

theorem re_one_real_LSeries_nonneg (χ : DirichletCharacter ℂ q) (h : χ ^ 2 = 1) {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ (LSeries ↗Λ σ + LSeries (↗χ * ↗Λ) σ).re := by
  have hσ' : 1 < (σ:ℂ).re := by simpa using hσ
  have h0 : LSeriesSummable ↗Λ σ := ArithmeticFunction.LSeriesSummable_vonMangoldt hσ'
  have hs1 : LSeriesSummable (↗χ * ↗Λ) σ := LSeriesSummable_twist_vonMangoldt χ hσ'
  set F : ℕ → ℂ := fun n ↦ 1 + χ n with hF
  have hfun : (↗Λ + ↗χ * ↗Λ : ℕ → ℂ) = fun n ↦ F n * Λ n := by
    ext n; simp only [Pi.add_apply, Pi.mul_apply, hF]; ring
  rw [← LSeries_add h0 hs1, hfun]
  refine re_LSeries_mul_vonMangoldt_nonneg (fun n ↦ ?_) (hfun ▸ h0.add hs1)
  simp only [hF]
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr h (n : ZMod q) with h' | h' | h' <;> simp [h']

lemma LSeries_twist_vonMangoldt_eq_LFunction [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (↗χ * ↗Λ) s = -deriv (LFunction χ) s / LFunction χ s := by
  rw [LSeries_twist_vonMangoldt_eq χ hs, LFunction_eq_LSeries χ hs]
  congr 2
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hs] with z hz
  exact (LFunction_eq_LSeries χ hz).symm

end LandauSiegel
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

end P2M_MangoldtPositivity
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

section P2M_PageAux

open scoped ComplexOrder
p2m_open "Complex Filter Topology Set Metric DirichletCharacter P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.DirichletCharacter"

namespace LandauSiegel

lemma exists_zeta_near_one_bounds : ∃ A : ℝ, 0 ≤ A ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
    ‖riemannZeta σ - 1 / ((σ:ℂ) - 1)‖ ≤ A ∧ ‖deriv riemannZeta σ + 1 / ((σ:ℂ) - 1) ^ 2‖ ≤ A := by
  obtain ⟨A₀, hA₀⟩ := (isCompact_Icc (a := (1:ℝ)) (b := 2)).exists_bound_of_continuousOn
    ((differentiable_zeta0.continuous.comp continuous_ofReal).continuousOn)
  obtain ⟨A₁, hA₁⟩ := (isCompact_Icc (a := (1:ℝ)) (b := 2)).exists_bound_of_continuousOn
    (((differentiable_zeta0.contDiff (n := 1)).continuous_deriv le_rfl |>.comp
      continuous_ofReal).continuousOn)
  refine ⟨max (max A₀ A₁) 0, le_max_right _ _, fun σ h1 h2 ↦ ?_⟩
  have hσ1 : (σ:ℂ) ≠ 1 := by
    intro h; apply_fun Complex.re at h; simp at h; linarith
  have e0 := zeta0_apply_of_ne_one hσ1
  have b0 := hA₀ σ ⟨h1.le, h2⟩
  have b1 := hA₁ σ ⟨h1.le, h2⟩
  simp only [Function.comp_apply] at b0 b1
  constructor
  · rw [← e0]; exact b0.trans ((le_max_left _ _).trans (le_max_left _ _))
  ·
    have hloc : riemannZeta =ᶠ[𝓝 (σ:ℂ)] fun s ↦ zeta0 s + 1 / (s - 1) := by
      filter_upwards [eventually_ne_nhds hσ1] with s hs
      rw [zeta0_apply_of_ne_one hs]; ring
    have hd : deriv riemannZeta σ = deriv zeta0 σ + deriv (fun s : ℂ ↦ 1 / (s - 1)) σ := by
      rw [hloc.deriv_eq, deriv_fun_add (differentiable_zeta0 σ)]
      exact DifferentiableAt.div (differentiableAt_const _) (differentiableAt_fun_id.sub_const 1)
        (sub_ne_zero.mpr hσ1)
    have hd2 : deriv (fun s : ℂ ↦ 1 / (s - 1)) σ = -(1 / ((σ:ℂ) - 1) ^ 2) := by
      have := (hasDerivAt_id (σ:ℂ)).sub_const 1 |>.inv (sub_ne_zero.mpr hσ1)
      have h' : (fun s : ℂ ↦ 1 / (s - 1)) = (fun x ↦ id x - 1)⁻¹ := by ext; simp [one_div]
      rw [h', this.deriv]
      simp only [id_eq]
      field_simp
    rw [hd, hd2, neg_add_cancel_right]
    exact b1.trans ((le_max_right _ _).trans (le_max_left _ _))

lemma exists_neg_re_logDeriv_zeta_le : ∃ A₁ δ₀ : ℝ, 0 ≤ A₁ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
    ∀ σ : ℝ, 1 < σ → σ - 1 ≤ δ₀ →
      (-(deriv riemannZeta σ / riemannZeta σ)).re ≤ 1 / (σ - 1) + A₁ := by
  obtain ⟨A, hA0, hA⟩ := exists_zeta_near_one_bounds
  refine ⟨4 * A + 1, min 1 (1 / (2 * A + 2)), by positivity, by positivity, min_le_left _ _,
    fun σ h1 hδ ↦ ?_⟩
  set u := σ - 1 with hu
  have hu0 : 0 < u := by linarith
  have hu1 : u ≤ 1 := hδ.trans (min_le_left _ _)
  have hAu : A * u ≤ 1/2 := by
    have : u ≤ 1 / (2 * A + 2) := hδ.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    nlinarith
  obtain ⟨hz, hz'⟩ := hA σ h1 (by linarith)
  have hσ1 : (σ:ℂ) - 1 = ((u:ℝ):ℂ) := by rw [hu]; push_cast; ring
  rw [hσ1, ← ofReal_one, ← ofReal_div] at hz
  rw [hσ1, ← ofReal_pow, ← ofReal_one, ← ofReal_div] at hz'

  have hζpos := riemannZeta_ofReal_pos h1
  obtain ⟨hζre, hζim⟩ := Complex.pos_iff.mp hζpos
  have hζre_lb : 1 / u - A ≤ (riemannZeta σ).re := by
    have := (abs_re_le_norm _).trans hz
    rw [sub_re, ofReal_re] at this
    have := neg_le_of_abs_le this
    linarith
  have hζ're : -(deriv riemannZeta σ).re ≤ 1 / u ^ 2 + A := by
    have := (abs_re_le_norm _).trans hz'
    rw [add_re, ofReal_re] at this
    have := (abs_le.mp this).1
    linarith

  have hreal : riemannZeta σ = ((riemannZeta σ).re : ℂ) :=
    Complex.ext (by simp) (by simp [← hζim])
  rw [neg_re, hreal, Complex.div_ofReal_re]
  have hlb : 1 / (2 * u) ≤ (riemannZeta ↑σ).re := by
    calc 1 / (2 * u) = 1 / u - 1 / (2 * u) := by field_simp; ring
      _ ≤ 1 / u - A := by
          gcongr
          rw [le_div_iff₀ (by positivity)]; linarith
      _ ≤ _ := hζre_lb
  have hpos : 0 < (riemannZeta ↑σ).re := lt_of_lt_of_le (by positivity) hlb
  rw [← neg_div, div_le_iff₀ hpos]
  set v := 1 / u with hv
  have hv1 : 1 ≤ v := by rw [hv, le_div_iff₀ hu0]; linarith
  have hAv : A ≤ v / 2 := by
    rw [hv]; rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2), div_eq_mul_inv, mul_comm, ← div_eq_mul_inv,
      le_div_iff₀ hu0]; linarith
  have e1 : 4 * A ^ 2 ≤ 2 * A * v := by nlinarith
  have e2 : 2 * A ≤ A * v + v := by
    rcases le_or_gt 2 v with h | h
    · nlinarith
    · nlinarith
  have key : 1 / u ^ 2 + A ≤ (1 / u + (4 * A + 1)) * (1 / u - A) := by
    rw [show 1 / u ^ 2 = v ^ 2 by rw [hv]; field_simp, show 1 / u = v from hv.symm]
    nlinarith
  calc -(deriv riemannZeta ↑σ).re ≤ 1 / u ^ 2 + A := hζ're
    _ ≤ (1 / u + (4 * A + 1)) * (1 / u - A) := key
    _ ≤ (1 / u + (4 * A + 1)) * (riemannZeta ↑σ).re := by
        refine mul_le_mul_of_nonneg_left hζre_lb ?_
        have : 0 < 1 / u := by positivity
        positivity

lemma log_inv_le_two_div_sqrt {d k : ℝ} (hd : 0 < d) (hk : 1 ≤ k) :
    Real.log (1 / (k * d)) ≤ 2 / Real.sqrt d := by
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  calc Real.log (1 / (k * d)) ≤ Real.log (1 / d) := by
        refine Real.log_le_log (by positivity) ?_
        rw [div_le_div_iff_of_pos_left one_pos (by positivity) hd]; nlinarith
    _ = 2 * Real.log (1 / Real.sqrt d) := by
        rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_sqrt hd.le]; ring
    _ ≤ 2 * (1 / Real.sqrt d - 1) := by
        gcongr; exact Real.log_le_sub_one_of_pos (by positivity)
    _ ≤ 2 / Real.sqrt d := by rw [mul_sub, mul_one_div]; linarith

lemma no_small_d {a b e K ℒ d c : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (he : 0 ≤ e) (hK : 0 ≤ K)
    (hℒ : 1 ≤ ℒ) (hd : 0 < d) (hdc : d * ℒ < c) (hc1 : c ≤ 1 / (2 * a * e + 1) ^ 2)
    (hc2 : c ≤ 1 / (2 * a * (b + K) + 1))
    (hineq : 1 / (a * d) ≤ b * ℒ + e / Real.sqrt d + K) : False := by
  have hdc' : d < c := by nlinarith
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd

  have h1 : b * ℒ + K < 1 / (2 * a * d) := by
    have hpos : 0 < 2 * a * (b + K) + 1 := by positivity
    have : d * ℒ < 1 / (2 * a * (b + K) + 1) := hdc.trans_le hc2
    rw [lt_div_iff₀ hpos] at this
    rw [lt_div_iff₀ (by positivity)]
    have hKℒ : K ≤ K * ℒ := le_mul_of_one_le_right hK hℒ
    calc (b * ℒ + K) * (2 * a * d) ≤ (b * ℒ + K * ℒ) * (2 * a * d) := by gcongr
      _ = d * ℒ * (2 * a * (b + K)) := by ring
      _ < 1 := by nlinarith

  have h2 : e / Real.sqrt d ≤ 1 / (2 * a * d) := by
    have hd' : d ≤ 1 / (2 * a * e + 1) ^ 2 := hdc'.le.trans hc1
    have hsq : Real.sqrt d ≤ 1 / (2 * a * e + 1) := by
      rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ 1 / (2 * a * e + 1)), one_div_pow]
      exact Real.sqrt_le_sqrt hd'
    rw [div_le_div_iff₀ hsd (by positivity)]
    have hds : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hd.le
    have : e * (2 * a) * Real.sqrt d ≤ 1 := by
      have h3 : Real.sqrt d * (2 * a * e + 1) ≤ 1 := by
        rwa [le_div_iff₀ (by positivity)] at hsq
      nlinarith
    have h4 := mul_le_mul_of_nonneg_right this hsd.le
    nlinarith
  have : 1 / (a * d) = 1 / (2 * a * d) + 1 / (2 * a * d) := by field_simp; ring
  linarith

theorem master : ∃ K δ₀ : ℝ, 0 ≤ K ∧ 0 < δ₀ ∧ δ₀ ≤ 1/12 ∧
    ∀ (σ : ℝ), 1 < σ → σ - 1 ≤ δ₀ →
      (-(deriv riemannZeta σ / riemannZeta σ)).re ≤ 1 / (σ - 1) + K ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
        ∃ Z : Multiset ℂ,
          (∀ ρ ∈ Z, ‖ρ‖ ≤ 1/4 ∧ LFunction χ (σ + ρ) = 0 ∧ ρ.re < 0) ∧
          (∀ z : ℂ, ‖z‖ ≤ 1/4 → LFunction χ (σ + z) = 0 → z ∈ Z) ∧
          (∀ z : ℂ, ‖z‖ ≤ 1/4 → LFunction χ (σ + z) = 0 → deriv (LFunction χ) (σ + z) = 0 →
            z ∈ Z.erase z) ∧
          (∀ ρ ∈ Z, zeroTerm ρ ≤ 0) ∧
          -(deriv (LFunction χ) σ / LFunction χ σ).re
            ≤ 16 * (Real.log q + 1) + 16 * Real.log (1 / (σ - 1)) + K + (Z.map zeroTerm).sum := by
  obtain ⟨A₁, δ₁, hA₁, hδ₁, hδ₁1, hζ'⟩ := exists_neg_re_logDeriv_zeta_le
  obtain ⟨A, hA, hζ⟩ := exists_riemannZeta_le
  set K := max A₁ (16 * (Real.log 4 + Real.log (1 + A) + 1)) with hK
  refine ⟨K, min δ₁ (1/12), le_max_of_le_left hA₁, by positivity, min_le_right _ _,
    fun σ h1 hδ ↦ ⟨?_, fun q _ χ hχ ↦ ?_⟩⟩
  · exact (hζ' σ h1 (hδ.trans (min_le_left _ _))).trans (by gcongr; exact le_max_left _ _)
  · have hσ2 : σ ≤ 3/2 := by linarith [hδ.trans (min_le_right δ₁ (1/12))]
    obtain ⟨Z, hZ1, hZ2, hZ3, hbound⟩ := neg_re_logDeriv_LFunction_le χ hχ h1 hσ2
    refine ⟨Z, hZ1, hZ2, hZ3, fun ρ hρ ↦ zeroTerm_nonpos (hZ1 ρ hρ).1 (hZ1 ρ hρ).2.2.le, ?_⟩
    refine hbound.trans ?_
    have hu : 0 < σ - 1 := by linarith
    have hu1 : σ - 1 ≤ 1 := by linarith
    have hq : (1:ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hζb := hζ σ h1 (by linarith)
    have hζpos : 0 < ‖riemannZeta σ‖ := norm_pos_iff.mpr (riemannZeta_ofReal_pos h1).ne'
    have hζb' : ‖riemannZeta σ‖ ≤ (1 + A) * (1 / (σ - 1)) := by
      calc ‖riemannZeta σ‖ ≤ 1 / (σ - 1) + A := hζb
        _ ≤ 1 / (σ - 1) + A * (1 / (σ - 1)) := by
            gcongr
            have : 1 ≤ 1 / (σ - 1) := by rw [le_div_iff₀ hu]; linarith
            nlinarith
        _ = (1 + A) * (1 / (σ - 1)) := by ring
    have hlog : Real.log (4 * q * ‖riemannZeta σ‖)
        ≤ Real.log 4 + Real.log q + Real.log (1 + A) + Real.log (1 / (σ - 1)) := by
      rw [← Real.log_mul (by norm_num) (by positivity), ← Real.log_mul (by positivity) (by positivity),
        ← Real.log_mul (by positivity) (by positivity)]
      exact Real.log_le_log (by positivity) (by nlinarith)
    have : 16 * (Real.log 4 + Real.log (1 + A) + 1) ≤ K := le_max_right _ _
    nlinarith [hlog]

end LandauSiegel
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

end P2M_PageAux
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

section P2M_Page

open scoped ComplexOrder LSeries.notation
p2m_open "Complex Filter Topology Set Metric DirichletCharacter P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.DirichletCharacter"
open ArithmeticFunction (vonMangoldt)

local notation "Λ" => vonMangoldt

namespace LandauSiegel

lemma re_neg_logDeriv_zeta_eq {σ : ℝ} (hσ : 1 < σ) :
    (LSeries ↗Λ σ).re = (-(deriv riemannZeta σ / riemannZeta σ)).re := by
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hσ), neg_div]

lemma re_neg_logDeriv_LFunction_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ : ℝ}
    (hσ : 1 < σ) :
    (LSeries (↗χ * ↗Λ) σ).re = -(deriv (LFunction χ) σ / LFunction χ σ).re := by
  rw [LSeries_twist_vonMangoldt_eq_LFunction χ (by simpa using hσ), neg_div, neg_re]

lemma zeroTerm_of_real_zero {σ β : ℝ} (h : β < σ) (h4 : σ - β ≤ 1/4) :
    ‖((β - σ : ℝ) : ℂ)‖ ≤ 1/4 ∧ zeroTerm ((β - σ : ℝ) : ℂ) ≤ -1 / (σ - β) + 1 := by
  constructor
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_pos (by linarith)]; exact h4
  · have := zeroTerm_real_le (d := σ - β) (by linarith) h4
    rwa [show -(σ - β) = β - σ by ring] at this

theorem page_complex : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ ^ 2 ≠ 1 → ∀ β : ℝ, LFunction χ β = 0 → β ≤ 1 - c / (Real.log q + 1) := by
  obtain ⟨K, δ₀, hK, hδ₀, hδ₀', M⟩ := master

  set c : ℝ := min (δ₀ / 7) (min (1 / (2 * 14 * 160 + 1) ^ 2) (1 / (2 * 14 * (80 + (8 * K + 4)) + 1)))
    with hc
  have hc0 : 0 < c := by positivity
  refine ⟨c, hc0, fun q _ χ hχ2 β hβ ↦ ?_⟩
  have hχ : χ ≠ 1 := fun h ↦ hχ2 (by rw [h, one_pow])
  set ℒ := Real.log q + 1 with hℒ
  have hℒ1 : 1 ≤ ℒ := by have := Real.log_natCast_nonneg q; linarith
  by_contra hcon
  push Not at hcon

  have hβ1 : β < 1 := by
    by_contra h; push Not at h
    exact LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by simpa using h) hβ
  set d := 1 - β with hd
  have hd0 : 0 < d := by linarith
  have hdℒ : d * ℒ < c := by
    have : c / ℒ > 1 - β := by linarith
    rwa [gt_iff_lt, lt_div_iff₀ (by linarith)] at this
  have hdc : d < c := by nlinarith
  have hd7 : 7 * d ≤ δ₀ := by
    have : c ≤ δ₀ / 7 := min_le_left _ _
    linarith

  set σ := 1 + 6 * d with hσdef
  have hσ1 : 1 < σ := by linarith
  have hσδ : σ - 1 ≤ δ₀ := by linarith
  obtain ⟨hZ0, ML⟩ := M σ hσ1 hσδ
  obtain ⟨Z₁, hZ₁a, hZ₁b, -, hZ₁neg, hB₁⟩ := ML q χ hχ
  obtain ⟨Z₂, -, -, -, hZ₂neg, hB₂⟩ := ML q (χ ^ 2) hχ2

  obtain ⟨hnorm, hterm⟩ := zeroTerm_of_real_zero (σ := σ) (β := β) (by linarith) (by linarith)
  have hmem : ((β - σ : ℝ) : ℂ) ∈ Z₁ := hZ₁b _ hnorm (by push_cast; ring_nf; ring_nf at hβ; simpa using hβ)
  have hS₁ : (Z₁.map zeroTerm).sum ≤ -1 / (σ - β) + 1 :=
    (multiset_sum_le_one_term hZ₁neg hmem).trans hterm
  have hS₂ : (Z₂.map zeroTerm).sum ≤ 0 := multiset_sum_le_of_nonpos hZ₂neg

  have hpos := re_three_four_one_LSeries_nonneg χ hσ1
  simp only [add_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero] at hpos
  rw [re_neg_logDeriv_zeta_eq hσ1, re_neg_logDeriv_LFunction_eq χ hσ1,
    re_neg_logDeriv_LFunction_eq (χ ^ 2) hσ1] at hpos

  have hσβ : σ - β = 7 * d := by rw [hσdef, hd]; ring
  have hu : σ - 1 = 6 * d := by rw [hσdef]; ring
  rw [hσβ] at hS₁
  rw [hu] at hZ0 hB₁ hB₂
  have hlog : Real.log (1 / (6 * d)) ≤ 2 / Real.sqrt d := log_inv_le_two_div_sqrt hd0 (by norm_num)
  have hineq : 1 / (14 * d) ≤ 80 * ℒ + 160 / Real.sqrt d + (8 * K + 4) := by
    have e1 : 4 * (1 / (7 * d)) - 3 * (1 / (6 * d)) = 1 / (14 * d) := by field_simp; ring
    have e2 : (160 : ℝ) / Real.sqrt d = 80 * (2 / Real.sqrt d) := by ring
    have e3 : (-1 : ℝ) / (7 * d) = -(1 / (7 * d)) := by ring
    linarith [hpos, hZ0, hB₁, hB₂, hS₁, hS₂, hlog, e1, e2, e3]
  exact no_small_d (a := 14) (b := 80) (e := 160) (K := 8 * K + 4) (by norm_num) (by norm_num)
    (by norm_num) (by positivity) hℒ1 hd0 hdℒ ((min_le_right _ _).trans (min_le_left _ _))
    ((min_le_right _ _).trans (min_le_right _ _)) hineq

theorem page_two_real : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q),
    χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → χ₁ ≠ 1 → χ₂ ≠ 1 → χ₁ ≠ χ₂ →
    ∀ β₁ β₂ : ℝ, LFunction χ₁ β₁ = 0 → LFunction χ₂ β₂ = 0 →
      min β₁ β₂ ≤ 1 - c / (Real.log q + 1) := by
  obtain ⟨K, δ₀, hK, hδ₀, hδ₀', M⟩ := master
  set c : ℝ := min (δ₀ / 3) (min (1 / (2 * 6 * 96 + 1) ^ 2) (1 / (2 * 6 * (48 + (4 * K + 2)) + 1)))
    with hc
  have hc0 : 0 < c := by positivity
  refine ⟨c, hc0, fun q _ χ₁ χ₂ h₁ h₂ h₁' h₂' hne β₁ β₂ hβ₁ hβ₂ ↦ ?_⟩
  have h₁₂ : χ₁ * χ₂ ≠ 1 := by
    intro h
    apply hne
    have e1 : χ₂ = χ₁⁻¹ := eq_inv_of_mul_eq_one_right h
    have e2 : χ₁⁻¹ = χ₁ := inv_eq_of_mul_eq_one_right (by rw [← sq, h₁])
    rw [e1, e2]
  set ℒ := Real.log q + 1 with hℒ
  have hℒ1 : 1 ≤ ℒ := by have := Real.log_natCast_nonneg q; linarith
  by_contra hcon
  push Not at hcon
  have hb₁ : 1 - c / ℒ < β₁ := hcon.trans_le (min_le_left _ _)
  have hb₂ : 1 - c / ℒ < β₂ := hcon.trans_le (min_le_right _ _)
  have hβ₁1 : β₁ < 1 := by
    by_contra h; push Not at h
    exact LFunction_ne_zero_of_one_le_re χ₁ (.inl h₁') (by simpa using h) hβ₁
  have hβ₂1 : β₂ < 1 := by
    by_contra h; push Not at h
    exact LFunction_ne_zero_of_one_le_re χ₂ (.inl h₂') (by simpa using h) hβ₂
  set d := 1 - min β₁ β₂ with hd
  have hd0 : 0 < d := by
    have := min_le_left β₁ β₂; linarith
  have hd₁ : 1 - β₁ ≤ d := by have := min_le_left β₁ β₂; linarith
  have hd₂ : 1 - β₂ ≤ d := by have := min_le_right β₁ β₂; linarith
  have hdℒ : d * ℒ < c := by
    have : c / ℒ > d := by rw [hd]; linarith
    rwa [gt_iff_lt, lt_div_iff₀ (by linarith)] at this
  have hdc : d < c := by nlinarith
  have hd3 : 3 * d ≤ δ₀ := by
    have : c ≤ δ₀ / 3 := min_le_left _ _
    linarith
  set σ := 1 + 2 * d with hσdef
  have hσ1 : 1 < σ := by linarith
  have hσδ : σ - 1 ≤ δ₀ := by linarith
  obtain ⟨hZ0, ML⟩ := M σ hσ1 hσδ
  obtain ⟨Z₁, -, hZ₁b, -, hZ₁neg, hB₁⟩ := ML q χ₁ h₁'
  obtain ⟨Z₂, -, hZ₂b, -, hZ₂neg, hB₂⟩ := ML q χ₂ h₂'
  obtain ⟨Z₃, -, -, -, hZ₃neg, hB₃⟩ := ML q (χ₁ * χ₂) h₁₂
  obtain ⟨hn₁, ht₁⟩ := zeroTerm_of_real_zero (σ := σ) (β := β₁) (by linarith) (by linarith)
  obtain ⟨hn₂, ht₂⟩ := zeroTerm_of_real_zero (σ := σ) (β := β₂) (by linarith) (by linarith)
  have hm₁ : ((β₁ - σ : ℝ) : ℂ) ∈ Z₁ := hZ₁b _ hn₁ (by push_cast; ring_nf; ring_nf at hβ₁; simpa using hβ₁)
  have hm₂ : ((β₂ - σ : ℝ) : ℂ) ∈ Z₂ := hZ₂b _ hn₂ (by push_cast; ring_nf; ring_nf at hβ₂; simpa using hβ₂)
  have hS₁ : (Z₁.map zeroTerm).sum ≤ -1 / (σ - β₁) + 1 := (multiset_sum_le_one_term hZ₁neg hm₁).trans ht₁
  have hS₂ : (Z₂.map zeroTerm).sum ≤ -1 / (σ - β₂) + 1 := (multiset_sum_le_one_term hZ₂neg hm₂).trans ht₂
  have hS₃ : (Z₃.map zeroTerm).sum ≤ 0 := multiset_sum_le_of_nonpos hZ₃neg
  have hpos := re_two_real_LSeries_nonneg χ₁ χ₂ h₁ h₂ hσ1
  simp only [add_re] at hpos
  rw [re_neg_logDeriv_zeta_eq hσ1, re_neg_logDeriv_LFunction_eq χ₁ hσ1,
    re_neg_logDeriv_LFunction_eq χ₂ hσ1, re_neg_logDeriv_LFunction_eq (χ₁ * χ₂) hσ1] at hpos
  have hu : σ - 1 = 2 * d := by rw [hσdef]; ring
  rw [hu] at hZ0 hB₁ hB₂ hB₃

  have hf₁ : -1 / (σ - β₁) ≤ -(1 / (3 * d)) := by
    rw [neg_div, neg_le_neg_iff]; exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hf₂ : -1 / (σ - β₂) ≤ -(1 / (3 * d)) := by
    rw [neg_div, neg_le_neg_iff]; exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hlog : Real.log (1 / (2 * d)) ≤ 2 / Real.sqrt d := log_inv_le_two_div_sqrt hd0 (by norm_num)
  have hineq : 1 / (6 * d) ≤ 48 * ℒ + 96 / Real.sqrt d + (4 * K + 2) := by
    have e1 : 2 * (1 / (3 * d)) - 1 / (2 * d) = 1 / (6 * d) := by field_simp; ring
    have e2 : (96 : ℝ) / Real.sqrt d = 48 * (2 / Real.sqrt d) := by ring
    linarith [hpos, hZ0, hB₁, hB₂, hB₃, hS₁, hS₂, hS₃, hlog, e1, e2, hf₁, hf₂]
  exact no_small_d (a := 6) (b := 48) (e := 96) (K := 4 * K + 2) (by norm_num) (by norm_num)
    (by norm_num) (by positivity) hℒ1 hd0 hdℒ ((min_le_right _ _).trans (min_le_left _ _))
    ((min_le_right _ _).trans (min_le_right _ _)) hineq

theorem page_two_zeros : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ ^ 2 = 1 → χ ≠ 1 → ∀ β₁ β₂ : ℝ, β₁ < β₂ → LFunction χ β₁ = 0 → LFunction χ β₂ = 0 →
      β₁ ≤ 1 - c / (Real.log q + 1) := by
  obtain ⟨K, δ₀, hK, hδ₀, hδ₀', M⟩ := master
  set c : ℝ := min (δ₀ / 3) (min (1 / (2 * 6 * 32 + 1) ^ 2) (1 / (2 * 6 * (16 + (2 * K + 2)) + 1)))
    with hc
  have hc0 : 0 < c := by positivity
  refine ⟨c, hc0, fun q _ χ h h' β₁ β₂ hlt hβ₁ hβ₂ ↦ ?_⟩
  set ℒ := Real.log q + 1 with hℒ
  have hℒ1 : 1 ≤ ℒ := by have := Real.log_natCast_nonneg q; linarith
  by_contra hcon
  push Not at hcon
  have hβ₂1 : β₂ < 1 := by
    by_contra hh; push Not at hh
    exact LFunction_ne_zero_of_one_le_re χ (.inl h') (by simpa using hh) hβ₂
  set d := 1 - β₁ with hd
  have hd0 : 0 < d := by linarith
  have hdℒ : d * ℒ < c := by
    have : c / ℒ > d := by rw [hd]; linarith
    rwa [gt_iff_lt, lt_div_iff₀ (by linarith)] at this
  have hdc : d < c := by nlinarith
  have hd3 : 3 * d ≤ δ₀ := by
    have : c ≤ δ₀ / 3 := min_le_left _ _
    linarith
  set σ := 1 + 2 * d with hσdef
  have hσ1 : 1 < σ := by linarith
  have hσδ : σ - 1 ≤ δ₀ := by linarith
  obtain ⟨hZ0, ML⟩ := M σ hσ1 hσδ
  obtain ⟨Z, -, hZb, -, hZneg, hB⟩ := ML q χ h'
  obtain ⟨hn₁, ht₁⟩ := zeroTerm_of_real_zero (σ := σ) (β := β₁) (by linarith) (by linarith)
  obtain ⟨hn₂, ht₂⟩ := zeroTerm_of_real_zero (σ := σ) (β := β₂) (by linarith) (by linarith)
  have hm₁ : ((β₁ - σ : ℝ) : ℂ) ∈ Z := hZb _ hn₁ (by push_cast; ring_nf; ring_nf at hβ₁; simpa using hβ₁)
  have hm₂ : ((β₂ - σ : ℝ) : ℂ) ∈ Z := hZb _ hn₂ (by push_cast; ring_nf; ring_nf at hβ₂; simpa using hβ₂)
  have hne : ((β₂ - σ : ℝ) : ℂ) ≠ ((β₁ - σ : ℝ) : ℂ) := by
    intro he; have := ofReal_injective he; linarith
  have hm₂' : ((β₂ - σ : ℝ) : ℂ) ∈ Z.erase ((β₁ - σ : ℝ) : ℂ) := (Multiset.mem_erase_of_ne hne).mpr hm₂
  have hS : (Z.map zeroTerm).sum ≤ (-1 / (σ - β₁) + 1) + (-1 / (σ - β₂) + 1) :=
    (multiset_sum_le_two_terms hZneg hm₁ hm₂').trans (add_le_add ht₁ ht₂)
  have hpos := re_one_real_LSeries_nonneg χ h hσ1
  simp only [add_re] at hpos
  rw [re_neg_logDeriv_zeta_eq hσ1, re_neg_logDeriv_LFunction_eq χ hσ1] at hpos
  have hu : σ - 1 = 2 * d := by rw [hσdef]; ring
  rw [hu] at hZ0 hB
  have hf₁ : -1 / (σ - β₁) ≤ -(1 / (3 * d)) := by
    rw [neg_div, neg_le_neg_iff]; exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hf₂ : -1 / (σ - β₂) ≤ -(1 / (3 * d)) := by
    rw [neg_div, neg_le_neg_iff]; exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have hlog : Real.log (1 / (2 * d)) ≤ 2 / Real.sqrt d := log_inv_le_two_div_sqrt hd0 (by norm_num)
  have hineq : 1 / (6 * d) ≤ 16 * ℒ + 32 / Real.sqrt d + (2 * K + 2) := by
    have e1 : 2 * (1 / (3 * d)) - 1 / (2 * d) = 1 / (6 * d) := by field_simp; ring
    have e2 : (32 : ℝ) / Real.sqrt d = 16 * (2 / Real.sqrt d) := by ring
    linarith [hpos, hZ0, hB, hS, hlog, e1, e2, hf₁, hf₂]
  exact no_small_d (a := 6) (b := 16) (e := 32) (K := 2 * K + 2) (by norm_num) (by norm_num)
    (by norm_num) (by positivity) hℒ1 hd0 hdℒ ((min_le_right _ _).trans (min_le_left _ _))
    ((min_le_right _ _).trans (min_le_right _ _)) hineq

theorem page_double_zero : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ ^ 2 = 1 → χ ≠ 1 → ∀ β : ℝ, LFunction χ β = 0 → deriv (LFunction χ) β = 0 →
      β ≤ 1 - c / (Real.log q + 1) := by
  obtain ⟨K, δ₀, hK, hδ₀, hδ₀', M⟩ := master
  set c : ℝ := min (δ₀ / 3) (min (1 / (2 * 6 * 32 + 1) ^ 2) (1 / (2 * 6 * (16 + (2 * K + 2)) + 1)))
    with hc
  have hc0 : 0 < c := by positivity
  refine ⟨c, hc0, fun q _ χ h h' β hβ hβ' ↦ ?_⟩
  set ℒ := Real.log q + 1 with hℒ
  have hℒ1 : 1 ≤ ℒ := by have := Real.log_natCast_nonneg q; linarith
  by_contra hcon
  push Not at hcon
  have hβ1 : β < 1 := by
    by_contra hh; push Not at hh
    exact LFunction_ne_zero_of_one_le_re χ (.inl h') (by simpa using hh) hβ
  set d := 1 - β with hd
  have hd0 : 0 < d := by linarith
  have hdℒ : d * ℒ < c := by
    have : c / ℒ > d := by rw [hd]; linarith
    rwa [gt_iff_lt, lt_div_iff₀ (by linarith)] at this
  have hdc : d < c := by nlinarith
  have hd3 : 3 * d ≤ δ₀ := by
    have : c ≤ δ₀ / 3 := min_le_left _ _
    linarith
  set σ := 1 + 2 * d with hσdef
  have hσ1 : 1 < σ := by linarith
  have hσδ : σ - 1 ≤ δ₀ := by linarith
  obtain ⟨hZ0, ML⟩ := M σ hσ1 hσδ
  obtain ⟨Z, -, hZb, hZc, hZneg, hB⟩ := ML q χ h'
  obtain ⟨hn, ht⟩ := zeroTerm_of_real_zero (σ := σ) (β := β) (by linarith) (by linarith)
  have hz0 : LFunction χ (σ + ((β - σ : ℝ) : ℂ)) = 0 := by
    push_cast; ring_nf; ring_nf at hβ; simpa using hβ
  have hz1 : deriv (LFunction χ) (σ + ((β - σ : ℝ) : ℂ)) = 0 := by
    push_cast; ring_nf; ring_nf at hβ'; simpa using hβ'
  have hm : ((β - σ : ℝ) : ℂ) ∈ Z := hZb _ hn hz0
  have hm' : ((β - σ : ℝ) : ℂ) ∈ Z.erase ((β - σ : ℝ) : ℂ) := hZc _ hn hz0 hz1
  have hS : (Z.map zeroTerm).sum ≤ (-1 / (σ - β) + 1) + (-1 / (σ - β) + 1) :=
    (multiset_sum_le_two_terms hZneg hm hm').trans (add_le_add ht ht)
  have hpos := re_one_real_LSeries_nonneg χ h hσ1
  simp only [add_re] at hpos
  rw [re_neg_logDeriv_zeta_eq hσ1, re_neg_logDeriv_LFunction_eq χ hσ1] at hpos
  have hu : σ - 1 = 2 * d := by rw [hσdef]; ring
  have hσβ : σ - β = 3 * d := by rw [hσdef, hd]; ring
  rw [hu] at hZ0 hB
  rw [hσβ] at hS
  have hlog : Real.log (1 / (2 * d)) ≤ 2 / Real.sqrt d := log_inv_le_two_div_sqrt hd0 (by norm_num)
  have hineq : 1 / (6 * d) ≤ 16 * ℒ + 32 / Real.sqrt d + (2 * K + 2) := by
    have e1 : 2 * (1 / (3 * d)) - 1 / (2 * d) = 1 / (6 * d) := by field_simp; ring
    have e2 : (32 : ℝ) / Real.sqrt d = 16 * (2 / Real.sqrt d) := by ring
    have e3 : (-1 : ℝ) / (3 * d) = -(1 / (3 * d)) := by ring
    linarith [hpos, hZ0, hB, hS, hlog, e1, e2, e3]
  exact no_small_d (a := 6) (b := 16) (e := 32) (K := 2 * K + 2) (by norm_num) (by norm_num)
    (by norm_num) (by positivity) hℒ1 hd0 hdℒ ((min_le_right _ _).trans (min_le_left _ _))
    ((min_le_right _ _).trans (min_le_right _ _)) hineq

theorem landau_page : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ₁ χ₂ : DirichletCharacter ℂ q)
    (β₁ β₂ : ℝ), χ₁ ≠ 1 → χ₂ ≠ 1 →
    1 - c / (Real.log q + 1) < β₁ → 1 - c / (Real.log q + 1) < β₂ →
    LFunction χ₁ β₁ = 0 → LFunction χ₂ β₂ = 0 →
      χ₁ = χ₂ ∧ β₁ = β₂ ∧ χ₁ ^ 2 = 1 ∧ deriv (LFunction χ₁) β₁ ≠ 0 := by
  obtain ⟨c₁, hc₁, H₁⟩ := page_complex
  obtain ⟨c₂, hc₂, H₂⟩ := page_two_real
  obtain ⟨c₃, hc₃, H₃⟩ := page_two_zeros
  obtain ⟨c₄, hc₄, H₄⟩ := page_double_zero
  set c := min (min c₁ c₂) (min c₃ c₄) with hc
  refine ⟨c, by positivity, fun q _ χ₁ χ₂ β₁ β₂ h₁ h₂ hb₁ hb₂ hz₁ hz₂ ↦ ?_⟩
  have hℒ : 0 < Real.log q + 1 := by have := Real.log_natCast_nonneg q; linarith
  have mono : ∀ {c' β : ℝ}, c ≤ c' → 1 - c / (Real.log q + 1) < β → ¬ β ≤ 1 - c' / (Real.log q + 1) := by
    intro c' β hcc' hβ hle
    have : c / (Real.log q + 1) ≤ c' / (Real.log q + 1) := by gcongr
    linarith
  have hcc₁ : c ≤ c₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hcc₂ : c ≤ c₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hcc₃ : c ≤ c₃ := (min_le_right _ _).trans (min_le_left _ _)
  have hcc₄ : c ≤ c₄ := (min_le_right _ _).trans (min_le_right _ _)

  have hr₁ : χ₁ ^ 2 = 1 := by
    by_contra h; exact mono hcc₁ hb₁ (H₁ q χ₁ h β₁ hz₁)
  have hr₂ : χ₂ ^ 2 = 1 := by
    by_contra h; exact mono hcc₁ hb₂ (H₁ q χ₂ h β₂ hz₂)

  have heq : χ₁ = χ₂ := by
    by_contra hne
    have := H₂ q χ₁ χ₂ hr₁ hr₂ h₁ h₂ hne β₁ β₂ hz₁ hz₂
    rcases le_total β₁ β₂ with h | h
    · rw [min_eq_left h] at this; exact mono hcc₂ hb₁ this
    · rw [min_eq_right h] at this; exact mono hcc₂ hb₂ this
  subst heq

  have hβ : β₁ = β₂ := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact mono hcc₃ hb₁ (H₃ q χ₁ hr₁ h₁ β₁ β₂ h hz₁ hz₂)
    · exact mono hcc₃ hb₂ (H₃ q χ₁ hr₁ h₁ β₂ β₁ h hz₂ hz₁)
  refine ⟨rfl, hβ, hr₁, fun hd ↦ mono hcc₄ hb₁ (H₄ q χ₁ hr₁ h₁ β₁ hz₁ hd)⟩

end LandauSiegel
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

end P2M_Page
p2m_reactivate "P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LandauSiegel"

open scoped ComplexOrder in
open Complex Set Metric _root_.LSeries _root_.P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball.LSeries in
theorem solution {a : ℕ → ℂ} (ha : 0 ≤ a) {x : ℝ}
    (hx : abscissaOfAbsConv a ≤ x) {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball (x:ℂ) r))
    (hfa : ∀ s ∈ ball (x:ℂ) r, x < s.re → f s = LSeries a s) :
    abscissaOfAbsConv a < x := LSeries.abscissaOfAbsConv_lt_of_differentiableOn_ball' ha hx hr hf hfa

end S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball
end P2MW
export P2MW.S_LSeries_abscissaOfAbsConv_lt_of_differentiableOn_ball (solution)
