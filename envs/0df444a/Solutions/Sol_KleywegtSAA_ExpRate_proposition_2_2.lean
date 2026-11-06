-- Prove2me | solution 1 for KleywegtSAA.ExpRate.proposition_2_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T01:55:23.746166+00:00
-- url     : https://prove2.me/submissions/3fb712c9-d1e5-4553-a2a7-998eb92888e3

import Mathlib
import Definitions.Def_KleywegtSAA_ExpRate_Setting
import Theorems.Thm_KleywegtSAA_ExpRate_union_bound
import Theorems.Thm_KleywegtSAA_ExpRate_alpha_pos
import Theorems.Thm_KleywegtSAA_ExpRate_deviation_le_two_exp

open MeasureTheory ProbabilityTheory Filter Topology
open KleywegtSAA.ExpRate

theorem solution
    {X : Type*} (S : Finset X) (hS : S.Nonempty)
    {𝒲 : Type*} [MeasurableSpace 𝒲] (G : X → 𝒲 → ℝ) (hG : ∀ x ∈ S, Measurable (G x))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℕ → Ω → 𝒲) (hWm : ∀ n, Measurable (W n)) (hind : iIndepFun W P)
    (hid : ∀ n, IdentDistrib (W n) (W 0) P P)
    (hint : ∀ x ∈ S, Integrable (fun ω => G x (W 0 ω)) P)
    (hA : AssumptionA S G P W) :
    ∀ ε : ℝ, 0 ≤ ε → ∃ γ : ℝ, 0 < γ ∧
      Filter.limsup (fun N : ℕ => ((1 / (N : ℝ) : ℝ) : EReal) *
          ENNReal.log (1 - P {ω | epsSet S hS (sampleObj G W N ω) ε ⊆
            epsSet S hS (trueObj G P W) ε})) atTop ≤ ((-γ : ℝ) : EReal) := by
  intro ε hε
  by_cases hne : (nonOptSet S hS (trueObj G P W) ε).Nonempty
  · set r := alpha S hS (trueObj G P W) ε hne / 2 with hr_def
    have hr : 0 < r := by
      have := alpha_pos S hS (trueObj G P W) ε hε hne
      positivity
    have hdev := deviation_le_two_exp S hS G hG P W hWm hind hid hint hA r hr
    choose! γx γx' hγx hγx' hb using hdev
    set γ0 := S.inf' hS (fun x => min (γx x) (γx' x)) with hγ0_def
    have hγ0 : 0 < γ0 :=
      (Finset.lt_inf'_iff hS).2 (fun x hx => lt_min (hγx x hx) (hγx' x hx))
    have hγ0le : ∀ x ∈ S, γ0 ≤ γx x ∧ γ0 ≤ γx' x := fun x hx => by
      have := Finset.inf'_le (fun x => min (γx x) (γx' x)) hx
      exact ⟨this.trans (min_le_left _ _), this.trans (min_le_right _ _)⟩
    set C : ℝ := 2 * (S.card : ℝ) with hC_def
    have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    have hC : 0 < C := by positivity
    have key : ∀ N : ℕ, 1 ≤ N →
        1 - P {ω | epsSet S hS (sampleObj G W N ω) ε ⊆ epsSet S hS (trueObj G P W) ε} ≤
          ENNReal.ofReal (C * Real.exp (-((N : ℝ) * γ0))) := by
      intro N hN
      refine (union_bound S hS G P W ε hε hne N).trans ?_
      calc ∑ x ∈ S, P {ω | alpha S hS (trueObj G P W) ε hne / 2 ≤
              |sampleObj G W N ω x - trueObj G P W x|}
          ≤ ∑ x ∈ S, ENNReal.ofReal (Real.exp (-((N : ℝ) * γx x)) +
              Real.exp (-((N : ℝ) * γx' x))) := Finset.sum_le_sum (fun x hx => hb x hx N hN)
        _ ≤ ∑ x ∈ S, ENNReal.ofReal (2 * Real.exp (-((N : ℝ) * γ0))) := by
            refine Finset.sum_le_sum (fun x hx => ENNReal.ofReal_le_ofReal ?_)
            have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
            have h1 : Real.exp (-((N : ℝ) * γx x)) ≤ Real.exp (-((N : ℝ) * γ0)) :=
              Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left (hγ0le x hx).1 hN0))
            have h2 : Real.exp (-((N : ℝ) * γx' x)) ≤ Real.exp (-((N : ℝ) * γ0)) :=
              Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left (hγ0le x hx).2 hN0))
            linarith
        _ = ENNReal.ofReal (C * Real.exp (-((N : ℝ) * γ0))) := by
            rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [hC_def]; ring
    refine ⟨γ0 / 2, by positivity, ?_⟩
    apply Filter.limsup_le_of_le (by isBoundedDefault)
    obtain ⟨N0, hN0⟩ := exists_nat_ge (2 * Real.log C / γ0)
    filter_upwards [eventually_ge_atTop (max N0 1)] with N hN
    have hN1 : 1 ≤ N := le_of_max_le_right hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hNge : 2 * Real.log C / γ0 ≤ N :=
      le_trans hN0 (by exact_mod_cast le_of_max_le_left hN)
    rw [div_le_iff₀ hγ0] at hNge
    calc ((1 / (N : ℝ) : ℝ) : EReal) * ENNReal.log
          (1 - P {ω | epsSet S hS (sampleObj G W N ω) ε ⊆ epsSet S hS (trueObj G P W) ε})
        ≤ ((1 / (N : ℝ) : ℝ) : EReal) *
            ENNReal.log (ENNReal.ofReal (C * Real.exp (-((N : ℝ) * γ0)))) :=
          mul_le_mul_of_nonneg_left (ENNReal.log_le_log (key N hN1))
            (by exact_mod_cast (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ)))
      _ = (((1 / (N : ℝ)) * Real.log (C * Real.exp (-((N : ℝ) * γ0))) : ℝ) : EReal) := by
          rw [ENNReal.log_ofReal_of_pos (by positivity)]
          rfl
      _ ≤ ((-(γ0 / 2) : ℝ) : EReal) := by
          apply EReal.coe_le_coe_iff.2
          rw [Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp, one_div,
            inv_mul_le_iff₀ hNpos]
          nlinarith
  · refine ⟨1, one_pos, ?_⟩
    have hall : ∀ N : ℕ,
        {ω | epsSet S hS (sampleObj G W N ω) ε ⊆ epsSet S hS (trueObj G P W) ε} = Set.univ := by
      intro N
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro x hx
      refine ⟨hx.1, ?_⟩
      by_contra hlt
      exact hne ⟨x, Finset.mem_filter.2 ⟨hx.1, lt_of_not_ge hlt⟩⟩
    apply Filter.limsup_le_of_le (by isBoundedDefault)
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < 1 / (N : ℝ) := by
      have : (0 : ℝ) < N := by exact_mod_cast hN
      positivity
    rw [hall N, measure_univ, tsub_self, ENNReal.log_zero, EReal.coe_mul_bot_of_pos hNpos]
    exact bot_le
