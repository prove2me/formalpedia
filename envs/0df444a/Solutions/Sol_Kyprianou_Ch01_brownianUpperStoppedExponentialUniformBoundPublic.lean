-- Prove2me | solution 1 for Kyprianou.Ch01.brownianUpperStoppedExponentialUniformBoundPublic
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-18T09:31:31.821658+00:00
-- url     : https://prove2.me/submissions/50505942-f99c-4fd2-ba3f-32c7dd2e2863

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace UBDAux

theorem stopped_le {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (x : ℝ) (hx : 0 < x) (ω : Ω)
    (hcont : Continuous (fun t : ℝ≥0 => X t ω)) (h0 : X 0 ω = 0) (T : ℝ≥0) :
    X (match firstUpperPassage X x ω with
        | none => T
        | some t => min t T) ω ≤ x := by
  unfold firstUpperPassage
  split_ifs with hex
  · set τ0 := sInf ({t : ℝ≥0 | 0 < t ∧ x < X t ω} : Set ℝ≥0) with hτ0
    have hbefore : ∀ t : ℝ≥0, t < τ0 → X t ω ≤ x := by
      intro t ht
      by_contra hc
      have hlt : x < X t ω := not_le.mp hc
      have htpos : 0 < t := by
        rcases eq_or_lt_of_le (show (0:ℝ≥0) ≤ t from t.2) with h | h
        · rw [← h, h0] at hlt; linarith
        · exact h
      exact absurd (csInf_le (OrderBot.bddBelow ({t : ℝ≥0 | 0 < t ∧ x < X t ω} : Set ℝ≥0))
        (show t ∈ ({t : ℝ≥0 | 0 < t ∧ x < X t ω} : Set ℝ≥0) from ⟨htpos, hlt⟩)) (not_le.mpr ht)
    have hat : X τ0 ω ≤ x := by
      by_contra hc
      have hlt : x < X τ0 ω := not_le.mp hc
      have hU : {t : ℝ≥0 | x < X t ω} ∈ nhds τ0 :=
        (isOpen_lt continuous_const hcont).mem_nhds hlt
      rcases eq_or_lt_of_le (show (0:ℝ≥0) ≤ τ0 from τ0.2) with h | h
      · rw [← h, h0] at hlt; linarith
      · obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds hU ⟨0, h⟩
        obtain ⟨m, hm1, hm2⟩ := exists_between hl
        have : x < X m ω := hsub ⟨hm1, hm2.le⟩
        exact absurd (hbefore m hm2) (not_le.mpr this)
    show X (min τ0 T) ω ≤ x
    rcases eq_or_lt_of_le (min_le_left τ0 T) with h | h
    · rw [h]; exact hat
    · exact hbefore _ h
  · show X T ω ≤ x
    by_contra hc
    have hlt : x < X T ω := not_le.mp hc
    rcases eq_or_lt_of_le (show (0:ℝ≥0) ≤ T from T.2) with h | h
    · rw [← h, h0] at hlt; linarith
    · exact hex ⟨T, h, hlt⟩

end UBDAux

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q x : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q) (hx : 0 < x)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    let theta : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
    let F : ℕ → Ω → ℝ := fun N ω =>
      let T : ℝ≥0 := N
      let tauT : ℝ≥0 :=
        match firstUpperPassage X x ω with
        | none => T
        | some t => min t T
      Real.exp (theta * X tauT ω - q * (tauT : ℝ))
    ∀ᵐ ω ∂P, ∀ N : ℕ,
      ‖F N ω‖ ≤ Real.exp (theta * x) := by
  intro theta F
  have htheta : 0 ≤ theta := by
    apply div_nonneg _ (by positivity)
    have h1 : |gamma| ≤ Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg sigma])
    linarith [le_abs_self gamma]
  have h0 : ∀ ω, X 0 ω = 0 := fun ω => congrFun hX.1.start_zero ω
  filter_upwards [hX.2.1] with ω hω
  intro N
  simp only [F]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
  set s : ℝ≥0 := (match firstUpperPassage X x ω with
        | none => (N : ℝ≥0)
        | some t => min t (N : ℝ≥0)) with hs
  have hle : X s ω ≤ x := UBDAux.stopped_le X x hx ω hω (h0 ω) (N : ℝ≥0)
  have hspos : (0 : ℝ) ≤ (s : ℝ) := s.2
  nlinarith [mul_le_mul_of_nonneg_left hle htheta, mul_nonneg hq.le hspos]
