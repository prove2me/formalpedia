-- Prove2me | solution 1 for Kyprianou.Ch02.canonicalMarginalSmallTimeExplicitDataV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:00:26.678999+00:00
-- url     : https://prove2.me/submissions/03358466-b619-4bd0-8963-8cff02f2762b

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral

import Theorems.Thm_levy_foundations_public_semigroup_joint_smalltime_triplet_data
import Theorems.Thm_levy_foundations_public_semigroup_smallball_variance_bound
import Theorems.Thm_levy_foundations_public_semigroup_psi_integral_identity
import Theorems.Thm_ProbabilityTheory_leanlevy_chat27_triple_ext_public
import Theorems.Thm_ProbabilityTheory_LevyKhintchineTriple_exponent_def
import Theorems.Thm_ProbabilityTheory_LevyKhintchineTriple_exponent_continuous
import Theorems.Thm_ProbabilityTheory_LevyKhintchineTriple_exponent_zero
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false
open Filter Topology Set

theorem solution
    (M : {t : ℝ // 0 < t} → ProbabilityMeasure ℝ)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hT : ∀ t ξ, charFun (M t : Measure ℝ) ξ =
      Complex.exp (((t.val : ℝ) : ℂ) * (Complex.I * ((T.drift * ξ : ℝ) : ℂ) - (((T.gaussianVariance : ℝ) * ξ ^ 2 / 2 : ℝ) : ℂ) + ∫ y, ProbabilityTheory.levyCompensatedIntegrand ξ y ∂T.levyMeasure))) :
    ∃ (r b_r : ℝ) (σ_sq_r : ℝ≥0) (ts : ℕ → {t : ℝ // 0 < t}),
      r ∈ Set.Ioc (1 / 2 : ℝ) 1 ∧
      T.levyMeasure {x | |x| = r} = 0 ∧
      Tendsto (fun n => (ts n).val) atTop (nhds (0 : ℝ)) ∧
      Tendsto (fun n => (ts n).val⁻¹ *
        ∫ x in {x | |x| < r}, x ∂(M (ts n) : Measure ℝ))
        atTop (nhds b_r) ∧
      Tendsto (fun n => (ts n).val⁻¹ *
        ∫ x in {x | |x| < r}, x ^ 2 ∂(M (ts n) : Measure ℝ))
        atTop (nhds (σ_sq_r : ℝ)) ∧
      T.drift = b_r + ∫ x in {x | r ≤ |x| ∧ |x| < 1}, x ∂T.levyMeasure ∧
      (T.gaussianVariance : ℝ) =
        (σ_sq_r : ℝ) - ∫ x in {x | |x| < r}, x ^ 2 ∂T.levyMeasure ∧
      ∀ f : BoundedContinuousFunction ℝ ℝ,
        (∃ r' > 0, ∀ x, |x| < r' → f x = 0) →
        Tendsto (fun n => (ts n).val⁻¹ *
          ∫ x, f x ∂(M (ts n) : Measure ℝ))
          atTop (nhds (∫ x, f x ∂T.levyMeasure)) := by
  have hBridge (ξ : ℝ) : (Complex.I * ((T.drift * ξ : ℝ) : ℂ) - (((T.gaussianVariance : ℝ) * ξ ^ 2 / 2 : ℝ) : ℂ) + ∫ y, ProbabilityTheory.levyCompensatedIntegrand ξ y ∂T.levyMeasure) = T.exponent ξ := by
    rw [ProbabilityTheory.LevyKhintchineTriple.exponent_def]
    push_cast
    ring
  let S : ProbabilityTheory.ConvolutionSemigroup :=
    { exponent := T.exponent
      exponent_continuous := ProbabilityTheory.LevyKhintchineTriple.exponent_continuous T
      exponent_zero := ProbabilityTheory.LevyKhintchineTriple.exponent_zero T
      measure := M
      charFun_eq := fun t ξ => by
        change charFun (M t : Measure ℝ) ξ = _
        rw [hT t ξ, hBridge ξ] }
  obtain ⟨r, b, v, ν, hν, ts, hr, hnull, ht, hb, hv, hjump⟩ :=
    levy_foundations_public_semigroup_joint_smalltime_triplet_data S
  have hr0 : 0 < r := by linarith [hr.1]
  have hnn : 0 ≤ (v : ℝ) - ∫ x in {x | |x| < r}, x ^ 2 ∂ν := by
    have hle := levy_foundations_public_semigroup_smallball_variance_bound
      S hr0 hν hnull hv hjump
    linarith
  let U : ProbabilityTheory.LevyKhintchineTriple :=
    ⟨b + ∫ x in {x | r ≤ |x| ∧ |x| < 1}, x ∂ν,
      Real.toNNReal ((v : ℝ) - ∫ x in {x | |x| < r}, x ^ 2 ∂ν), ν, hν⟩
  have hEq : T = U := by
    apply ProbabilityTheory.leanlevy_chat27_triple_ext_public
    intro ξ
    change S.exponent ξ = U.exponent ξ
    rw [ProbabilityTheory.LevyKhintchineTriple.exponent_def U ξ]
    change _ = ↑(b + ∫ x in {x | r ≤ |x| ∧ |x| < 1}, x ∂ν) * ↑ξ * I -
      ↑((Real.toNNReal ((v : ℝ) - ∫ x in {x | |x| < r}, x ^ 2 ∂ν) : ℝ≥0) : ℝ) *
        ↑ξ ^ 2 / 2 + ∫ x, ProbabilityTheory.levyCompensatedIntegrand ξ x ∂ν
    rw [Real.coe_toNNReal _ hnn]
    exact levy_foundations_public_semigroup_psi_integral_identity
      S hr b v hν hnull ht hb hv hjump ξ
  rw [hEq]
  refine ⟨r, b, v, ts, hr, hnull, ht, hb, hv, rfl, ?_, hjump⟩
  exact Real.coe_toNNReal _ hnn
