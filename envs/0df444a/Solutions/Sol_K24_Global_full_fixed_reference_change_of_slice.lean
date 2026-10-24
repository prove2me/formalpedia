-- Prove2me | solution 1 for K24.Global.full_fixed_reference_change_of_slice
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T18:52:28.870987+00:00
-- url     : https://prove2.me/submissions/c655cb27-35cd-4291-a61f-d5b7922c0b3c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_K24GlobalStatement
import Theorems.Thm_K24_Global_uniform_analytic_conclusions
import Theorems.Thm_K24_Global_FlatTorus_sharpness_analytic
import Theorems.Thm_K24_Global_FlatTorus_metric_positivity

-- Complete local proof from Residual.lean

set_option autoImplicit false
open Filter Topology
open scoped Manifold ContDiff NNReal ENNReal

namespace K24.Global.FlatTorus

/-- OPEN analytic residual of the original sharpness statement. Only the two
proved metric-positivity clauses and the derived final impossibility clause are
removed. Every other binder and clause is retained in its original order. -/
def RemainingAnalyticStatement : Prop :=
  ∀ alpha : HolderExponent,
    IsManifold I4 ∞ Torus ∧
    ∃ rho : CircleAction Torus, ∃ C : ℝ,
      rho.act = translate ∧ 0 < C ∧
      IsInvariantCov2 rho flatMetric ∧
      VectorHaarIntegrable rho testVector ∧ IsNonzeroVector rho testVector ∧
      vectorHolderENorm 3 alpha.value testVector < ⊤ ∧
      0 < vectorHolderNorm 3 alpha.value testVector ∧
      (∀ n : ℕ,
        tensorHolderENorm 2 alpha.value (perturbation alpha.value n) < ⊤ ∧
        tensorHolderENorm 3 alpha.value (perturbation alpha.value n) < ⊤ ∧
        covectorHolderENorm 1 alpha.value (projectedDefect rho alpha.value n) < ⊤ ∧
        CovectorHaarIntegrable rho (unprojectedDefect alpha.value n) ∧
        tensorHolderNorm 3 alpha.value (perturbation alpha.value n) ≤ C) ∧
      Tendsto (fun n : ℕ => tensorHolderNorm 2 alpha.value (perturbation alpha.value n))
        atTop (𝓝 0) ∧
      (∀ n : ℕ, 2 ≤ n →
        Real.rpow Real.pi (-(alpha.value : ℝ)) ≤
          covectorHolderNorm 1 alpha.value (projectedDefect rho alpha.value n) ∧
        actualVectorDifference rho alpha.value n = projectedDefect rho alpha.value n)

end K24.Global.FlatTorus

-- Complete local proof from ConditionalRoot.lean

set_option autoImplicit false
open Filter Topology
open scoped Manifold ContDiff NNReal ENNReal

namespace K24.Global.FlatTorus

/-- A positive uniform defect lower bound is incompatible with a fixed
multiple of a tensor norm tending to zero. This uses the actual operator equality. -/
theorem PublicReduction.no_shifted_estimate_of_convergence
    (alpha : HolderExponent) (rho : CircleAction Torus)
    (hconv : Tendsto
      (fun n : ℕ => tensorHolderNorm 2 alpha.value (perturbation alpha.value n))
      atTop (𝓝 0))
    (hfields : ∀ n : ℕ, 2 ≤ n →
      Real.rpow Real.pi (-(alpha.value : ℝ)) ≤
        covectorHolderNorm 1 alpha.value (projectedDefect rho alpha.value n) ∧
      actualVectorDifference rho alpha.value n = projectedDefect rho alpha.value n) :
    ¬ (∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, 2 ≤ n →
      covectorHolderNorm 1 alpha.value (actualVectorDifference rho alpha.value n) ≤
        K * tensorHolderNorm 2 alpha.value (perturbation alpha.value n) *
          vectorHolderNorm 3 alpha.value testVector) := by
  rintro ⟨K, _hK, hest⟩
  have hlim : Tendsto
      (fun n : ℕ => K * tensorHolderNorm 2 alpha.value (perturbation alpha.value n) *
        vectorHolderNorm 3 alpha.value testVector) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (hconv.const_mul K).mul_const (vectorHolderNorm 3 alpha.value testVector)
  have hlower : ∀ᶠ n : ℕ in atTop,
      Real.rpow Real.pi (-(alpha.value : ℝ)) ≤
        K * tensorHolderNorm 2 alpha.value (perturbation alpha.value n) *
          vectorHolderNorm 3 alpha.value testVector := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    calc
      Real.rpow Real.pi (-(alpha.value : ℝ)) ≤
          covectorHolderNorm 1 alpha.value (projectedDefect rho alpha.value n) :=
        (hfields n hn).1
      _ = covectorHolderNorm 1 alpha.value (actualVectorDifference rho alpha.value n) :=
        congrArg (covectorHolderNorm 1 alpha.value) (hfields n hn).2.symm
      _ ≤ K * tensorHolderNorm 2 alpha.value (perturbation alpha.value n) *
          vectorHolderNorm 3 alpha.value testVector := hest n hn
  have hnonpos : Real.rpow Real.pi (-(alpha.value : ℝ)) ≤ 0 :=
    ge_of_tendsto hlim hlower
  exact (not_le_of_gt (Real.rpow_pos_of_pos Real.pi_pos _)) hnonpos

/-- Exact conditional reduction. The analytic antecedent remains OPEN. -/
theorem PublicReduction.sharpness_of_remaining_analytic :
    RemainingAnalyticStatement → SharpnessStatement := by
  intro h alpha
  rcases h alpha with
    ⟨hM, rho, C, hrho, hC, hinv, hhaar, hnonzero, hVfin, hVpos, hall, hconv, hfields⟩
  refine ⟨hM, rho, C, hrho, hC, metric_positivity.1, hinv, hhaar,
    hnonzero, hVfin, hVpos, hall, hconv, ?_, ?_⟩
  · intro n hn
    exact ⟨metric_positivity.2 alpha n hn, hfields n hn⟩
  · exact PublicReduction.no_shifted_estimate_of_convergence alpha rho hconv hfields

end K24.Global.FlatTorus

namespace K24.Global

universe u

/-- Both analytic inputs remain open; this only fixes the exact root reduction. -/
def FrozenRootReductionTarget : Prop :=
  (UniformHolderNaturalStatement.{u} ∧
    UniformHolderShiftedStatement.{u} ∧
    UniformSobolevStatement.{u}) →
  FlatTorus.RemainingAnalyticStatement → FullK24Statement.{u}

/-- The two explicit open analytic inputs complete the original root by using
its proved public positivity child and the convergence contradiction. -/
theorem conditional_full_k24 :
  (UniformHolderNaturalStatement.{u} ∧
    UniformHolderShiftedStatement.{u} ∧
    UniformSobolevStatement.{u}) →
  FlatTorus.RemainingAnalyticStatement → FullK24Statement.{u} := by
  intro hUniform hSharpness
  exact ⟨hUniform.1, hUniform.2.1, hUniform.2.2,
    FlatTorus.PublicReduction.sharpness_of_remaining_analytic hSharpness⟩

end K24.Global

universe u

/-- Original FullK24 root, reduced to exactly two registered Open obligations. -/
theorem solution : K24.Global.FullK24Statement.{u} := by
  exact K24.Global.conditional_full_k24.{u}
    K24.Global.uniform_analytic_conclusions.{u}
    K24.Global.FlatTorus.sharpness_analytic
