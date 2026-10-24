-- Prove2me | solution 1 for K24.Global.FlatTorus.sharpness_analytic
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T19:14:46.084657+00:00
-- url     : https://prove2.me/submissions/890f3237-caf7-4f8e-aab4-1dd75a30d4e5

import Definitions.Def_K24GlobalStatement
import Theorems.Thm_K24_Global_FlatTorus_geometric_sharpness

set_option autoImplicit false
open Filter Topology
open scoped Manifold ContDiff NNReal ENNReal
open K24.Global K24.Global.FlatTorus

theorem solution :
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
        actualVectorDifference rho alpha.value n = projectedDefect rho alpha.value n) := by
  intro alpha
  rcases geometric_sharpness alpha with
    ⟨hM, rho, C, hact, hC, hmetric, hinvariant, hVI, hVzero, hVfinite, hVpos, hnorms, hconv, hlarge, hfailure⟩
  refine ⟨hM, rho, C, hact, hC, hinvariant, hVI, hVzero, hVfinite, hVpos, hnorms, hconv, ?_⟩
  intro n hn
  exact ⟨(hlarge n hn).2.1, (hlarge n hn).2.2⟩

#print axioms solution
