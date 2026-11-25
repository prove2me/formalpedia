-- Prove2me | solution 1 for GlobalTheory.ThetaGauss.exists_mean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:02:48.385096+00:00
-- url     : https://prove2.me/submissions/88634a4d-67d4-4dc8-993c-3c2d72fdf19c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Theorems.Thm_GlobalTheory_ThetaGauss_transl_apply
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk


attribute [local simp] GlobalTheory.ThetaGauss.transl_apply

set_option autoImplicit false
open Matrix Filter Topology Metric
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaGauss
variable {g : ℕ}
namespace GlobalTheory.ThetaGauss
theorem _root_.solution : ∃ ℓ : C(Set.Icc (0 : ℝ) (2 * Real.pi), ℂ) →L[ℂ] ℂ,
    ∀ (f : C(Set.Icc (0 : ℝ) (2 * Real.pi), ℂ)) (k : ℂ → ℂ) (r : ℝ), Differentiable ℂ k →
      (∀ φ, f φ = k (circleMap 0 r φ)) → ℓ f = k 0 := by
  let p : ℝ → Set.Icc (0 : ℝ) (2 * Real.pi) := Set.projIcc 0 (2 * Real.pi) Real.two_pi_pos.le
  have hp : Continuous p := continuous_projIcc
  let L : C(Set.Icc (0 : ℝ) (2 * Real.pi), ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ φ in (0 : ℝ)..(2 * Real.pi), f (p φ)
      map_add' := fun a b => intervalIntegral.integral_add
        ((a.continuous.comp hp).intervalIntegrable _ _) ((b.continuous.comp hp).intervalIntegrable _ _)
      map_smul' := fun a b => intervalIntegral.integral_smul a _ }
  have hL : ∀ f, ‖L f‖ ≤ |2 * Real.pi - 0| * ‖f‖ := fun f => by
    rw [mul_comm _ ‖f‖]
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => f.norm_coe_le_norm _
  refine ⟨(2 * Real.pi)⁻¹ • L.mkContinuous _ hL, fun f k r hk hf => ?_⟩
  rw [← (hk.diffContOnCl (s := ball 0 |r|)).circleAverage, Real.circleAverage_def]
  change (2 * Real.pi)⁻¹ • ∫ φ in (0 : ℝ)..(2 * Real.pi), f (p φ) = _
  congr 1
  refine intervalIntegral.integral_congr fun φ hφ => ?_
  rw [Set.uIcc_of_le Real.two_pi_pos.le] at hφ
  simp only [hf, p, Set.projIcc_of_mem _ hφ]
end GlobalTheory.ThetaGauss
