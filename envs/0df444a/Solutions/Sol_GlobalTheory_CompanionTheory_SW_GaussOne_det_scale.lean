-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GaussOne.det_scale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:18:55.947315+00:00
-- url     : https://prove2.me/submissions/c29e84d1-77c9-4b11-a15f-681e90f87439

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SimultaneousNormalFormMajorant
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_RealGaussianFourierTransform

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GaussOne
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.SW.GaussOne
theorem _root_.solution {g S : Matrix ι ι ℝ} {e : ι → ℝ} (he : ∀ i, e i = 1 ∨ e i = -1)
    (hS : gᵀ * S * g = Matrix.diagonal e) : Real.sqrt |S.det| * |g.det| = 1 := by
  have h1 : g.det ^ 2 * S.det = ∏ i, e i := by
    have := congrArg Matrix.det hS
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at this
    rw [← this]; ring
  have h2 : |∏ i, e i| = 1 := by
    rw [Finset.abs_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    rcases he i with h | h <;> simp [h]
  have h3 : |S.det| * |g.det| ^ 2 = 1 := by
    rw [← h2, ← h1, abs_mul, abs_pow]; ring
  have h4 : Real.sqrt (|S.det| * |g.det| ^ 2) = 1 := by rw [h3]; simp
  rwa [Real.sqrt_mul (abs_nonneg _), Real.sqrt_sq (abs_nonneg _)] at h4
end GlobalTheory.CompanionTheory.SW.GaussOne
