-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThW.GaussOrth.abs_det_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:35:08.139268+00:00
-- url     : https://prove2.me/submissions/3dde8a72-5c58-4176-a20d-12e04d89eebd

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianChangeOfVariablesIsometry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW GlobalTheory.CompanionTheory.SW.ThW.GaussOrth
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
namespace GlobalTheory.CompanionTheory.SW.ThW.GaussOrth
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {g M : Matrix ι ι ℝ}
    (hM : M.det ≠ 0) (h : gᵀ * M * g = M) : |g.det| = 1 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at h1
  have h2 : g.det * g.det = 1 := by
    apply mul_right_cancel₀ hM
    rw [one_mul]
    calc g.det * g.det * M.det = g.det * M.det * g.det := by ring
      _ = M.det := h1
  have h3 : |g.det| * |g.det| = 1 := by rw [← abs_mul, h2, abs_one]
  have h4 : 0 ≤ |g.det| := abs_nonneg _
  nlinarith [sq_nonneg (|g.det| - 1), sq_nonneg (|g.det| + 1)]
end GlobalTheory.CompanionTheory.SW.ThW.GaussOrth
