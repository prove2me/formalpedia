-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThW.GaussOrth.measurePreserving_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:35:09.499579+00:00
-- url     : https://prove2.me/submissions/84c49212-7182-432e-aa00-05c0308edb1e

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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {g : Matrix ι ι ℝ}
    (h : |g.det| = 1) : MeasurePreserving (fun x : ι → ℝ => g *ᵥ x) volume volume := by
  have hd : g.det ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at h
    exact zero_ne_one h
  refine ⟨(Continuous.matrix_mulVec continuous_const continuous_id).measurable, ?_⟩
  have := Real.map_matrix_volume_pi_eq_smul_volume_pi hd
  have e : (fun x : ι → ℝ => g *ᵥ x) = ⇑(Matrix.toLin' g) := by
    ext x i
    simp [Matrix.toLin'_apply]
  rw [e, this, abs_inv, h]
  simp
end GlobalTheory.CompanionTheory.SW.ThW.GaussOrth
