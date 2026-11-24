-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThW.GaussOrth.quad_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:35:10.382432+00:00
-- url     : https://prove2.me/submissions/9fc04459-f72f-446d-b73a-faf98b6474c9

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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (g M : Matrix ι ι ℝ) (x : ι → ℝ) :
    (g *ᵥ x) ⬝ᵥ (M *ᵥ (g *ᵥ x)) = x ⬝ᵥ ((gᵀ * M * g) *ᵥ x) := by
  have h : (gᵀ * M * g) *ᵥ x = gᵀ *ᵥ (M *ᵥ (g *ᵥ x)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [h, Matrix.dotProduct_mulVec x gᵀ, Matrix.vecMul_transpose]
end GlobalTheory.CompanionTheory.SW.ThW.GaussOrth
