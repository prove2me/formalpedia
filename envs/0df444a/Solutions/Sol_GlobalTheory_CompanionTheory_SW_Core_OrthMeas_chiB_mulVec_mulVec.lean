-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.OrthMeas.chiB_mulVec_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:20:12.783652+00:00
-- url     : https://prove2.me/submissions/f3c614a6-4828-4a61-a46f-48454cddf1f0

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_WeilOrthogonalGroupInvariance

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.OrthMeas
namespace GlobalTheory.CompanionTheory.SW.Core.OrthMeas
theorem _root_.solution {R : Type} [CommRing R] {ι : Type} [Fintype ι]
    (ψ : AddChar R ℂ) (B g : Matrix ι ι R) (hg : gᵀ * B * g = B) (x y : ι → R) :
    chiB ψ B (g *ᵥ x) (g *ᵥ y) = chiB ψ B x y := by
  have h : (g *ᵥ x) ⬝ᵥ (B *ᵥ (g *ᵥ y)) = x ⬝ᵥ (B *ᵥ y) := by
    conv_rhs => rw [← hg]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x gᵀ,
      Matrix.vecMul_transpose]
  simp only [chiB, h]
end GlobalTheory.CompanionTheory.SW.Core.OrthMeas
