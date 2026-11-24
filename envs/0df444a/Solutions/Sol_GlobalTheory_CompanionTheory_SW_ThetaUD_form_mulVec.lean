-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThetaUD.form_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:35:03.798272+00:00
-- url     : https://prove2.me/submissions/6115709e-acf8-47ea-9230-b7cb5bb38637

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ThetaFunctionModularity

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThetaUD
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.SW.ThetaUD
theorem _root_.solution {R ι : Type} [CommRing R] [Fintype ι] (G Q : Matrix ι ι R) (h : Gᵀ * Q * G = Q)
    (v : ι → R) : (G *ᵥ v) ⬝ᵥ (Q *ᵥ (G *ᵥ v)) = v ⬝ᵥ (Q *ᵥ v) := by
  conv_rhs => rw [← h]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v, Matrix.vecMul_transpose]
end GlobalTheory.CompanionTheory.SW.ThetaUD
