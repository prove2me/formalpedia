-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CoordMat.dot_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:12:19.829351+00:00
-- url     : https://prove2.me/submissions/5da36e17-9674-4888-a132-c1e53e49a16f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TraceGramDetNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CoordMat
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.CoordMat
theorem _root_.solution {ι A : Type} [Fintype ι] [CommRing A] (g P : Matrix ι ι A) (u v : ι → A) :
    u ⬝ᵥ (gᵀ * P * g) *ᵥ v = (g *ᵥ u) ⬝ᵥ P *ᵥ (g *ᵥ v) := by
  rw [← Matrix.vecMul_transpose g u, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc]
end GlobalTheory.CompanionTheory.SW.CoordMat
