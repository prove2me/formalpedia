-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.TraceCoord.dot_mulVec_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:01.595238+00:00
-- url     : https://prove2.me/submissions/03d34300-c992-4282-a997-fca1a191a89a

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsTraceFormGramMatrixInBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TraceCoord
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {d M : ℕ}
namespace GlobalTheory.CompanionTheory.SW.TraceCoord
theorem _root_.solution {n : Type} [Fintype n] (P : Matrix n n R) (u w : n → R) :
    (P *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (Pᵀ *ᵥ w) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
end GlobalTheory.CompanionTheory.SW.TraceCoord
