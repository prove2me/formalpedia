-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.Eigen.II_mul_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:55:19.358154+00:00
-- url     : https://prove2.me/submissions/d3f34243-a70a-4a15-ba7c-e73e4a37350d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockMatrixMulBlocks
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldUniformizerNormProperties
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricSubgroupCompactOpenMeasure
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_MemIntegralGLIffIntegralUnitDetStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParahoricCharacterModulusPropertiesStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicTestFunctionEquivariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.Eigen
variable {F : Type} [Field F]
namespace GlobalTheory.CompanionTheory.QL.Eigen
theorem _root_.solution {O : Subring F} {ϖ : F} {a b c : ℕ} {X : Matrix (Fin a) (Fin b) F}
    {Y : Matrix (Fin b) (Fin c) F} (hX : X ∈ IIset O ϖ) (hY : Y ∈ intMat O b c) :
    X * Y ∈ IIset O ϖ := fun i j => by
  choose f hf hfe using hX
  refine ⟨∑ k, f i k * Y k j, O.sum_mem fun k _ => O.mul_mem (hf i k) (hY k j), ?_⟩
  rw [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [hfe, mul_assoc]
end GlobalTheory.CompanionTheory.QL.Eigen
