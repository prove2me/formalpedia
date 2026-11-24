-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.OrthHaar.transvection_mulVec_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:17:22.260889+00:00
-- url     : https://prove2.me/submissions/ae6be4b5-3c71-4b37-90ea-a24f941cb986

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixInductionTransvectionDiagonalStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MapMulVecEqOfTransposeMulMulEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Adelic GlobalTheory.CompanionTheory.Adelic.OrthHaar
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.Adelic.OrthHaar
theorem _root_.solution (i j : ι) (c : R) (f : ι → R) (k : ι) :
    (Matrix.transvection i j c *ᵥ f) k = f k + if k = i then c * f j else 0 := by
  by_cases hk : k = i
  · subst hk
    simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec]
  · simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec, hk]
end GlobalTheory.CompanionTheory.Adelic.OrthHaar
