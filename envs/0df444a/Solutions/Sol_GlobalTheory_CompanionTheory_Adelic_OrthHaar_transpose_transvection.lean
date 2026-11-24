-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.OrthHaar.transpose_transvection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:17:21.599797+00:00
-- url     : https://prove2.me/submissions/aed2399b-4b4f-4aed-87d7-ea311c501a5e

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
variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.Adelic.OrthHaar
theorem _root_.solution (i j : ι) (c : R) :
    (Matrix.transvection i j c)ᵀ = Matrix.transvection j i c := by
  simp [Matrix.transvection, Matrix.transpose_add, Matrix.transpose_one]
end GlobalTheory.CompanionTheory.Adelic.OrthHaar
