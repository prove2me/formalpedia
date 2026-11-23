-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Adelic.OrthHaar.scale_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:59.04883+00:00
-- url     : https://prove2.me/submissions/38dbc11a-7ee3-477d-9e22-32f1b004bdd0

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixInductionTransvectionDiagonalStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MapMulVecEqOfTransposeMulMulEq
import Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_OrthHaar_scale_of_isUnit

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
theorem _root_.solution {A B : Matrix ι ι R} (hA : IsUnit A.det) (hB : IsUnit B.det) :
    scale (A * B) = scale A * scale B := by
  have hAB : IsUnit (A * B).det := by
    rw [Matrix.det_mul]
    exact hA.mul hB
  have e : mulVecEquiv (A * B) hAB = (mulVecEquiv B hB).trans (mulVecEquiv A hA) :=
    ContinuousAddEquiv.ext fun x => (Matrix.mulVec_mulVec x A B).symm
  rw [scale_of_isUnit hAB, scale_of_isUnit hA, scale_of_isUnit hB, e, addEquivAddHaarChar_trans,
    mul_comm]
end GlobalTheory.CompanionTheory.Adelic.OrthHaar
