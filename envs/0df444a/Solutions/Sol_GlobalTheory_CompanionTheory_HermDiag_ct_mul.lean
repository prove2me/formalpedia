-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermDiag.ct_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:33:31.358395+00:00
-- url     : https://prove2.me/submissions/dd95b22c-5b0c-429c-bab0-f1ce29dde354

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatrixDiagonalizable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermDiag
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.HermDiag
theorem _root_.solution (σ : R →+* R) {a b c : Type} [Fintype b] (x : Matrix a b R) (y : Matrix b c R) :
    ct σ (x * y) = ct σ y * ct σ x := by
  unfold ct
  rw [Matrix.map_mul, Matrix.transpose_mul]
end GlobalTheory.CompanionTheory.HermDiag
