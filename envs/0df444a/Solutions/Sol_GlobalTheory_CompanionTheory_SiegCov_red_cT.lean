-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegCov.red_cT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:38:50.422832+00:00
-- url     : https://prove2.me/submissions/54148431-abfe-4a8c-a06b-486d667224ae

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MatrixGaussSumCongrInvariance

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegCov
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.SiegCov
theorem _root_.solution (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ) (k : ℕ) {a b : ℕ}
    (x : Matrix (Fin a) (Fin b) R) : red ϖ k (cT σ x) = cT (barσ σ ϖ hf k) (red ϖ k x) := by
  ext i j
  exact (barσ_mk σ ϖ hf k (x j i)).symm
end GlobalTheory.CompanionTheory.SiegCov
