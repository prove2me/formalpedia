-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegLoc.HermOrth.trace_red_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:38:48.3258+00:00
-- url     : https://prove2.me/submissions/3457c712-ca69-4ba9-83c4-9c74cd0d2752

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCharacterOrthogonality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc GlobalTheory.CompanionTheory.SiegLoc.HermOrth
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.SiegLoc.HermOrth
theorem _root_.solution (ϖ : R) (k n : ℕ) (b y : Matrix (Fin n) (Fin n) R) :
    Matrix.trace (red ϖ k b * red ϖ k y) = Ideal.Quotient.mk (lev ϖ k) (Matrix.trace (b * y)) := by
  unfold PositivityTheory.PfSWUS.Loc.red
  rw [← Matrix.map_mul]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply, map_sum]
end GlobalTheory.CompanionTheory.SiegLoc.HermOrth
