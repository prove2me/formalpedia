-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegCov.trace_cov
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:00:01.424365+00:00
-- url     : https://prove2.me/submissions/7cd88552-d825-46b5-a95b-b033b1bd0157

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MatrixGaussSumCongrInvariance
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegCov_cT_cT

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
variable {A : Type} [CommRing A]
namespace GlobalTheory.CompanionTheory.SiegCov
theorem _root_.solution (τ : A →+* A) (hτ : ∀ a, τ (τ a) = a) {m n : ℕ}
    (D g' : Matrix (Fin n) (Fin n) A) (E p' : Matrix (Fin m) (Fin m) A)
    (x : Matrix (Fin m) (Fin n) A) :
    Matrix.trace ((cT τ g' * D * g') * (cT τ x * (cT τ p' * E * p') * x)) =
      Matrix.trace (D * (cT τ (p' * x * cT τ g') * E * (p' * x * cT τ g'))) := by
  rw [cT_mul, cT_mul, cT_cT τ hτ]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (cT τ g')]
  simp only [Matrix.mul_assoc]
end GlobalTheory.CompanionTheory.SiegCov
