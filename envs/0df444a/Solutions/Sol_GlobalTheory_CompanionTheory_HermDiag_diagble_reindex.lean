-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermDiag.diagble_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:38:14.430998+00:00
-- url     : https://prove2.me/submissions/5892f6da-e9c7-481c-8e11-d8d7dee42ac2

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
variable {σ : R →+* R} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
namespace GlobalTheory.CompanionTheory.HermDiag
theorem _root_.solution (e : κ ≃ ι) {h : Matrix ι ι R} (hd : Diagble σ (h.submatrix e e)) :
    Diagble σ h := by
  obtain ⟨g, g', d, hg, hg', hfix, hdiag⟩ := hd
  refine ⟨g.submatrix e.symm e.symm, g'.submatrix e.symm e.symm, fun i => d (e.symm i),
    ?_, ?_, fun i => hfix _, ?_⟩
  · rw [Matrix.submatrix_mul_equiv, hg]; simp
  · rw [Matrix.submatrix_mul_equiv, hg']; simp
  · have hct : ct σ (g.submatrix e.symm e.symm) = (ct σ g).submatrix e.symm e.symm := rfl
    have hh : h = (h.submatrix e e).submatrix e.symm e.symm := by ext i j; simp
    rw [hct, hh, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hdiag]
    ext i j
    simp [Matrix.diagonal_apply]
end GlobalTheory.CompanionTheory.HermDiag
