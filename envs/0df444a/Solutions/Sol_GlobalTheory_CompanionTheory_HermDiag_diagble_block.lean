-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermDiag.diagble_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:38:13.51461+00:00
-- url     : https://prove2.me/submissions/967e6968-37e8-4ccd-b534-f707af8ee411

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatrixDiagonalizable
import Theorems.Thm_GlobalTheory_CompanionTheory_HermDiag_ct_apply

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
theorem _root_.solution {a : R} (ha : σ a = a) {D : Matrix ι ι R} (hd : Diagble σ D) :
    Diagble σ (Matrix.fromBlocks (Matrix.diagonal fun _ : Unit => a) 0 0 D) := by
  obtain ⟨g, g', d, hg, hg', hfix, hdiag⟩ := hd
  refine ⟨Matrix.fromBlocks 1 0 0 g, Matrix.fromBlocks 1 0 0 g', Sum.elim (fun _ => a) d,
    ?_, ?_, ?_, ?_⟩
  · rw [Matrix.fromBlocks_multiply]; simp [hg]
  · rw [Matrix.fromBlocks_multiply]; simp [hg']
  · rintro (i | i)
    · simpa using ha
    · simpa using hfix i
  · have hct : ct σ (Matrix.fromBlocks (1 : Matrix Unit Unit R) 0 0 g) =
        Matrix.fromBlocks 1 0 0 (ct σ g) := by
      ext (i | i) (j | j) <;> simp [ct_apply, Matrix.one_apply]
    rw [hct, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_diagonal]
    simp [hdiag]
end GlobalTheory.CompanionTheory.HermDiag
