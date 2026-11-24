-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermDiag.diagble_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:38:15.244562+00:00
-- url     : https://prove2.me/submissions/96492494-2deb-440a-af37-2a2d396fd3f3

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
theorem _root_.solution {h : Matrix ι ι R} {c : R} (hc : σ c = c) (hd : Diagble σ h) :
    Diagble σ (c • h) := by
  obtain ⟨g, g', d, hg, hg', hfix, hdiag⟩ := hd
  refine ⟨g, g', fun i => c * d i, hg, hg', fun i => by simp [hc, hfix], ?_⟩
  have : Matrix.diagonal (fun i => c * d i) = c • Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
  rw [this, ← hdiag]
  simp [Matrix.mul_smul, Matrix.smul_mul]
end GlobalTheory.CompanionTheory.HermDiag
