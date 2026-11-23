-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermDiag.diagble_of_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:36:21.454262+00:00
-- url     : https://prove2.me/submissions/366061b8-76d5-4f9f-a7da-33bb8ee82ee0

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatrixDiagonalizable
import Theorems.Thm_GlobalTheory_CompanionTheory_HermDiag_ct_mul

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
theorem _root_.solution {h p p' : Matrix ι ι R} (h1 : p * p' = 1) (h2 : p' * p = 1)
    (hd : Diagble σ (ct σ p * h * p)) : Diagble σ h := by
  obtain ⟨g, g', d, hg, hg', hfix, hdiag⟩ := hd
  refine ⟨p * g, g' * p', d, ?_, ?_, hfix, ?_⟩
  · calc p * g * (g' * p') = p * (g * g') * p' := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, Matrix.mul_one, h1]
  · calc g' * p' * (p * g) = g' * (p' * p) * g := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h2, Matrix.mul_one, hg']
  · rw [ct_mul, ← hdiag]
    simp only [Matrix.mul_assoc]
end GlobalTheory.CompanionTheory.HermDiag
