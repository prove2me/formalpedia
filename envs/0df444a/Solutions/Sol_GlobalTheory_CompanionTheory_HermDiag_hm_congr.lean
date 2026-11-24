-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermDiag.hm_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:38:12.345795+00:00
-- url     : https://prove2.me/submissions/1927df8d-09ca-4f63-aa59-ea2205490632

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
theorem _root_.solution (hinv : ∀ a, σ (σ a) = a) {h : Matrix ι ι R} (hh : Hm σ h) (p : Matrix ι ι R) :
    Hm σ (ct σ p * h * p) := by
  have hc : ct σ (ct σ p * h * p) = ct σ p * h * p := by
    have h1 : ct σ h = h := by ext i j; exact hh j i
    have h2 : ct σ (ct σ p) = p := by ext i j; exact hinv _
    rw [ct_mul, ct_mul, h1, h2, Matrix.mul_assoc]
  intro i j
  exact congrFun (congrFun hc j) i
end GlobalTheory.CompanionTheory.HermDiag
