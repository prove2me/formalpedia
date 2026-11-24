-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermDiag.herm_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:23:22.871267+00:00
-- url     : https://prove2.me/submissions/57bc4c50-b4d0-4373-8372-691287bd242a

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatrixDiagonalizable
import Theorems.Thm_GlobalTheory_CompanionTheory_HermDiag_diagble_fin

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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ),
    IsUnrQuad R σ ϖ q ε → ∀ (n : ℕ) (h : Matrix (Fin n) (Fin n) R), cT σ h = h →
    ∃ (g g' : Matrix (Fin n) (Fin n) R) (d : Fin n → R), g * g' = 1 ∧ g' * g = 1 ∧
      (∀ i, σ (d i) = d i) ∧ cT σ g * h * g = Matrix.diagonal d := by
  intro R _ σ ϖ q ε hR n h hh
  obtain ⟨g, g', d, h1, h2, h3, h4⟩ :=
    diagble_fin hR n h (fun i j => congrFun (congrFun hh j) i)
  exact ⟨g, g', d, h1, h2, h3, h4⟩
end GlobalTheory.CompanionTheory.HermDiag
