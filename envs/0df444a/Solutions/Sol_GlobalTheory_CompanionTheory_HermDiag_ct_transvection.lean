-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermDiag.ct_transvection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:38:12.481091+00:00
-- url     : https://prove2.me/submissions/6ab695c7-b1b5-4a1c-a060-c0cfa57e3b2f

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
variable {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ}
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.HermDiag
theorem _root_.solution (i j : ι) (s : R) :
    ct σ (Matrix.transvection j i s) = Matrix.transvection i j (σ s) := by
  unfold ct Matrix.transvection
  ext a b
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, map_add,
    Matrix.one_apply, Matrix.single_apply]
  by_cases hab : a = b
  · subst hab
    by_cases h1 : j = a ∧ i = a
    · obtain ⟨rfl, rfl⟩ := h1; simp
    · have h2 : ¬ (i = a ∧ j = a) := fun h => h1 ⟨h.2, h.1⟩
      simp [h1, h2]
  · have hba : ¬ b = a := fun h => hab h.symm
    by_cases h1 : j = b ∧ i = a
    · have h2 : i = a ∧ j = b := ⟨h1.2, h1.1⟩
      simp [hab, hba, h1, h2]
    · have h2 : ¬ (i = a ∧ j = b) := fun h => h1 ⟨h.2, h.1⟩
      simp [hab, hba, h1, h2]
end GlobalTheory.CompanionTheory.HermDiag
