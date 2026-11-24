-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermDiag.exists_pivot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:28:05.907638+00:00
-- url     : https://prove2.me/submissions/df258426-3387-4896-8ef1-68cd6a4f707b

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatrixDiagonalizable
import Theorems.Thm_GlobalTheory_CompanionTheory_HermDiag_ct_one
import Theorems.Thm_GlobalTheory_CompanionTheory_HermDiag_pivot_offdiag

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
theorem _root_.solution (hR : IsUnrQuad R σ ϖ q ε) {h : Matrix ι ι R} (hh : Hm σ h) {i j : ι}
    (hy : h i j ∉ lev ϖ 1) :
    ∃ (k : ι) (p p' : Matrix ι ι R), p * p' = 1 ∧ p' * p = 1 ∧
      (ct σ p * h * p) k k ∉ lev ϖ 1 := by
  by_cases h1 : ∃ k, h k k ∉ lev ϖ 1
  · obtain ⟨k, hk⟩ := h1
    exact ⟨k, 1, 1, by simp, by simp, by simpa [ct_one] using hk⟩
  · push_neg at h1
    have hij : i ≠ j := by
      rintro rfl
      exact hy (h1 i)
    obtain ⟨p, p', a, b, c⟩ := pivot_offdiag hR hh hij (h1 i) (h1 j) hy
    exact ⟨i, p, p', a, b, c⟩
end GlobalTheory.CompanionTheory.HermDiag
