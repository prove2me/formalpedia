-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermDiag.pivot_offdiag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:11:55.641536+00:00
-- url     : https://prove2.me/submissions/ee7fdd86-aae4-43a7-aab8-3733ed7f67ea

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatrixDiagonalizable
import Theorems.Thm_GlobalTheory_CompanionTheory_HermDiag_exists_trace
import Theorems.Thm_GlobalTheory_CompanionTheory_HermDiag_ct_transvection

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
    (hij : i ≠ j) (hi : h i i ∈ lev ϖ 1) (hj : h j j ∈ lev ϖ 1) (hy : h i j ∉ lev ϖ 1) :
    ∃ p p' : Matrix ι ι R, p * p' = 1 ∧ p' * p = 1 ∧ (ct σ p * h * p) i i ∉ lev ϖ 1 := by
  obtain ⟨s, hs⟩ := exists_trace hR hy
  refine ⟨Matrix.transvection j i s, Matrix.transvection j i (-s), ?_, ?_, ?_⟩
  · rw [Matrix.transvection_mul_transvection_same _ _ hij.symm]; simp
  · rw [Matrix.transvection_mul_transvection_same _ _ hij.symm]; simp
  · rw [ct_transvection, Matrix.mul_transvection_apply_same, Matrix.transvection_mul_apply_same,
      Matrix.transvection_mul_apply_same]
    intro hmem
    apply hs
    have : s * h i j + σ (s * h i j) =
        (h i i + σ s * h j i + s * (h i j + σ s * h j j)) - h i i - s * σ s * h j j := by
      rw [map_mul, hh i j]; ring
    rw [this]
    exact Ideal.sub_mem _ (Ideal.sub_mem _ hmem hi) (Ideal.mul_mem_left _ _ hj)
end GlobalTheory.CompanionTheory.HermDiag
