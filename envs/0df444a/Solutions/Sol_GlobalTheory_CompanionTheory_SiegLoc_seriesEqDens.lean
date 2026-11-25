-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegLoc.seriesEqDens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:35:16.666281+00:00
-- url     : https://prove2.me/submissions/ea767028-dca5-474b-ab6b-a681b8b8e4ff

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianMatrixDiagonalizableStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelShiftStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelOneStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardRangeMulQuotientBoundedLevelStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MatrixGaussSumDiagonalFactorStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MatrixGaussSumCongrInvarianceStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicityReductionDiagonalProdStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianCharacterOrthogonalityStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianRepCountFourierExpansionStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SeriesEqDens
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_gauss_full
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_mk_lft
import Theorems.Thm_GlobalTheory_T_hermitian_character_orthogonality
import Theorems.Thm_GlobalTheory_T_hermitian_rep_count_fourier_expansion
import Theorems.Thm_GlobalTheory_T_unramified_quotient_card
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.GaussRec.mk_lft



set_option autoImplicit false
noncomputable section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc
namespace GlobalTheory.CompanionTheory.SiegLoc
theorem _root_.solution : SeriesEqDens := by
  intro R _ σ ϖ q ε hR ψ hψ m n _ S T hS hT α hα
  have hfin : ∀ k, Finite (R ⧸ lev ϖ k) := fun k => Nat.finite_of_card_ne_zero (by
    rw [GlobalTheory.T.unramified_quotient_card R σ ϖ q ε hR k]
    have := hR.one_lt
    exact pow_ne_zero _ (by omega))
  letI : ∀ k, Fintype (R ⧸ lev ϖ k) := fun k => Fintype.ofFinite _
  have hε : (ε : ℂ) ^ 2 = 1 := by
    rcases hR.eps with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  have : siegAt ϖ σ ψ q ε m T = fun k => ((densAt σ ϖ S T k : ℝ) : ℂ) := funext fun k =>
    GlobalTheory.T.hermitian_rep_count_fourier_expansion R σ ϖ q ε hR ψ hψ m n k S T hS.1 hT.1 (GlobalTheory.T.hermitian_character_orthogonality R σ ϖ q ε hR ψ hψ n k)
      (fun B hB => gauss_full hR hψ hε k S hS B hB)
  rw [this]
  exact (Complex.continuous_ofReal.tendsto α).comp hα
end GlobalTheory.CompanionTheory.SiegLoc
