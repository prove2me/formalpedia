-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegLoc.gauss1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:59:04.60748+00:00
-- url     : https://prove2.me/submissions/65e6c6e6-2afa-48ae-b32d-afceef43e14b

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
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_mk_lft
import Theorems.Thm_GlobalTheory_T_gauss_sum_hermitian_norm_level_one
import Theorems.Thm_GlobalTheory_T_gauss_sum_hermitian_norm_level_shift
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
theorem _root_.solution {R : Type} [CommRing R] {σ : R →+* R} {ϖ : R} {q : ℕ} {ε : ℤ} (hR : IsUnrQuad R σ ϖ q ε)
    [∀ k, Fintype (R ⧸ lev ϖ k)] {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ)
    (hε : (ε : ℂ) ^ 2 = 1) (j : ℕ) (a : R) (ha : σ a = a) (ha' : a ∉ lev ϖ 1) :
    (∑ w : R ⧸ lev ϖ j, ψ j (Ideal.Quotient.mk (lev ϖ j) a * (barσ σ ϖ hR.fix_ϖ j w * w))) = ((ε : ℂ) * q) ^ j := by
  induction j using Nat.twoStepInduction with
  | zero =>
    have : Subsingleton (R ⧸ lev ϖ 0) := Ideal.Quotient.subsingleton_iff.2 (by simp [lev])
    rw [Fintype.sum_subsingleton _ 0]
    simp
  | one => simpa using GlobalTheory.T.gauss_sum_hermitian_norm_level_one R σ ϖ q ε hR ψ hψ a ha ha'
  | more j ih _ =>
    rw [GlobalTheory.T.gauss_sum_hermitian_norm_level_shift R σ ϖ q ε hR ψ hψ j a ha ha', ih, pow_add, mul_pow (ε : ℂ) (q : ℂ) 2, hε]
    ring
end GlobalTheory.CompanionTheory.SiegLoc
