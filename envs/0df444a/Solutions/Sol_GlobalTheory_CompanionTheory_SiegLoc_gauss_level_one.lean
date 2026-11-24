-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegLoc.gauss_level_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:34:01.239685+00:00
-- url     : https://prove2.me/submissions/a6d17506-3de0-42a9-a85d-334f4ef91a8d

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResidueAlgebraUnramifiedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelOne
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_GaussOne_gauss_core
import Theorems.Thm_GlobalTheory_T_residue_algebra_unramified


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc
namespace GlobalTheory.CompanionTheory.SiegLoc
theorem _root_.solution : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ)
    (hR : IsUnrQuad R σ ϖ q ε) [∀ k, Fintype (R ⧸ lev ϖ k)] (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ),
    IsLevelChars σ ϖ ψ → ∀ (a : R), σ a = a → a ∉ lev ϖ 1 →
    (∑ w : R ⧸ lev ϖ 1, ψ 1 (Ideal.Quotient.mk (lev ϖ 1) a * (barσ σ ϖ hR.fix_ϖ 1 w * w))) =
      (ε : ℂ) * q := by
  intro R _ σ ϖ q ε hR _ ψ hψ a ha hna
  have hex : ∃ b, σ b = b ∧ ψ 1 (Ideal.Quotient.mk _ (a * b)) ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hna (hψ.prim a ha hcon)
  obtain ⟨b, hb, hχ⟩ := hex
  refine GaussOne.gauss_core (GlobalTheory.T.residue_algebra_unramified R σ ϖ q ε hR) (ψ 1) _ (Ideal.Quotient.mk _ b) ?_ ?_
  · rw [barσ_mk, hb]
  · rwa [← map_mul]
end GlobalTheory.CompanionTheory.SiegLoc
