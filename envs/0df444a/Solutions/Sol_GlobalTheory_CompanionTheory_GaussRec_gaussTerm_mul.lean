-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GaussRec.gaussTerm_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:35:57.749001+00:00
-- url     : https://prove2.me/submissions/85025a60-bd4b-4b9c-9983-bc1029b86ba9

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelShift
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_gaussTerm_mk
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_mk_lft
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_psi_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.GaussRec.mk_lft

set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GaussRec
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.GaussRec
theorem _root_.solution {σ : R →+* R} {ϖ : R} (hfix : σ ϖ = ϖ)
    {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ) (j : ℕ) (a x : R) :
    gaussTerm σ ϖ hfix ψ a (j + 2) (Ideal.Quotient.mk _ (ϖ * x))
      = gaussTerm σ ϖ hfix ψ a j (Ideal.Quotient.mk _ x) := by
  rw [gaussTerm_mk, gaussTerm_mk, ← psi_pow hψ j 2 (a * (σ x * x))]
  congr 2
  simp only [map_mul, hfix]
  ring
end GlobalTheory.CompanionTheory.GaussRec
