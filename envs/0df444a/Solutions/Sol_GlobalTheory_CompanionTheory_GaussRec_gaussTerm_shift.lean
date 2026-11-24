-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GaussRec.gaussTerm_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:35:58.606219+00:00
-- url     : https://prove2.me/submissions/ac7c47b8-23a0-44ff-b79d-3d0521085780

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelShift
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_gaussTerm_mk
import Theorems.Thm_GlobalTheory_CompanionTheory_GaussRec_traceChar_mk
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_mem_lev_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_SiegLoc_psi_pow


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GaussRec
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.GaussRec
theorem _root_.solution {σ : R →+* R} {ϖ : R} (hinv : ∀ a, σ (σ a) = a) (hfix : σ ϖ = ϖ)
    {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ} (hψ : IsLevelChars σ ϖ ψ) (j : ℕ) {a : R} (ha : σ a = a)
    (x y : R) :
    gaussTerm σ ϖ hfix ψ a (j + 2) (Ideal.Quotient.mk _ x + Ideal.Quotient.mk _ (ϖ ^ (j + 1) * y))
      = gaussTerm σ ϖ hfix ψ a (j + 2) (Ideal.Quotient.mk _ x)
        * traceChar σ ϖ hfix ψ (a * σ x) (Ideal.Quotient.mk _ y) := by
  have hp := psi_pow hψ 1 (j + 1) (a * σ x * y + σ (a * σ x * y))
  rw [show 1 + (j + 1) = j + 2 by omega] at hp
  rw [← map_add, gaussTerm_mk, gaussTerm_mk, traceChar_mk, ← hp, ← AddChar.map_add_eq_mul,
    ← map_add]
  congr 1
  rw [Ideal.Quotient.eq]
  refine mem_lev_iff.2 ⟨ϖ ^ j * (a * σ y * y), ?_⟩
  simp only [map_mul, map_add, map_pow, hfix, ha, hinv]
  ring
end GlobalTheory.CompanionTheory.GaussRec
