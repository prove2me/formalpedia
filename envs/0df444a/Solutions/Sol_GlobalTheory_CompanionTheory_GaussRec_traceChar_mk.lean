-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.GaussRec.traceChar_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:27.242348+00:00
-- url     : https://prove2.me/submissions/4ae536cb-9c03-48a5-b07d-5025f8824bd1

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCardStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussSumHermitianNormLevelShift

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
theorem _root_.solution (σ : R →+* R) (ϖ : R) (hfix : σ ϖ = ϖ) (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ)
    (c y : R) :
    traceChar σ ϖ hfix ψ c (Ideal.Quotient.mk _ y)
      = ψ 1 (Ideal.Quotient.mk _ (c * y + σ (c * y))) := by
  show ψ 1 (Ideal.Quotient.mk (lev ϖ 1) c * Ideal.Quotient.mk _ y
    + barσ σ ϖ hfix 1 (Ideal.Quotient.mk (lev ϖ 1) c * Ideal.Quotient.mk _ y)) = _
  rw [← map_mul, barσ_mk, ← map_add]
end GlobalTheory.CompanionTheory.GaussRec
