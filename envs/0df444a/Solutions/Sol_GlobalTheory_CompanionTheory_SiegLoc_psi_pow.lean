-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegLoc.psi_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:42.294578+00:00
-- url     : https://prove2.me/submissions/42b1a004-6320-4bf2-876d-07b474c29711

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FixedNondeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory.PfSWUS.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegLoc
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.SiegLoc
theorem _root_.solution {σ : R →+* R} {ϖ : R} {ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ}
    (hψ : IsLevelChars σ ϖ ψ) (k j : ℕ) (a : R) :
    ψ (k + j) (Ideal.Quotient.mk _ (ϖ ^ j * a)) = ψ k (Ideal.Quotient.mk _ a) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← ih, ← Nat.add_assoc, pow_succ', mul_assoc]
    exact hψ.compat (k + j) (ϖ ^ j * a)
end GlobalTheory.CompanionTheory.SiegLoc
