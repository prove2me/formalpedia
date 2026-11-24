-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.HenselStep.cT_cT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:51:56.963484+00:00
-- url     : https://prove2.me/submissions/ef27b93e-fdfe-4c16-bef0-faa4cd91c50b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResidueAlgebraUnramified
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFibreGramDifferential
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCard
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHermitianRepsCountSucc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.HenselStep
variable {R : Type} [CommRing R] {a b c : ℕ}
namespace GlobalTheory.CompanionTheory.UnrDens.HenselStep
theorem _root_.solution (σ : R →+* R) (h : ∀ r, σ (σ r) = r) (x : Matrix (Fin a) (Fin b) R) :
    cT σ (cT σ x) = x := by
  ext i j; simp [cT, h]
end GlobalTheory.CompanionTheory.UnrDens.HenselStep
