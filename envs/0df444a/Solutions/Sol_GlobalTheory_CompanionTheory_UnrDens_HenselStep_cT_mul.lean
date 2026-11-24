-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.HenselStep.cT_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:51:57.978801+00:00
-- url     : https://prove2.me/submissions/5b7fdefc-a6d7-4039-bcc1-a94d0b77c40d

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
theorem _root_.solution (σ : R →+* R) (x : Matrix (Fin a) (Fin b) R) (y : Matrix (Fin b) (Fin c) R) :
    cT σ (x * y) = cT σ y * cT σ x := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]
end GlobalTheory.CompanionTheory.UnrDens.HenselStep
