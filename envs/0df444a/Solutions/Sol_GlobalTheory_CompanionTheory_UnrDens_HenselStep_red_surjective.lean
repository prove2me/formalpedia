-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.HenselStep.red_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:52:02.831138+00:00
-- url     : https://prove2.me/submissions/b44b16af-fb38-46d2-9805-a0601b8a9ba0

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
theorem _root_.solution (ϖ : R) (k : ℕ) :
    Function.Surjective (red ϖ k : Matrix (Fin a) (Fin b) R → _) := fun t =>
  ⟨fun i j => Function.surjInv Ideal.Quotient.mk_surjective (t i j), by
    ext i j; exact Function.surjInv_eq _ _⟩
end GlobalTheory.CompanionTheory.UnrDens.HenselStep
