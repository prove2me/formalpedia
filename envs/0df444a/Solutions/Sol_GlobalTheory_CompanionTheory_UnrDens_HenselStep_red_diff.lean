-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.HenselStep.red_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:52:01.703917+00:00
-- url     : https://prove2.me/submissions/3004d9c9-2e83-4cfd-9a55-127edd9db7d3

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResidueAlgebraUnramified
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFibreGramDifferential
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCard
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHermitianRepsCountSucc
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_red_add
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_red_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_red_cT

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
variable {σ : R →+* R} {ϖ : R}
namespace GlobalTheory.CompanionTheory.UnrDens.HenselStep
theorem _root_.solution (hf : σ ϖ = ϖ) (S : Matrix (Fin a) (Fin a) R) (x y : Matrix (Fin a) (Fin b) R) :
    red ϖ 1 (cT σ y * S * x + cT σ x * S * y) =
      cT (barσ σ ϖ hf 1) (red ϖ 1 y) * red ϖ 1 S * red ϖ 1 x +
        cT (barσ σ ϖ hf 1) (red ϖ 1 x) * red ϖ 1 S * red ϖ 1 y := by
  simp only [red_add, red_mul, red_cT σ ϖ hf]
end GlobalTheory.CompanionTheory.UnrDens.HenselStep
