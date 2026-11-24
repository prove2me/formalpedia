-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.UnrDens.HenselStep.gram_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:52:00.811312+00:00
-- url     : https://prove2.me/submissions/21eedeff-176d-461c-8ce6-71e3eef12e35

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResidueAlgebraUnramified
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardFibreGramDifferential
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedQuotientCard
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnimodularHermitianRepsCountSucc
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_cT_add
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_HenselStep_cT_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_GramDiff_cT_smul


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
theorem _root_.solution (σ : R →+* R) {r : R} (hc : σ r = r) (S : Matrix (Fin a) (Fin a) R)
    (x y : Matrix (Fin a) (Fin b) R) :
    cT σ (x + r • y) * S * (x + r • y) =
      cT σ x * S * x + r • (cT σ y * S * x + cT σ x * S * y) + (r * r) • (cT σ y * S * y) := by
  rw [cT_add, cT_smul, hc]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
  abel
end GlobalTheory.CompanionTheory.UnrDens.HenselStep
