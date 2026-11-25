-- Prove2me | solution 1 for GlobalTheory.T.matrixFamilyBilateralSubstitution_comp_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:24:42.830521+00:00
-- url     : https://prove2.me/submissions/2bb8c496-e317-4df7-839b-e33c90e83868

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixFamilyBilateralSubstitutionCompEqMul
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TotalDegreeSubstFLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixFamilyBilateralSubstitutionCompEqMulStatement
import Theorems.Thm_GlobalTheory_CompactHowe_substF_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {ι : Type} {N n : ℕ} (h h' : ι → Matrix (Fin N) (Fin N) ℂ) (g g' : ι → Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin N × Fin n) ℂ), GlobalTheory.CompactHowe.substF h g (GlobalTheory.CompactHowe.substF h' g' P) = GlobalTheory.CompactHowe.substF (h * h') (g * g') P := by
  first | exact @GlobalTheory.CompactHowe.substF_mul | exact GlobalTheory.CompactHowe.substF_mul | (intros; apply GlobalTheory.CompactHowe.substF_mul <;> assumption)
end _root_.GlobalTheory.T
