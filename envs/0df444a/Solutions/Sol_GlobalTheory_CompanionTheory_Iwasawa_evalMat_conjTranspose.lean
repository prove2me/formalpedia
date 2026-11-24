-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwasawa.evalMat_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:41:03.391916+00:00
-- url     : https://prove2.me/submissions/3f3c071a-2f16-4c7c-9efc-4b43fb268c0f

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaChol
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUpperMulUnitaryComplex
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwasawa_evalMat_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwasawa
namespace GlobalTheory.CompanionTheory.Iwasawa
theorem _root_.solution {ι : Type} {n : ℕ} (w : ι) (X : Matrix (Fin n) (Fin n) (ι → ℂ)) :
    evalMat w Xᴴ = (evalMat w X)ᴴ := by
  ext i j
  simp only [evalMat_apply, Matrix.conjTranspose_apply]
  rfl
end GlobalTheory.CompanionTheory.Iwasawa
