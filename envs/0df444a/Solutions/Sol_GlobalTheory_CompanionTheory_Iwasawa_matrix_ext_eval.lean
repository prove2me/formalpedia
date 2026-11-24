-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwasawa.matrix_ext_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:40:44.837381+00:00
-- url     : https://prove2.me/submissions/f01581cf-4740-4755-81b7-7a020131fe64

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
theorem _root_.solution {ι : Type} {n : ℕ} {X X' : Matrix (Fin n) (Fin n) (ι → ℂ)}
    (h : ∀ w, evalMat w X = evalMat w X') : X = X' := by
  ext i j w
  have := congrFun (congrFun (h w) i) j
  rwa [evalMat_apply, evalMat_apply] at this
end GlobalTheory.CompanionTheory.Iwasawa
