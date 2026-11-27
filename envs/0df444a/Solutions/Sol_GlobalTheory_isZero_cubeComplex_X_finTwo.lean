-- Prove2me | solution 1 for GlobalTheory.isZero_cubeComplex_X_finTwo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:39:25.465565+00:00
-- url     : https://prove2.me/submissions/305ad7f4-c8f2-4854-ad05-109ab4b626f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Theorems.Thm_GlobalTheory_isZero_cubeComplex_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
open GlobalTheory
variable {R : Type u} [Ring R]
namespace GlobalTheory
theorem _root_.solution (A : Cube.{v} (Fin 2) R) {p : ℕ} (h : 3 ≤ p) :
    IsZero ((cubeComplex A).X p) :=
  isZero_cubeComplex_X A (by rw [Fintype.card_fin]; omega)
end GlobalTheory
