-- Prove2me | solution 1 for GlobalTheory.DiagonalTimesLowerTriangular.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:43:43.512921+00:00
-- url     : https://prove2.me/submissions/43082786-8b39-4f9e-9090-226057aa459d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiagMulOfLower
import Theorems.Thm_GlobalTheory_DiagonalTimesLowerTriangular_diag_mul_of_lower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DiagonalTimesLowerTriangular
namespace GlobalTheory.DiagonalTimesLowerTriangular
theorem _root_.solution : ∀ {K : Type} [inst : CommRing K] {s : ℕ} {a b : Matrix (Fin s) (Fin s) K}, (∀ (i j : Fin s), i < j → a i j = (0 : K)) → (∀ (i j : Fin s), i < j → b i j = (0 : K)) → ∀ (i : Fin s), (a * b) i i = a i i * b i i :=
  fun ha hb => diag_mul_of_lower ha hb
end GlobalTheory.DiagonalTimesLowerTriangular
