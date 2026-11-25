-- Prove2me | solution 1 for GlobalTheory.Sandwich.HodgeTateBound.mul_swap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:12:18.619349+00:00
-- url     : https://prove2.me/submissions/ac115e5f-b3c7-4b70-9c33-ed376c2e653f

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FontaineAinfLocalDomainXiAdicOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SmulMemRange
import Theorems.Thm_GlobalTheory_Sandwich_HodgeTateBound_right_cancel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh.Up GlobalTheory.Sandwich Matrix
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.Sandwich.HodgeTateBound
variable {A O : Type} [CommRing A] [CommRing O] {h : ℕ}
namespace GlobalTheory.Sandwich.HodgeTateBound
theorem _root_.solution [IsDomain A] {F G : Matrix (Fin h) (Fin h) A} {μ : A} (hμ : μ ≠ 0)
    (hGF : G * F = μ • (1 : Matrix (Fin h) (Fin h) A)) :
    F * G = μ • (1 : Matrix (Fin h) (Fin h) A) := by
  apply right_cancel hμ hGF
  rw [Matrix.mul_assoc, hGF]
  simp
end GlobalTheory.Sandwich.HodgeTateBound
