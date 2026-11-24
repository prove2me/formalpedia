-- Prove2me | solution 1 for GlobalTheory.WeylInt.intQ_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:28.516261+00:00
-- url     : https://prove2.me/submissions/36d51a55-85a0-4b0b-8f0a-f7708a12c6cf

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LowerTriIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.WeylInt
open Formalism.GradedWeylDivisibility
namespace GlobalTheory.WeylInt
theorem _root_.solution (r n : ℕ) (P : MvPolynomial (Fin r × Fin n) ℤ) :
    intQ r n P = MvPolynomial.map (Int.castRingHom ℚ) P := rfl
end GlobalTheory.WeylInt
