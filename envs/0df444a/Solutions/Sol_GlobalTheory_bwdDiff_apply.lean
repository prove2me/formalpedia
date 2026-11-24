-- Prove2me | solution 1 for GlobalTheory.bwdDiff_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:38:39.964147+00:00
-- url     : https://prove2.me/submissions/0d0dcf25-926e-4ea3-8d2c-7b91a7c1b228

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
variable {G M : Type*} [AddCommGroup G] [AddCommGroup M]
namespace GlobalTheory
theorem _root_.solution (g : G) (φ : G → M) (x : G) : bwdDiff g φ x = φ x - φ (x - g) := rfl
end GlobalTheory
