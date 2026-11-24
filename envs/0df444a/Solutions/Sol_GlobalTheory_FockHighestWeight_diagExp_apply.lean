-- Prove2me | solution 1 for GlobalTheory.FockHighestWeight.diagExp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:22.861068+00:00
-- url     : https://prove2.me/submissions/c3e319d8-56bb-4ed6-bcb5-5d88dacb725e

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LowerTriOfInterlaced

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open GlobalTheory GlobalTheory.FockHighestWeight
variable {r n : ℕ}
namespace GlobalTheory.FockHighestWeight
theorem _root_.solution (ν : Fin n → ℕ) (a : Fin r) (s : Fin n) :
    diagExp r ν (a, s) = if a.val = s.val then ν s else 0 := rfl
end GlobalTheory.FockHighestWeight
