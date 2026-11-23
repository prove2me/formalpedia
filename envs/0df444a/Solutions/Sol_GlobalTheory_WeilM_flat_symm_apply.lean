-- Prove2me | solution 1 for GlobalTheory.WeilM.flat_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:07.926828+00:00
-- url     : https://prove2.me/submissions/519fee8e-9055-4772-b207-697ffe599b75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSplittingSplitOm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped NNReal Kronecker
open GlobalTheory GlobalTheory.WeilM
variable {R : Type} [CommRing R]
variable {α β κ : Type}
namespace GlobalTheory.WeilM
theorem _root_.solution (σ : κ ≃ α × β) (u : κ → R) (i : α) (j : β) : (flat σ).symm u i j = u (σ.symm (i, j)) := rfl
end GlobalTheory.WeilM
