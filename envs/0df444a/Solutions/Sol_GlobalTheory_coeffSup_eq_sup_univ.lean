-- Prove2me | solution 1 for GlobalTheory.coeffSup_eq_sup_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:31:48.842183+00:00
-- url     : https://prove2.me/submissions/faaad5db-6c75-4c0b-9f22-846cb6929b43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TensorContentEqPolyContentScalarCoeffs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
noncomputable section
open scoped NNReal TensorProduct
variable {ι M Γ₀ : Type*} [Zero M] [LinearOrderedCommMonoidWithZero Γ₀]
variable {N : M → Γ₀}
namespace GlobalTheory
theorem _root_.solution [Fintype ι] (h0 : N 0 = 0) (c : ι →₀ M) :
    coeffSup N c = Finset.univ.sup fun i => N (c i) :=
  eq_of_forall_ge_iff fun γ => by simp [coeffSup_le_iff h0]
end GlobalTheory
