-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.repr_apply_of_semilinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:08:45.729725+00:00
-- url     : https://prove2.me/submissions/c4b629a8-8f63-45be-8148-42bebda56a98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L M G ι : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup M] [Module L M]
namespace GlobalTheory.GaloisDescent
theorem _root_.solution (s : L →+* L) (b : Basis ι L M) (φ : M →+ M)
    (hφ : ∀ a i, φ (a • b i) = s a • b i) (w : M) (i : ι) :
    b.repr (φ w) i = s (b.repr w i) := by
  classical
  conv_lhs => rw [← b.linearCombination_repr w, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum, map_sum]
  simp only [hφ, map_smul, Basis.repr_self, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finsupp.mem_support_iff]
  split_ifs with h
  · rfl
  · rw [not_not.1 h, map_zero]
end GlobalTheory.GaloisDescent
