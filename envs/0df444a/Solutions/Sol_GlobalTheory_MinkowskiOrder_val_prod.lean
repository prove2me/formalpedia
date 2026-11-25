-- Prove2me | solution 1 for GlobalTheory.MinkowskiOrder.val_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:07:09.029365+00:00
-- url     : https://prove2.me/submissions/080be66b-5cef-4b94-a02f-ca91cba7addb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsInvariantNatLengthLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardFiniteSubgroupGLIntDvd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.MinkowskiOrder
namespace GlobalTheory.MinkowskiOrder
theorem _root_.solution (n p l : ℕ) (hp : p.Prime) (hl : l.Prime) (hne : p ≠ l) :
    (∏ i : Fin n, (l ^ n - l ^ (i : ℕ))).factorization p
      = ∑ i ∈ Finset.range n, padicValNat p (l ^ (i + 1) - 1) := by
  haveI := Fact.mk hp
  haveI := Fact.mk hl
  have hne0 : ∀ i, i < n → l ^ n - l ^ i ≠ 0 := fun i hi =>
    Nat.sub_ne_zero_of_lt (Nat.pow_lt_pow_right hl.one_lt hi)
  rw [Fin.prod_univ_eq_prod_range (fun i => l ^ n - l ^ i) n,
    Nat.factorization_prod (fun i hi => hne0 i (Finset.mem_range.mp hi)), Finsupp.finset_sum_apply,
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have e : l ^ n - l ^ (n - 1 - i) = l ^ (n - 1 - i) * (l ^ (i + 1) - 1) := by
    rw [Nat.mul_sub, ← pow_add, mul_one]
    congr 2
    omega
  have h1 : l ^ (i + 1) - 1 ≠ 0 :=
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) hl.one_lt)
  rw [e, Nat.factorization_def _ hp, padicValNat.mul (pow_ne_zero _ hl.ne_zero) h1,
    padicValNat_prime_prime_pow _ hne, zero_add]
end GlobalTheory.MinkowskiOrder
