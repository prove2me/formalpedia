-- Prove2me | solution 1 for GlobalTheory.PDivGroup.exists_primitive_system
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:31:56.234874+00:00
-- url     : https://prove2.me/submissions/211faaf5-86dd-4da7-80b6-de40754f5f3c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
import Theorems.Thm_GlobalTheory_PDivGroup_tateLevel_apply
import Theorems.Thm_GlobalTheory_PDivGroup_pt_surjective
import Theorems.Thm_GlobalTheory_AugCot_baseChangeAug_tmul
import Theorems.Thm_GlobalTheory_AugCot_baseChangeEquiv_tmul_d
import Theorems.Thm_GlobalTheory_AugCot_mvPolynomialBasis_apply
import Theorems.Thm_GlobalTheory_IsBicharacter_one
import Theorems.Thm_GlobalTheory_PDivGroup_muLieGen_dlogT
import Theorems.Thm_GlobalTheory_PDiv_digit_zero
import Theorems.Thm_GlobalTheory_PDiv_muChar_muT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.AugCot.baseChangeAug_tmul
attribute [local simp] GlobalTheory.AugCot.baseChangeEquiv_tmul_d
attribute [local simp] GlobalTheory.AugCot.mvPolynomialBasis_apply
attribute [local simp] GlobalTheory.PDiv.digit_zero
attribute [local simp] GlobalTheory.PDiv.muChar_muT
attribute [local simp] GlobalTheory.PDivGroup.muLieGen_dlogT


attribute [local simp] GlobalTheory.PDivGroup.tateLevel_apply

set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
open GlobalTheory
open GlobalTheory.PDivGroup
open PDiv TateFree
variable {p : ℕ} {O : Type} [CommRing O] (G : PDivGroup p O)
variable (C : Type) [Field C] [Algebra O C] [IsIntegrallyClosedIn O C] [IsAlgClosed C]
  [CharZero C]
include C
variable [Fact p.Prime]
variable (p O)
namespace GlobalTheory.PDivGroup
theorem _root_.solution : ∃ ζ : ℕ → O, ζ 0 = 1 ∧ (∀ n, ζ (n + 1) ^ p = ζ n) ∧
    ∀ n, IsPrimitiveRoot (ζ n) (p ^ n) := by
  have hp : p.Prime := Fact.out
  have hi : Function.Injective (algebraMap O C) := IsIntegralClosure.algebraMap_injective O O C
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C p
  obtain ⟨η, rfl⟩ := IsIntegrallyClosedIn.isIntegral_iff.1
    ((hξ.isIntegral hp.pos).tower_top (A := O))
  have hη : IsPrimitiveRoot η p := hξ.of_map_of_injective hi
  obtain ⟨t, ht⟩ := (mu p O).pt_surjective C 1
    (muPoint O η (by rw [pow_one]; exact hη.pow_eq_one))
  have h1 : muRoot t 1 = η := (DFunLike.congr_fun ht _).trans (muPoint_muT _ _)
  have h2 : ∀ n, muRoot t (n + 1) ^ p ^ n = η := fun n => by
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ', pow_mul, muRoot_succ_pow, ih]
  refine ⟨muRoot t, by simpa using muRoot_pow_self t 0, muRoot_succ_pow t, fun n => ?_⟩
  cases n with
  | zero => rw [show muRoot t 0 = 1 by simpa using muRoot_pow_self t 0, pow_zero]; exact .one
  | succ n =>
    have := (algebraMap O C).domain_nontrivial
    rw [← orderOf_eq_prime_pow (by rw [h2]; exact hη.ne_one hp.one_lt) (muRoot_pow_self t (n + 1))]
    exact IsPrimitiveRoot.orderOf _
end GlobalTheory.PDivGroup
