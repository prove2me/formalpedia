-- Prove2me | solution 1 for GlobalTheory.TateFree.surjective_of_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:24:33.742571+00:00
-- url     : https://prove2.me/submissions/ad7d0dea-bfd2-4836-aad1-994748bce66d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsCounitEqOneMulEqZeroOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvEqOneOfForallPairing
import Theorems.Thm_GlobalTheory_TateFree_mem_pow_smul_top_iff
import Theorems.Thm_GlobalTheory_isPrecomplete_of_finite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module
open GlobalTheory
open GlobalTheory.TateFree
variable {p : ℕ} [Fact p.Prime] {M N : Type} [AddCommGroup M] [Module ℤ_[p] M] [AddCommGroup N]
  [Module ℤ_[p] N]
namespace GlobalTheory.TateFree
theorem _root_.solution (f : M →ₗ[ℤ_[p]] N) [Module.Finite ℤ_[p] M]
    (hN : ∀ y : N, (∀ n, ∃ z, (p : ℤ_[p]) ^ n • z = y) → y = 0)
    (h : ∀ y, ∃ x z, (p : ℤ_[p]) • z = y - f x) : Function.Surjective f := by
  have := isPrecomplete_of_finite (IsLocalRing.maximalIdeal ℤ_[p]) M
  have : IsHausdorff (IsLocalRing.maximalIdeal ℤ_[p]) N := ⟨fun y hy => hN y fun n =>
    (mem_pow_smul_top_iff n y).1 (SModEq.zero.1 (hy n))⟩
  refine surjective_of_mkQ_comp_surjective (I := IsLocalRing.maximalIdeal ℤ_[p]) fun y => ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨x, z, hz⟩ := h y
  refine ⟨x, ((Submodule.Quotient.eq _).2 ?_).symm⟩
  have := (mem_pow_smul_top_iff 1 (y - f x)).2 ⟨z, by rw [pow_one, hz]⟩
  rwa [pow_one] at this
end GlobalTheory.TateFree
