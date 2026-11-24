-- Prove2me | solution 1 for GlobalTheory.sum_neg_one_pow_hdim_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:40:13.032635+00:00
-- url     : https://prove2.me/submissions/8a121560-1600-4b4d-9f72-27f546679e9a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Theorems.Thm_GlobalTheory_ExactSeq_sum_neg_one_pow_finrank_eq_add
import Theorems.Thm_GlobalTheory_cohOn_sum_neg_one_pow_finrank_eq_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Module
universe t v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}
variable (k : Type v) [Field k] [Algebra k Γ(X, ⊤)]
  {S : ShortComplex X.Modules} (hS : S.ShortExact)
include hS
namespace GlobalTheory
theorem _root_.solution (N : ℕ) (h₁ : ∀ i < N, Module.Finite k (coh S.X₁ i))
    (h₃ : ∀ i < N, Module.Finite k (coh S.X₃ i)) (hN : Subsingleton (coh S.X₁ N)) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * hdim k S.X₂ i =
      ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * hdim k S.X₁ i +
        ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * hdim k S.X₃ i :=
  cohOn.sum_neg_one_pow_finrank_eq_add hS ⊤ k N h₁ h₃ (Function.injective_of_subsingleton _)
end GlobalTheory
