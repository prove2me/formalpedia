-- Prove2me | solution 1 for GlobalTheory.RowSpan.exists_weight_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:27:10.174494+00:00
-- url     : https://prove2.me/submissions/5a69eb7b-8449-42f8-8c2c-d87d42e2462f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_InvariantOperatorValueTriangularChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_EqZeroOfFischSelf
import Theorems.Thm_GlobalTheory_RowSpan_weight_lt_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowSpan
open MvPolynomial Formalism.L2.Pj
variable {T : Type} {r : T → ℕ} {n : ℕ} {k : Type} [Field k]
variable {σ : Type} (w : σ → ℕ)
namespace GlobalTheory.RowSpan
theorem _root_.solution (f : MvPolynomial σ k →ₐ[k] MvPolynomial σ k)
    (hf : ∀ ℓ, ∀ m ∈ (f (X ℓ) - X ℓ).support, Finsupp.weight w m < w ℓ) (P : MvPolynomial σ k) :
    ∀ m' ∈ (f P - P).support, ∃ m ∈ P.support, Finsupp.weight w m' < Finsupp.weight w m := by
  classical
  intro m' hm'
  have e : f P - P = ∑ m ∈ P.support, P.coeff m • (f (monomial m 1) - monomial m 1) := by
    nth_rewrite 1 [P.as_sum]
    nth_rewrite 3 [P.as_sum]
    rw [map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_sub, ← map_smul, smul_monomial, smul_eq_mul, mul_one]
  rw [e] at hm'
  obtain ⟨m, hm, h⟩ := Finset.mem_biUnion.1 (support_sum hm')
  exact ⟨m, hm, weight_lt_monomial w f hf m m' (support_smul h)⟩
end GlobalTheory.RowSpan
