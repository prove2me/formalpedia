-- Prove2me | solution 1 for GlobalTheory.CMVal.TermUnit.term_unit_and_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:55:08.823171+00:00
-- url     : https://prove2.me/submissions/6e5ddffc-b874-40d6-a793-1d4d1c0819aa

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdNormSq
import Theorems.Thm_GlobalTheory_CMVal_TermUnit_term_unit
import Theorems.Thm_GlobalTheory_CMVal_TermUnit_norm_term
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub


section
open NumberField IsDedekindDomain GlobalTheory.CMVal
namespace GlobalTheory.CMVal.TermUnit
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
private theorem term_mul' (φ : I → E →+* ℂ) (k : ℕ) (κ : I → ℕ) (σ : ℂ) (y x : E) :
    term φ k κ σ (y * x) = term φ k κ σ y * term φ k κ σ x := by
  simp only [term, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [map_mul, mul_inv, norm_mul, mul_pow]
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
  ring
end GlobalTheory.CMVal.TermUnit
end

set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.TermUnit
variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]
namespace GlobalTheory.CMVal.TermUnit
theorem _root_.solution (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (h : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (x : E) :
    (∀ u : (OF E)ˣ, term φ (2 * s) κ σ (algebraMap (OF E) E u * x) = term φ (2 * s) κ σ x) ∧
      (x ≠ 0 → ‖term φ (2 * s) κ σ x‖ = |(Algebra.norm ℚ x : ℝ)| ^ (-((s : ℝ) + σ.re))) := by
  refine ⟨fun u => ?_, fun hx => norm_term h s κ σ hx⟩
  rw [term_mul', term_unit h s κ σ u, one_mul]
end GlobalTheory.CMVal.TermUnit
