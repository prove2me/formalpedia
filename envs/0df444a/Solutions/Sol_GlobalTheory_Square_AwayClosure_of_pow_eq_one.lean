-- Prove2me | solution 1 for GlobalTheory.Square.AwayClosure.of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:57:13.258801+00:00
-- url     : https://prove2.me/submissions/7bad1744-1e3f-40de-9c47-a1c58bed4ed8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_ReductionLemmaZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMulPowIntegral
import Theorems.Thm_GlobalTheory_Square_AwayClosure_of_integral
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)
noncomputable section
open GlobalTheory GlobalTheory.Square GlobalTheory.Square.AwayClosure
variable {K : Type} [Field K] [NumberField K]
open NumberField IsDedekindDomain Finset
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Square.AwayClosure
namespace _root_.GlobalTheory.Square.AwayClosure
theorem _root_.solution (m : ℕ) {x : K} {k : ℕ} (hk : 0 < k) (h : x ^ k = 1) :
    _root_.GlobalTheory.Square.IsAwayUnit m x := by
  have hx : x ≠ 0 := by
    rintro rfl
    simp [zero_pow hk.ne'] at h
  have hxi : IsIntegral ℤ x := IsIntegral.of_pow hk (h ▸ isIntegral_one)
  have hxinv : IsIntegral ℤ x⁻¹ :=
    IsIntegral.of_pow hk (by rw [inv_pow, h, inv_one]; exact isIntegral_one)
  exact _root_.GlobalTheory.Square.AwayClosure.of_integral (k := 0) (l := 0) (a := ⟨x, hxi⟩)
    (b := ⟨x⁻¹, hxinv⟩) hx (by rw [pow_zero, mul_one]; rfl) (by rw [pow_zero, mul_one]; rfl)
end _root_.GlobalTheory.Square.AwayClosure
end GlobalTheory.Square.AwayClosure
