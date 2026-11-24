-- Prove2me | solution 1 for GlobalTheory.Square.AwayClosure.of_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:13:55.947836+00:00
-- url     : https://prove2.me/submissions/d6fc15be-f7cc-4dcf-823f-676d68e23d97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_ReductionLemmaZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMulPowIntegral
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
theorem _root_.solution {m k l : ℕ} {x : K} (hx : x ≠ 0) {a b : 𝓞 K}
    (ha : x * (m : K) ^ k = a) (hb : x⁻¹ * (m : K) ^ l = b) : _root_.GlobalTheory.Square.IsAwayUnit m x := by
  have hab : ((m : K)) ^ (k + l) = (a : K) * (b : K) := by
    rw [← ha, ← hb, pow_add]
    field_simp
  refine ⟨a, k, k + l, ⟨b, RingOfIntegers.coe_injective ?_⟩, ha⟩
  simpa using hab
end _root_.GlobalTheory.Square.AwayClosure
end GlobalTheory.Square.AwayClosure
