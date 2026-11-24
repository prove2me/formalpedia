-- Prove2me | solution 1 for GlobalTheory.Square.AwayClosure.of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:57:12.48912+00:00
-- url     : https://prove2.me/submissions/8e36ebad-4f61-4a64-9512-c6dbe55ac0ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_ReductionLemmaZero
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMulPowIntegral
import Theorems.Thm_GlobalTheory_Square_IsAwayUnit_of_dvd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution {m k : ℕ} {a : 𝓞 K} (h : a ∣ (m : 𝓞 K) ^ k) :
    _root_.GlobalTheory.Square.IsAwayUnit m (a : K) :=
  _root_.GlobalTheory.Square.IsAwayUnit.of_dvd h
end _root_.GlobalTheory.Square.AwayClosure
end GlobalTheory.Square.AwayClosure
