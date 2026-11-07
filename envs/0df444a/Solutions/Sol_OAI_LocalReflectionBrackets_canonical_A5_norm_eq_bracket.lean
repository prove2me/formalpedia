-- Prove2me | solution 1 for OAI.LocalReflectionBrackets.canonical_A5_norm_eq_bracket
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:04:13.280066+00:00
-- url     : https://prove2.me/submissions/5baf1156-c3b8-4600-a80c-114de2d8d4df

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CrossFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LocalBrackets
import Theorems.Thm_OAI_LocalReflectionBrackets_canonical_phase_norm
import Theorems.Thm_OAI_LocalReflectionBrackets_canonical_A5_normalized
import Theorems.Thm_OAI_FiniteRayExpansion_norm_char_unit


set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped Classical BigOperators
open AddChar MulChar
open scoped Classical BigOperators
open AddChar MulChar
open OAI.LocalReflectionBrackets
variable {F : Type*} [Field F] [Fintype F]
open ActualEisensteinCubic
attribute [local instance] OAI.LocalReflectionBrackets.quotientFieldNormalized
attribute [local instance] OAI.LocalReflectionBrackets.quotientFintypeNormalized
namespace OAI.LocalReflectionBrackets
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (hψ : ψ.IsPrimitive)
    (j : ℕ) (hj6 : j < 6) (σ ε : (O ⧸ P)ˣ) (x : O ⧸ P) :
    ‖activeRow (canonicalSextic P hgood) ψ j σ ε x‖ =
      ‖bracket (canonicalSextic P hgood) j x‖ := by
  rw [canonical_A5_normalized P hgood hchar ψ hψ j hj6 σ ε x,
    norm_mul, norm_mul, canonical_phase_norm P hgood hchar ψ hψ j hj6 ε,
    FiniteRayExpansion.norm_char_unit, one_mul, one_mul]
end OAI.LocalReflectionBrackets
