-- Prove2me | solution 1 for OAI.CompletedGauss.reflectedBranch_normalized_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:32:59.10421+00:00
-- url     : https://prove2.me/submissions/b9f5eb4f-00b2-483f-9ea1-e3786ebc8bd9

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_NormalizedMass
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectedBranches
import Theorems.Thm_OAI_CompletedGauss_reflectedBranch_norm_bound
import Theorems.Thm_OAI_CompletedGauss_reflectionExtractedDivisor_ne_zero

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
open scoped BigOperators
open scoped BigOperators Classical
open OAI.CompletedGauss
open ActualEisensteinCubic LocalReflectionBrackets
namespace OAI.CompletedGauss
theorem _root_.solution {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (n b : O) (U B : ℝ) (hU : 0<U) (hB : 0<B) :
    ‖reflectedBranch P hg j e n b‖ /
      (Real.sqrt ((Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*U)*
        ((Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)*B)) ≤
      1/(Real.sqrt U*B*Real.sqrt ((Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
        (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ))) := by
  have hn (v : Fin 3) : 0<(Ideal.absNorm (reflectionExtractedDivisor P j e v):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) j e v
      (Ideal.absNorm_eq_zero_iff.mp hz))
  have hs (v : Fin 3) : 0<Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e v):ℝ) := Real.sqrt_pos.mpr (hn v)
  have hsu : 0<Real.sqrt U := Real.sqrt_pos.mpr hU
  apply (div_le_div_of_nonneg_right (reflectedBranch_norm_bound P hg j e n b) (by positivity)).trans
  rw [Real.sqrt_mul (hn 1).le,Real.sqrt_mul (hn 0).le]
  have he := Real.sq_sqrt (hn 2).le
  apply le_of_eq
  field_simp [(hs 0).ne', (hs 1).ne', (hs 2).ne', (hn 2).ne', hsu.ne', hB.ne']
  nlinarith
end OAI.CompletedGauss
