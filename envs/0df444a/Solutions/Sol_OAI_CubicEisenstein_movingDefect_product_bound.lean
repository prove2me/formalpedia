-- Prove2me | solution 1 for OAI.CubicEisenstein.movingDefect_product_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:25:28.658437+00:00
-- url     : https://prove2.me/submissions/59aac651-47ec-4b41-8a1a-02efc32c8d7b

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ArbitraryCuspPullback
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspDilation
import Theorems.Thm_OAI_CubicEisenstein_smoothCuspSeedDefect_support


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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open Filter MeasureTheory
open scoped BigOperators Classical Topology
open OAI.CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace
namespace OAI.CubicEisenstein
theorem _root_.solution
    (f : KernelQuotient→ℂ) (K C : ℝ) (hK : 0≤K) (hC : 0≤C)
    (hdec : ∀w : HyperbolicSpace, ∀r : CuspCosets,1<cosetHeight r w →
      ‖f (integralOrbitProjection globalKubotaKernel w)‖≤K/(cosetHeight r w)^3)
    (hbound : ∀A : ℝ,1≤A → ∀w : HyperbolicSpace,
      ‖smoothCuspSeedDefect A (2*A) (4/3) w‖≤C*A^2)
    (A : ℝ) (hA : 1<A) (q : KernelQuotient) :
    ‖f q‖*‖kernelQuotientDefect A (2*A) (4/3) q‖≤K*C/A := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change ‖f (integralOrbitProjection globalKubotaKernel w)‖*
      ‖smoothCuspSeedDefect A (2*A) (4/3) w‖≤_
    have hApos : 0<A := zero_lt_one.trans hA
    by_cases hz : smoothCuspSeedDefect A (2*A) (4/3) w=0
    · rw [hz,norm_zero,mul_zero]
      positivity
    obtain ⟨r,hr,hr'⟩ := smoothCuspSeedDefect_support A (2*A) (4/3) (by linarith) w hz
    have hheight : 0<cosetHeight r w := hApos.trans_le hr
    have hf : ‖f (integralOrbitProjection globalKubotaKernel w)‖≤K/A^3 := by
      apply (hdec w r (hA.trans_le hr)).trans
      apply div_le_div_of_nonneg_left hK (pow_pos hApos 3)
      exact pow_le_pow_left₀ hApos.le hr 3
    calc
      _ ≤ (K/A^3)*(C*A^2) := mul_le_mul hf (hbound A hA.le w) (norm_nonneg _) (by positivity)
      _ = K*C/A := by field_simp
end OAI.CubicEisenstein
