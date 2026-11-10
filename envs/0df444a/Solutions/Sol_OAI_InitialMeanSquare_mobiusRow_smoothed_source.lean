-- Prove2me | solution 1 for OAI.InitialMeanSquare.mobiusRow_smoothed_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T08:56:38.426229+00:00
-- url     : https://prove2.me/submissions/21c78dc8-abc4-41f9-ab31-095c9d00268b

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_UniformTailBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CubeBlocks
import Theorems.Thm_OAI_InitialMeanSquare_mobiusRow_norm
import Theorems.Thm_OAI_SecondPassArithmetic_inputConjugateRow_eq_truncated_add_tail
import Theorems.Thm_OAI_SecondPassArithmetic_truncatedSecondSource_eq_nonzero_add_zero


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
open scoped BigOperators Classical SchwartzMap
open OAI.InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic
open FirstCauchyArithmetic (supportMobius supportConjugateSum)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι→OAI.InitialMeanSquare.O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})
variable (hp : ∀i,p i≠0) (hinj : Function.Injective (fun i => Ideal.span {p i}))
  (hc : ∀i,ringChar (OAI.InitialMeanSquare.O⧸Ideal.span {p i})≠2)
include hc
namespace OAI.InitialMeanSquare
theorem _root_.solution (F : Finset ι) (Ψ : O→*ℂ) (m : O)
    (H : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y)
    (K : Finset ι→Finset ι→Finset O) :
    (∑'z:O,W (‖eisEmbedding z‖^2/Y)*(‖mobiusRow p hg F Ψ m H z‖^2:ℝ))=
      truncatedSecondSource p hp hg hinj F (conjugateMonoid Ψ) m 1 1
        (fun S => star (H S)) W Y (fun G E => (K G E).erase 0)+
      truncatedSecondZero p hg F (conjugateMonoid Ψ) m 1 1
        (fun S => star (H S)) W Y K+
      secondSourceTail p hp hg hinj F (conjugateMonoid Ψ) m 1 1
        (fun S => star (H S)) W Y K := by
  simp_rw [mobiusRow_norm p hg]
  rw [inputConjugateRow_eq_truncated_add_tail p hp hg hinj hc F
    (conjugateMonoid Ψ) m 1 1 (fun S => star (H S)) W Y hY K]
  rw [truncatedSecondSource_eq_nonzero_add_zero p hp hg hinj]
end OAI.InitialMeanSquare
