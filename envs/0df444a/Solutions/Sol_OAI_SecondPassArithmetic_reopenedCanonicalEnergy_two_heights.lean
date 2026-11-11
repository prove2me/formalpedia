-- Prove2me | solution 1 for OAI.SecondPassArithmetic.reopenedCanonicalEnergy_two_heights
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:41:08.513623+00:00
-- url     : https://prove2.me/submissions/f707132e-9ae1-4467-8dec-c9c4ac748317

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_UnitRows
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspHeight
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BarrierPotential
import Theorems.Thm_OAI_SecondPassArithmetic_reopenedCanonicalRow_two_heights

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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog)
open JointLogSeparation (frequencyTwist)
variable {ι : Type*} [DecidableEq ι] (p : ι→ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})
namespace OAI.SecondPassArithmetic
theorem _root_.solution (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O→(ι→₀ℕ)→ℂ) (Ψ : ActualEisensteinCubic.O→*ℂ) (m : ActualEisensteinCubic.O)
    (g : 𝓢(ℝ,ℂ)) (X Ksrc oldHeight newHeight : ℝ) (hX : 0<X) :
    (∑I∈labels,nonzeroRowMajorantSum
      (reopenedCanonicalRow p hp hcop hg pool Q (β I) (normHeightTwist Ψ oldHeight) m
        (ConcretePrimeRowBridge.idealGenerator I)
        (fun S=>frequencyTwist g newHeight (columnLog p X S))) Ksrc).re=
    (∑I∈labels,nonzeroRowMajorantSum
      (reopenedCanonicalRow p hp hcop hg pool Q (β I) Ψ m
        (ConcretePrimeRowBridge.idealGenerator I)
        (fun S=>frequencyTwist g (oldHeight+newHeight) (columnLog p X S))) Ksrc).re := by
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro I hI
  unfold nonzeroRowMajorantSum
  apply tsum_congr
  intro z
  rw [reopenedCanonicalRow_two_heights p hp hcop hg pool Q (β I) Ψ m _ z g X oldHeight newHeight hX]
end OAI.SecondPassArithmetic
