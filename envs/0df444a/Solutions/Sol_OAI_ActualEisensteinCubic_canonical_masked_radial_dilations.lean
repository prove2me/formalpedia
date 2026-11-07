-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.canonical_masked_radial_dilations
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:12:42.666274+00:00
-- url     : https://prove2.me/submissions/24a53154-554a-4553-b3e3-32b8d35c03b4

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticRadialPoisson
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_IdealGenerators
import Theorems.Thm_OAI_ActualEisensteinCubic_tsum_masked_radial_dilations
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSexticRow_mul
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSexticRow_radial_summable


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
open OAI.ActualEisensteinCubic
open ConcreteTraceCRT
open ConcreteTraceCRT EisensteinSchwartzPoisson
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    {α ι : Type*} [DecidableEq α] [Fintype ι]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (S : Finset α)
    (Q : ι → Ideal O) [∀ i, (Q i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime Q))
    (hgood : ∀ i, lambda ∉ Q i) (j : ι → ℕ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' u : O, rowCoprimeMask P S u * finiteSexticRow Q hgood j u *
      W (‖eisEmbedding u‖ ^ 2 / scale)) =
      ∑ E ∈ S.powerset,
        (UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) *
          finiteSexticRow Q hgood j (primeSubsetGenerator P E) *
          ∑' z : O, finiteSexticRow Q hgood j z *
            W (‖eisEmbedding z‖ ^ 2 /
              (scale / ‖eisEmbedding (primeSubsetGenerator P E)‖ ^ 2)) := by
  exact tsum_masked_radial_dilations P hinj S (finiteSexticRow Q hgood j)
    (finiteSexticRow_mul Q hgood j) W scale
    (finiteSexticRow_radial_summable Q hcop hgood j W scale hscale)
end OAI.ActualEisensteinCubic
