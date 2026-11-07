-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.finiteSquarefreeRow_pair_radial_poisson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:35:14.7772+00:00
-- url     : https://prove2.me/submissions/0029c319-514b-415a-bf5c-6e4f62618600

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_IdealGenerators
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
import Theorems.Thm_OAI_ActualEisensteinCubic_activeExponent_ne_zero
import Theorems.Thm_OAI_ActualEisensteinCubic_activeExponent_lt_six
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_pair_activeSupport
import Theorems.Thm_OAI_ActualEisensteinCubic_canonical_masked_radial_poisson_collected


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
open OAI.ActualEisensteinCubic
open ConcreteTraceCRT EisensteinSchwartzPoisson
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    {ι : Type*} [DecidableEq ι] (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hgood : ∀ i, lambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' u : O, (star (finiteSquarefreeRow P hgood S u) *
      finiteSquarefreeRow P hgood T u) * W (‖eisEmbedding u‖ ^ 2 / scale)) =
      squarefreePairPoissonKernel P hinj hgood S T W scale := by
  calc
    _ = ∑' u : O, rowCoprimeMask P (S ∩ T) u *
        finiteSexticRow (activePrimes P S T) (fun i => hgood i.val)
          (activeExponent S T) u * W (‖eisEmbedding u‖ ^ 2 / scale) := by
      apply tsum_congr
      intro u
      rw [finiteSquarefreeRow_pair_activeSupport]
    _ = _ := canonical_masked_radial_poisson_collected P hinj (S ∩ T)
      (activePrimes P S T) (activePrimes_pairwise_isCoprime P hinj S T)
      (fun i => hgood i.val) (fun i => hchar i.val)
      (activeExponent S T) (activeExponent_ne_zero S T) (activeExponent_lt_six S T)
      W scale hscale
end OAI.ActualEisensteinCubic
