-- Prove2me | solution 1 for OAI.MixedCrossSeparation.activeConvertedGauss_eq_columnBlocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:26:39.373688+00:00
-- url     : https://prove2.me/submissions/46d8fb73-d61e-4300-8679-506593de8620

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CompletedExpansion
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RayCharacters
import Theorems.Thm_OAI_MixedCrossSeparation_convertedColumnBlock_image
import Theorems.Thm_OAI_MixedCrossSeparation_quadraticCrossPhase_image
import Theorems.Thm_OAI_MixedCrossSeparation_activeConvertedGauss_separated

section
namespace OAI
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
open scoped BigOperators Classical
namespace RayFourExpansion
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase QuadraticGaussRay
open ActualEisensteinCoordinates MixedCrossSeparation
end RayFourExpansion
namespace MixedCrossSeparation
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
open QuadraticGaussRay ActualEisensteinCoordinates GaussGeneratorTransport
private theorem negative_active_image {ι : Type*} [DecidableEq ι] (S T : Finset ι) :
    (Finset.univ.filter (fun i : activeSupport S T => i.val ∈ S \ T)).image Subtype.val = S \ T := by
  ext i
  constructor
  · intro hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp ha).2
  · intro hi
    exact Finset.mem_image.mpr ⟨⟨i, Finset.mem_union_left _ hi⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩
private theorem positive_active_image {ι : Type*} [DecidableEq ι] (S T : Finset ι) :
    (Finset.univ.filter (fun i : activeSupport S T => i.val ∉ S \ T)).image Subtype.val = T \ S := by
  ext i
  constructor
  · intro hi
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hi
    have hm := a.property
    rcases Finset.mem_union.mp hm with hleft | hright
    · exact ((Finset.mem_filter.mp ha).2 hleft).elim
    · exact hright
  · intro hi
    have hn : i ∉ S \ T := fun h => (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp h).1
    exact Finset.mem_image.mpr ⟨⟨i, Finset.mem_union_right _ hi⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩, rfl⟩
end MixedCrossSeparation
namespace FirstCauchyArithmetic
section
open ActualEisensteinCubic CoprimeMobiusExtension
end
section
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedCrossSeparation RayFourExpansion
end
open ActualEisensteinCubic ConcretePrimeRowBridge
end FirstCauchyArithmetic
end
end OAI
end

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
open scoped BigOperators Classical
open OAI.MixedCrossSeparation
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
open QuadraticGaussRay ActualEisensteinCoordinates GaussGeneratorTransport
namespace OAI.MixedCrossSeparation
theorem _root_.solution
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hprimary : ∀ i, lambda ^ 2 ∣ p i - 1) (S T : Finset ι) :
    activeConvertedGauss p hp hg S T =
      convertedColumnBlock p hp hg (S \ T) true *
        convertedColumnBlock p hp hg (T \ S) false *
          quadraticCrossPhase p hg (S \ T) (T \ S) := by
  rw [activeConvertedGauss_separated p hp hg hprimary S T]
  rw [convertedColumnBlock_image p hp hg Subtype.val Subtype.val_injective,
    convertedColumnBlock_image p hp hg Subtype.val Subtype.val_injective,
    quadraticCrossPhase_image p hg Subtype.val Subtype.val_injective,
    negative_active_image, positive_active_image]
end OAI.MixedCrossSeparation
