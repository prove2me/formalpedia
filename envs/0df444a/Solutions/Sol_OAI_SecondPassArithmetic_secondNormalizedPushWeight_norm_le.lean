-- Prove2me | solution 1 for OAI.SecondPassArithmetic.secondNormalizedPushWeight_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:36:43.886131+00:00
-- url     : https://prove2.me/submissions/ff0987e0-368f-4355-a337-42936fab6a38

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_UnrestrictedCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ConjugateProfiles
import Theorems.Thm_OAI_SecondPassArithmetic_secondExpansionPushWeight_at_source
import Theorems.Thm_OAI_SecondPassArithmetic_secondNormalizedExpansionWeight_norm_le

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
open scoped BigOperators Classical SchwartzMap ContDiff FourierTransform
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FirstCauchyArithmetic (supportMobius)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj
namespace OAI.SecondPassArithmetic
theorem _root_.solution
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (C D : Finset ι) (Ψ : O →* ℂ) (m c d r : O) (z : SecondRayIndex)
    (X Y : ℝ) (hX : 0 < X) (hY : 0 ≤ Y)
    (s : Finset (SecondExpansionData ι)) (hs : ∀ x ∈ s, InSecondQuotientSector p r x)
    (hΨG : ∀ x ∈ s, ‖Ψ (∏ i ∈ x.sourceCommon, p i)‖ ≤ 1)
    (hΨV : ∀ x ∈ s, ‖Ψ (∏ i ∈ x.overlap, p i)‖ ≤ 1)
    (y : SecondSupportData ι) (hy : y ∈ s.image (expansionSupportData C D)) :
    ‖secondExpansionPushWeight C D s (secondNormalizedExpansionWeight p hp hcop hg Ψ m c d z X Y) y *
      (secondExpansionScale p X r y : ℂ)⁻¹‖ ≤
      Y * ‖eisEmbedding r‖ ^ 2 / X ^ 2 * ‖secondRayCoefficient z‖ := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  rw [secondExpansionPushWeight_at_source p hinj C D r s hs _ x hx]
  exact secondNormalizedExpansionWeight_norm_le p hp hcop hg hinj hc C D Ψ m c d r z X Y hX hY
    x (hΨG x hx) (hΨV x hx)
end OAI.SecondPassArithmetic
