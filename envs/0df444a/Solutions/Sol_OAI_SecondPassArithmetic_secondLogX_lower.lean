-- Prove2me | solution 1 for OAI.SecondPassArithmetic.secondLogX_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T15:12:27.963708+00:00
-- url     : https://prove2.me/submissions/92feaef8-e1fc-47ed-b0aa-c9030ccd59a1

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_GreenIntegrals
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_GreenIdentity
import Theorems.Thm_OAI_SecondPassArithmetic_normLogScale_pos
import Theorems.Thm_OAI_SecondPassArithmetic_normLogBin_scale_bounds
import Theorems.Thm_OAI_SecondPassArithmetic_secondSupportedSector_mem
import Theorems.Thm_OAI_FirstPassCubeLabels_primeProductNorm_pos
import Theorems.Thm_OAI_FirstPassCubeLabels_primeProductNorm_union
import Theorems.Thm_OAI_SecondPassArithmetic_primeProductNorm_ge_one


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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
variable {ι : Type*} [DecidableEq ι]
  (p : ι → OAI.SecondPassArithmetic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
include hp
omit [∀ (i : ι), (span {p i}).IsMaximal]
namespace OAI.SecondPassArithmetic
theorem _root_.solution (D F R : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (X M : ℝ) (hX : 0 < X) (x : SecondExpansionData ι)
    (hx : x ∈ secondSupportedSector p F K R X M) :
    Real.exp (-M) ≤ secondLogX p R X (secondLogIndex p D x) := by
  obtain ⟨hG,hE,hV,hk0,hk,hr,hs⟩ := secondSupportedSector_mem p F K R X M x hx
  have he := (normLogBin_scale_bounds (primeProductNorm p x.divisor) (primeProductNorm_ge_one p hp _)).1
  have hv := (normLogBin_scale_bounds (primeProductNorm p x.overlap) (primeProductNorm_ge_one p hp _)).1
  have hGR : primeProductNorm p x.sourceCommon = primeProductNorm p x.divisor * primeProductNorm p R := by
    rw [← hr, ← FirstPassCubeLabels.primeProductNorm_union p x.divisor (x.sourceCommon\x.divisor) Finset.disjoint_sdiff,
      Finset.union_sdiff_of_subset hE]
  have hprod : secondLogE (secondLogIndex p D x) * secondLogV (secondLogIndex p D x) * primeProductNorm p R ≤ X*Real.exp M := by
    calc
      _ ≤ primeProductNorm p x.divisor * primeProductNorm p x.overlap * primeProductNorm p R := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul he hv (normLogScale_pos _).le
          (FirstPassCubeLabels.primeProductNorm_pos p hp _).le)
          (FirstPassCubeLabels.primeProductNorm_pos p hp _).le
      _ = primeProductNorm p x.sourceCommon * primeProductNorm p x.overlap := by rw [hGR]; ring
      _ ≤ _ := hs.2
  unfold secondLogX
  apply (le_div_iff₀ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _))
    (FirstPassCubeLabels.primeProductNorm_pos p hp R))).mpr
  calc
    _ ≤ Real.exp (-M) * (X*Real.exp M) := mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = X := by rw [Real.exp_neg]; field_simp
end OAI.SecondPassArithmetic
