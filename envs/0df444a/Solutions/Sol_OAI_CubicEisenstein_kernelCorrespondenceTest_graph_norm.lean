-- Prove2me | solution 1 for OAI.CubicEisenstein.kernelCorrespondenceTest_graph_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:00:43.174525+00:00
-- url     : https://prove2.me/submissions/6b365956-ed32-4a56-bbe2-5aa6b37c4905

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CorrespondencePullback
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_RamifiedSixBranches
import Theorems.Thm_OAI_CubicEisenstein_kernelCorrespondenceTest_energy_le
import Theorems.Thm_OAI_CubicEisenstein_kernelCorrespondenceL2_norm_le
import Theorems.Thm_OAI_CubicEisenstein_kernelCorrespondenceTest_mass
import Theorems.Thm_OAI_CubicEisenstein_kernelEnergyGraphCore_norm_sq


set_option autoImplicit false
open OAI
noncomputable section
open OAI.CubicEisenstein
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
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise Manifold ContDiff ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding
local notation "O" => ActualEisensteinCubic.O
variable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤globalKubotaKernel) (hJK : J≤globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
namespace OAI.CubicEisenstein
theorem _root_.solution (f : kernelSmoothTests) :
    ‖kernelEnergyGraphCore (kernelCorrespondenceTest hHK hJK e g he f)‖≤
      Real.sqrt ((H.relIndex globalKubotaKernel:ℝ)*(J.relIndex globalKubotaKernel:ℝ))*
        ‖kernelEnergyGraphCore f‖ := by
  have hm := kernelCorrespondenceL2_norm_le hHK hJK e g he (kernelSmoothTestsToL2 f)
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr hm
  rw [←kernelCorrespondenceTest_mass hHK hJK e g he,mul_pow,
    Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))] at hs
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [kernelEnergyGraphCore_norm_sq,mul_pow,
    Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),kernelEnergyGraphCore_norm_sq]
  have he := kernelCorrespondenceTest_energy_le hHK hJK e g he f
  nlinarith
end OAI.CubicEisenstein
