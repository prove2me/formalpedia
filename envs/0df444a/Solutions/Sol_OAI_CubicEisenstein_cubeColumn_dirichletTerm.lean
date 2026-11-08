-- Prove2me | solution 1 for OAI.CubicEisenstein.cubeColumn_dirichletTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:59:51.056418+00:00
-- url     : https://prove2.me/submissions/1051b4cc-1bd8-4ab4-a209-6fb29ca9eeb1

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_PrincipalTruncation
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_FrequencyCutoffs
import Theorems.Thm_OAI_CubicEisenstein_cubeColumn_arithmetic_sum
import Theorems.Thm_OAI_CubicEisenstein_cubeColumn_norm
import Theorems.Thm_OAI_CubicEisenstein_cube_norm_weight_algebra
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_norm_sq_eq_absNorm_span
import Theorems.Thm_OAI_CubicEisenstein_unramifiedNormWeight_of_good


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
open scoped BigOperators Classical
open OAI.CubicEisenstein
open ActualEisensteinCubic ConcreteTraceCRT CubicJacobiGlobal UniqueFactorizationMonoid CompletedGauss
open PrimaryIdealUnitReindex (GoodIdeal)
namespace OAI.CubicEisenstein
theorem _root_.solution (s : ℂ) (b : Bool) (n : ℕ) (I : GoodIdeal) :
    arithmeticDirichletTerm s 0 (cubeColumnMap (b,n,I)).1 =
      ramifiedRatio s^(n+1) * ((idealTotient I.1:ℂ)*unramifiedNormWeight (3*s-2) I.1) := by
  have hI : Ideal.absNorm I.1 ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr (primaryGenerator_ne_zero_ideal I.1 I.2)
  change (if cubeColumn b n I=0 then 0 else
    ((‖eisEmbedding (cubeColumn b n I)‖^2:ℝ):ℂ)^(-s)*
      arithmeticResidueSum 0 (cubeColumn b n I)) = _
  rw [if_neg (cubeColumn_ne_zero b n I),eisEmbedding_norm_sq_eq_absNorm_span,
    Complex.ofReal_natCast,cubeColumn_norm,cubeColumn_arithmetic_sum,
    unramifiedNormWeight_of_good _ _ I.2]
  calc
    _ = (((3^(3*(n+1))*Ideal.absNorm I.1^3:ℕ):ℂ)^(-s) *
        (3^(3*(n+1))*Ideal.absNorm I.1^2:ℕ))*(idealTotient I.1:ℂ) := by
      push_cast
      ring
    _ = (ramifiedRatio s^(n+1)*(Ideal.absNorm I.1:ℂ)^(-(3*s-2)))*(idealTotient I.1:ℂ) := by
      rw [cube_norm_weight_algebra s n (Ideal.absNorm I.1) hI]
    _ = _ := by ring
end OAI.CubicEisenstein
