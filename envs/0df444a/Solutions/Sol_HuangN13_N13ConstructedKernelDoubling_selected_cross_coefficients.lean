-- Prove2me | solution 1 for HuangN13.N13ConstructedKernelDoubling.selected_cross_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:39:04.956034+00:00
-- url     : https://prove2.me/submissions/e056acc2-c38b-4e9a-b977-5ecb08517399

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_DoublingStatementCore
import Theorems.Thm_HuangN13_N13ActualPrincipalNorm_norm_of_actual_shape
import Theorems.Thm_HuangN13_N13CenteredPrincipalNumerator_multiplier_of_centered_double
import Theorems.Thm_HuangN13_N13PrincipalHermiteNormalization_normalize_actual_numerator
import Theorems.Thm_MazurProof_N13BranchLeading_branch_min_order
import Theorems.Thm_MazurProof_N13BranchNorm_evalPoly_ne_zero
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_ker_mumfordEval
import Theorems.Thm_MazurProof_N13GeneralizedMumfordIntegral_recompose
import Theorems.Thm_MazurProof_N13GoodSexticCoordinateEquiv_sexticYInGood_root
import Theorems.Thm_MazurProof_SexticMumford_recompose

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13Infinity
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
theorem functionFieldToLaurent_injective :
    Function.Injective (functionFieldToLaurent K) :=
  (functionFieldToLaurent K).injective
end
end MazurProof.N13Infinity
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13InfinityMinus
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
theorem functionFieldToLaurentMinus_injective :
    Function.Injective (functionFieldToLaurentMinus K) :=
  (functionFieldToLaurentMinus K).injective
end
end MazurProof.N13InfinityMinus
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries nonZeroDivisors
namespace MazurProof.N13InfinityMinus
noncomputable section
universe u
variable (K : Type u) [Field K] [CharZero K]
@[simp] theorem functionFieldToLaurentMinus_algebraMap
    (z : N13Mumford.CoordinateRing K) :
    functionFieldToLaurentMinus K
        (algebraMap (N13Mumford.CoordinateRing K)
          (N13Mumford.FunctionField K) z) =
      coordinateToLaurentMinus K z := by
  exact IsFractionRing.lift_algebraMap
    (coordinateToLaurentMinus_injective K) z
end
end MazurProof.N13InfinityMinus
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GeneralizedMumfordIntegral
noncomputable section
universe u
variable {R : Type u} [CommRing R]
@[simp] theorem xClass_natCast (n : ℕ) :
    xClass (n : R[X]) =
      (n : CoordinateRing (R := R)) :=
  map_natCast xClassHom n
end
end MazurProof.N13GeneralizedMumfordIntegral
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GeneralizedMumfordIntegral
noncomputable section
universe u
variable {R : Type u} [CommRing R]
@[simp] theorem xClass_add (p q : R[X]) :
    xClass (p + q) = xClass p + xClass q :=
  map_add xClassHom p q
end
end MazurProof.N13GeneralizedMumfordIntegral
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GeneralizedMumfordIntegral
noncomputable section
universe u
variable {R : Type u} [CommRing R]
@[simp] theorem mumfordEval_yClass
    (D : SemiMumford (R := R)) :
    mumfordEval D yClass =
      Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X])) D.v :=
  AdjoinRoot.lift_root (mumford_root_relation D)
end
end MazurProof.N13GeneralizedMumfordIntegral
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GeneralizedMumfordIntegral
noncomputable section
universe u
variable {R : Type u} [CommRing R]
/-- Membership in a generalized Mumford graph ideal is the single monic
divisibility condition obtained by substituting `Y = v`. -/
theorem mem_mumfordIdeal_iff
    [Nontrivial R]
    (D : SemiMumford (R := R))
    (z : CoordinateRing (R := R)) :
    z ∈ mumfordIdeal D.u D.v ↔
      D.u ∣ coeff0 z + coeffY z * D.v := by
  rw [← ker_mumfordEval D, RingHom.mem_ker]
  conv_lhs =>
    rw [← recompose z]
  simp only [map_add, map_mul, mumfordEval_xClass,
    mumfordEval_yClass]
  change
    Ideal.Quotient.mk (Ideal.span ({D.u} : Set R[X]))
        (coeff0 z + coeffY z * D.v) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]
end
end MazurProof.N13GeneralizedMumfordIntegral
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GoodSexticCoordinateEquiv
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
@[simp] theorem toGood_xClass (p : K[X]) :
    toGood (K := K) (SexticMumford.xClass (M (K := K)) p) =
      N13GeneralizedMumfordIntegral.xClass p := by
  change
    toGood (K := K)
        (AdjoinRoot.of
          (SexticMumford.curvePoly (M (K := K))) p) =
      goodXHom (K := K) p
  exact AdjoinRoot.lift_of (MazurProof.N13GoodSexticCoordinateEquiv.sexticYInGood_root (K := K))
end
end MazurProof.N13GoodSexticCoordinateEquiv
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GoodSexticCoordinateEquiv
noncomputable section
universe u
variable {K : Type u} [Field K] [CharZero K]
@[simp] theorem toGood_yClass :
    toGood (K := K) (SexticMumford.yClass (M (K := K))) =
      sexticYInGood (K := K) :=
  AdjoinRoot.lift_root (MazurProof.N13GoodSexticCoordinateEquiv.sexticYInGood_root (K := K))
end
end MazurProof.N13GoodSexticCoordinateEquiv
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13TwoAdicDisks
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicDisks.instFactPrimeOfNatNat_fLT
theorem y_eq_zeroDiskY
    (x : R₂) (hx : x ∈ maximal)
    {y : R₂}
    (hy : N13GoodModelTwo.AffineEquation x y)
    (hymem : y ∈ maximal) :
    y = zeroDiskY x hx :=
  y_eq_of_mem_maximal x y (zeroDiskY x hx)
    (h_isUnit_of_mem_zeroDisk hx)
    hy (zeroDiskY_spec x hx).1 hymem
    (zeroDiskY_spec x hx).2
end
end MazurProof.N13TwoAdicDisks
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13TwoAdicDisks
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicDisks.instFactPrimeOfNatNat_fLT
@[simp] theorem zeroDiskY_zero :
    zeroDiskY 0 maximal.zero_mem = 0 := by
  symm
  apply y_eq_zeroDiskY 0 maximal.zero_mem
  · simp [N13GoodModelTwo.AffineEquation,
      N13GoodModelTwo.h, N13GoodModelTwo.rhs]
  · exact maximal.zero_mem
end
end MazurProof.N13TwoAdicDisks
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13TwoAdicDisks
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicDisks.instFactPrimeOfNatNat_fLT
theorem y_eq_negOneDiskY
    (x : R₂) (hx : x + 1 ∈ maximal)
    {y : R₂}
    (hy : N13GoodModelTwo.AffineEquation x y)
    (hymem : y ∈ maximal) :
    y = negOneDiskY x hx :=
  y_eq_of_mem_maximal x y (negOneDiskY x hx)
    (h_isUnit_of_mem_negOneDisk hx)
    hy (negOneDiskY_spec x hx).1 hymem
    (negOneDiskY_spec x hx).2
end
end MazurProof.N13TwoAdicDisks
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13TwoAdicDisks
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicDisks.instFactPrimeOfNatNat_fLT
@[simp] theorem negOneDiskY_negOne :
    negOneDiskY (-1) (by simp) = 0 := by
  symm
  apply y_eq_negOneDiskY (-1) (by simp)
  · simp [N13GoodModelTwo.AffineEquation,
      N13GoodModelTwo.h, N13GoodModelTwo.rhs]
    ring
  · exact maximal.zero_mem
end
end MazurProof.N13TwoAdicDisks
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13TwoAdicAbelChartData
noncomputable section
namespace DiskPair
variable (P : DiskPair)
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
@[simp] theorem basePair_y₀ :
    basePair.y₀ = 0 :=
  N13TwoAdicDisks.zeroDiskY_zero
end DiskPair
end
end MazurProof.N13TwoAdicAbelChartData
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13TwoAdicAbelChartData
noncomputable section
namespace DiskPair
variable (P : DiskPair)
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
@[simp] theorem basePair_y₁ :
    basePair.y₁ = 0 :=
  N13TwoAdicDisks.negOneDiskY_negOne
end DiskPair
end
end MazurProof.N13TwoAdicAbelChartData
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13TwoAdicAbelChartData
noncomputable section
namespace DiskPair
variable (P : DiskPair)
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
@[simp] theorem basePair_u :
    basePair.u =
      N13FormalAbelLinearization.uBase := by
  simp [u, basePair, N13FormalAbelLinearization.uBase]
  ring
end DiskPair
end
end MazurProof.N13TwoAdicAbelChartData
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13TwoAdicAbelChartData
noncomputable section
namespace DiskPair
variable (P : DiskPair)
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
@[simp] theorem basePair_v :
    basePair.v = 0 := by
  change basePair.interpolate basePair.y₀ basePair.y₁ = 0
  rw [basePair_y₀, basePair_y₁]
  simp [interpolate]
end DiskPair
end
end MazurProof.N13TwoAdicAbelChartData
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
theorem u_sub_base (P : DiskPair) :
    P.u - N13AbelChartBase.baseSmoothMumford.u =
      _root_.Polynomial.C (-(P.x₀ + (P.x₁ + 1))) * X +
        _root_.Polynomial.C (P.x₀ * P.x₁) := by
  simp [N13TwoAdicAbelChartData.DiskPair.u,
    N13FormalAbelLinearization.uBase]
  ring
end
end MazurProof.N13MumfordFormalTransitionJet
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordCenteredDoublingJet
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13MumfordCenteredDoublingJet.instFactPrimeOfNatNat_fLT
/-- The monic quadratic obtained by squaring the centered `u`-transition and
cancelling one copy of the fixed base polynomial to first order. -/
def centeredSquareU (P : DiskPair) : R₂[X] :=
  P.u + P.u - N13AbelChartBase.baseSmoothMumford.u
end
end MazurProof.N13MumfordCenteredDoublingJet
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordCenteredDoublingJet
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13MumfordCenteredDoublingJet.instFactPrimeOfNatNat_fLT
/-- Cross-multiplication removes every overlap denominator: the error between
the unreduced numerator `u_P²` and its centered monic normalization is exactly
the square of the deviation from the base polynomial. -/
theorem u_sq_sub_base_mul_centeredSquareU
    (P : DiskPair) :
    P.u ^ 2 -
        N13AbelChartBase.baseSmoothMumford.u *
          centeredSquareU P =
      (P.u - N13AbelChartBase.baseSmoothMumford.u) ^ 2 := by
  simp only [centeredSquareU]
  ring
end
end MazurProof.N13MumfordCenteredDoublingJet
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalKernelDoublingAdapter
noncomputable section
universe u
namespace NearBaseFamily
variable {H : AddSubgroup RationalPic}
attribute [local instance] MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT
/-- Near-base graph recovery supplies the exact centered Picard realization
required by `RationalKernelDoublingData`. -/
theorem realize
    (F : NearBaseFamily H) (z : H) :
    N13TwoAdicAbelChartPic.DiskPair.centeredPic
        (F.pair z) =
      N13TwoAdicAbelChartSection.subgroupToPic H z := by
  calc
    N13TwoAdicAbelChartPic.DiskPair.centeredPic
          (F.pair z) =
        (F.graph z).centeredPic := by
      simpa [pair] using
        ((F.graph z).centeredPic_eq_diskPair_centeredPic).symm
    _ = N13TwoAdicAbelChartSection.subgroupToPic H z :=
      F.realize_graph z
end NearBaseFamily
end
end MazurProof.N13RationalKernelDoublingAdapter
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13MumfordCenteredDoublingAdapter
noncomputable section
open MazurProof.N13RationalKernelDoublingAdapter
attribute [local instance] MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT
/-- The pair selected at `2 • z` represents twice the centered Picard class
of the pair selected at `z`.  This is a formal consequence of pointwise
realization and additivity, independent of the coordinate calculation. -/
theorem centeredPic_pair_two_nsmul
    {H : AddSubgroup RationalPic}
    (F : NearBaseFamily H)
    (z : H) :
    N13TwoAdicAbelChartPic.DiskPair.centeredPic
        (F.pair (2 • z)) =
      2 • N13TwoAdicAbelChartPic.DiskPair.centeredPic
        (F.pair z) := by
  calc
    N13TwoAdicAbelChartPic.DiskPair.centeredPic
          (F.pair (2 • z)) =
        N13TwoAdicAbelChartSection.subgroupToPic H (2 • z) :=
      F.realize (2 • z)
    _ = 2 • N13TwoAdicAbelChartSection.subgroupToPic H z := by
      exact
        map_nsmul
          (N13TwoAdicAbelChartSection.subgroupToPic H) 2 z
    _ = 2 • N13TwoAdicAbelChartPic.DiskPair.centeredPic
          (F.pair z) := by
      rw [F.realize z]
end
end MazurProof.N13MumfordCenteredDoublingAdapter
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13HermiteResidualDivisibility
noncomputable section
open Polynomial N13CenteredHermiteFirstOrder
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT
def residual (a₀ a₁ b₀ b₁ : R₂) : R₂[X] :=
  (X ^ 2 + X) * quad a₀ a₁ ^ 2 -
    quad a₀ a₁ * lin b₀ b₁ * (X ^ 3 + X + 1) -
      lin b₀ b₁ ^ 2 * X ^ 3
end
end MazurProof.N13HermiteResidualDivisibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13HermiteResidualDivisibility
noncomputable section
open Polynomial N13CenteredHermiteFirstOrder
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT
theorem norm_factor (a₀ a₁ b₀ b₁ : R₂) :
    ((X ^ 2 + X) * quad a₀ a₁) ^ 2 -
      ((X ^ 2 + X) * quad a₀ a₁) * lin b₀ b₁ *
        N13GeneralizedMumfordIntegral.hPoly -
      lin b₀ b₁ ^ 2 * N13GeneralizedMumfordIntegral.rhsPoly =
        (X ^ 2 + X) * residual a₀ a₁ b₀ b₁ := by
  simp only [residual, N13GeneralizedMumfordIntegral.hPoly,
    N13GeneralizedMumfordIntegral.rhsPoly]
  ring
end
end MazurProof.N13HermiteResidualDivisibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13NormalizedHermiteResidual
noncomputable section
open Polynomial N13CenteredHermiteFirstOrder N13HermiteResidualDivisibility
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
theorem coordIdeal_le_maximal (P : DiskPair) : I P ≤ N13TwoAdicDisks.maximal := by
  apply Ideal.span_le.mpr
  rintro a ⟨j, rfl⟩
  exact P.coord_mem_maximal j
end
end MazurProof.N13NormalizedHermiteResidual
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13NormalizedHermiteResidual
noncomputable section
open Polynomial N13CenteredHermiteFirstOrder N13HermiteResidualDivisibility
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicDisks.instFactPrimeOfNatNat_fLT
theorem one_sub_unit (P : DiskPair) (b : R₂) (hb : b ∈ I P * I P) : IsUnit (1 - b) := by
  have hi : I P * I P ≤ I P := Ideal.mul_le_left
  have hm := coordIdeal_le_maximal P (hi hb)
  apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal isUnit_one
  convert N13TwoAdicDisks.maximal.neg_mem hm using 1 <;> ring
end
end MazurProof.N13NormalizedHermiteResidual
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13NormalizedHermiteResidual
noncomputable section
open Polynomial N13CenteredHermiteFirstOrder N13HermiteResidualDivisibility
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT
theorem residual_coeff_six (a₀ a₁ b₀ b₁ : R₂) :
    (N13HermiteResidualDivisibility.residual a₀ a₁ b₀ b₁).coeff 6 = 1 - b₁ := by
  -- Use a helper lemma to compute the coefficient
  have h : (N13HermiteResidualDivisibility.residual a₀ a₁ b₀ b₁) =
      Polynomial.C (1 - b₁) * Polynomial.X ^ 6 +
      Polynomial.C (-a₁*b₁ + 2*a₁ - b₀ - b₁^2 + 1) * Polynomial.X ^ 5 +
      Polynomial.C (-a₀*b₁ + 2*a₀ + a₁^2 - a₁*b₀ + 2*a₁ - 2*b₀*b₁ - b₁) * Polynomial.X ^ 4 +
      Polynomial.C (2*a₀*a₁ - a₀*b₀ + 2*a₀ + a₁^2 - a₁*b₁ - b₀^2 - b₀ - b₁) * Polynomial.X ^ 3 +
      Polynomial.C (a₀^2 + 2*a₀*a₁ - a₀*b₁ - a₁*b₀ - a₁*b₁ - b₀) * Polynomial.X ^ 2 +
      Polynomial.C (a₀^2 - a₀*b₀ - a₀*b₁ - a₁*b₀) * Polynomial.X +
      Polynomial.C (-a₀*b₀) := by
    unfold N13HermiteResidualDivisibility.residual N13HermiteResidualDivisibility.quad N13HermiteResidualDivisibility.lin
    simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_one, map_ofNat]
    ring
  rw [h]
  -- Now compute coeff 6 of the sum
  -- Only the first term contributes to coeff 6
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  -- Handle the remaining terms: constant polynomials have coeff n = 0 for n > 0
  -- Use coeff_eq_zero_of_natDegree_lt for constant polynomials
  simp [Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.natDegree_C,
    Polynomial.natDegree_pow, Polynomial.coeff_C_mul_X_pow]
  <;> norm_num
  <;> rfl
end
end MazurProof.N13NormalizedHermiteResidual
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13NormalizedHermiteResidual
noncomputable section
open Polynomial N13CenteredHermiteFirstOrder N13HermiteResidualDivisibility
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT
theorem residual_degree_le (a₀ a₁ b₀ b₁ : R₂) :
    (N13HermiteResidualDivisibility.residual a₀ a₁ b₀ b₁).natDegree ≤ 6 := by
  unfold N13HermiteResidualDivisibility.residual N13HermiteResidualDivisibility.quad N13HermiteResidualDivisibility.lin
  compute_degree!
end
end MazurProof.N13NormalizedHermiteResidual
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CenteredNormFirstOrder
noncomputable section
open Polynomial N13CenteredHermiteFirstOrder
private theorem map_zero_of_coeff_mem {R : Type*} [CommRing R]
    (J : Ideal R) (p : R[X]) (h : ∀ n, p.coeff n ∈ J) :
    p.map (Ideal.Quotient.mk J) = 0 := by
  ext n
  simpa using Ideal.Quotient.eq_zero_iff_mem.mpr (h n)
end
end MazurProof.N13CenteredNormFirstOrder
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CenteredNormFirstOrder
noncomputable section
open Polynomial N13CenteredHermiteFirstOrder
private theorem map_eq_of_coeff_sub_mem {R : Type*} [CommRing R]
    (J : Ideal R) (p q : R[X]) (h : ∀ n, (p - q).coeff n ∈ J) :
    p.map (Ideal.Quotient.mk J) = q.map (Ideal.Quotient.mk J) := by
  apply sub_eq_zero.mp
  simpa only [Polynomial.map_sub] using map_zero_of_coeff_mem J (p - q) h
end
end MazurProof.N13CenteredNormFirstOrder
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CenteredNormFirstOrder
noncomputable section
open Polynomial N13CenteredHermiteFirstOrder
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT MazurProof.N13MumfordCenteredDoublingJet.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
/-- Squaring a coefficientwise first-order deviation kills it modulo I². -/
theorem mapped_u_square (P : DiskPair) :
    (P.u ^ 2).map (Ideal.Quotient.mk (I P * I P)) =
      (N13AbelChartBase.baseSmoothMumford.u *
        N13MumfordCenteredDoublingJet.centeredSquareU P).map
          (Ideal.Quotient.mk (I P * I P)) := by
  let U := N13AbelChartBase.baseSmoothMumford.u
  let δ := P.u - U
  have hx₀ : P.x₀ ∈ I P := Ideal.subset_span (Set.mem_range_self (0 : Fin 2))
  have hx₁ : P.x₁ + 1 ∈ I P := Ideal.subset_span (Set.mem_range_self (1 : Fin 2))
  have hc₁ : -(P.x₀ + (P.x₁ + 1)) ∈ I P := (I P).neg_mem ((I P).add_mem hx₀ hx₁)
  have hc₀ : P.x₀ * P.x₁ ∈ I P := (I P).mul_mem_right _ hx₀
  have hδ : δ ∈ Ideal.map (_root_.Polynomial.C : R₂ →+* R₂[X]) (I P) := by
    rw [show δ = _root_.Polynomial.C (-(P.x₀ + (P.x₁ + 1))) * X + _root_.Polynomial.C (P.x₀ * P.x₁) from
      N13MumfordFormalTransitionJet.u_sub_base P]
    exact (Ideal.map _root_.Polynomial.C (I P)).add_mem
      ((Ideal.map _root_.Polynomial.C (I P)).mul_mem_right X (Ideal.mem_map_of_mem _root_.Polynomial.C hc₁))
      (Ideal.mem_map_of_mem _root_.Polynomial.C hc₀)
  have hδ₂ : δ ^ 2 ∈ Ideal.map (_root_.Polynomial.C : R₂ →+* R₂[X]) (I P * I P) := by
    rw [Ideal.map_mul, pow_two]
    exact Ideal.mul_mem_mul hδ hδ
  have hk : RingHom.ker (Ideal.Quotient.mk (I P * I P)) = I P * I P := by
    ext a
    exact Ideal.Quotient.eq_zero_iff_mem
  have hz : (δ ^ 2).map (Ideal.Quotient.mk (I P * I P)) = 0 := by
    have hmem : δ ^ 2 ∈ RingHom.ker (Polynomial.mapRingHom (Ideal.Quotient.mk (I P * I P))) := by
      rw [Polynomial.ker_mapRingHom, hk]
      exact hδ₂
    exact RingHom.mem_ker.mp hmem
  have hid := congrArg (Polynomial.map (Ideal.Quotient.mk (I P * I P)))
    (N13MumfordCenteredDoublingJet.u_sq_sub_base_mul_centeredSquareU P)
  rw [Polynomial.map_sub] at hid
  apply sub_eq_zero.mp
  rw [hid]
  exact hz
end
end MazurProof.N13CenteredNormFirstOrder
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CenteredNormFirstOrder
noncomputable section
open Polynomial N13CenteredHermiteFirstOrder
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT MazurProof.N13MumfordCenteredDoublingJet.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
/-- All centered cross coefficients, including the required 1 and 3,
follow from a normalized Hermite numerator and its exact norm. -/
theorem cross_coefficients_of_norm
    (P Q : DiskPair) (A b : R₂[X]) (k : R₂) (hA : A.Monic)
    (hcenter : ∀ n, (A - N13MumfordCenteredDoublingJet.centeredSquareU P).coeff n ∈ I P * I P)
    (hb : ∀ n, b.coeff n ∈ I P * I P)
    (hnorm :
      (N13AbelChartBase.baseSmoothMumford.u * A) ^ 2 -
        (N13AbelChartBase.baseSmoothMumford.u * A) * b *
          N13GeneralizedMumfordIntegral.hPoly -
        b ^ 2 * N13GeneralizedMumfordIntegral.rhsPoly =
      _root_.Polynomial.C k * P.u ^ 2 * N13AbelChartBase.baseSmoothMumford.u * Q.u) :
    ∀ n, (P.u ^ 2 - N13AbelChartBase.baseSmoothMumford.u * Q.u).coeff n ∈ I P * I P := by
  let J := I P * I P
  let q : R₂ →+* (R₂ ⧸ J) := Ideal.Quotient.mk J
  let U := N13AbelChartBase.baseSmoothMumford.u.map q
  let V := P.u.map q
  let W := Q.u.map q
  let Abar := A.map q
  have hUm : U.Monic := N13AbelChartBase.baseSmoothMumford.u_monic.map q
  have hVm : V.Monic := P.u_monic.map q
  have hWm : W.Monic := Q.u_monic.map q
  have hAm : Abar.Monic := hA.map q
  have hbzero : b.map q = 0 := map_zero_of_coeff_mem J b hb
  have hAc : Abar = (N13MumfordCenteredDoublingJet.centeredSquareU P).map q :=
    map_eq_of_coeff_sub_mem J _ _ hcenter
  have hV : V ^ 2 = U * Abar := by
    rw [hAc]
    simpa only [Polynomial.map_pow, Polynomial.map_mul] using mapped_u_square P
  have he : U ^ 2 * Abar ^ 2 = _root_.Polynomial.C (q k) * (V ^ 2 * U * W) := by
    have h := congrArg (Polynomial.mapRingHom q) hnorm
    simp only [Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_mul, Polynomial.map_C, hbzero,
      mul_zero, zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] at h
    change (U * Abar) ^ 2 = _root_.Polynomial.C (q k) * V ^ 2 * U * W at h
    convert h using 1 <;> ring
  have hk : q k = 1 := by
    have hl := congrArg Polynomial.leadingCoeff he
    rw [((hUm.pow 2).mul (hAm.pow 2)).leadingCoeff,
      (((hVm.pow 2).mul hUm).mul hWm).leadingCoeff_C_mul] at hl
    exact hl.symm
  rw [hk, C_1, one_mul, hV] at he
  have hAW : Abar = W := by
    apply ((hUm.pow 2).mul hAm).isRegular.left
    change (U ^ 2 * Abar) * Abar = (U ^ 2 * Abar) * W
    calc
      _ = U ^ 2 * Abar ^ 2 := by ring
      _ = (U * Abar) * U * W := he
      _ = _ := by ring
  have hzero : (P.u ^ 2 - N13AbelChartBase.baseSmoothMumford.u * Q.u).map q = 0 := by
    have hz : V ^ 2 - U * W = 0 := by rw [hV, hAW, sub_self]
    simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul] using hz
  intro n
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hc := congrArg (fun p : (R₂ ⧸ J)[X] => p.coeff n) hzero
  simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using hc
end
end MazurProof.N13CenteredNormFirstOrder
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CenteredPrincipalNumerator
noncomputable section
open SexticMumford
open scoped nonZeroDivisors
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT
theorem tensor_numerator_mem_product
    (D₀ D₁ D₂ D₃ : N13Mumford.SemiMumford K) (α : Fˣ)
    (h : mumfordIdealUnit M D₀ * mumfordIdealUnit M D₁ * toPrincipalIdeal R F α =
      mumfordIdealUnit M D₂ * mumfordIdealUnit M D₃) :
    ∃ z : R,
      z ∈ (mumfordIdeal M D₂.u D₂.v * mumfordIdeal M D₃.u D₃.v) *
        (mumfordIdeal M (conjugateSemiMumford M D₀).u (conjugateSemiMumford M D₀).v *
          mumfordIdeal M (conjugateSemiMumford M D₁).u (conjugateSemiMumford M D₁).v) ∧
      algebraMap R F z = (α : F) * algebraMap R F (xClass M (D₀.u * D₁.u)) := by
  have hx (D : N13Mumford.SemiMumford K) :
      algebraMap R F (xClass M D.u) ∈
        (mumfordIdealUnit M D : FractionalIdeal R⁰ F) *
          (mumfordIdealUnit M (conjugateSemiMumford M D) : FractionalIdeal R⁰ F) := by
    rw [coe_mumfordIdealUnit, coe_mumfordIdealUnit,
      conjugateSemiMumford_u, conjugateSemiMumford_v,
      mumfordIdeal_mul_conj_fractional]
    exact FractionalIdeal.mem_coeIdeal_of_mem R⁰
      (Ideal.subset_span (Set.mem_singleton (xClass M D.u)))
  have hα : (α : F) ∈ (toPrincipalIdeal R F α : FractionalIdeal R⁰ F) := by
    rw [coe_toPrincipalIdeal]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  have hmem := FractionalIdeal.mul_mem_mul
    (FractionalIdeal.mul_mem_mul (hx D₀) (hx D₁)) hα
  have hf := congrArg (fun U : InvFrac M => (U : FractionalIdeal R⁰ F)) h
  simp only [Units.val_mul] at hf
  have he :
      ((mumfordIdealUnit M D₀ : FractionalIdeal R⁰ F) *
          mumfordIdealUnit M (conjugateSemiMumford M D₀)) *
        ((mumfordIdealUnit M D₁ : FractionalIdeal R⁰ F) *
          mumfordIdealUnit M (conjugateSemiMumford M D₁)) * toPrincipalIdeal R F α =
      ((mumfordIdealUnit M D₂ : FractionalIdeal R⁰ F) * mumfordIdealUnit M D₃) *
        ((mumfordIdealUnit M (conjugateSemiMumford M D₀) : FractionalIdeal R⁰ F) *
          mumfordIdealUnit M (conjugateSemiMumford M D₁)) := by
    calc
      _ = ((mumfordIdealUnit M D₀ : FractionalIdeal R⁰ F) * mumfordIdealUnit M D₁ *
          toPrincipalIdeal R F α) *
        ((mumfordIdealUnit M (conjugateSemiMumford M D₀) : FractionalIdeal R⁰ F) *
          mumfordIdealUnit M (conjugateSemiMumford M D₁)) := by ac_rfl
      _ = _ := by rw [hf]
  rw [he] at hmem
  simp only [coe_mumfordIdealUnit, ← FractionalIdeal.coeIdeal_mul] at hmem
  obtain ⟨z, hz, hze⟩ := (FractionalIdeal.mem_coeIdeal R⁰).mp hmem
  refine ⟨z, hz, ?_⟩
  simpa only [xClass_mul, map_mul, mul_comm, mul_left_comm, mul_assoc] using hze
end
end MazurProof.N13CenteredPrincipalNumerator
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CenteredNumeratorPoleBounds
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator
open scoped LaurentSeries nonZeroDivisors
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT
theorem positive_numerator_order (P : DiskPair) (α : Fˣ) (n : R)
    (hn : algebraMap R F n = (α : F) * algebraMap R F (xClass M (P.mumford.u ^ 2)))
    (hα : Multiplicative.toAdd ((N13Infinity.positiveInfinityOrder K).ordPlus α) = 0) :
    (N13Infinity.coordinateToLaurent K n).order = -4 := by
  have ha : N13Infinity.functionFieldToLaurent K (α : F) ≠ 0 := by
    simpa only [map_zero] using (N13Infinity.functionFieldToLaurent_injective K).ne α.ne_zero
  have hu : P.mumford.u ^ 2 ≠ 0 := pow_ne_zero 2 P.mumford.u_monic.ne_zero
  have hm := congrArg (N13Infinity.functionFieldToLaurent K) hn
  rw [map_mul, N13Infinity.functionFieldToLaurent_algebraMap,
    N13Infinity.functionFieldToLaurent_algebraMap,
    N13Infinity.coordinateToLaurent_xClass] at hm
  change N13Infinity.coordinateToLaurent K n =
    N13Infinity.functionFieldToLaurent K (α : F) *
      N13BranchNorm.evalPoly K (P.mumford.u ^ 2) at hm
  change (N13Infinity.functionFieldToLaurent K (α : F)).order = 0 at hα
  rw [hm, HahnSeries.order_mul ha (N13BranchNorm.evalPoly_ne_zero K hu), hα,
    N13BranchNorm.evalPoly_order K _ hu, natDegree_pow,
    show P.mumford.u.natDegree = 2 from
      N13TwoAdicAbelChartPic.DiskPair.sexticSemi_u_natDegree P]
  norm_num
end
end MazurProof.N13CenteredNumeratorPoleBounds
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CenteredNumeratorPoleBounds
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator
open scoped LaurentSeries nonZeroDivisors
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT
theorem negative_numerator_order (P : DiskPair) (α : Fˣ) (n : R)
    (hn : algebraMap R F n = (α : F) * algebraMap R F (xClass M (P.mumford.u ^ 2)))
    (hα : Multiplicative.toAdd ((N13InfinityMinus.negativeInfinityOrder K).ordPlus α) = 0) :
    (N13InfinityMinus.coordinateToLaurentMinus K n).order = -4 := by
  have ha : N13InfinityMinus.functionFieldToLaurentMinus K (α : F) ≠ 0 := by
    simpa only [map_zero] using (N13InfinityMinus.functionFieldToLaurentMinus_injective K).ne α.ne_zero
  have hu : P.mumford.u ^ 2 ≠ 0 := pow_ne_zero 2 P.mumford.u_monic.ne_zero
  have hm := congrArg (N13InfinityMinus.functionFieldToLaurentMinus K) hn
  rw [map_mul, N13InfinityMinus.functionFieldToLaurentMinus_algebraMap,
    N13InfinityMinus.functionFieldToLaurentMinus_algebraMap,
    N13InfinityMinus.coordinateToLaurentMinus_xClass] at hm
  change N13InfinityMinus.coordinateToLaurentMinus K n =
    N13InfinityMinus.functionFieldToLaurentMinus K (α : F) *
      N13BranchNorm.evalPoly K (P.mumford.u ^ 2) at hm
  change (N13InfinityMinus.functionFieldToLaurentMinus K (α : F)).order = 0 at hα
  rw [hm, HahnSeries.order_mul ha (N13BranchNorm.evalPoly_ne_zero K hu), hα,
    N13BranchNorm.evalPoly_order K _ hu, natDegree_pow,
    show P.mumford.u.natDegree = 2 from
      N13TwoAdicAbelChartPic.DiskPair.sexticSemi_u_natDegree P]
  norm_num
end
end MazurProof.N13CenteredNumeratorPoleBounds
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CenteredNumeratorPoleBounds
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator
open scoped LaurentSeries nonZeroDivisors
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT
theorem polynomial_bounds (n : R) (hne : n ≠ 0)
    (hp : (N13Infinity.coordinateToLaurent K n).order = -4)
    (hm : (N13InfinityMinus.coordinateToLaurentMinus K n).order = -4) :
    (coeff0 M n).natDegree ≤ 4 ∧ (coeffY M n).natDegree ≤ 1 := by
  let p := coeff0 M n
  let q := coeffY M n
  have hr : N13BranchNorm.linearFunction K p q = n := recompose M n
  have hx := N13BranchLeading.branch_min_order K p q (by rwa [hr])
  rw [hr, hp, hm, min_self] at hx
  have hb : N13BranchLeading.poleDegree K p q ≤ 4 := by omega
  change p.natDegree ≤ 4 ∧ q.natDegree ≤ 1
  by_cases hq : q = 0
  · simp only [N13BranchLeading.poleDegree, hq, if_true] at hb
    refine ⟨(le_max_left _ _).trans hb, ?_⟩
    rw [hq, Polynomial.natDegree_zero]
    exact Nat.zero_le _
  · simp only [N13BranchLeading.poleDegree, hq, if_false] at hb
    have h2 := (le_max_right _ _).trans hb
    exact ⟨(le_max_left _ _).trans hb, by omega⟩
end
end MazurProof.N13CenteredNumeratorPoleBounds
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GoodCenteredNumerator
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT
theorem toGood_recompose (n : R) :
    toGood n = gx (goodP n) + gx (goodQ n) * gy := by
  conv_lhs => rw [← recompose M n]
  rw [map_add, map_mul,
    N13GoodSexticCoordinateEquiv.toGood_xClass,
    N13GoodSexticCoordinateEquiv.toGood_xClass,
    N13GoodSexticCoordinateEquiv.toGood_yClass]
  simp only [goodP, goodQ, N13GoodSexticCoordinateEquiv.sexticYInGood,
    N13GoodSexticCoordinateEquiv.goodXHom_apply,
    N13GeneralizedMumfordIntegral.xClass_add,
    N13GeneralizedMumfordIntegral.xClass_mul,
    N13GeneralizedMumfordIntegral.xClass_natCast]
  have h2 : N13GeneralizedMumfordIntegral.xClass (2 : K[X]) = 2 := by
    have := N13GeneralizedMumfordIntegral.xClass_natCast (R := K) 2
    exact_mod_cast this
  rw [h2]
  ring
end
end MazurProof.N13GoodCenteredNumerator
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GoodCenteredNumerator
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem toGood_mumfordIdeal (P : DiskPair) :
    Ideal.map toGood (mumfordIdeal M P.mumford.u P.mumford.v) =
      N13GeneralizedMumfordIntegral.mumfordIdeal
        (N13TwoAdicMumfordTransport.mapPoly P.u)
        (N13TwoAdicMumfordTransport.mapPoly P.v) := by
  have ht := N13TwoAdicMumfordTransport.map_mumfordIdeal_sexticSemi P.smoothMumford 0
  change Ideal.map toSextic
    (N13GeneralizedMumfordIntegral.mumfordIdeal
      (N13TwoAdicMumfordTransport.mapPoly P.u)
      (N13TwoAdicMumfordTransport.mapPoly P.v)) =
        mumfordIdeal M P.mumford.u P.mumford.v at ht
  have hi : toGood.comp toSextic = RingHom.id Good := by
    exact RingHom.ext fun z =>
      (N13GoodSexticCoordinateEquiv.coordinateRingEquiv (K := K)).symm_apply_apply z
  rw [← ht, Ideal.map_map, hi, Ideal.map_id]
end
end MazurProof.N13GoodCenteredNumerator
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GoodCenteredNumerator
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem base_divides_goodP (n : R)
    (hn : n ∈ mumfordIdeal M B.mumford.u B.mumford.v) :
    (X ^ 2 + X : K[X]) ∣ goodP n := by
  let D := N13TwoAdicMumfordTransport.baseChange B.smoothMumford
  have hu : D.u = X ^ 2 + X := by
    simp [D, N13TwoAdicMumfordTransport.mapPoly, N13FormalAbelLinearization.uBase]
  have hv : D.v = 0 := by simp [D]
  have hm := Ideal.mem_map_of_mem toGood hn
  rw [toGood_mumfordIdeal] at hm
  change toGood n ∈ N13GeneralizedMumfordIntegral.mumfordIdeal D.u D.v at hm
  have hd := (N13GeneralizedMumfordIntegral.mem_mumfordIdeal_iff D (toGood n)).mp hm
  rw [hu, hv, mul_zero, add_zero, toGood_recompose] at hd
  simpa only [map_add, N13GeneralizedMumfordIntegral.coeff0_xClass,
    N13GeneralizedMumfordIntegral.coeff0_xClass_mul_yClass, add_zero] using hd
end
end MazurProof.N13GoodCenteredNumerator
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GoodCenteredNumerator
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT
theorem good_degrees (n : R)
    (hp : (coeff0 M n).natDegree ≤ 4) (hq : (coeffY M n).natDegree ≤ 1) :
    (goodP n).natDegree ≤ 4 ∧ (goodQ n).natDegree ≤ 1 := by
  have hh : (N13GeneralizedMumfordIntegral.hPoly (R := K)).natDegree ≤ 3 := by
    unfold N13GeneralizedMumfordIntegral.hPoly
    compute_degree!
  constructor
  · apply (natDegree_add_le _ _).trans
    apply max_le hp
    exact natDegree_mul_le.trans (by omega)
  · change ((2 : K[X]) * coeffY M n).natDegree ≤ 1
    have he := natDegree_mul_le (p := (2 : K[X])) (q := coeffY M n)
    simpa using he.trans (by simpa using hq)
end
end MazurProof.N13GoodCenteredNumerator
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GoodCenteredNumerator
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT
theorem exists_good_hermite_shape (n : R)
    (hp : (coeff0 M n).natDegree ≤ 4) (hq : (coeffY M n).natDegree ≤ 1)
    (hbase : n ∈ mumfordIdeal M B.mumford.u B.mumford.v) :
    ∃ A b : K[X], A.natDegree ≤ 2 ∧ b.natDegree ≤ 1 ∧
      toGood n = gx ((X ^ 2 + X) * A) + gx b * gy := by
  obtain ⟨A, hA⟩ := base_divides_goodP n hbase
  have hg := good_degrees n hp hq
  refine ⟨A, goodQ n, ?_, hg.2, ?_⟩
  · by_cases hz : A = 0
    · simp [hz]
    · have hU : (X ^ 2 + X : K[X]).Monic := by monicity!
      have hd : (X ^ 2 + X : K[X]).natDegree = 2 := by compute_degree!
      have hp' := hg.1
      rw [hA, natDegree_mul hU.ne_zero hz, hd] at hp'
      omega
  · rw [toGood_recompose, hA]
end
end MazurProof.N13GoodCenteredNumerator
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GoodCenteredNumerator
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT
theorem selected_base_membership
    (P Q : DiskPair) (n : R)
    (hn : n ∈ (mumfordIdeal M Q.mumford.u Q.mumford.v *
        mumfordIdeal M B.mumford.u B.mumford.v) *
      (mumfordIdeal M (conjugateSemiMumford M P.mumford.toSemi).u
        (conjugateSemiMumford M P.mumford.toSemi).v) ^ 2) :
    n ∈ mumfordIdeal M B.mumford.u B.mumford.v :=
  Ideal.mul_le_right (Ideal.mul_le_left hn)
end
end MazurProof.N13GoodCenteredNumerator
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13IntegralMatchedNorm
noncomputable section
open Polynomial N13CenteredPrincipalNumerator N13ActualHermiteEquations
attribute [local instance] MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralMatchedNorm.instFactPrimeOfNatNat_fLT
theorem norm_map (A b : R₂[X]) :
    (normPoly A b).map c =
      ((X ^ 2 + X) * A.map c) ^ 2 -
        ((X ^ 2 + X) * A.map c) * b.map c * N13GeneralizedMumfordIntegral.hPoly -
        (b.map c) ^ 2 * N13GeneralizedMumfordIntegral.rhsPoly := by
  simp [normPoly, U, N13FormalAbelLinearization.uBase,
    N13GeneralizedMumfordIntegral.hPoly, N13GeneralizedMumfordIntegral.rhsPoly]
end
end MazurProof.N13IntegralMatchedNorm
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13IntegralMatchedNorm
noncomputable section
open Polynomial N13CenteredPrincipalNumerator N13ActualHermiteEquations
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralMatchedNorm.instFactPrimeOfNatNat_fLT
theorem norm_leading (P : DiskPair) (d₀ d₁ e₀ e₁ : R₂)
    (he₁ : e₁ ∈ N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P) :
    (normPoly (N13HermiteResidualDivisibility.quad d₀ d₁)
      (N13HermiteResidualDivisibility.lin e₀ e₁)).leadingCoeff = 1 - e₁ := by
  have hu := N13NormalizedHermiteResidual.one_sub_unit P e₁ he₁
  have hd : (N13HermiteResidualDivisibility.residual d₀ d₁ e₀ e₁).natDegree = 6 := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
      (N13NormalizedHermiteResidual.residual_degree_le _ _ _ _)
    rw [N13NormalizedHermiteResidual.residual_coeff_six]
    exact hu.ne_zero
  have hf : normPoly (N13HermiteResidualDivisibility.quad d₀ d₁)
      (N13HermiteResidualDivisibility.lin e₀ e₁) =
        U * N13HermiteResidualDivisibility.residual d₀ d₁ e₀ e₁ := by
    simpa [normPoly, U, N13FormalAbelLinearization.uBase] using
      N13HermiteResidualDivisibility.norm_factor d₀ d₁ e₀ e₁
  rw [hf, leadingCoeff_monic_mul N13AbelChartBase.baseSmoothMumford.u_monic,
    leadingCoeff, hd, N13NormalizedHermiteResidual.residual_coeff_six]
end
end MazurProof.N13IntegralMatchedNorm
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13IntegralMatchedNorm
noncomputable section
open Polynomial N13CenteredPrincipalNumerator N13ActualHermiteEquations
attribute [local instance] _root_.MazurProof.N13IntegralMatchedNorm.instFactPrimeOfNatNat_fLT
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralMatchedNorm.instFactPrimeOfNatNat_fLT
theorem descend_actual_norm
    (P Q : DiskPair) (A b : K[X]) (t : K) (ht : t ≠ 0)
    (d₀ d₁ e₀ e₁ : R₂)
    (hA : A = _root_.Polynomial.C t * (N13HermiteResidualDivisibility.quad d₀ d₁).map c)
    (hb : b = _root_.Polynomial.C t * (N13HermiteResidualDivisibility.lin e₀ e₁).map c)
    (he₁ : e₁ ∈ N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P)
    (k : Kˣ)
    (hnorm : ((X ^ 2 + X) * A) ^ 2 -
        ((X ^ 2 + X) * A) * b * N13GeneralizedMumfordIntegral.hPoly -
        b ^ 2 * N13GeneralizedMumfordIntegral.rhsPoly =
      _root_.Polynomial.C (k : K) * (P.u.map c) ^ 2 * (X ^ 2 + X) * Q.u.map c) :
    normPoly (N13HermiteResidualDivisibility.quad d₀ d₁)
      (N13HermiteResidualDivisibility.lin e₀ e₁) =
        _root_.Polynomial.C (1 - e₁) * P.u ^ 2 * U * Q.u := by
  let N := normPoly (N13HermiteResidualDivisibility.quad d₀ d₁)
    (N13HermiteResidualDivisibility.lin e₀ e₁)
  let T := P.u ^ 2 * U * Q.u
  have hTm : (T.map c).Monic :=
    (((P.u_monic.pow 2).mul N13AbelChartBase.baseSmoothMumford.u_monic).mul Q.u_monic).map c
  have hlN : (N.map c).leadingCoeff = c (1 - e₁) := by
    rw [Polynomial.leadingCoeff_map_of_injective (f := c) (IsFractionRing.injective R₂ K)]
    exact congrArg c (norm_leading P d₀ d₁ e₀ e₁ he₁)
  have he : _root_.Polynomial.C (t ^ 2) * N.map c = _root_.Polynomial.C (k : K) * T.map c := by
    calc
      _root_.Polynomial.C (t ^ 2) * N.map c =
          ((X ^ 2 + X) * A) ^ 2 -
            ((X ^ 2 + X) * A) * b * N13GeneralizedMumfordIntegral.hPoly -
            b ^ 2 * N13GeneralizedMumfordIntegral.rhsPoly := by
        simp only [hA, hb]
        dsimp [N]
        rw [norm_map, map_pow]
        ring
      _ = _root_.Polynomial.C (k : K) * (P.u.map c) ^ 2 * (X ^ 2 + X) * Q.u.map c := hnorm
      _ = _root_.Polynomial.C (k : K) * T.map c := by
        simp [T, U, N13FormalAbelLinearization.uBase, mul_assoc]
  have hk : t ^ 2 * c (1 - e₁) = (k : K) := by
    have hl := congrArg Polynomial.leadingCoeff he
    rw [leadingCoeff_mul, leadingCoeff_C, hlN, hTm.leadingCoeff_C_mul] at hl
    exact hl
  have hmapped : N.map c = _root_.Polynomial.C (c (1 - e₁)) * T.map c := by
    apply mul_left_cancel₀ (show (_root_.Polynomial.C (t ^ 2) : K[X]) ≠ 0 from C_ne_zero.mpr (pow_ne_zero 2 ht))
    rw [he, ← hk, map_mul, mul_assoc]
  apply Polynomial.map_injective c (IsFractionRing.injective R₂ K)
  simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
    N, T, mul_assoc] using hmapped
end
end MazurProof.N13IntegralMatchedNorm
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13IntegralHermiteCoefficientBounds
noncomputable section
open Polynomial N13CenteredHermiteFirstOrder N13HermiteResidualDivisibility
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT
private theorem linear_coefficients_mem (J : Ideal R₂) (a b : R₂)
    (ha : a ∈ J) (hb : b ∈ J) : ∀ n, (_root_.Polynomial.C a + _root_.Polynomial.C b * X).coeff n ∈ J := by
  intro n
  rcases n with _ | n
  · simpa using ha
  · rcases n with _ | n
    · simpa using hb
    · have hz : (_root_.Polynomial.C a + _root_.Polynomial.C b * X).coeff (n + 1 + 1) = 0 := by simp
      rw [hz]
      exact J.zero_mem
end
end MazurProof.N13IntegralHermiteCoefficientBounds
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13IntegralHermiteCoefficientBounds
noncomputable section
open Polynomial N13CenteredHermiteFirstOrder N13HermiteResidualDivisibility
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT
theorem quad_monic (a b : R₂) : (quad a b).Monic := by
  unfold quad
  monicity!
end
end MazurProof.N13IntegralHermiteCoefficientBounds
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13IntegralHermiteCoefficientBounds
noncomputable section
open Polynomial N13CenteredHermiteFirstOrder N13HermiteResidualDivisibility
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT
theorem lin_coefficients_mem (P : DiskPair) (e₀ e₁ : R₂)
    (he₀ : e₀ ∈ I P * I P) (he₁ : e₁ ∈ I P * I P) :
    ∀ n, (lin e₀ e₁).coeff n ∈ I P * I P :=
  linear_coefficients_mem (I P * I P) e₀ e₁ he₀ he₁
end
end MazurProof.N13IntegralHermiteCoefficientBounds
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13IntegralHermiteCoefficientBounds
noncomputable section
open Polynomial N13CenteredHermiteFirstOrder N13HermiteResidualDivisibility
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT MazurProof.N13MumfordCenteredDoublingJet.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
theorem centered_coefficients_mem (P : DiskPair) (d₀ d₁ : R₂)
    (hd₀ : d₀ - 2 * P.x₀ * P.x₁ ∈ I P * I P)
    (hd₁ : d₁ + 2 * (P.x₀ + P.x₁) + 1 ∈ I P * I P) :
    ∀ n, (quad d₀ d₁ - N13MumfordCenteredDoublingJet.centeredSquareU P).coeff n ∈ I P * I P := by
  have he : quad d₀ d₁ - N13MumfordCenteredDoublingJet.centeredSquareU P =
      _root_.Polynomial.C (d₀ - 2 * P.x₀ * P.x₁) + _root_.Polynomial.C (d₁ + 2 * (P.x₀ + P.x₁) + 1) * X := by
    simp only [quad, N13MumfordCenteredDoublingJet.centeredSquareU,
      N13TwoAdicAbelChartData.DiskPair.u, N13AbelChartBase.baseSmoothMumford_u,
      N13FormalAbelLinearization.uBase, map_add, map_sub, map_mul, map_ofNat, map_one]
    ring
  rw [he]
  exact linear_coefficients_mem (I P * I P) _ _ hd₀ hd₁
end
end MazurProof.N13IntegralHermiteCoefficientBounds
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ConstructedKernelDoubling
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator
open N13CenteredNumeratorPoleBounds N13GoodCenteredNumerator
open N13PrincipalHermiteNormalization N13ActualPrincipalNorm N13IntegralMatchedNorm
open N13IntegralHermiteCoefficientBounds
attribute [local instance] _root_.MazurProof.N13ConstructedKernelDoubling.instFactPrimeOfNatNat_fLT
attribute [local instance] MazurProof.N13ActualPrincipalNorm.instFactPrimeOfNatNat_fLT MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralMatchedNorm.instFactPrimeOfNatNat_fLT MazurProof.N13PrincipalHermiteNormalization.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem selected_cross_coefficients
    {H : AddSubgroup N13RationalKernelDoublingAdapter.RationalPic}
    (L : N13RationalKernelDoublingAdapter.NearBaseFamily H) (z : H) :
    ∀ i, ((L.pair z).u ^ 2 - N13AbelChartBase.baseSmoothMumford.u *
        (L.pair (2 • z)).u).coeff i ∈
      N13TwoAdicKernelChart.coordIdeal L.coord z * N13TwoAdicKernelChart.coordIdeal L.coord z := by
  let P := L.pair z
  let Q := L.pair (2 • z)
  obtain ⟨α, hα, hp, hm⟩ := HuangN13.N13CenteredPrincipalNumerator.multiplier_of_centered_double P Q
    (N13MumfordCenteredDoublingAdapter.centeredPic_pair_two_nsmul L z)
  obtain ⟨n, hmem, he⟩ := tensor_numerator_mem_product
    P.mumford.toSemi P.mumford.toSemi Q.mumford.toSemi B.mumford.toSemi α hα
  have hmem' : n ∈ (mumfordIdeal M Q.mumford.u Q.mumford.v *
      mumfordIdeal M B.mumford.u B.mumford.v) *
    (mumfordIdeal M (conjugateSemiMumford M P.mumford.toSemi).u
      (conjugateSemiMumford M P.mumford.toSemi).v) ^ 2 := by
    rw [pow_two]
    exact hmem
  have he' : algebraMap R F n = (α : F) * algebraMap R F (xClass M (P.mumford.u ^ 2)) := by
    rw [pow_two]
    exact he
  have hn : n ≠ 0 := by
    intro hz
    have hx : algebraMap R F (xClass M (P.mumford.u ^ 2)) ≠ 0 := by
      have h0 := (IsFractionRing.injective R F).ne
        (xClass_ne_zero M (pow_ne_zero 2 P.mumford.u_monic.ne_zero))
      rw [map_zero] at h0
      exact h0
    rw [hz, map_zero] at he'
    exact mul_ne_zero α.ne_zero hx he'.symm
  have hsmall := polynomial_bounds n hn
    (positive_numerator_order P α n he' hp) (negative_numerator_order P α n he' hm)
  obtain ⟨A, b, hA, hb, hshape⟩ := exists_good_hermite_shape n hsmall.1 hsmall.2
    (selected_base_membership P Q n hmem')
  obtain ⟨t, d₀, d₁, e₀, e₁, ht, hAmatch, hbmatch, he₀, he₁, hd₀, hd₁⟩ :=
    HuangN13.N13PrincipalHermiteNormalization.normalize_actual_numerator P Q n A b hn hA hb hshape hmem'
  -- hα belongs to this exact α; no independent norm multiplier is selected.
  obtain ⟨k, hnormQ⟩ := HuangN13.N13ActualPrincipalNorm.norm_of_actual_shape P Q α n A b hα he' hshape
  have hnormZ := descend_actual_norm P Q A b t ht d₀ d₁ e₀ e₁ hAmatch hbmatch he₁ k
    (by simpa only [N13TwoAdicMumfordTransport.mapPoly_apply] using hnormQ)
  have hcross := N13CenteredNormFirstOrder.cross_coefficients_of_norm P Q
    (N13HermiteResidualDivisibility.quad d₀ d₁)
    (N13HermiteResidualDivisibility.lin e₀ e₁) (1 - e₁)
    (quad_monic d₀ d₁) (centered_coefficients_mem P d₀ d₁ hd₀ hd₁)
    (lin_coefficients_mem P e₀ e₁ he₀ he₁) hnormZ
  intro i
  exact hcross i
end
end MazurProof.N13ConstructedKernelDoubling
end
end


set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
theorem solution
    {H : AddSubgroup MazurProof.N13RationalKernelDoublingAdapter.RationalPic}
    (L : MazurProof.N13RationalKernelDoublingAdapter.NearBaseFamily H) (z : H) :
    ∀ i, ((L.pair z).u ^ 2 - MazurProof.N13AbelChartBase.baseSmoothMumford.u *
        (L.pair (2 • z)).u).coeff i ∈
      MazurProof.N13TwoAdicKernelChart.coordIdeal L.coord z * MazurProof.N13TwoAdicKernelChart.coordIdeal L.coord z := by
  exact MazurProof.N13ConstructedKernelDoubling.selected_cross_coefficients L z
