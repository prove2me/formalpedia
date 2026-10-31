-- Prove2me | solution 1 for HuangN13.N13RationalKernelDoublingAdapter.NearBaseFamily.squareJet_sub_double_coord_mem_sq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:33:14.380132+00:00
-- url     : https://prove2.me/submissions/2676c614-5627-4956-8319-0697c4f7ea73

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_DoublingStatementCore
import Theorems.Thm_MazurProof_N13FormalCurveOverlap_ofOverlap_mul
import Theorems.Thm_MazurProof_N13FormalCurveOverlap_ofOverlap_oneOverlap
import Theorems.Thm_MazurProof_N13FormalCurveOverlap_ofOverlap_toOverlap
import Theorems.Thm_MazurProof_N13FormalLineBundleCech_mulOverlap_assoc

set_option autoImplicit false

section
section
set_option autoImplicit false
namespace MazurProof.N13FormalLineBundleCech
noncomputable section
open HahnSeries
open scoped LaurentSeries
theorem mulOverlap_comm
    {R : Type*} [CommRing R]
    (z w : N13CechLaurentSeriesCore.Overlap (R := R)) :
    mulOverlap z w = mulOverlap w z := by
  apply Prod.ext <;>
    simp [mulOverlap]
  <;> ring
end
end MazurProof.N13FormalLineBundleCech
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13FormalLineBundleCech
noncomputable section
open HahnSeries
open scoped LaurentSeries
@[simp] theorem mul_oneOverlap
    {R : Type*} [CommRing R]
    (z : N13CechLaurentSeriesCore.Overlap (R := R)) :
    mulOverlap z oneOverlap = z := by
  apply Prod.ext <;>
    simp [mulOverlap, oneOverlap]
end
end MazurProof.N13FormalLineBundleCech
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13FormalLineBundleCech
noncomputable section
open HahnSeries
open scoped LaurentSeries
theorem mulOverlap_add_right
    {R : Type*} [CommRing R]
    (x y z : N13CechLaurentSeriesCore.Overlap (R := R)) :
    mulOverlap x (y + z) =
      mulOverlap x y + mulOverlap x z :=
  (leftMul x).map_add y z
end
end MazurProof.N13FormalLineBundleCech
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13FormalLineBundleCech
noncomputable section
open HahnSeries
open scoped LaurentSeries
theorem mulOverlap_add_left
    {R : Type*} [CommRing R]
    (x y z : N13CechLaurentSeriesCore.Overlap (R := R)) :
    mulOverlap (x + y) z =
      mulOverlap x z + mulOverlap y z := by
  rw [mulOverlap_comm (x + y) z,
    mulOverlap_add_right,
    mulOverlap_comm z x,
    mulOverlap_comm z y]
end
end MazurProof.N13FormalLineBundleCech
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13FormalLineBundleCech
noncomputable section
open HahnSeries
open scoped LaurentSeries
namespace NearIdentityTransition
variable (g : NearIdentityTransition)
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem square_transition :
    g.square.transition =
      mulOverlap g.transition g.transition :=
  rfl
end NearIdentityTransition
end
end MazurProof.N13FormalLineBundleCech
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13FormalLineBundleCech
noncomputable section
open HahnSeries
open scoped LaurentSeries
namespace NearIdentityTransition
variable (g : NearIdentityTransition)
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Squaring a transition is linear to first order.  The exact error is the
product of the transition displacement with itself. -/
theorem square_deviation :
    g.square.transition - oneOverlap -
          (g.deviation + g.deviation) =
      mulOverlap g.deviation g.deviation := by
  have htransition :
      g.transition = g.deviation + oneOverlap := by
    rw [deviation, sub_add_cancel]
  rw [square_transition, htransition]
  simp only [mulOverlap_add_left, mulOverlap_add_right,
    oneOverlap_mul, mul_oneOverlap]
  abel
end NearIdentityTransition
end
end MazurProof.N13FormalLineBundleCech
end
end

section
section
set_option autoImplicit false
open Polynomial
open scoped LaurentSeries PowerSeries
namespace MazurProof.N13MumfordFormalTransition
noncomputable section
attribute [local instance] tInvInvertible
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
@[simp] theorem nearIdentityTransition_transition
    (D : NearBaseMumford) :
    (nearIdentityTransition D).transition =
      N13FormalCurveOverlap.toOverlap
        (transitionUnit D : FormalCurve) :=
  rfl
end
end MazurProof.N13MumfordFormalTransition
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Multiplication is additive in its left argument, hence also preserves
subtraction there. -/
theorem mulOverlap_sub_left
    (x y z : Overlap) :
    N13FormalLineBundleCech.mulOverlap (x - y) z =
      N13FormalLineBundleCech.mulOverlap x z -
        N13FormalLineBundleCech.mulOverlap y z := by
  rw [N13FormalLineBundleCech.mulOverlap_comm (x - y) z,
    N13FormalLineBundleCech.mulOverlap_comm x z,
    N13FormalLineBundleCech.mulOverlap_comm y z]
  exact
    (N13FormalLineBundleCech.leftMul z).map_sub x y
end
end MazurProof.N13MumfordFormalTransitionJet
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
/-- Multiply the transition displacement back by the fixed base
trivialization.  This removes the inverse power series exactly. -/
def weightedDeviation (P : DiskPair) : Overlap :=
  weightedDeviationOfTransition (diskTransition P)
end
end MazurProof.N13MumfordFormalTransitionJet
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- After restoring one fixed base factor, the nonlinear error in transition
squaring is one raw displacement times one weighted displacement. -/
theorem square_weightedDeviation
    (g : N13FormalLineBundleCech.NearIdentityTransition) :
    weightedDeviationOfTransition g.square -
          (weightedDeviationOfTransition g +
            weightedDeviationOfTransition g) =
      N13FormalLineBundleCech.mulOverlap
        g.deviation (weightedDeviationOfTransition g) := by
  have h :=
    congrArg
      (fun z : Overlap =>
        N13FormalLineBundleCech.mulOverlap z baseOverlap)
      g.square_deviation
  simpa only [weightedDeviationOfTransition,
    N13FormalLineBundleCech.NearIdentityTransition.deviation,
    mulOverlap_sub_left,
    N13FormalLineBundleCech.mulOverlap_add_left,
    N13FormalLineBundleCech.mulOverlap_assoc] using h
end
end MazurProof.N13MumfordFormalTransitionJet
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The inverse fixed base transition in overlap coordinates. -/
def baseInverseOverlap : Overlap :=
  N13FormalCurveOverlap.toOverlap
    ((N13MumfordFormalTransition.baseFormalPolyUnit⁻¹ :
      FormalCurveˣ) : FormalCurve)
end
end MazurProof.N13MumfordFormalTransitionJet
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Restoring the base denominator and then multiplying by its inverse
recovers the raw transition displacement. -/
theorem weightedDeviation_mul_baseInverse (P : DiskPair) :
    N13FormalLineBundleCech.mulOverlap
        (weightedDeviation P) baseInverseOverlap =
      (diskTransition P).deviation := by
  rw [weightedDeviation, weightedDeviationOfTransition, baseOverlap,
    baseInverseOverlap,
    N13FormalLineBundleCech.mulOverlap_assoc,
    ← N13FormalCurveOverlap.toOverlap_mul]
  simp
end
end MazurProof.N13MumfordFormalTransitionJet
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
theorem weightedDeviation_eq (P : DiskPair) :
    weightedDeviation P =
      (N13FormalCurveOverlap.polyAtTInv
        (P.u - N13AbelChartBase.baseSmoothMumford.u), 0) := by
  apply N13FormalCurveOverlap.ofOverlap_injective
  rw [weightedDeviation, weightedDeviationOfTransition, baseOverlap,
    N13FormalCurveOverlap.ofOverlap_mul]
  simp only [diskTransition,
    N13FormalLineBundleCech.NearIdentityTransition.deviation,
    N13MumfordFormalTransition.nearIdentityTransition_transition,
    map_sub, N13FormalCurveOverlap.ofOverlap_toOverlap,
    N13FormalCurveOverlap.ofOverlap_oneOverlap]
  simp only [N13MumfordFormalTransition.transitionUnit,
    N13TwoAdicAbelChartRecover.NearBaseMumford.ofDiskPair_u]
  change
    (((N13MumfordFormalTransition.formalPolyUnit
          P.u P.u_monic : FormalCurve) *
          ((N13MumfordFormalTransition.baseFormalPolyUnit⁻¹ :
            FormalCurveˣ) : FormalCurve) - 1) *
        (N13MumfordFormalTransition.baseFormalPolyUnit :
          FormalCurve)) =
      N13FormalCurveOverlap.ofOverlap
        (N13FormalCurveOverlap.polyAtTInv P.u -
            N13FormalCurveOverlap.polyAtTInv
              N13AbelChartBase.baseSmoothMumford.u,
          0)
  calc
    _ =
        (N13MumfordFormalTransition.formalPolyUnit
            P.u P.u_monic : FormalCurve) -
          (N13MumfordFormalTransition.baseFormalPolyUnit :
            FormalCurve) := by
      rw [sub_mul, mul_assoc]
      simp
    _ =
        algebraMap Laurent FormalCurve
          (N13FormalCurveOverlap.polyAtTInv P.u -
            N13FormalCurveOverlap.polyAtTInv
              N13AbelChartBase.baseSmoothMumford.u) := by
      rw [N13MumfordFormalTransition.coe_formalPolyUnit]
      change
        _ -
            (N13MumfordFormalTransition.formalPolyUnit
              N13AbelChartBase.baseSmoothMumford.u
              N13AbelChartBase.baseSmoothMumford.u_monic :
              FormalCurve) =
          _
      rw [N13MumfordFormalTransition.coe_formalPolyUnit]
      rw [map_sub]
    _ =
        N13FormalCurveOverlap.ofOverlap
          (N13FormalCurveOverlap.polyAtTInv P.u -
              N13FormalCurveOverlap.polyAtTInv
                N13AbelChartBase.baseSmoothMumford.u,
            0) := by
      simp [N13FormalCurveOverlap.ofOverlap]
end
end MazurProof.N13MumfordFormalTransitionJet
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
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
@[simp] theorem weightedDeviation_coeff_negOne (P : DiskPair) :
    (weightedDeviation P).1.coeff (-1) =
      -(P.x₀ + (P.x₁ + 1)) := by
  rw [weightedDeviation_eq, u_sub_base]
  simp [N13FormalCurveOverlap.polyAtTInv,
    N13FormalCurveOverlap.tPow,
    HahnSeries.algebraMap_apply',
    HahnSeries.coeff_mul_single]
end
end MazurProof.N13MumfordFormalTransitionJet
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
@[simp] theorem weightedDeviation_coeff_zero (P : DiskPair) :
    (weightedDeviation P).1.coeff 0 =
      P.x₀ * P.x₁ := by
  rw [weightedDeviation_eq, u_sub_base]
  simp [N13FormalCurveOverlap.polyAtTInv,
    N13FormalCurveOverlap.tPow,
    HahnSeries.algebraMap_apply',
    HahnSeries.coeff_mul_single]
end
end MazurProof.N13MumfordFormalTransitionJet
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
@[simp] theorem weightedDeviation_snd (P : DiskPair) :
    (weightedDeviation P).2 = 0 := by
  rw [weightedDeviation_eq]
end
end MazurProof.N13MumfordFormalTransitionJet
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Multiplying a coefficientwise ideal-valued Laurent series by an
arbitrary Laurent series preserves coefficientwise ideal membership. -/
theorem coeff_mul_mem_leftIdeal
    (I : Ideal R₂) (f g : Laurent)
    (hf : ∀ n : ℤ, f.coeff n ∈ I)
    (n : ℤ) :
    (f * g).coeff n ∈ I := by
  rw [HahnSeries.coeff_mul]
  exact Ideal.sum_mem _ fun p _ =>
    I.mul_mem_right (g.coeff p.2) (hf p.1)
end
end MazurProof.N13MumfordFormalTransitionJet
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- Products of two coefficientwise ideal-valued Laurent series have all
coefficients in the product ideal. -/
theorem coeff_mul_mem_ideal_mul
    (I J : Ideal R₂) (f g : Laurent)
    (hf : ∀ n : ℤ, f.coeff n ∈ I)
    (hg : ∀ n : ℤ, g.coeff n ∈ J)
    (n : ℤ) :
    (f * g).coeff n ∈ I * J := by
  rw [HahnSeries.coeff_mul]
  exact Ideal.sum_mem _ fun p _ =>
    Ideal.mul_mem_mul (hf p.1) (hg p.2)
end
end MazurProof.N13MumfordFormalTransitionJet
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
/-- Every coefficient of the finite weighted displacement is generated by
the two disk coordinates. -/
theorem weightedDeviation_coeff_mem_coordIdeal
    (P : DiskPair) (n : ℤ) :
    (weightedDeviation P).1.coeff n ∈
      N13TwoAdicKernelChart.coordIdeal
        N13TwoAdicAbelChartData.DiskPair.coord P := by
  let I :=
    N13TwoAdicKernelChart.coordIdeal
      N13TwoAdicAbelChartData.DiskPair.coord P
  have ha : P.x₀ ∈ I := by
    apply Ideal.subset_span
    exact Set.mem_range_self (0 : Fin 2)
  have hb : P.x₁ + 1 ∈ I := by
    apply Ideal.subset_span
    exact Set.mem_range_self (1 : Fin 2)
  by_cases hnNegOne : n = -1
  · subst n
    rw [weightedDeviation_coeff_negOne]
    exact I.neg_mem (I.add_mem ha hb)
  · by_cases hnZero : n = 0
    · subst n
      rw [weightedDeviation_coeff_zero]
      exact I.mul_mem_right P.x₁ ha
    · have hcoeff :
          (weightedDeviation P).1.coeff n = 0 := by
        have hnAddOne : n + 1 ≠ 0 := by
          omega
        rw [weightedDeviation_eq, u_sub_base]
        simp [N13FormalCurveOverlap.polyAtTInv,
          N13FormalCurveOverlap.tPow,
          HahnSeries.algebraMap_apply',
          HahnSeries.coeff_mul_single,
          hnAddOne, hnZero]
      rw [hcoeff]
      exact I.zero_mem
end
end MazurProof.N13MumfordFormalTransitionJet
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT
/-- The scalar component of the raw transition displacement is the weighted
finite displacement times the fixed inverse denominator. -/
theorem deviation_fst_eq_weighted_mul_baseInverse (P : DiskPair) :
    (diskTransition P).deviation.1 =
      (weightedDeviation P).1 * baseInverseOverlap.1 := by
  have h :=
    congrArg Prod.fst (weightedDeviation_mul_baseInverse P)
  simpa only [N13FormalLineBundleCech.mulOverlap,
    weightedDeviation_snd, zero_mul, zero_mul,
    zero_add, add_zero] using h.symm
end
end MazurProof.N13MumfordFormalTransitionJet
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
/-- The raw transition still vanishes coefficientwise modulo the moving
coordinate ideal; no inverse-series coefficients are expanded. -/
theorem deviation_coeff_mem_coordIdeal
    (P : DiskPair) (n : ℤ) :
    (diskTransition P).deviation.1.coeff n ∈
      N13TwoAdicKernelChart.coordIdeal
        N13TwoAdicAbelChartData.DiskPair.coord P := by
  rw [deviation_fst_eq_weighted_mul_baseInverse]
  exact
    coeff_mul_mem_leftIdeal
      (N13TwoAdicKernelChart.coordIdeal
        N13TwoAdicAbelChartData.DiskPair.coord P)
      (weightedDeviation P).1 baseInverseOverlap.1
      (weightedDeviation_coeff_mem_coordIdeal P) n
end
end MazurProof.N13MumfordFormalTransitionJet
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
@[simp] theorem firstJet_weightedDeviation_zero (P : DiskPair) :
    firstJet (weightedDeviation P) 0 =
      P.x₀ - P.x₀ * (P.x₁ + 1) := by
  simp [firstJet]
  ring
end
end MazurProof.N13MumfordFormalTransitionJet
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
@[simp] theorem firstJet_weightedDeviation_one (P : DiskPair) :
    firstJet (weightedDeviation P) 1 =
      (P.x₁ + 1) + P.x₀ * (P.x₁ + 1) := by
  simp [firstJet]
  ring
end
end MazurProof.N13MumfordFormalTransitionJet
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
theorem firstJet_weightedDeviation_sub_coord_mem_sq
    (P : DiskPair) (i : Fin 2) :
    firstJet (weightedDeviation P) i -
        N13TwoAdicAbelChartData.DiskPair.coord P i ∈
      N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P *
        N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P := by
  let I :=
    N13TwoAdicKernelChart.coordIdeal
      N13TwoAdicAbelChartData.DiskPair.coord P
  have ha : P.x₀ ∈ I := by
    apply Ideal.subset_span
    exact Set.mem_range_self (0 : Fin 2)
  have hb : P.x₁ + 1 ∈ I := by
    apply Ideal.subset_span
    exact Set.mem_range_self (1 : Fin 2)
  have hab : P.x₀ * (P.x₁ + 1) ∈ I * I :=
    Ideal.mul_mem_mul ha hb
  fin_cases i
  · change
      firstJet (weightedDeviation P) 0 - P.x₀ ∈ I * I
    rw [firstJet_weightedDeviation_zero]
    convert (I * I).neg_mem hab using 1
    ring
  · change
      firstJet (weightedDeviation P) 1 - (P.x₁ + 1) ∈ I * I
    rw [firstJet_weightedDeviation_one]
    convert hab using 1
    ring
end
end MazurProof.N13MumfordFormalTransitionJet
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
/-- Every scalar Laurent coefficient in the weighted square error is
quadratic in the disk coordinates. -/
theorem square_error_coeff_mem_coordIdeal_sq
    (P : DiskPair) (n : ℤ) :
    (N13FormalLineBundleCech.mulOverlap
        (diskTransition P).deviation
        (weightedDeviation P)).1.coeff n ∈
      N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P *
        N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P := by
  change
    ((diskTransition P).deviation.1 *
        (weightedDeviation P).1 +
      (diskTransition P).deviation.2 *
          (weightedDeviation P).2 *
        N13FormalLineBundleCech.rhsInfinity).coeff n ∈ _
  rw [weightedDeviation_snd]
  simp only [mul_zero, zero_mul, add_zero]
  exact
    coeff_mul_mem_ideal_mul
      (N13TwoAdicKernelChart.coordIdeal
        N13TwoAdicAbelChartData.DiskPair.coord P)
      (N13TwoAdicKernelChart.coordIdeal
        N13TwoAdicAbelChartData.DiskPair.coord P)
      (diskTransition P).deviation.1
      (weightedDeviation P).1
      (deviation_coeff_mem_coordIdeal P)
      (weightedDeviation_coeff_mem_coordIdeal P) n
end
end MazurProof.N13MumfordFormalTransitionJet
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
/-- The first jet of the weighted square error is quadratic. -/
theorem firstJet_square_error_mem_coordIdeal_sq
    (P : DiskPair) (i : Fin 2) :
    firstJet
        (N13FormalLineBundleCech.mulOverlap
          (diskTransition P).deviation
          (weightedDeviation P)) i ∈
      N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P *
        N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P := by
  let I :=
    N13TwoAdicKernelChart.coordIdeal
      N13TwoAdicAbelChartData.DiskPair.coord P
  fin_cases i
  · exact
      (I * I).neg_mem
        (square_error_coeff_mem_coordIdeal_sq P 0)
  · exact
      (I * I).add_mem
        ((I * I).neg_mem
          (square_error_coeff_mem_coordIdeal_sq P (-1)))
        (square_error_coeff_mem_coordIdeal_sq P 0)
end
end MazurProof.N13MumfordFormalTransitionJet
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
/-- The weighted first jet of the squared actual transition is twice the
weighted first jet, modulo the moving coordinate ideal squared. -/
theorem firstJet_square_sub_double_mem_coordIdeal_sq
    (P : DiskPair) (i : Fin 2) :
    firstJet
          (weightedDeviationOfTransition
            (diskTransition P).square) i -
        (firstJet (weightedDeviation P) i +
          firstJet (weightedDeviation P) i) ∈
      N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P *
        N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P := by
  have h :=
    congrArg
      (fun z : Overlap => firstJet z i)
      (square_weightedDeviation (diskTransition P))
  have hjet :
      firstJet
            (weightedDeviationOfTransition
              (diskTransition P).square) i -
          (firstJet (weightedDeviation P) i +
            firstJet (weightedDeviation P) i) =
      firstJet
          (N13FormalLineBundleCech.mulOverlap
            (diskTransition P).deviation
            (weightedDeviation P)) i := by
    fin_cases i <;>
      simp [weightedDeviation, firstJet,
        HahnSeries.coeff_sub, HahnSeries.coeff_add] at h ⊢ <;>
      linear_combination h
  rw [hjet]
  exact firstJet_square_error_mem_coordIdeal_sq P i
end
end MazurProof.N13MumfordFormalTransitionJet
end
end

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13MumfordFormalTransitionJet
noncomputable section
attribute [local instance] MazurProof.N13IntegralCechObstruction.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
/-- The actual squared transition has first jet equal to twice the disk
coordinate, modulo the square of the disk-coordinate ideal. -/
theorem firstJet_square_sub_double_coord_mem_sq
    (P : DiskPair) (i : Fin 2) :
    firstJet
          (weightedDeviationOfTransition
            (diskTransition P).square) i -
        (N13TwoAdicAbelChartData.DiskPair.coord P i +
          N13TwoAdicAbelChartData.DiskPair.coord P i) ∈
      N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P *
        N13TwoAdicKernelChart.coordIdeal
          N13TwoAdicAbelChartData.DiskPair.coord P := by
  let I :=
    N13TwoAdicKernelChart.coordIdeal
      N13TwoAdicAbelChartData.DiskPair.coord P
  have hsquare :=
    firstJet_square_sub_double_mem_coordIdeal_sq P i
  have hcoord :=
    firstJet_weightedDeviation_sub_coord_mem_sq P i
  have hsum : _ ∈ I * I :=
    (I * I).add_mem hsquare
      ((I * I).add_mem hcoord hcoord)
  convert hsum using 1
  ring
end
end MazurProof.N13MumfordFormalTransitionJet
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
attribute [local instance] MazurProof.N13RationalKernelDoublingAdapter.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
/-- Existing transition algebra proves that the square jet is twice the
original disk coordinate modulo the square of its coordinate ideal. -/
theorem squareJet_sub_double_coord_mem_sq
    (F : NearBaseFamily H) (z : H) (i : Fin 2) :
    F.squareJet z i -
        (F.coord z i + F.coord z i) ∈
      N13TwoAdicKernelChart.coordIdeal F.coord z *
        N13TwoAdicKernelChart.coordIdeal F.coord z := by
  simpa [squareJet, coord,
    N13TwoAdicKernelChart.coordIdeal] using
    N13MumfordFormalTransitionJet.firstJet_square_sub_double_coord_mem_sq
      (F.pair z) i
end NearBaseFamily
end
end MazurProof.N13RationalKernelDoublingAdapter
end
end


set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13RationalKernelDoublingAdapter.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT
theorem solution {H : AddSubgroup MazurProof.N13RationalKernelDoublingAdapter.RationalPic}
    (F : MazurProof.N13RationalKernelDoublingAdapter.NearBaseFamily H) (z : H) (i : Fin 2) :
    F.squareJet z i -
        (F.coord z i + F.coord z i) ∈
      MazurProof.N13TwoAdicKernelChart.coordIdeal F.coord z *
        MazurProof.N13TwoAdicKernelChart.coordIdeal F.coord z := by
  exact MazurProof.N13RationalKernelDoublingAdapter.NearBaseFamily.squareJet_sub_double_coord_mem_sq F z i
