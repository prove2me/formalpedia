-- Prove2me | solution 1 for HuangN13.N13PrincipalHermiteNormalization.normalize_actual_numerator
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:31:12.115023+00:00
-- url     : https://prove2.me/submissions/69bd4600-a741-4745-856c-25007e372d5f

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_DoublingStatementCore
import Theorems.Thm_MazurProof_N13GoodPointFirstJet_root_jet
import Theorems.Thm_MazurProof_N13GoodSexticMumfordTransport_sextic_mumfordIdeal_eq_of_dvd_sub

set_option autoImplicit false

section
section
set_option autoImplicit false
open Polynomial
namespace MazurProof.N13GeneralizedMumfordReduction
noncomputable section
@[simp] theorem reduceBase_two :
    reduceBase (2 : R₂) = 0 := by
  rw [← RingHom.mem_ker, reduceBase, PadicInt.ker_toZMod,
    PadicInt.maximalIdeal_eq_span_p]
  exact Ideal.subset_span (by simp)
end
end MazurProof.N13GeneralizedMumfordReduction
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
@[simp] theorem u_eval_x₀ :
    P.u.eval P.x₀ = 0 := by
  simp [u]
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
@[simp] theorem u_eval_x₁ :
    P.u.eval P.x₁ = 0 := by
  simp [u]
end DiskPair
end
end MazurProof.N13TwoAdicAbelChartData
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GoodPointFirstJet
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Polynomial MulOpposite
universe u
variable {K : Type u} [Field K]
def pointJet (x y s : K)
    (hc : y ^ 2 + (x ^ 3 + x + 1) * y - (x ^ 5 + x ^ 4) = 0)
    (hd : (2 * y + (x ^ 3 + x + 1)) * s +
      (3 * x ^ 2 + 1) * y - (5 * x ^ 4 + 4 * x ^ 3) = 0) : Good K →+* Dual K :=
  AdjoinRoot.lift (polynomialJet x) (y, s) (MazurProof.N13GoodPointFirstJet.root_jet x y s hc hd)
end
end MazurProof.N13GoodPointFirstJet
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GoodPointFirstJet
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Polynomial MulOpposite
universe u
variable {K : Type u} [Field K]
section
variable (x y s : K)
variable (hc : y ^ 2 + (x ^ 3 + x + 1) * y - (x ^ 5 + x ^ 4) = 0)
variable (hd : (2 * y + (x ^ 3 + x + 1)) * s +
  (3 * x ^ 2 + 1) * y - (5 * x ^ 4 + 4 * x ^ 3) = 0)
@[simp] theorem pointJet_xClass (p : K[X]) :
    pointJet x y s hc hd (N13GeneralizedMumfordIntegral.xClass p) =
      (p.eval x, p.derivative.eval x) := AdjoinRoot.lift_of _
end
end
end MazurProof.N13GoodPointFirstJet
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GoodPointFirstJet
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Polynomial MulOpposite
universe u
variable {K : Type u} [Field K]
section
variable (x y s : K)
variable (hc : y ^ 2 + (x ^ 3 + x + 1) * y - (x ^ 5 + x ^ 4) = 0)
variable (hd : (2 * y + (x ^ 3 + x + 1)) * s +
  (3 * x ^ 2 + 1) * y - (5 * x ^ 4 + 4 * x ^ 3) = 0)
@[simp] theorem pointJet_yClass :
    pointJet x y s hc hd N13GeneralizedMumfordIntegral.yClass = (y, s) :=
  AdjoinRoot.lift_root _
end
end
end MazurProof.N13GoodPointFirstJet
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GoodPointFirstJet
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Polynomial MulOpposite
universe u
variable {K : Type u} [Field K]
section
variable (x y s : K)
variable (hc : y ^ 2 + (x ^ 3 + x + 1) * y - (x ^ 5 + x ^ 4) = 0)
variable (hd : (2 * y + (x ^ 3 + x + 1)) * s +
  (3 * x ^ 2 + 1) * y - (5 * x ^ 4 + 4 * x ^ 3) = 0)
theorem square_graph_maps_to_zero (u v : K[X])
    (hu : u.eval x = 0) (hv : v.eval x = y)
    (n : Good K) (hn : n ∈ N13GeneralizedMumfordIntegral.mumfordIdeal u v ^ 2) :
    pointJet x y s hc hd n = 0 := by
  let f : Good K →+* K :=
    (TrivSqZeroExt.fstHom K K K).toRingHom.comp (pointJet x y s hc hd)
  have hI : N13GeneralizedMumfordIntegral.mumfordIdeal u v ≤ RingHom.ker f := by
    rw [N13GeneralizedMumfordIntegral.mumfordIdeal, Ideal.span_le]
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · change (pointJet x y s hc hd (N13GeneralizedMumfordIntegral.xClass u)).fst = 0
      simpa using hu
    · change (pointJet x y s hc hd (N13GeneralizedMumfordIntegral.ySubClass v)).fst = 0
      simp [N13GeneralizedMumfordIntegral.ySubClass, hv]
  have hsquare : N13GeneralizedMumfordIntegral.mumfordIdeal u v ^ 2 ≤
      RingHom.ker (pointJet x y s hc hd) := by
    rw [pow_two]
    apply Ideal.mul_le.mpr
    intro a ha b hb
    have hfa : (pointJet x y s hc hd a).fst = 0 := hI ha
    have hfb : (pointJet x y s hc hd b).fst = 0 := hI hb
    change pointJet x y s hc hd (a * b) = 0
    rw [map_mul]
    apply TrivSqZeroExt.ext <;>
      simp [hfa, hfb, smul_eq_mul, op_smul_eq_smul]
  exact hsquare hn
end
end
end MazurProof.N13GoodPointFirstJet
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13GoodPointFirstJet
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Polynomial MulOpposite
universe u
variable {K : Type u} [Field K]
section
variable (x y s : K)
variable (hc : y ^ 2 + (x ^ 3 + x + 1) * y - (x ^ 5 + x ^ 4) = 0)
variable (hd : (2 * y + (x ^ 3 + x + 1)) * s +
  (3 * x ^ 2 + 1) * y - (5 * x ^ 4 + 4 * x ^ 3) = 0)
include hc hd in
theorem value_derivative_of_square_graph
    (u v p q : K[X]) (hu : u.eval x = 0) (hv : v.eval x = y)
    (hn : N13GeneralizedMumfordIntegral.xClass p +
        N13GeneralizedMumfordIntegral.xClass q * N13GeneralizedMumfordIntegral.yClass ∈
      N13GeneralizedMumfordIntegral.mumfordIdeal u v ^ 2) :
    p.eval x + q.eval x * y = 0 ∧
      p.derivative.eval x + q.derivative.eval x * y + q.eval x * s = 0 := by
  have hj := square_graph_maps_to_zero x y s hc hd u v hu hv _ hn
  constructor
  · simpa using congrArg TrivSqZeroExt.fst hj
  · have hs := congrArg TrivSqZeroExt.snd hj
    simp [smul_eq_mul, op_smul_eq_smul] at hs
    convert hs using 1 <;> ring
end
end
end MazurProof.N13GoodPointFirstJet
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CenteredHermiteFirstOrder
noncomputable section
private theorem cancel_unit_mem {R : Type*} [CommRing R]
    (I : Ideal R) {a u : R} (hu : IsUnit u) (h : a * u ∈ I) : a ∈ I :=
  (Ideal.unit_mul_mem_iff_mem I hu).mp (by simpa [mul_comm] using h)
end
end MazurProof.N13CenteredHermiteFirstOrder
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CenteredHermiteFirstOrder
noncomputable section
/-- Evaluation at two points separated by a unit detects both coefficients
of a linear polynomial modulo any ideal. -/
theorem linear_coeff_mem {R : Type*} [CommRing R]
    (I : Ideal R) (x₀ x₁ c₀ c₁ : R) (hd : IsUnit (x₁ - x₀))
    (h₀ : c₀ + c₁ * x₀ ∈ I) (h₁ : c₀ + c₁ * x₁ ∈ I) :
    c₀ ∈ I ∧ c₁ ∈ I := by
  have hm : c₁ * (x₁ - x₀) ∈ I := by
    convert I.sub_mem h₁ h₀ using 1 <;> ring
  have hc₁ := cancel_unit_mem I hd hm
  refine ⟨?_, hc₁⟩
  convert I.sub_mem h₀ (I.mul_mem_right x₀ hc₁) using 1 <;> ring
end
end MazurProof.N13CenteredHermiteFirstOrder
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CenteredHermiteFirstOrder
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicKernelChart.instFactPrimeOfNatNat_fLT MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT
theorem uBase_eval_mem (P : DiskPair) (j : Fin 2) :
    x P j ^ 2 + x P j ∈ I P := by
  have hx₀ : P.x₀ ∈ I P := Ideal.subset_span (Set.mem_range_self (0 : Fin 2))
  have hx₁ : P.x₁ + 1 ∈ I P := Ideal.subset_span (Set.mem_range_self (1 : Fin 2))
  fin_cases j
  · convert (I P).mul_mem_right (P.x₀ + 1) hx₀ using 1 <;> simp [x] <;> ring
  · convert (I P).mul_mem_left P.x₁ hx₁ using 1 <;> simp [x] <;> ring
end
end MazurProof.N13CenteredHermiteFirstOrder
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CenteredHermiteFirstOrder
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicDisks.instFactPrimeOfNatNat_fLT MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT
theorem uBase_derivative_unit (P : DiskPair) (j : Fin 2) :
    IsUnit (2 * x P j + 1) := by
  fin_cases j
  · apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal isUnit_one
    convert N13TwoAdicDisks.maximal.mul_mem_left 2 P.x₀_mem using 1 <;>
      simp [x] <;> ring
  · apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal isUnit_neg_one
    convert N13TwoAdicDisks.maximal.mul_mem_left 2 P.x₁_add_one_mem using 1 <;>
      simp [x] <;> ring
end
end MazurProof.N13CenteredHermiteFirstOrder
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CenteredHermiteFirstOrder
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicDisks.instFactPrimeOfNatNat_fLT MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT
theorem oppositeY_unit (P : DiskPair) (j : Fin 2) : IsUnit (oppositeY P j) := by
  have h₀ : IsUnit (P.y₀ + N13GoodModelTwo.h P.x₀) := by
    apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal
      (N13TwoAdicDisks.h_isUnit_of_mem_zeroDisk P.x₀_mem)
    convert P.y₀_spec.2 using 1 <;> ring
  have h₁ : IsUnit (P.y₁ + N13GoodModelTwo.h P.x₁) := by
    apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal
      (N13TwoAdicDisks.h_isUnit_of_mem_negOneDisk P.x₁_add_one_mem)
    convert P.y₁_spec.2 using 1 <;> ring
  fin_cases j
  · convert h₀.neg using 1 <;> simp [oppositeY] <;> ring
  · convert h₁.neg using 1 <;> simp [oppositeY] <;> ring
end
end MazurProof.N13CenteredHermiteFirstOrder
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13CenteredHermiteFirstOrder
noncomputable section
attribute [local instance] MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT
/-- The equations are value and derivative vanishing of the actual
numerator uBase*A+b*y on the opposite sheet. The tangent slopes are
arbitrary integral values here; only their integrality is used. -/
theorem hermite_coefficients_mod_square
    (P : DiskPair) (a₀ a₁ b₀ b₁ : R₂) (slope : Fin 2 → R₂)
    (hvalue : ∀ j,
      (x P j ^ 2 + x P j) * (x P j ^ 2 + a₁ * x P j + a₀) +
        (b₀ + b₁ * x P j) * oppositeY P j = 0)
    (hderivative : ∀ j,
      (2 * x P j + 1) * (x P j ^ 2 + a₁ * x P j + a₀) +
        (x P j ^ 2 + x P j) * (2 * x P j + a₁) +
        b₁ * oppositeY P j + (b₀ + b₁ * x P j) * slope j = 0) :
    b₀ ∈ I P * I P ∧ b₁ ∈ I P * I P ∧
      a₀ - 2 * P.x₀ * P.x₁ ∈ I P * I P ∧
      a₁ + 2 * (P.x₀ + P.x₁) + 1 ∈ I P * I P := by
  let A (j : Fin 2) := x P j ^ 2 + a₁ * x P j + a₀
  let b (j : Fin 2) := b₀ + b₁ * x P j
  let u (j : Fin 2) := x P j ^ 2 + x P j
  have hu (j : Fin 2) : u j ∈ I P := uBase_eval_mem P j
  have hb (j : Fin 2) : b j ∈ I P := by
    apply cancel_unit_mem (I P) (oppositeY_unit P j)
    have he : b j * oppositeY P j = -(u j * A j) := by
      dsimp [A, b, u]
      linear_combination hvalue j
    rw [he]
    exact (I P).neg_mem ((I P).mul_mem_right (A j) (hu j))
  have hbc := linear_coeff_mem (I P) P.x₀ P.x₁ b₀ b₁
    P.x₁_sub_x₀_isUnit (hb 0) (hb 1)
  have hA (j : Fin 2) : A j ∈ I P := by
    apply cancel_unit_mem (I P) (uBase_derivative_unit P j)
    have he : A j * (2 * x P j + 1) =
        -(u j * (2 * x P j + a₁) + b₁ * oppositeY P j + b j * slope j) := by
      dsimp [A, b, u]
      linear_combination hderivative j
    rw [he]
    exact (I P).neg_mem ((I P).add_mem
      ((I P).add_mem ((I P).mul_mem_right _ (hu j))
        ((I P).mul_mem_right _ hbc.2)) ((I P).mul_mem_right _ (hb j)))
  have hlinear (j : Fin 2) : a₀ + (a₁ - 1) * x P j ∈ I P := by
    convert (I P).sub_mem (hA j) (hu j) using 1 <;> dsimp [A, u] <;> ring
  have hac := linear_coeff_mem (I P) P.x₀ P.x₁ a₀ (a₁ - 1)
    P.x₁_sub_x₀_isUnit (hlinear 0) (hlinear 1)
  have hb₂ (j : Fin 2) : b j ∈ I P * I P := by
    apply cancel_unit_mem (I P * I P) (oppositeY_unit P j)
    have he : b j * oppositeY P j = -(u j * A j) := by
      dsimp [A, b, u]
      linear_combination hvalue j
    rw [he]
    exact (I P * I P).neg_mem (Ideal.mul_mem_mul (hu j) (hA j))
  have hbc₂ := linear_coeff_mem (I P * I P) P.x₀ P.x₁ b₀ b₁
    P.x₁_sub_x₀_isUnit (hb₂ 0) (hb₂ 1)
  have hAu (j : Fin 2) : A j + u j ∈ I P * I P := by
    apply cancel_unit_mem (I P * I P) (uBase_derivative_unit P j)
    have he : (A j + u j) * (2 * x P j + 1) =
        -(b₁ * oppositeY P j + b j * slope j + u j * (a₁ - 1)) := by
      dsimp [A, b, u]
      linear_combination hderivative j
    rw [he]
    exact (I P * I P).neg_mem ((I P * I P).add_mem
      ((I P * I P).add_mem ((I P * I P).mul_mem_right _ hbc₂.2)
        ((I P * I P).mul_mem_right _ (hb₂ j))) (Ideal.mul_mem_mul (hu j) hac.2))
  have hzero : (a₀ - 2 * P.x₀ * P.x₁) +
      (a₁ + 2 * (P.x₀ + P.x₁) + 1) * P.x₀ ∈ I P * I P := by
    convert hAu 0 using 1 <;> dsimp [A, u, x] <;> ring
  have hone : (a₀ - 2 * P.x₀ * P.x₁) +
      (a₁ + 2 * (P.x₀ + P.x₁) + 1) * P.x₁ ∈ I P * I P := by
    convert hAu 1 using 1 <;> dsimp [A, u, x] <;> ring
  have hcenter := linear_coeff_mem (I P * I P) P.x₀ P.x₁
    (a₀ - 2 * P.x₀ * P.x₁) (a₁ + 2 * (P.x₀ + P.x₁) + 1)
    P.x₁_sub_x₀_isUnit hzero hone
  exact ⟨hbc₂.1, hbc₂.2, hcenter.1, hcenter.2⟩
end
end MazurProof.N13CenteredHermiteFirstOrder
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13IntegralHermiteNumerator
noncomputable section
open N13CenteredHermiteFirstOrder
attribute [local instance] MazurProof.N13IntegralHermiteNumerator.instFactPrimeOfNatNat_fLT
private theorem residueMatrix_mul_inverse (s₀ s₁ : ZMod 2) :
    residueMatrix s₀ s₁ * residueInverse s₀ s₁ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [residueMatrix, residueInverse, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring_nf <;>
    simp [show (2 : ZMod 2) = 0 from rfl]
end
end MazurProof.N13IntegralHermiteNumerator
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13IntegralHermiteNumerator
noncomputable section
open N13CenteredHermiteFirstOrder
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralHermiteNumerator.instFactPrimeOfNatNat_fLT
private theorem reduce_matrix (P : DiskPair) (s : Fin 2 → R₂) :
    (matrix P s).map N13GeneralizedMumfordReduction.reduceBase =
      residueMatrix (N13GeneralizedMumfordReduction.reduceBase (s 0))
        (N13GeneralizedMumfordReduction.reduceBase (s 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [matrix, residueMatrix, Matrix.map, oppositeY,
      N13GoodModelTwo.h, map_add, map_sub, map_neg, map_mul, map_pow] <;>
    first | rfl | decide | (ring_nf; simp [show (2 : ZMod 2) = 0 from rfl])
end
end MazurProof.N13IntegralHermiteNumerator
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13IntegralHermiteNumerator
noncomputable section
open N13CenteredHermiteFirstOrder
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicDisks.instFactPrimeOfNatNat_fLT MazurProof.N13IntegralHermiteNumerator.instFactPrimeOfNatNat_fLT
theorem matrix_det_unit (P : DiskPair) (s : Fin 2 → R₂) :
    IsUnit (matrix P s).det := by
  let r := N13GeneralizedMumfordReduction.reduceBase
  have hunit : IsUnit (r (matrix P s).det) := by
    rw [r.map_det]
    change IsUnit ((matrix P s).map r).det
    rw [reduce_matrix]
    exact Matrix.isUnit_det_of_right_inverse
      (residueMatrix_mul_inverse (r (s 0)) (r (s 1)))
  have hres : r (matrix P s).det = 1 := by
    rcases N13GoodModelTwo.fixedTwo_eq_zero_or_one (r (matrix P s).det)
      (ZMod.pow_card _) with hz | ho
    · exact (hunit.ne_zero hz).elim
    · exact ho
  apply N13TwoAdicDisks.isUnit_of_sub_mem_maximal isUnit_one
  have hker : (matrix P s).det - 1 ∈ RingHom.ker r := by
    change r ((matrix P s).det - 1) = 0
    rw [map_sub, hres, map_one, sub_self]
  simpa only [r, N13GeneralizedMumfordReduction.reduceBase, PadicInt.ker_toZMod] using hker
end
end MazurProof.N13IntegralHermiteNumerator
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13IntegralHermiteNumerator
noncomputable section
open N13CenteredHermiteFirstOrder
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
theorem exists_coefficients (P : DiskPair) (s : Fin 2 → R₂) :
    ∃ a₀ a₁ b₀ b₁ : R₂,
      (∀ j, (x P j ^ 2 + x P j) * (x P j ^ 2 + a₁ * x P j + a₀) +
        (b₀ + b₁ * x P j) * oppositeY P j = 0) ∧
      (∀ j, (2 * x P j + 1) * (x P j ^ 2 + a₁ * x P j + a₀) +
        (x P j ^ 2 + x P j) * (2 * x P j + a₁) +
        b₁ * oppositeY P j + (b₀ + b₁ * x P j) * s j = 0) := by
  have hsurj : Function.Surjective (matrix P s).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (matrix_det_unit P s))
  obtain ⟨c, hc⟩ := hsurj (rightSide P)
  refine ⟨c 0, c 1, c 2, c 3, ?_, ?_⟩
  · intro j
    fin_cases j
    · have h := congrFun hc (0 : Fin 4)
      simp [matrix, rightSide, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h
      dsimp [x]
      linear_combination h
    · have h := congrFun hc (1 : Fin 4)
      simp [matrix, rightSide, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h
      dsimp [x]
      linear_combination h
  · intro j
    fin_cases j
    · have h := congrFun hc (2 : Fin 4)
      simp [matrix, rightSide, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h
      dsimp [x]
      linear_combination h
    · have h := congrFun hc (3 : Fin 4)
      simp [matrix, rightSide, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h
      dsimp [x]
      linear_combination h
end
end MazurProof.N13IntegralHermiteNumerator
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13IntegralHermiteNumerator
noncomputable section
open N13CenteredHermiteFirstOrder
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
/-- Actual integral coefficients satisfying all four Hermite equations and
the required first-order normalization, without any existence assumption. -/
theorem exists_normalized_coefficients (P : DiskPair) (s : Fin 2 → R₂) :
    ∃ a₀ a₁ b₀ b₁ : R₂,
      (∀ j, (x P j ^ 2 + x P j) * (x P j ^ 2 + a₁ * x P j + a₀) +
        (b₀ + b₁ * x P j) * oppositeY P j = 0) ∧
      (∀ j, (2 * x P j + 1) * (x P j ^ 2 + a₁ * x P j + a₀) +
        (x P j ^ 2 + x P j) * (2 * x P j + a₁) +
        b₁ * oppositeY P j + (b₀ + b₁ * x P j) * s j = 0) ∧
      b₀ ∈ I P * I P ∧ b₁ ∈ I P * I P ∧
      a₀ - 2 * P.x₀ * P.x₁ ∈ I P * I P ∧
      a₁ + 2 * (P.x₀ + P.x₁) + 1 ∈ I P * I P := by
  obtain ⟨a₀, a₁, b₀, b₁, hv, hd⟩ := exists_coefficients P s
  exact ⟨a₀, a₁, b₀, b₁, hv, hd, hermite_coefficients_mod_square P _ _ _ _ s hv hd⟩
end
end MazurProof.N13IntegralHermiteNumerator
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13HermiteResidualDivisibility
noncomputable section
open Polynomial N13CenteredHermiteFirstOrder
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT
theorem opposite_curve (P : DiskPair) (j : Fin 2) :
    oppositeY P j ^ 2 + (x P j ^ 3 + x P j + 1) * oppositeY P j -
      (x P j ^ 2 + x P j) * x P j ^ 3 = 0 := by
  fin_cases j
  · have h := P.y₀_spec.1
    dsimp [N13GoodModelTwo.AffineEquation, N13GoodModelTwo.h, N13GoodModelTwo.rhs] at h
    dsimp [x, oppositeY, N13GoodModelTwo.h]
    linear_combination h
  · have h := P.y₁_spec.1
    dsimp [N13GoodModelTwo.AffineEquation, N13GoodModelTwo.h, N13GoodModelTwo.rhs] at h
    dsimp [x, oppositeY, N13GoodModelTwo.h]
    linear_combination h
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
theorem slope_relation (P : DiskPair) (j : Fin 2) :
    (2 * oppositeY P j + (x P j ^ 3 + x P j + 1)) * slope P j +
      (3 * x P j ^ 2 + 1) * oppositeY P j -
        (5 * x P j ^ 4 + 4 * x P j ^ 3) = 0 := by
  have hi : (2 * oppositeY P j + (x P j ^ 3 + x P j + 1)) *
      (↑((vertical_derivative_unit P j).unit⁻¹) : R₂) = 1 := by
    exact (vertical_derivative_unit P j).mul_val_inv
  dsimp [slope]
  linear_combination
    (5 * x P j ^ 4 + 4 * x P j ^ 3 -
      (3 * x P j ^ 2 + 1) * oppositeY P j) * hi
end
end MazurProof.N13HermiteResidualDivisibility
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ActualHermiteEquations
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator N13GoodCenteredNumerator
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem curve (P : DiskPair) (j : Fin 2) :
    y P j ^ 2 + (x P j ^ 3 + x P j + 1) * y P j -
      (x P j ^ 5 + x P j ^ 4) = 0 := by
  have h := congrArg c (N13HermiteResidualDivisibility.opposite_curve P j)
  simp only [map_sub, map_add, map_mul, map_pow, map_one, map_zero] at h
  change y P j ^ 2 + (x P j ^ 3 + x P j + 1) * y P j -
    (x P j ^ 2 + x P j) * x P j ^ 3 = 0 at h
  linear_combination h
end
end MazurProof.N13ActualHermiteEquations
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ActualHermiteEquations
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator N13GoodCenteredNumerator
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem tangent (P : DiskPair) (j : Fin 2) :
    (2 * y P j + (x P j ^ 3 + x P j + 1)) * s P j +
      (3 * x P j ^ 2 + 1) * y P j - (5 * x P j ^ 4 + 4 * x P j ^ 3) = 0 := by
  have h := congrArg c (N13HermiteResidualDivisibility.slope_relation P j)
  simp only [map_sub, map_add, map_mul, map_pow, map_one, map_zero, map_ofNat] at h
  exact h
end
end MazurProof.N13ActualHermiteEquations
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ActualHermiteEquations
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator N13GoodCenteredNumerator
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem U_root (P : DiskPair) (j : Fin 2) : (U P).eval (x P j) = 0 := by
  fin_cases j <;>
    simp [U, x, N13CenteredHermiteFirstOrder.x,
      N13TwoAdicMumfordTransport.mapPoly, Polynomial.eval_map_apply]
end
end MazurProof.N13ActualHermiteEquations
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ActualHermiteEquations
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator N13GoodCenteredNumerator
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem V_eval (P : DiskPair) (j : Fin 2) : (V P).eval (x P j) = y P j := by
  fin_cases j <;>
    simp [V, x, y, N13CenteredHermiteFirstOrder.x,
      N13CenteredHermiteFirstOrder.oppositeY,
      N13TwoAdicMumfordTransport.mapPoly, Polynomial.eval_map_apply,
      N13GeneralizedMumfordIntegral.hPoly, N13GoodModelTwo.h]
end
end MazurProof.N13ActualHermiteEquations
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ActualHermiteEquations
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator N13GoodCenteredNumerator
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem map_conjugate_graph (P : DiskPair) :
    Ideal.map toGood
      (mumfordIdeal M (conjugateSemiMumford M P.mumford.toSemi).u
        (conjugateSemiMumford M P.mumford.toSemi).v) =
      N13GeneralizedMumfordIntegral.mumfordIdeal (U P) (V P) := by
  let p := N13TwoAdicMumfordTransport.mapPoly P.v
  let W := N13GoodSexticMumfordTransport.completedGraph p
  have hmod : U P ∣ (-W) - (-(W % U P)) := by
    refine ⟨-(W / U P), ?_⟩
    have h := EuclideanDomain.mod_add_div W (U P)
    linear_combination h
  have ht : Ideal.map toSextic
      (N13GeneralizedMumfordIntegral.mumfordIdeal (U P) (V P)) =
        mumfordIdeal M (U P) (-(W % U P)) := by
    rw [N13GoodSexticMumfordTransport.map_mumfordIdeal]
    have hv : N13GoodSexticMumfordTransport.completedGraph (V P) = -W := by
      dsimp [V, W, p, N13GoodSexticMumfordTransport.completedGraph]
      ring
    rw [hv]
    exact N13GoodSexticMumfordTransport.sextic_mumfordIdeal_eq_of_dvd_sub _ _ _ hmod
  have hi : toGood.comp toSextic = RingHom.id Good := by
    exact RingHom.ext fun z =>
      (N13GoodSexticCoordinateEquiv.coordinateRingEquiv (K := K)).symm_apply_apply z
  change Ideal.map toGood (mumfordIdeal M (U P) (-(W % U P))) = _
  rw [← ht, Ideal.map_map, hi, Ideal.map_id]
end
end MazurProof.N13ActualHermiteEquations
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13ActualHermiteEquations
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator N13GoodCenteredNumerator
attribute [local instance] _root_.MazurProof.N13ActualHermiteEquations.instFactPrimeOfNatNat_fLT
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT
theorem hermite_equations_of_product_membership
    (P Q : DiskPair) (n : R) (A b : K[X])
    (hshape : toGood n = gx ((X ^ 2 + X) * A) + gx b * gy)
    (hmem : n ∈ (mumfordIdeal M Q.mumford.u Q.mumford.v *
        mumfordIdeal M B.mumford.u B.mumford.v) *
      (mumfordIdeal M (conjugateSemiMumford M P.mumford.toSemi).u
        (conjugateSemiMumford M P.mumford.toSemi).v) ^ 2) :
    (∀ j, (x P j ^ 2 + x P j) * A.eval (x P j) + b.eval (x P j) * y P j = 0) ∧
      (∀ j, (2 * x P j + 1) * A.eval (x P j) +
        (x P j ^ 2 + x P j) * A.derivative.eval (x P j) +
        b.derivative.eval (x P j) * y P j + b.eval (x P j) * s P j = 0) := by
  have hn : n ∈ (mumfordIdeal M (conjugateSemiMumford M P.mumford.toSemi).u
      (conjugateSemiMumford M P.mumford.toSemi).v) ^ 2 := Ideal.mul_le_right hmem
  have hg := Ideal.mem_map_of_mem toGood hn
  rw [Ideal.map_pow, map_conjugate_graph, hshape] at hg
  have hj (j : Fin 2) := N13GoodPointFirstJet.value_derivative_of_square_graph
    (x P j) (y P j) (s P j) (curve P j) (tangent P j)
    (U P) (V P) ((X ^ 2 + X) * A) b (U_root P j) (V_eval P j) hg
  constructor
  · intro j
    simpa using (hj j).1
  · intro j
    have hd := (hj j).2
    simpa [derivative_mul, derivative_pow, add_assoc] using hd
end
end MazurProof.N13ActualHermiteEquations
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalHermiteMatrix
noncomputable section
open N13CenteredPrincipalNumerator N13ActualHermiteEquations
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem matrixQ_unit (P : DiskPair) : IsUnit (matrixQ P) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  have h := (N13IntegralHermiteNumerator.matrix_det_unit P
    (N13HermiteResidualDivisibility.slope P)).map c
  rw [c.map_det] at h
  change IsUnit (matrixQ P).det at h
  exact h
end
end MazurProof.N13RationalHermiteMatrix
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalHermiteMatrix
noncomputable section
open N13CenteredPrincipalNumerator N13ActualHermiteEquations
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT
theorem matrixQ_injective (P : DiskPair) : Function.Injective (matrixQ P).mulVec :=
  Matrix.mulVec_injective_iff_isUnit.mpr (matrixQ_unit P)
end
end MazurProof.N13RationalHermiteMatrix
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalHermiteMatrix
noncomputable section
open N13CenteredPrincipalNumerator N13ActualHermiteEquations
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem matrix_equation (P : DiskPair) (t a₀ a₁ b₀ b₁ : K)
    (hv : ∀ j, (x P j ^ 2 + x P j) * (t * x P j ^ 2 + a₁ * x P j + a₀) +
      (b₀ + b₁ * x P j) * y P j = 0)
    (hd : ∀ j, (2 * x P j + 1) * (t * x P j ^ 2 + a₁ * x P j + a₀) +
      (x P j ^ 2 + x P j) * (2 * t * x P j + a₁) +
      b₁ * y P j + (b₀ + b₁ * x P j) * s P j = 0) :
    (matrixQ P).mulVec ![a₀, a₁, b₀, b₁] = t • rhsQ P := by
  have hv₀ := hv 0
  have hv₁ := hv 1
  have hd₀ := hd 0
  have hd₁ := hd 1
  dsimp [x, y, s, N13CenteredHermiteFirstOrder.x] at hv₀ hv₁ hd₀ hd₁
  ext j
  fin_cases j <;>
    simp [matrixQ, rhsQ, N13IntegralHermiteNumerator.matrix,
      N13IntegralHermiteNumerator.rightSide, Matrix.map,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, smul_eq_mul, map_ofNat]
  · linear_combination hv₀
  · linear_combination hv₁
  · linear_combination hd₀
  · linear_combination hd₁
end
end MazurProof.N13RationalHermiteMatrix
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalHermiteMatrix
noncomputable section
open N13CenteredPrincipalNumerator N13ActualHermiteEquations
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13RationalHermiteMatrix.instFactPrimeOfNatNat_fLT
theorem exists_integral_solution (P : DiskPair) :
    ∃ a₀ a₁ b₀ b₁ : R₂,
      (matrixQ P).mulVec ![c a₀, c a₁, c b₀, c b₁] = rhsQ P ∧
      b₀ ∈ N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P ∧
      b₁ ∈ N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P ∧
      a₀ - 2 * P.x₀ * P.x₁ ∈
        N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P ∧
      a₁ + 2 * (P.x₀ + P.x₁) + 1 ∈
        N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P := by
  obtain ⟨a₀, a₁, b₀, b₁, hv, hd, hm⟩ :=
    N13IntegralHermiteNumerator.exists_normalized_coefficients P
      (N13HermiteResidualDivisibility.slope P)
  refine ⟨a₀, a₁, b₀, b₁, ?_, hm⟩
  have hvQ (j : Fin 2) :
      (x P j ^ 2 + x P j) * (1 * x P j ^ 2 + c a₁ * x P j + c a₀) +
        (c b₀ + c b₁ * x P j) * y P j = 0 := by
    have h := congrArg c (hv j)
    simp only [map_add, map_mul, map_pow, map_zero, one_mul] at h ⊢
    exact h
  have hdQ (j : Fin 2) :
      (2 * x P j + 1) * (1 * x P j ^ 2 + c a₁ * x P j + c a₀) +
        (x P j ^ 2 + x P j) * (2 * 1 * x P j + c a₁) +
        c b₁ * y P j + (c b₀ + c b₁ * x P j) * s P j = 0 := by
    have h := congrArg c (hd j)
    simp only [map_add, map_mul, map_pow, map_zero, map_one, map_ofNat,
      one_mul, mul_one] at h ⊢
    exact h
  simpa only [one_smul] using matrix_equation P 1 (c a₀) (c a₁) (c b₀) (c b₁) hvQ hdQ
end
end MazurProof.N13RationalHermiteMatrix
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13RationalHermiteMatrix
noncomputable section
open N13CenteredPrincipalNumerator N13ActualHermiteEquations
attribute [local instance] _root_.MazurProof.N13RationalHermiteMatrix.instFactPrimeOfNatNat_fLT
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13RationalHermiteMatrix.instFactPrimeOfNatNat_fLT
/-- Rational Hermite data are a scalar multiple of an integral normalized
solution. This is an equality of coefficients, with their I² bounds retained. -/
theorem coefficients_are_scaled_integral (P : DiskPair) (t a₀ a₁ b₀ b₁ : K)
    (hv : ∀ j, (x P j ^ 2 + x P j) * (t * x P j ^ 2 + a₁ * x P j + a₀) +
      (b₀ + b₁ * x P j) * y P j = 0)
    (hd : ∀ j, (2 * x P j + 1) * (t * x P j ^ 2 + a₁ * x P j + a₀) +
      (x P j ^ 2 + x P j) * (2 * t * x P j + a₁) +
      b₁ * y P j + (b₀ + b₁ * x P j) * s P j = 0) :
    ∃ d₀ d₁ e₀ e₁ : R₂,
      a₀ = t * c d₀ ∧ a₁ = t * c d₁ ∧ b₀ = t * c e₀ ∧ b₁ = t * c e₁ ∧
      e₀ ∈ N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P ∧
      e₁ ∈ N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P ∧
      d₀ - 2 * P.x₀ * P.x₁ ∈
        N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P ∧
      d₁ + 2 * (P.x₀ + P.x₁) + 1 ∈
        N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P := by
  obtain ⟨d₀, d₁, e₀, e₁, hsol, hm⟩ := exists_integral_solution P
  have he : ![a₀, a₁, b₀, b₁] = t • ![c d₀, c d₁, c e₀, c e₁] := by
    apply matrixQ_injective P
    rw [matrix_equation P t a₀ a₁ b₀ b₁ hv hd, Matrix.mulVec_smul, hsol]
  refine ⟨d₀, d₁, e₀, e₁, ?_, ?_, ?_, ?_, hm⟩
  · simpa using congrFun he (0 : Fin 4)
  · simpa using congrFun he (1 : Fin 4)
  · simpa using congrFun he (2 : Fin 4)
  · simpa using congrFun he (3 : Fin 4)
end
end MazurProof.N13RationalHermiteMatrix
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrincipalHermiteNormalization
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator N13GoodCenteredNumerator
open N13ActualHermiteEquations N13RationalHermiteMatrix
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT
theorem quadratic_eq (A : K[X]) (hA : A.natDegree ≤ 2) :
    A = _root_.Polynomial.C (A.coeff 2) * X ^ 2 + _root_.Polynomial.C (A.coeff 1) * X + _root_.Polynomial.C (A.coeff 0) := by
  ext n
  by_cases hn : n ≤ 2
  · interval_cases n <;> simp
  · have hp : A.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have h₀ : n ≠ 0 := by omega
    have h₁ : n ≠ 1 := by omega
    have h₂ : n ≠ 2 := by omega
    simp [hp, h₀, h₁, h₂, Polynomial.coeff_C_mul, Polynomial.coeff_X,
      Polynomial.coeff_C, Ne.symm h₁]
end
end MazurProof.N13PrincipalHermiteNormalization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrincipalHermiteNormalization
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator N13GoodCenteredNumerator
open N13ActualHermiteEquations N13RationalHermiteMatrix
attribute [local instance] MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT
theorem linear_eq (b : K[X]) (hb : b.natDegree ≤ 1) :
    b = _root_.Polynomial.C (b.coeff 0) + _root_.Polynomial.C (b.coeff 1) * X := by
  ext n
  by_cases hn : n ≤ 1
  · interval_cases n <;> simp
  · have hp : b.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have h₀ : n ≠ 0 := by omega
    have h₁ : n ≠ 1 := by omega
    simp [hp, h₀, h₁, Polynomial.coeff_C_mul, Polynomial.coeff_X,
      Polynomial.coeff_C, Ne.symm h₁]
end
end MazurProof.N13PrincipalHermiteNormalization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrincipalHermiteNormalization
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator N13GoodCenteredNumerator
open N13ActualHermiteEquations N13RationalHermiteMatrix
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13RationalHermiteMatrix.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13PrincipalHermiteNormalization.instFactPrimeOfNatNat_fLT
theorem normalize_shape (P : DiskPair) (A b : K[X])
    (hA : A.natDegree ≤ 2) (hb : b.natDegree ≤ 1) (hne : A ≠ 0 ∨ b ≠ 0)
    (hv : ∀ j, (x P j ^ 2 + x P j) * A.eval (x P j) + b.eval (x P j) * y P j = 0)
    (hd : ∀ j, (2 * x P j + 1) * A.eval (x P j) +
      (x P j ^ 2 + x P j) * A.derivative.eval (x P j) +
      b.derivative.eval (x P j) * y P j + b.eval (x P j) * s P j = 0) :
    ∃ t : K, ∃ d₀ d₁ e₀ e₁ : ℤ_[2],
      t ≠ 0 ∧
      A = _root_.Polynomial.C t * (N13HermiteResidualDivisibility.quad d₀ d₁).map c ∧
      b = _root_.Polynomial.C t * (N13HermiteResidualDivisibility.lin e₀ e₁).map c ∧
      e₀ ∈ N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P ∧
      e₁ ∈ N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P ∧
      d₀ - 2 * P.x₀ * P.x₁ ∈
        N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P ∧
      d₁ + 2 * (P.x₀ + P.x₁) + 1 ∈
        N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P := by
  have ha := quadratic_eq A hA
  have hb' := linear_eq b hb
  have hAe (j : Fin 2) : A.eval (x P j) =
      A.coeff 2 * x P j ^ 2 + A.coeff 1 * x P j + A.coeff 0 := by
    have h := congrArg (fun p : K[X] => p.eval (x P j)) ha
    simpa only [eval_add, eval_mul, eval_C, eval_pow, eval_X] using h
  have hAd (j : Fin 2) : A.derivative.eval (x P j) =
      2 * A.coeff 2 * x P j + A.coeff 1 := by
    have h := congrArg (fun p : K[X] => p.derivative.eval (x P j)) ha
    simp [derivative_mul, derivative_pow, -mul_eq_zero] at h
    convert h using 1 <;> ring
  have hbeval (j : Fin 2) : b.eval (x P j) = b.coeff 0 + b.coeff 1 * x P j := by
    have h := congrArg (fun p : K[X] => p.eval (x P j)) hb'
    simpa only [eval_add, eval_mul, eval_C, eval_X] using h
  have hbder (j : Fin 2) : b.derivative.eval (x P j) = b.coeff 1 := by
    have h := congrArg (fun p : K[X] => p.derivative.eval (x P j)) hb'
    simpa [derivative_mul] using h
  have hv' (j : Fin 2) :
      (x P j ^ 2 + x P j) *
        (A.coeff 2 * x P j ^ 2 + A.coeff 1 * x P j + A.coeff 0) +
      (b.coeff 0 + b.coeff 1 * x P j) * y P j = 0 := by
    rw [← hAe, ← hbeval]
    exact hv j
  have hd' (j : Fin 2) :
      (2 * x P j + 1) *
        (A.coeff 2 * x P j ^ 2 + A.coeff 1 * x P j + A.coeff 0) +
      (x P j ^ 2 + x P j) * (2 * A.coeff 2 * x P j + A.coeff 1) +
      b.coeff 1 * y P j + (b.coeff 0 + b.coeff 1 * x P j) * s P j = 0 := by
    have h := hd j
    rw [hAe, hAd, hbder, hbeval] at h
    exact h
  obtain ⟨d₀, d₁, e₀, e₁, h₀, h₁, k₀, k₁, hm⟩ :=
    coefficients_are_scaled_integral P (A.coeff 2) (A.coeff 0) (A.coeff 1)
      (b.coeff 0) (b.coeff 1) hv' hd'
  have hAe : A = _root_.Polynomial.C (A.coeff 2) * (N13HermiteResidualDivisibility.quad d₀ d₁).map c := by
    conv_lhs => rw [ha]
    simp only [N13HermiteResidualDivisibility.quad, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]
    rw [h₀, h₁]
    simp only [map_mul]
    ring
  have hbe : b = _root_.Polynomial.C (A.coeff 2) * (N13HermiteResidualDivisibility.lin e₀ e₁).map c := by
    conv_lhs => rw [hb']
    simp only [N13HermiteResidualDivisibility.lin, Polynomial.map_add,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
    rw [k₀, k₁]
    simp only [map_mul]
    ring
  refine ⟨A.coeff 2, d₀, d₁, e₀, e₁, ?_, hAe, hbe, hm⟩
  intro ht
  have hAz : A = 0 := by simpa only [ht, C_0, zero_mul] using hAe
  have hbz : b = 0 := by simpa only [ht, C_0, zero_mul] using hbe
  exact hne.elim (fun h => h hAz) (fun h => h hbz)
end
end MazurProof.N13PrincipalHermiteNormalization
end
end

section
section
set_option autoImplicit false
namespace MazurProof.N13PrincipalHermiteNormalization
noncomputable section
open Polynomial SexticMumford N13CenteredPrincipalNumerator N13GoodCenteredNumerator
open N13ActualHermiteEquations N13RationalHermiteMatrix
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT MazurProof.N13PrincipalHermiteNormalization.instFactPrimeOfNatNat_fLT
/-- Actual principal membership supplies the normalization hypotheses.
This is same-witness matching, not a separate choice of a divisor or class. -/
theorem normalize_actual_numerator (P Q : DiskPair) (n : R) (A b : K[X])
    (hn : n ≠ 0) (hA : A.natDegree ≤ 2) (hb : b.natDegree ≤ 1)
    (hshape : toGood n = gx ((X ^ 2 + X) * A) + gx b * gy)
    (hmem : n ∈ (mumfordIdeal M Q.mumford.u Q.mumford.v *
        mumfordIdeal M B.mumford.u B.mumford.v) *
      (mumfordIdeal M (conjugateSemiMumford M P.mumford.toSemi).u
        (conjugateSemiMumford M P.mumford.toSemi).v) ^ 2) :
    ∃ t : K, ∃ d₀ d₁ e₀ e₁ : ℤ_[2],
      t ≠ 0 ∧
      A = _root_.Polynomial.C t * (N13HermiteResidualDivisibility.quad d₀ d₁).map c ∧
      b = _root_.Polynomial.C t * (N13HermiteResidualDivisibility.lin e₀ e₁).map c ∧
      e₀ ∈ N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P ∧
      e₁ ∈ N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P ∧
      d₀ - 2 * P.x₀ * P.x₁ ∈
        N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P ∧
      d₁ + 2 * (P.x₀ + P.x₁) + 1 ∈
        N13CenteredHermiteFirstOrder.I P * N13CenteredHermiteFirstOrder.I P := by
  obtain ⟨hv, hd⟩ := hermite_equations_of_product_membership P Q n A b hshape hmem
  apply normalize_shape P A b hA hb ?_ hv hd
  by_contra hz
  push_neg at hz
  have he : toGood n = 0 := by simp [hshape, hz.1, hz.2]
  apply hn
  apply (N13GoodSexticCoordinateEquiv.coordinateRingEquiv (K := K)).symm.injective
  rw [map_zero]
  exact he
end
end MazurProof.N13PrincipalHermiteNormalization
end
end


set_option autoImplicit false
open Polynomial
attribute [local instance] MazurProof.N13CenteredHermiteFirstOrder.instFactPrimeOfNatNat_fLT MazurProof.N13CenteredPrincipalNumerator.instFactPrimeOfNatNat_fLT MazurProof.N13PrincipalHermiteNormalization.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartData.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicAbelChartPic.instFactPrimeOfNatNat_fLT MazurProof.N13TwoAdicMumfordTransport.instFactPrimeOfNatNat_fLT
theorem solution (P Q : MazurProof.N13CenteredPrincipalNumerator.DiskPair) (n : MazurProof.N13CenteredPrincipalNumerator.R) (A b : MazurProof.N13CenteredPrincipalNumerator.K[X])
    (hn : n ≠ 0) (hA : A.natDegree ≤ 2) (hb : b.natDegree ≤ 1)
    (hshape : MazurProof.N13GoodCenteredNumerator.toGood n = MazurProof.N13GoodCenteredNumerator.gx ((X ^ 2 + X) * A) + MazurProof.N13GoodCenteredNumerator.gx b * MazurProof.N13GoodCenteredNumerator.gy)
    (hmem : n ∈ (MazurProof.SexticMumford.mumfordIdeal MazurProof.N13CenteredPrincipalNumerator.M Q.mumford.u Q.mumford.v *
        MazurProof.SexticMumford.mumfordIdeal MazurProof.N13CenteredPrincipalNumerator.M MazurProof.N13CenteredPrincipalNumerator.B.mumford.u MazurProof.N13CenteredPrincipalNumerator.B.mumford.v) *
      (MazurProof.SexticMumford.mumfordIdeal MazurProof.N13CenteredPrincipalNumerator.M (MazurProof.SexticMumford.conjugateSemiMumford MazurProof.N13CenteredPrincipalNumerator.M P.mumford.toSemi).u
        (MazurProof.SexticMumford.conjugateSemiMumford MazurProof.N13CenteredPrincipalNumerator.M P.mumford.toSemi).v) ^ 2) :
    ∃ t : MazurProof.N13CenteredPrincipalNumerator.K, ∃ d₀ d₁ e₀ e₁ : ℤ_[2],
      t ≠ 0 ∧
      A = C t * (MazurProof.N13HermiteResidualDivisibility.quad d₀ d₁).map MazurProof.N13ActualHermiteEquations.c ∧
      b = C t * (MazurProof.N13HermiteResidualDivisibility.lin e₀ e₁).map MazurProof.N13ActualHermiteEquations.c ∧
      e₀ ∈ MazurProof.N13CenteredHermiteFirstOrder.I P * MazurProof.N13CenteredHermiteFirstOrder.I P ∧
      e₁ ∈ MazurProof.N13CenteredHermiteFirstOrder.I P * MazurProof.N13CenteredHermiteFirstOrder.I P ∧
      d₀ - 2 * P.x₀ * P.x₁ ∈
        MazurProof.N13CenteredHermiteFirstOrder.I P * MazurProof.N13CenteredHermiteFirstOrder.I P ∧
      d₁ + 2 * (P.x₀ + P.x₁) + 1 ∈
        MazurProof.N13CenteredHermiteFirstOrder.I P * MazurProof.N13CenteredHermiteFirstOrder.I P := by
  exact MazurProof.N13PrincipalHermiteNormalization.normalize_actual_numerator P Q n A b hn hA hb hshape hmem
