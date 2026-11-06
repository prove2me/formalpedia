-- Prove2me | solution 1 for OAI.RankTwoComplex.binary_gaussian_poisson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:46:20.073485+00:00
-- url     : https://prove2.me/submissions/bbe043b2-e205-4dcb-b530-9b125555a64b

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_BinaryGaussian
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


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
namespace RankTwoComplex
open Real
private theorem binary_split (a b d : ℂ) (m n : ℤ) :
    binaryGaussian a b d (m,n) =
      Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2) *
        Complex.exp (-(Real.pi : ℂ) * a * (m : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * (-(b * (n : ℂ))) * (m : ℂ)) := by
  dsimp [binaryGaussian]
  rw [← Complex.exp_add]
  congr 1
  ring
private theorem first_exponent_identity {a b d : ℂ} (ha : a ≠ 0) (k n : ℤ) :
    (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2) +
      (-(Real.pi : ℂ) / a * ((k : ℂ) + Complex.I * (-(b * (n : ℂ)))) ^ 2) =
      (-(Real.pi : ℂ) / a * (k : ℂ) ^ 2) +
        (-(Real.pi : ℂ) * schur a b d * (n : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * (Complex.I * b / a * (k : ℂ)) * (n : ℂ)) := by
  dsimp [schur]
  field_simp [ha]
  ring_nf
  simp [Complex.I_sq]
private theorem first_transform_term {a b d : ℂ} (ha : a ≠ 0) (k n : ℤ) :
    Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2) *
      Complex.exp (-(Real.pi : ℂ) / a *
        ((k : ℂ) + Complex.I * (-(b * (n : ℂ)))) ^ 2) =
      firstGaussian a b d (k,n) := by
  rw [← Complex.exp_add, first_exponent_identity ha k n, Complex.exp_add]
  rfl
private theorem first_poisson_slice {a b d : ℂ} (ha : 0 < a.re) (n : ℤ) :
    (∑' m : ℤ, binaryGaussian a b d (m,n)) =
      (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, firstGaussian a b d (k,n) := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  let C : ℂ := Complex.exp (-(Real.pi : ℂ) * d * (n : ℂ) ^ 2)
  let B : ℂ := -(b * (n : ℂ))
  let F : ℤ → ℂ := fun m => Complex.exp
    (-(Real.pi : ℂ) * a * (m : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * B * (m : ℂ))
  let H : ℤ → ℂ := fun k => Complex.exp
    (-(Real.pi : ℂ) / a * ((k : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' m : ℤ, binaryGaussian a b d (m,n)) = C * ∑' m : ℤ, F m := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    exact binary_split a b d m n
  have hpoisson : (∑' m : ℤ, F m) =
      (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k :=
    Complex.tsum_exp_neg_quadratic ha B
  calc
    (∑' m : ℤ, binaryGaussian a b d (m,n)) = C * ∑' m : ℤ, F m := hsplit
    _ = C * ((1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k) := by rw [hpoisson]
    _ = (1 / a ^ (1 / 2 : ℂ)) * (C * ∑' k : ℤ, H k) := by ring
    _ = (1 / a ^ (1 / 2 : ℂ)) * ∑' k : ℤ, firstGaussian a b d (k,n) := by
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      exact first_transform_term ha0 k n
private theorem second_poisson_slice {a b d : ℂ}
    (hδ : 0 < (schur a b d).re) (k : ℤ) :
    (∑' n : ℤ, firstGaussian a b d (k,n)) =
      (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
        ∑' l : ℤ, dualGaussian a b d (k,l) := by
  have hδ0 : schur a b d ≠ 0 := by
    intro h
    simp [h] at hδ
  let A : ℂ := schur a b d
  let B : ℂ := Complex.I * b / a * (k : ℂ)
  let C : ℂ := Complex.exp (-(Real.pi : ℂ) / a * (k : ℂ) ^ 2)
  let F : ℤ → ℂ := fun n => Complex.exp
    (-(Real.pi : ℂ) * A * (n : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * B * (n : ℂ))
  let H : ℤ → ℂ := fun l => Complex.exp
    (-(Real.pi : ℂ) / A * ((l : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' n : ℤ, firstGaussian a b d (k,n)) = C * ∑' n : ℤ, F n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rfl
  have hpoisson : (∑' n : ℤ, F n) =
      (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l :=
    Complex.tsum_exp_neg_quadratic hδ B
  have hterm (l : ℤ) : C * H l = dualGaussian a b d (k,l) := by
    have hb : Complex.I * B = -(b / a * (k : ℂ)) := by
      dsimp [B]
      field_simp
      ring_nf
      simp [Complex.I_sq]
    dsimp [H, dualGaussian, C, A]
    rw [hb]
    ring_nf
  calc
    (∑' n : ℤ, firstGaussian a b d (k,n)) = C * ∑' n : ℤ, F n := hsplit
    _ = C * ((1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l) := by rw [hpoisson]
    _ = (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) := by ring
    _ = (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          ∑' l : ℤ, dualGaussian a b d (k,l) := by
      change (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) =
        (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, dualGaussian a b d (k,l)
      congr 1
      rw [← tsum_mul_left]
      exact tsum_congr hterm
end RankTwoComplex
namespace GaussianShiftedPartition
open ActualEisensteinCubic ConcreteTraceCRT ConcreteBreveE
end GaussianShiftedPartition
namespace RankTwoAffine
open RankTwoComplex
end RankTwoAffine
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace RankTwoEisShift
end RankTwoEisShift
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
open OAI.RankTwoComplex
open Real
namespace OAI.RankTwoComplex
theorem _root_.solution {a b d : ℂ}
    (ha : 0 < a.re) (hδ : 0 < (schur a b d).re)
    (hO : Summable (binaryGaussian a b d))
    (hM : Summable (firstGaussian a b d))
    (hD : Summable (dualGaussian a b d)) :
    (∑' z : ℤ × ℤ, binaryGaussian a b d z) =
      (1 / a ^ (1 / 2 : ℂ)) *
        (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, dualGaussian a b d z := by
  have hOcomm :
      (∑' n : ℤ, ∑' m : ℤ, binaryGaussian a b d (m,n)) =
        ∑' m : ℤ, ∑' n : ℤ, binaryGaussian a b d (m,n) :=
    (show Summable (Function.uncurry (fun m n : ℤ => binaryGaussian a b d (m,n)))
      from hO).tsum_comm
  have hMcomm :
      (∑' n : ℤ, ∑' k : ℤ, firstGaussian a b d (k,n)) =
        ∑' k : ℤ, ∑' n : ℤ, firstGaussian a b d (k,n) :=
    (show Summable (Function.uncurry (fun k n : ℤ => firstGaussian a b d (k,n)))
      from hM).tsum_comm
  calc
    (∑' z : ℤ × ℤ, binaryGaussian a b d z) =
        ∑' m : ℤ, ∑' n : ℤ, binaryGaussian a b d (m,n) := hO.tsum_prod
    _ = ∑' n : ℤ, ∑' m : ℤ, binaryGaussian a b d (m,n) := hOcomm.symm
    _ = ∑' n : ℤ, (1 / a ^ (1 / 2 : ℂ)) *
          ∑' k : ℤ, firstGaussian a b d (k,n) := by
      apply tsum_congr
      intro n
      exact first_poisson_slice ha n
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' n : ℤ, ∑' k : ℤ, firstGaussian a b d (k,n)) := tsum_mul_left
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' n : ℤ, firstGaussian a b d (k,n)) := by
      rw [hMcomm]
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
            ∑' l : ℤ, dualGaussian a b d (k,l)) := by
      congr 1
      apply tsum_congr
      intro k
      exact second_poisson_slice hδ k
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' l : ℤ, dualGaussian a b d (k,l)) := by
      rw [tsum_mul_left]
      ring
    _ = (1 / a ^ (1 / 2 : ℂ)) *
          (1 / (schur a b d) ^ (1 / 2 : ℂ)) *
          ∑' z : ℤ × ℤ, dualGaussian a b d z := by
      rw [hD.tsum_prod]
end OAI.RankTwoComplex
