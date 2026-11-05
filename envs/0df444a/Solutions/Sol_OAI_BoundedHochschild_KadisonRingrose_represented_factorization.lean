-- Prove2me | solution 1 for OAI.BoundedHochschild.KadisonRingrose.represented_factorization
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:51:12.070796+00:00
-- url     : https://prove2.me/submissions/9868e13f-632b-468b-9ed1-d3d4a866d042

import Mathlib
import Definitions.Def_KadisonRingroseSupport2
import Theorems.Thm_OAI_BoundedHochschild_KadisonRingrose_exists_unital_completelyPositive_extension

set_option Elab.async false
set_option linter.all false

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
namespace HochschildMatrixDilation
noncomputable section
open scoped Matrix ComplexOrder
open Complex
variable {A : Type*} [CStarAlgebra A]

abbrev Mat (A : Type*) := CStarMatrix (Fin 2) (Fin 2) A

def diag (a b : A) : Mat A := CStarMatrix.ofMatrix !![a,0;0,b]

def offdiag (a b : A) : Mat A := CStarMatrix.ofMatrix !![0,a;b,0]

@[simp] lemma diag_zero_zero : diag (0:A) 0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl
@[simp] lemma diag_one_one : diag (1:A) 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl
@[simp] lemma diag_add (a b c d : A) : diag (a+c) (b+d) = diag a b + diag c d := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag]
@[simp] lemma diag_smul (z : ℂ) (a b : A) : diag (z • a) (z • b) = z • diag a b := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag]
@[simp] lemma diag_mul (a b c d : A) : diag a b * diag c d = diag (a*c) (b*d) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diag, CStarMatrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma star_diag (a b : A) : star (diag a b) = diag (star a) (star b) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diag, CStarMatrix.star_eq_conjTranspose]
@[simp] lemma star_offdiag (a b : A) : star (offdiag a b) = offdiag (star b) (star a) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [offdiag, CStarMatrix.star_eq_conjTranspose]
@[simp] lemma offdiag_mul (a b c d : A) :
    offdiag a b * offdiag c d = diag (a*d) (b*c) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diag, offdiag, CStarMatrix.mul_apply, Fin.sum_univ_two]

def diagHom : A × A →⋆ₐ[ℂ] Mat A where
  toFun a := diag a.1 a.2
  map_one' := diag_one_one
  map_mul' a b := (diag_mul _ _ _ _).symm
  map_zero' := diag_zero_zero
  map_add' a b := diag_add _ _ _ _
  commutes' z := by
    ext i j; fin_cases i <;> fin_cases j <;>
      rfl
  map_star' a := (star_diag _ _).symm

variable [PartialOrder A] [StarOrderedRing A]

lemma norm_diag_le (a b : A) : ‖diag a b‖ ≤ max ‖a‖ ‖b‖ := by
  exact NonUnitalStarAlgHom.norm_apply_le diagHom (a,b)

local instance : NonUnitalContinuousFunctionalCalculus ℝ (Mat A) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance : NonnegSpectrumClass ℝ (Mat A) :=
  CStarAlgebra.instNonnegSpectrumClass

lemma diagEntry_nonneg (M : Mat A) (hM : 0 ≤ M) (i : Fin 2) : 0 ≤ M i i := by
  have hs := CFC.sqrt_nonneg M
  have he : M = star (CFC.sqrt M) * CFC.sqrt M := by
    rw [hs.isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self M hM]
  rw [he, CStarMatrix.mul_apply]
  simp only [CStarMatrix.star_apply]
  exact Finset.sum_nonneg fun j _ => star_mul_self_nonneg _
end
end HochschildMatrixDilation
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

variable {M : Type*} [CStarAlgebra M]

def matrixScalarHom (k : ℕ) : M →⋆ₐ[ℂ] CStarMatrix (Fin k) (Fin k) M where
  toFun a := CStarMatrix.ofMatrix (Matrix.scalar (Fin k) a)
  map_zero' := (Matrix.scalar (Fin k)).map_zero
  map_one' := (Matrix.scalar (Fin k)).map_one
  map_add' a b := (Matrix.scalar (Fin k)).map_add a b
  map_mul' a b := (Matrix.scalar (Fin k)).map_mul a b
  commutes' _ := rfl
  map_star' a := by
    ext i j
    change (if i = j then star a else 0) = star (if j = i then a else 0)
    by_cases h : i = j
    · simp only [h, ite_true]
    · simp only [h, Ne.symm h, ite_false, star_zero]

@[simp] lemma matrixScalarHom_apply (k : ℕ) (a : M) (i j : Fin k) :
    matrixScalarHom k a i j = if i = j then a else 0 := rfl
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def positiveUnitBlock (a : A) : Mat A := 1 + offdiag a (star a)

lemma positiveUnitBlock_nonneg (a : A) (ha : ‖a‖ ≤ 1) : 0 ≤ positiveUnitBlock a := by
  have hsq : star a * a ≤ 1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg a)).mp
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg a]
  let d := CFC.sqrt (1 - star a * a)
  have hd : star d * d = 1 - star a * a := by
    rw [(CFC.sqrt_nonneg _).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self _ (sub_nonneg.mpr hsq)
  let R : Mat A := CStarMatrix.ofMatrix !![1, a; 0, d]
  have hR : star R * R = positiveUnitBlock a := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [R, positiveUnitBlock, offdiag, CStarMatrix.mul_apply, CStarMatrix.star_apply,
        Fin.sum_univ_two]
    · simp [R, positiveUnitBlock, offdiag, CStarMatrix.mul_apply, CStarMatrix.star_apply,
        Fin.sum_univ_two]
    · simp [R, positiveUnitBlock, offdiag, CStarMatrix.mul_apply, CStarMatrix.star_apply,
        Fin.sum_univ_two]
    · simp [R, positiveUnitBlock, offdiag, CStarMatrix.mul_apply, CStarMatrix.star_apply,
        Fin.sum_univ_two, hd]
  rw [← hR]
  exact star_mul_self_nonneg R

lemma norm_le_one_of_positiveUnitBlock (a : A) (ha : 0 ≤ positiveUnitBlock a) : ‖a‖ ≤ 1 := by
  let V : Mat A := CStarMatrix.ofMatrix !![-a, 0; 1, 0]
  have hp := diagEntry_nonneg (star V * positiveUnitBlock a * V)
    (star_left_conjugate_nonneg ha V) 0
  have he : (star V * positiveUnitBlock a * V) 0 0 = 1 - star a * a := by
    simp [V, positiveUnitBlock, offdiag, CStarMatrix.mul_apply, CStarMatrix.star_apply,
      Fin.sum_univ_two]
    noncomm_ring
  rw [he] at hp
  have hn := (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg a)).mpr
    (sub_nonneg.mp hp)
  rw [CStarRing.norm_star_mul_self] at hn
  exact (sq_le_one_iff₀ (norm_nonneg a)).mp (by simpa only [pow_two] using hn)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def positiveBlock (p q x : A) : Mat A := diag p q + offdiag x (star x)

omit [PartialOrder A] [StarOrderedRing A] in
lemma positiveBlock_one (x : A) : positiveBlock 1 1 x = positiveUnitBlock x := by
  rw [positiveBlock, diag_one_one]
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma positiveBlock_conjugate (p q x u v : A) :
    star (diag u v) * positiveBlock p q x * diag u v =
      positiveBlock (star u * p * u) (star v * q * v) (star u * x * v) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [positiveBlock, diag, offdiag, CStarMatrix.mul_apply, CStarMatrix.star_apply,
      Fin.sum_univ_two, star_mul, mul_assoc]

omit [PartialOrder A] [StarOrderedRing A] in
lemma diag_isUnit {u v : A} (hu : IsUnit u) (hv : IsUnit v) : IsUnit (diag u v) := by
  obtain ⟨u, rfl⟩ := hu
  obtain ⟨v, rfl⟩ := hv
  refine ⟨⟨diag (u : A) (v : A), diag (↑u⁻¹) (↑v⁻¹), ?_, ?_⟩, rfl⟩
  · rw [diag_mul]
    simp
  · rw [diag_mul]
    simp
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {D A B : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem positiveBlock_transfer_strict (ρ : D →⋆ₐ[ℂ] A) (σ : D →⋆ₐ[ℂ] B)
    (T : A →ₗ[ℂ] B) (hT : ∀ a, ‖T a‖ ≤ ‖a‖)
    (hmodule : ∀ d e a, T (ρ d * a * ρ e) = σ d * T a * σ e)
    (p q : D) (hp : IsStrictlyPositive p) (hq : IsStrictlyPositive q) (a : A)
    (ha : 0 ≤ positiveBlock (ρ p) (ρ q) a) :
    0 ≤ positiveBlock (σ p) (σ q) (T a) := by
  let u := p ^ (-(1 / 2) : ℝ)
  let v := q ^ (-(1 / 2) : ℝ)
  have hu := IsStrictlyPositive.rpow p (-(1 / 2) : ℝ) hp
  have hv := IsStrictlyPositive.rpow q (-(1 / 2) : ℝ) hq
  have hsu : star u = u := hu.nonneg.isSelfAdjoint.star_eq
  have hsv : star v = v := hv.nonneg.isSelfAdjoint.star_eq
  have hup : star u * p * u = 1 := by
    rw [hsu]
    exact CFC.conjugate_rpow_neg_one_half p hp
  have hvq : star v * q * v = 1 := by
    rw [hsv]
    exact CFC.conjugate_rpow_neg_one_half q hq
  have hρp : star (ρ u) * ρ p * ρ u = 1 := by
    simpa only [map_mul, map_star, map_one] using congrArg ρ hup
  have hρq : star (ρ v) * ρ q * ρ v = 1 := by
    simpa only [map_mul, map_star, map_one] using congrArg ρ hvq
  have hσp : star (σ u) * σ p * σ u = 1 := by
    simpa only [map_mul, map_star, map_one] using congrArg σ hup
  have hσq : star (σ v) * σ q * σ v = 1 := by
    simpa only [map_mul, map_star, map_one] using congrArg σ hvq
  have hρu : star (ρ u) = ρ u := by rw [← map_star, hsu]
  have hσu : star (σ u) = σ u := by rw [← map_star, hsu]
  have hnA : ‖ρ u * a * ρ v‖ ≤ 1 := by
    have h := star_left_conjugate_nonneg ha (diag (ρ u) (ρ v))
    rw [positiveBlock_conjugate, hρp, hρq, hρu, positiveBlock_one] at h
    exact norm_le_one_of_positiveUnitBlock _ h
  have hnB : ‖star (σ u) * T a * σ v‖ ≤ 1 := by
    rw [hσu, ← hmodule]
    exact (hT _).trans hnA
  have hpos := positiveUnitBlock_nonneg _ hnB
  have he := positiveBlock_conjugate (σ p) (σ q) (T a) (σ u) (σ v)
  rw [hσp, hσq, positiveBlock_one] at he
  rw [← he] at hpos
  exact (diag_isUnit (hu.isUnit.map σ.toMonoidHom) (hv.isUnit.map σ.toMonoidHom)).star_left_conjugate_nonneg_iff.mp hpos
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {D A B : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma starAlgHom_real_one (ρ : D →⋆ₐ[ℂ] A) (r : ℝ) :
    ρ (r • (1 : D)) = r • (1 : A) := by
  rw [← Complex.coe_smul, map_smul, map_one, Complex.coe_smul]

lemma positive_real_one (r : ℝ) (hr : 0 < r) : IsStrictlyPositive (r • (1 : D)) := by
  refine ⟨smul_nonneg hr.le zero_le_one, ?_⟩
  rw [← Algebra.algebraMap_eq_smul_one]
  exact (isUnit_iff_ne_zero.mpr hr.ne').map (algebraMap ℝ D)

omit [PartialOrder A] [StarOrderedRing A] in
lemma positiveBlock_add_real_one (p q x : A) (r : ℝ) :
    positiveBlock (p + r • 1) (q + r • 1) x = positiveBlock p q x + r • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [positiveBlock, diag, offdiag, add_comm]

theorem positiveBlock_transfer (ρ : D →⋆ₐ[ℂ] A) (σ : D →⋆ₐ[ℂ] B)
    (T : A →ₗ[ℂ] B) (hT : ∀ a, ‖T a‖ ≤ ‖a‖)
    (hmodule : ∀ d e a, T (ρ d * a * ρ e) = σ d * T a * σ e)
    (p q : D) (hp : 0 ≤ p) (hq : 0 ≤ q) (a : A)
    (ha : 0 ≤ positiveBlock (ρ p) (ρ q) a) :
    0 ≤ positiveBlock (σ p) (σ q) (T a) := by
  have heps (r : ℝ) (hr : 0 < r) :
      0 ≤ positiveBlock (σ p) (σ q) (T a) + r • 1 := by
    have h := positiveBlock_transfer_strict ρ σ T hT hmodule
      (p + r • 1) (q + r • 1)
      (IsStrictlyPositive.nonneg_add hp (positive_real_one r hr))
      (IsStrictlyPositive.nonneg_add hq (positive_real_one r hr)) a
    simp only [map_add, starAlgHom_real_one, positiveBlock_add_real_one] at h
    exact h (add_nonneg ha (smul_nonneg hr.le zero_le_one))
  have ht : Tendsto (fun n : ℕ => positiveBlock (σ p) (σ q) (T a) +
      (1 / ((n : ℝ) + 1)) • 1) atTop (𝓝 (positiveBlock (σ p) (σ q) (T a))) := by
    simpa only [zero_smul, add_zero] using
      (tendsto_const_nhds.add ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul
        (tendsto_const_nhds (x := (1 : Mat B)))))
  exact ge_of_tendsto' ht (fun n => heps _ (by positivity))
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def scalarMatrixHom (A : Type*) [CStarAlgebra A] (n : ℕ) :
    CStarMatrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] CStarMatrix (Fin n) (Fin n) A where
  toFun Q := Q.map (algebraMap ℂ A)
  map_zero' := by ext i j; exact map_zero (algebraMap ℂ A)
  map_add' Q R := by ext i j; exact map_add (algebraMap ℂ A) (Q i j) (R i j)
  map_one' := by
    ext i j
    change algebraMap ℂ A (if i = j then 1 else 0) = if i = j then 1 else 0
    split_ifs <;> simp
  map_mul' Q R := by
    ext i j
    change algebraMap ℂ A (∑ k, Q i k * R k j) =
      ∑ k, algebraMap ℂ A (Q i k) * algebraMap ℂ A (R k j)
    simp
  commutes' z := by
    ext i j
    change algebraMap ℂ A (if i = j then z else 0) =
      if i = j then algebraMap ℂ A z else 0
    split_ifs <;> simp
  map_star' Q := by
    ext i j
    exact map_star (StarAlgHom.ofId ℂ A) (Q j i)

@[simp] lemma scalarMatrixHom_apply (n : ℕ)
    (Q : CStarMatrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    scalarMatrixHom A n Q i j = algebraMap ℂ A (Q i j) := rfl

lemma scalarMatrixHom_injective [Nontrivial A] (n : ℕ) :
    Function.Injective (scalarMatrixHom A n) :=
  CStarMatrix.map_injective (algebraMap ℂ A).injective

def entrywiseMatrixLinear (T : A →ₗ[ℂ] B) (n : ℕ) :
    CStarMatrix (Fin n) (Fin n) A →ₗ[ℂ] CStarMatrix (Fin n) (Fin n) B :=
  CStarMatrix.mapₗ T

lemma linearMap_scalar_multiply (T : A →ₗ[ℂ] B) (z w : ℂ) (a : A) :
    T (algebraMap ℂ A z * a * algebraMap ℂ A w) =
      algebraMap ℂ B z * T a * algebraMap ℂ B w := by
  simp [Algebra.algebraMap_eq_smul_one]

lemma entrywiseMatrixLinear_scalar_actions (T : A →ₗ[ℂ] B) (n : ℕ)
    (Q R : CStarMatrix (Fin n) (Fin n) ℂ) (X : CStarMatrix (Fin n) (Fin n) A) :
    entrywiseMatrixLinear T n (scalarMatrixHom A n Q * X * scalarMatrixHom A n R) =
      scalarMatrixHom B n Q * entrywiseMatrixLinear T n X * scalarMatrixHom B n R := by
  apply CStarMatrix.ext
  intro i j
  change T (∑ k, (∑ l, algebraMap ℂ A (Q i l) * X l k) * algebraMap ℂ A (R k j)) =
    ∑ k, (∑ l, algebraMap ℂ B (Q i l) * T (X l k)) * algebraMap ℂ B (R k j)
  simp only [Finset.sum_mul, map_sum, linearMap_scalar_multiply]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Nontrivial A]

lemma scalarBlock_diagonals_nonneg (n : ℕ)
    (p q : CStarMatrix (Fin n) (Fin n) ℂ) (X : CStarMatrix (Fin n) (Fin n) A)
    (hX : 0 ≤ positiveBlock (scalarMatrixHom A n p) (scalarMatrixHom A n q) X) :
    0 ≤ p ∧ 0 ≤ q := by
  have hp := diagEntry_nonneg _ hX 0
  have hq := diagEntry_nonneg _ hX 1
  have hρ := scalarMatrixHom_injective (A := A) n
  constructor
  · apply (Compat.map_le_map_iff (scalarMatrixHom A n) hρ).mp
    simpa [positiveBlock, diag, offdiag] using hp
  · apply (Compat.map_le_map_iff (scalarMatrixHom A n) hρ).mp
    simpa [positiveBlock, diag, offdiag] using hq

theorem scalarPositiveBlock_transfer (T : A →ₗ[ℂ] B) (n : ℕ)
    (hT : ∀ X : CStarMatrix (Fin n) (Fin n) A, ‖X.map T‖ ≤ ‖X‖)
    (p q : CStarMatrix (Fin n) (Fin n) ℂ) (X : CStarMatrix (Fin n) (Fin n) A)
    (hX : 0 ≤ positiveBlock (scalarMatrixHom A n p) (scalarMatrixHom A n q) X) :
    0 ≤ positiveBlock (scalarMatrixHom B n p) (scalarMatrixHom B n q) (X.map T) := by
  obtain ⟨hp, hq⟩ := scalarBlock_diagonals_nonneg n p q X hX
  exact positiveBlock_transfer (scalarMatrixHom A n) (scalarMatrixHom B n)
    (entrywiseMatrixLinear T n) hT (entrywiseMatrixLinear_scalar_actions T n)
    p q hp hq X hX
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

universe u v w
namespace NaimarkZFC

def IsState {A : Type u} [CStarAlgebra A] (f : A →L[ℂ] ℂ) : Prop :=
  ‖f‖ = 1 ∧ ∀ a : A, (f (star a * a)).im = 0 ∧ 0 ≤ (f (star a * a)).re

section HNNWords

namespace HNNWord
variable {A B : Type*} [Mul B]

end HNNWord

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  (φ : A →⋆ₐ[ℂ] B) (v : Bool → B) (K : Bool → A → Prop)

variable (center r : Bool → A → A)
  (hc : ∀ i a, K i (center i a))
  (hr : ∀ i a, v i*φ a*v (!i) = v i*φ (center i a)*v (!i) + φ (r i a))
include hc hr

end HNNWords

section GNS

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def gnsVector (f : A →ₚ[ℂ] ℂ) : f.GNS := (f.toPreGNS 1 : f.GNS)

@[simp] theorem gns_apply_vector (f : A →ₚ[ℂ] ℂ) (a : A) :
    f.gnsStarAlgHom a (gnsVector f) = (f.toPreGNS a : f.GNS) := by
  simp [gnsVector]

@[simp] theorem gnsVector_coefficient (f : A →ₚ[ℂ] ℂ) (a : A) :
    ⟪gnsVector f, f.gnsStarAlgHom a (gnsVector f)⟫_ℂ = f a := by
  simp [gnsVector, Completion.inner_coe, PositiveLinearMap.preGNS_inner_def]

@[simp] theorem gnsVector_norm_sq (f : A →ₚ[ℂ] ℂ) :
    ‖gnsVector f‖ ^ 2 = (f 1).re := by
  simp only [gnsVector, Completion.norm_coe,
    PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.ofPreGNS_toPreGNS,
    star_one, one_mul]
  exact Real.sq_sqrt (f.map_nonneg (show (0 : A) ≤ 1 from zero_le_one)).1

theorem positive_norm_apply_le (f : A →ₚ[ℂ] ℂ) (a : A) :
    ‖f a‖ ≤ (f 1).re * ‖a‖ := by
  calc
    ‖f a‖ = ‖⟪gnsVector f, f.gnsStarAlgHom a (gnsVector f)⟫_ℂ‖ :=
      congrArg norm (gnsVector_coefficient f a).symm
    _ ≤ ‖gnsVector f‖ * ‖f.gnsStarAlgHom a (gnsVector f)‖ := norm_inner_le_norm _ _
    _ ≤ ‖gnsVector f‖ * (‖f.gnsStarAlgHom a‖ * ‖gnsVector f‖) := by
      gcongr
      exact (f.gnsStarAlgHom a).le_opNorm _
    _ ≤ ‖gnsVector f‖ * (‖a‖ * ‖gnsVector f‖) := by
      gcongr
      exact NonUnitalStarAlgHom.norm_apply_le f.gnsStarAlgHom a
    _ = (f 1).re * ‖a‖ := by rw [← gnsVector_norm_sq]; ring

def positiveCLM (f : A →ₚ[ℂ] ℂ) : A →L[ℂ] ℂ :=
  f.toLinearMap.mkContinuous (f 1).re (positive_norm_apply_le f)

@[simp] theorem positiveCLM_apply (f : A →ₚ[ℂ] ℂ) (a : A) : positiveCLM f a = f a := rfl

theorem positiveCLM_norm (f : A →ₚ[ℂ] ℂ) : ‖positiveCLM f‖ = (f 1).re := by
  have hpos : 0 ≤ f 1 := f.map_nonneg zero_le_one
  apply le_antisymm
  · exact (positiveCLM f).opNorm_le_bound hpos.1 (positive_norm_apply_le f)
  · calc
      (f 1).re = ‖f 1‖ := Complex.re_eq_norm.mpr hpos
      _ = ‖positiveCLM f 1‖ := rfl
      _ ≤ ‖positiveCLM f‖ * ‖(1 : A)‖ := (positiveCLM f).le_opNorm 1
      _ ≤ ‖positiveCLM f‖ * 1 := by
        gcongr
        exact (IsStarProjection.one A).norm_le _
      _ = ‖positiveCLM f‖ := mul_one _

def positiveOfSquares (f : A →L[ℂ] ℂ)
    (hf : ∀ a : A, (f (star a * a)).im = 0 ∧ 0 ≤ (f (star a * a)).re) :
    A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ f.toLinearMap fun x hx => by
    have hx' := StarOrderedRing.nonneg_iff.mp hx
    refine AddSubmonoid.closure_induction (fun x hx => ?_) (by simp)
      (fun x y _ _ hx hy => ?_) hx'
    · obtain ⟨a, rfl⟩ := hx
      exact ⟨(hf a).2, (hf a).1.symm⟩
    · simpa only [map_add] using add_nonneg hx hy

@[simp] theorem positiveOfSquares_apply (f : A →L[ℂ] ℂ)
    (hf : ∀ a : A, (f (star a * a)).im = 0 ∧ 0 ≤ (f (star a * a)).re) (a : A) :
    positiveOfSquares f hf a = f a := rfl

@[simp] theorem positiveCLM_positiveOfSquares (f : A →L[ℂ] ℂ)
    (hf : ∀ a : A, (f (star a * a)).im = 0 ∧ 0 ≤ (f (star a * a)).re) :
    positiveCLM (positiveOfSquares f hf) = f := by ext; rfl

theorem isState_iff (f : A →L[ℂ] ℂ) :
    IsState f ↔ f 1 = 1 ∧
      ∀ a : A, (f (star a * a)).im = 0 ∧ 0 ≤ (f (star a * a)).re := by
  constructor
  · rintro ⟨hnorm, hpos⟩
    refine ⟨?_, hpos⟩
    have hre : (f 1).re = 1 := by
      rw [← positiveOfSquares_apply f hpos 1, ← positiveCLM_norm,
        positiveCLM_positiveOfSquares, hnorm]
    have him : (f 1).im = 0 := by simpa using (hpos 1).1
    exact Complex.ext hre him
  · rintro ⟨hone, hpos⟩
    refine ⟨?_, hpos⟩
    have hn := positiveCLM_norm (positiveOfSquares f hpos)
    simpa only [positiveCLM_positiveOfSquares, positiveOfSquares_apply, hone,
      Complex.one_re] using hn

theorem state_map_star (f : A →L[ℂ] ℂ) (hf : IsState f) (a : A) :
    f (star a) = star (f a) := map_star (positiveOfSquares f hf.2) a

omit [PartialOrder A] [StarOrderedRing A] in

theorem state_norm_apply_le (f : A →L[ℂ] ℂ) (hf : IsState f) (a : A) : ‖f a‖ ≤ ‖a‖ := by
  simpa [hf.1] using f.le_opNorm a
end GNS
end NaimarkZFC
end
end OAI
end

section
namespace OAI

noncomputable section

namespace NaimarkZFC

variable {A : Type*} [CStarAlgebra A] (e : A) (he : IsStarProjection e)

open scoped ComplexOrder InnerProductSpace
open UniformSpace
open Filter Topology
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped ComplexOrder ComplexStarModule
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem selfAdjoint_nonneg_of_norm_one (g : selfAdjoint A →L[ℝ] ℝ)
    (hg : ‖g‖ ≤ 1) (h1 : g 1 = 1) (a : selfAdjoint A) (ha : 0 ≤ (a : A)) :
    0 ≤ g a := by
  have hau : (a : A) ≤ ‖a‖ • (1 : A) := by
    change (a : A) ≤ ‖(a : A)‖ • (1 : A)
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (CStarAlgebra.norm_le_iff_le_algebraMap (a : A) (norm_nonneg _) ha).mp le_rfl
  have hpos : 0 ≤ ‖a‖ • (1 : A) - (a : A) := sub_nonneg.mpr hau
  have hnorm : ‖‖a‖ • (1 : selfAdjoint A) - a‖ ≤ ‖a‖ := by
    change ‖‖a‖ • (1 : A) - (a : A)‖ ≤ ‖a‖
    apply (CStarAlgebra.norm_le_iff_le_algebraMap _ (norm_nonneg _) hpos).mpr
    simpa only [Algebra.algebraMap_eq_smul_one] using sub_le_self (‖a‖ • (1 : A)) ha
  have hb := g.le_opNorm (‖a‖ • (1 : selfAdjoint A) - a)
  have hc : ‖g (‖a‖ • (1 : selfAdjoint A) - a)‖ ≤ ‖a‖ :=
    hb.trans ((mul_le_mul_of_nonneg_right hg (norm_nonneg _)).trans (by simpa using hnorm))
  rw [map_sub, map_smul, h1, smul_eq_mul, mul_one, Real.norm_eq_abs] at hc
  have h := (le_abs_self _).trans hc
  linarith

def selfAdjointComplexify (g : selfAdjoint A →ₗ[ℝ] ℝ) : A →ₗ[ℂ] ℂ where
  toFun a := (g (realPart a) : ℂ) + Complex.I * (g (imaginaryPart a) : ℂ)
  map_add' a b := by simp only [map_add, Complex.ofReal_add, mul_add]; ring
  map_smul' z a := by
    simp only [realPart_smul, imaginaryPart_smul, map_sub, map_add, map_smul,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, smul_eq_mul]
    apply Complex.ext <;> simp

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem selfAdjointComplexify_coe (g : selfAdjoint A →ₗ[ℝ] ℝ) (a : selfAdjoint A) :
    selfAdjointComplexify g (a : A) = (g a : ℂ) := by
  simp [selfAdjointComplexify]

def selfAdjointPositive (g : selfAdjoint A →L[ℝ] ℝ) (hg : ‖g‖ ≤ 1) (h1 : g 1 = 1) :
    A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (selfAdjointComplexify g.toLinearMap) fun a ha => by
    let x : selfAdjoint A := ⟨a, ha.isSelfAdjoint⟩
    change 0 ≤ selfAdjointComplexify g.toLinearMap (x : A)
    rw [selfAdjointComplexify_coe]
    exact ⟨selfAdjoint_nonneg_of_norm_one g hg h1 x ha, by simp⟩

@[simp] theorem selfAdjointPositive_coe (g : selfAdjoint A →L[ℝ] ℝ)
    (hg : ‖g‖ ≤ 1) (h1 : g 1 = 1) (a : selfAdjoint A) :
    selfAdjointPositive g hg h1 (a : A) = (g a : ℂ) :=
  selfAdjointComplexify_coe _ _

@[simp] theorem selfAdjointPositive_one (g : selfAdjoint A →L[ℝ] ℝ)
    (hg : ‖g‖ ≤ 1) (h1 : g 1 = 1) : selfAdjointPositive g hg h1 1 = 1 := by
  simpa only [selfAdjoint.val_one, h1, Complex.ofReal_one] using selfAdjointPositive_coe g hg h1 1

def selfAdjointSubspace (S : StarSubalgebra ℂ A) : Submodule ℝ A :=
  (S.toSubalgebra.toSubmodule.restrictScalars ℝ) ⊓ selfAdjoint.submodule ℝ A

def selfAdjointSubspaceInclusion (S : StarSubalgebra ℂ A) :
    selfAdjointSubspace S →L[ℝ] S :=
  LinearMap.mkContinuous
    { toFun := fun a => ⟨a.val, a.property.1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl } 1 (fun a => by simp [one_mul])

omit [PartialOrder A] [StarOrderedRing A] in

theorem exists_state_extension_subalgebra
    (S : StarSubalgebra ℂ A) [IsClosed (S : Set A)]
    (f : S →L[ℂ] ℂ) (hf : IsState f) :
    ∃ F : A →L[ℂ] ℂ, IsState F ∧ ∀ a : S, F (a : A) = f a := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder S := CStarAlgebra.spectralOrder S
  let : StarOrderedRing S := CStarAlgebra.spectralOrderedRing S
  let g : selfAdjointSubspace S →L[ℝ] ℝ :=
    Complex.reCLM.comp ((f.restrictScalars ℝ).comp (selfAdjointSubspaceInclusion S))
  have hg : ‖g‖ ≤ 1 := by
    apply g.opNorm_le_bound zero_le_one
    intro a
    change ‖(f (selfAdjointSubspaceInclusion S a)).re‖ ≤ 1 * ‖a‖
    calc
      _ ≤ ‖f (selfAdjointSubspaceInclusion S a)‖ := by simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm _
      _ ≤ ‖selfAdjointSubspaceInclusion S a‖ := state_norm_apply_le f hf _
      _ = 1 * ‖a‖ := by simp [selfAdjointSubspaceInclusion]; rfl
  obtain ⟨G₀, hG₀, hnG₀⟩ := exists_extension_norm_eq (selfAdjointSubspace S) g
  let sa : selfAdjoint A →L[ℝ] A :=
    ((selfAdjoint.submodule ℝ A).subtype).mkContinuous 1 (fun a => by simp)
  let G := G₀.comp sa
  have hGn : ‖G‖ ≤ 1 := by
    apply G.opNorm_le_bound zero_le_one
    intro a
    calc
      ‖G a‖ ≤ ‖G₀‖ * ‖sa a‖ := G₀.le_opNorm _
      _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right (hnG₀.trans_le hg) (norm_nonneg _)
  have hG1 : G 1 = 1 := by
    let e : selfAdjointSubspace S := ⟨1, S.one_mem, IsSelfAdjoint.one A⟩
    have he := hG₀ e
    change G 1 = (f 1).re at he
    simpa only [(isState_iff f).mp hf |>.1, Complex.one_re] using he
  let F := positiveCLM (selfAdjointPositive G hGn hG1)
  have hF : IsState F := by
    apply (isState_iff _).mpr
    refine ⟨selfAdjointPositive_one G hGn hG1, fun a => ?_⟩
    exact ⟨((selfAdjointPositive G hGn hG1).map_nonneg
      (star_mul_self_nonneg a)).2.symm,
      ((selfAdjointPositive G hGn hG1).map_nonneg
      (star_mul_self_nonneg a)).1⟩
  refine ⟨F, hF, ?_⟩
  have hs (a : S) (ha : IsSelfAdjoint a) : F (a : A) = f a := by
    let b : selfAdjointSubspace S := ⟨(a : A), a.property, by
      change star (a : A) = (a : A)
      exact congrArg Subtype.val ha.star_eq⟩
    let bsa : selfAdjoint A := ⟨(a : A), b.property.2⟩
    have hfb : (f a).im = 0 := by
      have hh := state_map_star f hf a
      rw [ha.star_eq] at hh
      exact Complex.conj_eq_iff_im.mp hh.symm
    change selfAdjointPositive G hGn hG1 (bsa : A) = f a
    rw [selfAdjointPositive_coe]
    change (G₀ b : ℂ) = f a
    rw [hG₀ b]
    change ((f a).re : ℂ) = f a
    exact Complex.ext (by simp) (by simpa using hfb.symm)
  intro a
  have hdecomp := realPart_add_I_smul_imaginaryPart a
  rw [← hdecomp]
  change F (((realPart a : S) : A) + Complex.I • ((imaginaryPart a : S) : A)) = _
  simp only [map_add, map_smul]
  rw [hs _ (realPart a).property, hs _ (imaginaryPart a).property]

omit [PartialOrder A] [StarOrderedRing A] in

theorem character_isState (φ : WeakDual.characterSpace ℂ A) :
    IsState (WeakDual.toStrongDual (φ : WeakDual ℂ A)) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  apply (isState_iff _).mpr
  refine ⟨map_one φ, fun a => ?_⟩
  change (φ (star a * a)).im = 0 ∧ 0 ≤ (φ (star a * a)).re
  rw [map_mul, map_star]
  have h := star_mul_self_nonneg (φ a)
  exact ⟨h.2.symm, h.1⟩

omit [PartialOrder A] [StarOrderedRing A] in

theorem exists_norming_state [Nontrivial A] (a : A) [IsStarNormal a] :
    ∃ f : A →L[ℂ] ℂ, IsState f ∧ ‖f a‖ = ‖a‖ := by
  let S := StarAlgebra.elemental ℂ a
  have : IsClosed (S : Set A) := StarAlgebra.elemental.isClosed ℂ a
  let b : S := ⟨a, StarAlgebra.elemental.self_mem ℂ a⟩
  obtain ⟨z, hz, hnz⟩ :=
    (IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℂ) b).1
  obtain ⟨φ, hφ⟩ := WeakDual.CharacterSpace.mem_spectrum_iff_exists.mp hz
  obtain ⟨f, hf, hrest⟩ := exists_state_extension_subalgebra S
    (WeakDual.toStrongDual (φ : WeakDual ℂ S)) (character_isState φ)
  refine ⟨f, hf, ?_⟩
  change ‖f (b : A)‖ = ‖b‖
  rw [hrest b]
  change ‖φ b‖ = ‖b‖
  rw [hφ]
  exact hnz
end NaimarkZFC
end
end OAI
end

section
namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace

namespace WeakPureInfiniteness

section MatrixOperators

variable {n H : Type*} [Fintype n]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def matrixOperator (M : CStarMatrix n n (H →L[ℂ] H)) :
    (PiLp 2 (fun _ : n => H)) →L[ℂ] (PiLp 2 (fun _ : n => H)) :=
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : n => H)
  e.symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi fun i => ∑ j, (M i j).comp (ContinuousLinearMap.proj j)).comp
      e.toContinuousLinearMap)

omit [CompleteSpace H] in
@[simp]

lemma matrixOperator_apply (M : CStarMatrix n n (H →L[ℂ] H))
    (x : PiLp 2 (fun _ : n => H)) (i : n) :
    matrixOperator M x i = ∑ j, M i j (x j) := by
  simp [matrixOperator]

omit [CompleteSpace H] in
lemma matrixOperator_add (M N : CStarMatrix n n (H →L[ℂ] H)) :
    matrixOperator (M + N) = matrixOperator M + matrixOperator N := by
  ext x i
  simp [Finset.sum_add_distrib]

omit [CompleteSpace H] in
lemma matrixOperator_smul (c : ℂ) (M : CStarMatrix n n (H →L[ℂ] H)) :
    matrixOperator (c • M) = c • matrixOperator M := by
  ext x i
  simp [Finset.smul_sum]

omit [CompleteSpace H] in
lemma matrixOperator_zero : matrixOperator (0 : CStarMatrix n n (H →L[ℂ] H)) = 0 := by
  ext x i
  simp

omit [CompleteSpace H] in
lemma matrixOperator_mul (M N : CStarMatrix n n (H →L[ℂ] H)) :
    matrixOperator (M * N) = matrixOperator M * matrixOperator N := by
  ext x i
  simp only [matrixOperator_apply, CStarMatrix.mul_apply, sum_apply,
    mul_apply_eq_comp, map_sum]
  exact Finset.sum_comm

lemma matrixOperator_star (M : CStarMatrix n n (H →L[ℂ] H)) :
    matrixOperator (star M) = star (matrixOperator M) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [PiLp.inner_apply, matrixOperator_apply, sum_inner, inner_sum,
    CStarMatrix.star_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]
  exact Finset.sum_comm

noncomputable def matrixOperatorHom : CStarMatrix n n (H →L[ℂ] H) →⋆ₙₐ[ℂ]
    ((PiLp 2 (fun _ : n => H)) →L[ℂ] (PiLp 2 (fun _ : n => H))) where
  toFun := matrixOperator
  map_zero' := matrixOperator_zero
  map_add' := matrixOperator_add
  map_smul' := matrixOperator_smul
  map_mul' := matrixOperator_mul
  map_star' := matrixOperator_star

omit [CompleteSpace H] in
lemma matrixOperator_single [DecidableEq n] (M : CStarMatrix n n (H →L[ℂ] H)) (i j : n) (x : H) :
    matrixOperator M (PiLp.single 2 j x) i = M i j x := by
  simp [PiLp.single_apply, apply_ite]
end MatrixOperators
end WeakPureInfiniteness
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype I]

def algebraGram (a : I → M) : CStarMatrix I I M := fun i j => star (a i) * a j

lemma algebraGram_nonneg (a : I → M) : 0 ≤ algebraGram a := by
  classical
  cases isEmpty_or_nonempty I with
  | inl h =>
    have hz : algebraGram a = 0 := by ext i; exact isEmptyElim i
    rw [hz]
  | inr h =>
    let i₀ : I := Classical.choice h
    let R : CStarMatrix I I M := fun i j => if i = i₀ then a j else 0
    have heq : star R * R = algebraGram a := by
      ext i j
      change (∑ k, star (if k = i₀ then a i else 0) *
        (if k = i₀ then a j else 0)) = star (a i) * a j
      simp
    rw [← heq]
    exact star_mul_self_nonneg R

lemma weighted_algebraGram_nonneg (a : I → M) (q : M) (hq : 0 ≤ q) :
    0 ≤ CStarMatrix.ofMatrix (fun i j => star (a i) * q * a j) := by
  have hs : star (CFC.sqrt q) * CFC.sqrt q = q := by
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg q)).star_eq]
    exact CFC.sqrt_mul_sqrt_self q hq
  have heq : algebraGram (fun i => CFC.sqrt q * a i) =
      CStarMatrix.ofMatrix (fun i j => star (a i) * q * a j) := by
    ext i j
    change star (CFC.sqrt q * a i) * (CFC.sqrt q * a j) = _
    rw [star_mul]
    calc
      _ = star (a i) * (star (CFC.sqrt q) * CFC.sqrt q) * a j := by
        simp only [mul_assoc]
      _ = _ := by rw [hs]; rfl
  rw [← heq]
  exact algebraGram_nonneg (fun i : I => CFC.sqrt q * a i)

lemma algebraGram_left_le (a : I → M) (b : M) :
    algebraGram (fun i => b * a i) ≤ ‖b‖ ^ 2 • algebraGram a := by
  have hb : star b * b ≤ ‖b‖ ^ 2 • (1 : M) := by
    simpa only [star_one, one_mul, mul_one, CStarRing.norm_star_mul_self, pow_two]
      using CStarAlgebra.star_left_conjugate_le_norm_smul (a := (1 : M)) (b := star b * b)
  have hq := weighted_algebraGram_nonneg a (‖b‖ ^ 2 • (1 : M) - star b * b)
    (sub_nonneg.mpr hb)
  have heq : CStarMatrix.ofMatrix (fun i j => star (a i) * (‖b‖ ^ 2 • (1 : M) - star b * b) * a j) = ‖b‖ ^ 2 • algebraGram a - algebraGram (fun i => b * a i) := by
    ext i j
    change star (a i) * (‖b‖ ^ 2 • (1 : M) - star b * b) * a j =
      ‖b‖ ^ 2 • (star (a i) * a j) - star (b * a i) * (b * a j)
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, star_mul, mul_assoc]
  rw [heq] at hq
  exact sub_nonneg.mp hq

lemma operatorMatrix_quadratic_nonneg
    (A : CStarMatrix I I (H →L[ℂ] H)) (hA : 0 ≤ A) (ξ : I → H) :
    0 ≤ ∑ i, ∑ j, inner ℂ (ξ i) (A i j (ξ j)) := by
  have h := map_nonneg (WeakPureInfiniteness.matrixOperatorHom (n := I) (H := H)) hA
  have hi := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp h).inner_nonneg_right
    (WithLp.toLp 2 ξ)
  change 0 ≤ inner ℂ (WithLp.toLp 2 ξ)
    (WeakPureInfiniteness.matrixOperator A (WithLp.toLp 2 ξ)) at hi
  simpa only [PiLp.inner_apply, WeakPureInfiniteness.matrixOperator_apply,
    PiLp.toLp_apply, inner_sum] using hi

lemma completelyPositive_kernel_nonneg
    (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a : I → M) (ξ : I → H) :
    0 ≤ ∑ i, ∑ j, inner ℂ (ξ i) (φ (star (a i) * a j) (ξ j)) := by
  exact operatorMatrix_quadratic_nonneg _
    (φ.map_cstarMatrix_nonneg (algebraGram a) (algebraGram_nonneg a)) ξ
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {I : Type*}

def kernelForm (K : Matrix I I ℂ) (x y : I →₀ ℂ) : ℂ :=
  x.sum fun i a => y.sum fun j b => star a * K i j * b

lemma kernelForm_conj_symm (K : Matrix I I ℂ) (hK : K.IsHermitian) (x y : I →₀ ℂ) :
    star (kernelForm K y x) = kernelForm K x y := by
  classical
  simp only [kernelForm, Finsupp.sum, star_sum, star_mul, star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hK.apply i j]
  ring

lemma kernelForm_add_left (K : Matrix I I ℂ) (x y z : I →₀ ℂ) :
    kernelForm K (x + y) z = kernelForm K x z + kernelForm K y z := by
  classical
  unfold kernelForm
  apply Finsupp.sum_add_index'
  · intro i
    simp
  · intro i a b
    simp only [star_add, add_mul, Finsupp.sum, Finset.sum_add_distrib]

lemma kernelForm_smul_left (K : Matrix I I ℂ) (x y : I →₀ ℂ) (r : ℂ) :
    kernelForm K (r • x) y = star r * kernelForm K x y := by
  classical
  unfold kernelForm
  rw [Finsupp.sum_smul_index (by intro i; simp)]
  simp only [star_mul, mul_assoc, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma kernelForm_nonneg (K : Matrix I I ℂ) (hK : K.PosSemidef) (x : I →₀ ℂ) :
    0 ≤ kernelForm K x x := hK.2 x

def PositiveKernelPreSpace (K : Matrix I I ℂ) (_hK : K.PosSemidef) : Type _ := I →₀ ℂ

instance kernelPreAddCommGroup (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    AddCommGroup (PositiveKernelPreSpace K hK) := inferInstanceAs (AddCommGroup (I →₀ ℂ))

instance kernelPreModule (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    Module ℂ (PositiveKernelPreSpace K hK) := inferInstanceAs (Module ℂ (I →₀ ℂ))

abbrev positiveKernelCore (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    PreInnerProductSpace.Core ℂ (PositiveKernelPreSpace K hK) where
  inner := kernelForm K
  conj_inner_symm x y := kernelForm_conj_symm K hK.1 x y
  re_inner_nonneg x := (kernelForm_nonneg K hK x).1
  add_left := kernelForm_add_left K
  smul_left := kernelForm_smul_left K

instance kernelPreSeminormedAddCommGroup (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    SeminormedAddCommGroup (PositiveKernelPreSpace K hK) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := positiveKernelCore K hK)

instance kernelPreInnerProductSpace (K : Matrix I I ℂ) (hK : K.PosSemidef) :
    InnerProductSpace ℂ (PositiveKernelPreSpace K hK) :=
  InnerProductSpace.ofCore (positiveKernelCore K hK)

abbrev PositiveKernelHilbert (K : Matrix I I ℂ) (hK : K.PosSemidef) :=
  UniformSpace.Completion (PositiveKernelPreSpace K hK)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma completelyPositive_star (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a : M) :
    φ (star a) = star (φ a) := by
  obtain ⟨x, hx, _, rfl⟩ := CStarAlgebra.exists_sum_four_nonneg a
  have hxstar (i : Fin 4) : star (x i) = x i := (IsSelfAdjoint.of_nonneg (hx i)).star_eq
  have hystar (i : Fin 4) : star (φ (x i)) = φ (x i) :=
    (IsSelfAdjoint.of_nonneg (map_nonneg φ (hx i))).star_eq
  simp only [star_sum, star_smul, map_sum, map_smul, hxstar, hystar]

def stinespringKernel (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    Matrix (M × H) (M × H) ℂ :=
  fun p q => inner ℂ p.2 (φ (star p.1 * q.1) q.2)

lemma stinespringKernel_hermitian (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    (stinespringKernel φ).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro p q
  change star (inner ℂ q.2 (φ (star q.1 * p.1) p.2)) =
    inner ℂ p.2 (φ (star p.1 * q.1) q.2)
  rw [← starRingEnd_apply, inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_right]
  rw [← ContinuousLinearMap.star_eq_adjoint, ← completelyPositive_star]
  simp only [star_mul, star_star]

lemma kernelForm_coefficients {J : Type*}
    (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a : J → M) (ξ : J → H) (x : J →₀ ℂ) :
    kernelForm (fun i j => inner ℂ (ξ i) (φ (star (a i) * a j) (ξ j))) x x =
      ∑ i : x.support, ∑ j : x.support,
        inner ℂ (x i • ξ i) (φ (star (a i) * a j) (x j • ξ j)) := by
  classical
  unfold kernelForm
  rw [Finsupp.sum, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finsupp.sum, ← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [inner_smul_left, map_smul, inner_smul_right, starRingEnd_apply]
  ring

theorem stinespringKernel_positive (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    (stinespringKernel φ).PosSemidef := by
  classical
  refine ⟨stinespringKernel_hermitian φ, ?_⟩
  intro x
  change 0 ≤ kernelForm (fun p q : M × H =>
    inner ℂ p.2 (φ (star p.1 * q.1) q.2)) x x
  rw [kernelForm_coefficients]
  exact completelyPositive_kernel_nonneg φ
    (fun i : x.support => i.val.1) (fun i : x.support => x i • i.val.2)

abbrev StinespringSpace (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :=
  PositiveKernelHilbert (stinespringKernel φ) (stinespringKernel_positive φ)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H I : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Fintype I]

def operatorMatrixVectorFunctional (ξ : I → H) :
    CStarMatrix I I (H →L[ℂ] H) →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    { toFun A := ∑ i, ∑ j, inner ℂ (ξ i) (A i j (ξ j))
      map_add' A B := by
        simp only [CStarMatrix.add_apply, add_apply,
          inner_add_right, Finset.sum_add_distrib]
      map_smul' z A := by
        simp only [CStarMatrix.smul_apply, smul_apply,
          inner_smul_right, smul_eq_mul, Finset.mul_sum, RingHom.id_apply] }
    (fun A hA => operatorMatrix_quadratic_nonneg A hA ξ)

def cpMatrixVectorFunctional (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ : I → H) :
    CStarMatrix I I M →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    ((operatorMatrixVectorFunctional ξ).toLinearMap.comp (CStarMatrix.mapₗ φ.toLinearMap))
    (fun A hA => operatorMatrix_quadratic_nonneg _ (φ.map_cstarMatrix_nonneg A hA) ξ)

lemma completelyPositive_kernel_left_bound
    (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a : I → M) (ξ : I → H) (b : M) :
    (∑ i, ∑ j, inner ℂ (ξ i) (φ (star (b * a i) * (b * a j)) (ξ j))).re ≤
      ‖b‖ ^ 2 * (∑ i, ∑ j, inner ℂ (ξ i) (φ (star (a i) * a j) (ξ j))).re := by
  have h := (cpMatrixVectorFunctional φ ξ).monotone (algebraGram_left_le a b)
  change cpMatrixVectorFunctional φ ξ (algebraGram (fun i => b * a i)) ≤
    cpMatrixVectorFunctional φ ξ (‖b‖ ^ 2 • algebraGram a) at h
  rw [PositiveLinearMap.map_smul_of_tower] at h
  have hr := h.1
  rw [← Complex.coe_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hr
  exact hr
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def starConjugateLinear (T : A →ₗ[ℂ] B) : A →ₗ[ℂ] B where
  toFun a := star (T (star a))
  map_add' a b := by simp
  map_smul' z a := by simp

def paulsenSystem (A : Type*) [CStarAlgebra A] : Submodule ℂ (Mat A) where
  carrier := {X | ∃ z w : ℂ, X 0 0 = algebraMap ℂ A z ∧ X 1 1 = algebraMap ℂ A w}
  zero_mem' := ⟨0, 0, by simp, by simp⟩
  add_mem' := by
    rintro X Y ⟨z, w, hz, hw⟩ ⟨z', w', hz', hw'⟩
    exact ⟨z + z', w + w', by simp only [CStarMatrix.add_apply, map_add, hz, hz'],
      by simp only [CStarMatrix.add_apply, map_add, hw, hw']⟩
  smul_mem' := by
    rintro c X ⟨z, w, hz, hw⟩
    refine ⟨c * z, c * w, ?_, ?_⟩
    · simp only [CStarMatrix.smul_apply, hz, Algebra.smul_def, map_mul]
    · simp only [CStarMatrix.smul_apply, hw, Algebra.smul_def, map_mul]

lemma paulsenSystem_one : (1 : Mat A) ∈ paulsenSystem A := by
  exact ⟨1, 1, by simp, by simp⟩

lemma paulsenSystem_star (X : Mat A) (hX : X ∈ paulsenSystem A) :
    star X ∈ paulsenSystem A := by
  obtain ⟨z, w, hz, hw⟩ := hX
  refine ⟨star z, star w, ?_, ?_⟩
  · change star (X 0 0) = _
    rw [hz]
    exact (map_star (StarAlgHom.ofId ℂ A) z).symm
  · change star (X 1 1) = _
    rw [hw]
    exact (map_star (StarAlgHom.ofId ℂ A) w).symm

def paulsenLinear (f : A →ₗ[ℂ] ℂ) (T : A →ₗ[ℂ] B) : Mat A →ₗ[ℂ] Mat B where
  toFun X := CStarMatrix.ofMatrix !![
    algebraMap ℂ B (f (X 0 0)), T (X 0 1);
    starConjugateLinear T (X 1 0), algebraMap ℂ B (f (X 1 1))]
  map_add' X Y := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_smul' z X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Algebra.algebraMap_eq_smul_one, smul_smul]

def paulsenSystemMap (f : A →ₗ[ℂ] ℂ) (T : A →ₗ[ℂ] B) : paulsenSystem A →ₗ[ℂ] Mat B :=
  (paulsenLinear f T).comp (paulsenSystem A).subtype

lemma paulsenSystemMap_one (f : A →ₗ[ℂ] ℂ) (hf : f 1 = 1) (T : A →ₗ[ℂ] B) :
    paulsenSystemMap f T ⟨1, paulsenSystem_one⟩ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [paulsenSystemMap, paulsenLinear, starConjugateLinear, hf]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {A : Type*} [CStarAlgebra A]

def flipMatrixNesting (n k : ℕ) :
    CStarMatrix (Fin n) (Fin n) (CStarMatrix (Fin k) (Fin k) A) ≃⋆ₐ[ℂ]
      CStarMatrix (Fin k) (Fin k) (CStarMatrix (Fin n) (Fin n) A) where
  toFun X i j p q := X p q i j
  invFun X i j p q := X p q i j
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl
  map_mul' X Y := by
    ext i j p q
    change (∑ s : Fin n, (fun r t => ∑ l : Fin k, X p s r l * Y s q l t)) i j =
      (∑ l : Fin k, (fun r t => ∑ s : Fin n, X r s i l * Y s t l j)) p q
    simp only [Finset.sum_apply]
    exact Finset.sum_comm

@[simp] lemma flipMatrixNesting_apply (n k : ℕ)
    (X : CStarMatrix (Fin n) (Fin n) (CStarMatrix (Fin k) (Fin k) A))
    (i j : Fin k) (p q : Fin n) : flipMatrixNesting n k X i j p q = X p q i j := rfl
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma positiveBlock_zero_zero (p q x : A) : positiveBlock p q x 0 0 = p := by
  simp [positiveBlock, diag, offdiag]
lemma positiveBlock_zero_one (p q x : A) : positiveBlock p q x 0 1 = x := by
  simp [positiveBlock, diag, offdiag]
lemma positiveBlock_one_zero (p q x : A) : positiveBlock p q x 1 0 = star x := by
  simp [positiveBlock, diag, offdiag]
lemma positiveBlock_one_one (p q x : A) : positiveBlock p q x 1 1 = q := by
  simp [positiveBlock, diag, offdiag]

lemma paulsen_scalar_coefficient (f : A →ₗ[ℂ] ℂ) (hf : f 1 = 1) (z : ℂ) :
    f (algebraMap ℂ A z) = z := by
  simp [Algebra.algebraMap_eq_smul_one, hf]

lemma paulsen_diagonal_coefficient (f : A →ₗ[ℂ] ℂ) (hf : f 1 = 1)
    (X : paulsenSystem A) (i : Fin 2) :
    algebraMap ℂ A (f (X.val i i)) = X.val i i := by
  obtain ⟨z, w, hz, hw⟩ := X.property
  fin_cases i
  · exact (congrArg (fun a => algebraMap ℂ A (f a)) hz).trans
      ((congrArg (algebraMap ℂ A) (paulsen_scalar_coefficient f hf z)).trans hz.symm)
  · exact (congrArg (fun a => algebraMap ℂ A (f a)) hw).trans
      ((congrArg (algebraMap ℂ A) (paulsen_scalar_coefficient f hf w)).trans hw.symm)

variable [PartialOrder A] [StarOrderedRing A]

def paulsenMatrixDiagonal (f : A →ₗ[ℂ] ℂ) {n : ℕ} (i : Fin 2)
    (X : operatorSystemMatrices (paulsenSystem A) n) : CStarMatrix (Fin n) (Fin n) ℂ :=
  CStarMatrix.ofMatrix (fun p q => f (X.val p q i i))

def paulsenMatrixUpper {n : ℕ} (X : operatorSystemMatrices (paulsenSystem A) n) :
    CStarMatrix (Fin n) (Fin n) A := CStarMatrix.ofMatrix (fun p q => X.val p q 0 1)

lemma paulsenMatrix_lower {n : ℕ} (X : operatorSystemMatrices (paulsenSystem A) n)
    (hX : 0 ≤ X.val) (i j : Fin n) : X.val i j 1 0 = star (X.val j i 0 1) := by
  exact (congrArg (fun Y : CStarMatrix (Fin n) (Fin n) (Mat A) => Y i j 1 0)
    hX.isSelfAdjoint.star_eq).symm

lemma paulsenMatrix_source_block (f : A →ₗ[ℂ] ℂ) (hf : f 1 = 1) {n : ℕ}
    (X : operatorSystemMatrices (paulsenSystem A) n) (hX : 0 ≤ X.val) :
    flipMatrixNesting n 2 X.val = positiveBlock
      (scalarMatrixHom A n (paulsenMatrixDiagonal f 0 X))
      (scalarMatrixHom A n (paulsenMatrixDiagonal f 1 X)) (paulsenMatrixUpper X) := by
  let p := scalarMatrixHom A n (paulsenMatrixDiagonal f 0 X)
  let q := scalarMatrixHom A n (paulsenMatrixDiagonal f 1 X)
  let x := paulsenMatrixUpper X
  apply CStarMatrix.ext
  intro d e
  apply CStarMatrix.ext
  intro i j
  fin_cases d <;> fin_cases e
  · exact (paulsen_diagonal_coefficient f hf ⟨X.val i j, X.property i j⟩ 0).symm.trans
      (congrArg (fun Z : CStarMatrix (Fin n) (Fin n) A => Z i j)
        (positiveBlock_zero_zero p q x)).symm
  · exact (congrArg (fun Z : CStarMatrix (Fin n) (Fin n) A => Z i j)
      (positiveBlock_zero_one p q x)).symm
  · exact (paulsenMatrix_lower X hX i j).trans
      (congrArg (fun Z : CStarMatrix (Fin n) (Fin n) A => Z i j)
        (positiveBlock_one_zero p q x)).symm
  · exact (paulsen_diagonal_coefficient f hf ⟨X.val i j, X.property i j⟩ 1).symm.trans
      (congrArg (fun Z : CStarMatrix (Fin n) (Fin n) A => Z i j)
        (positiveBlock_one_one p q x)).symm

variable [PartialOrder B] [StarOrderedRing B]

lemma paulsenMatrix_target_block (f : A →ₗ[ℂ] ℂ) (T : A →ₗ[ℂ] B) {n : ℕ}
    (X : operatorSystemMatrices (paulsenSystem A) n) (hX : 0 ≤ X.val) :
    flipMatrixNesting n 2 (operatorSystemAmplification (paulsenSystem A)
      (paulsenSystemMap f T) n X) = positiveBlock
      (scalarMatrixHom B n (paulsenMatrixDiagonal f 0 X))
      (scalarMatrixHom B n (paulsenMatrixDiagonal f 1 X)) ((paulsenMatrixUpper X).map T) := by
  let p := scalarMatrixHom B n (paulsenMatrixDiagonal f 0 X)
  let q := scalarMatrixHom B n (paulsenMatrixDiagonal f 1 X)
  let x := (paulsenMatrixUpper X).map T
  apply CStarMatrix.ext
  intro d e
  apply CStarMatrix.ext
  intro i j
  fin_cases d <;> fin_cases e
  · exact (congrArg (fun Z : CStarMatrix (Fin n) (Fin n) B => Z i j)
      (positiveBlock_zero_zero p q x)).symm
  · exact (congrArg (fun Z : CStarMatrix (Fin n) (Fin n) B => Z i j)
      (positiveBlock_zero_one p q x)).symm
  · have hh : star (T (star (X.val i j 1 0))) = star (T (X.val j i 0 1)) := by
      have h := congrArg (fun a => star (T (star a))) (paulsenMatrix_lower X hX i j)
      simpa only [star_star] using h
    exact hh.trans (congrArg (fun Z : CStarMatrix (Fin n) (Fin n) B => Z i j)
      (positiveBlock_one_zero p q x)).symm
  · exact (congrArg (fun Z : CStarMatrix (Fin n) (Fin n) B => Z i j)
      (positiveBlock_one_one p q x)).symm
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder

namespace BoundedHochschild.KadisonRingrose

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B] [Nontrivial A]

theorem paulsenSystemMap_positive (f : A →ₗ[ℂ] ℂ) (hf : f 1 = 1) (T : A →ₗ[ℂ] B)
    (hT : ∀ n (X : CStarMatrix (Fin n) (Fin n) A), ‖X.map T‖ ≤ ‖X‖)
    (n : ℕ) (X : operatorSystemMatrices (paulsenSystem A) n) (hX : 0 ≤ X.val) :
    0 ≤ operatorSystemAmplification (paulsenSystem A) (paulsenSystemMap f T) n X := by
  have hs := map_nonneg (flipMatrixNesting (A := A) n 2) hX
  rw [paulsenMatrix_source_block f hf X hX] at hs
  have ht := scalarPositiveBlock_transfer T n (hT n)
    (paulsenMatrixDiagonal f 0 X) (paulsenMatrixDiagonal f 1 X) (paulsenMatrixUpper X) hs
  rw [← paulsenMatrix_target_block f T X hX] at ht
  have h := map_nonneg (flipMatrixNesting (A := B) n 2).symm ht
  simpa only [StarAlgEquiv.symm_apply_apply] using h
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def singleCStarMatrix {n : ℕ} (i j : Fin n) (a : A) : CStarMatrix (Fin n) (Fin n) A :=
  CStarMatrix.ofMatrix (Matrix.single i j a)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {I : Type*}

lemma kernelForm_mapDomain_left (K : Matrix I I ℂ) (f : I → I) (x y : I →₀ ℂ) :
    kernelForm K (Finsupp.mapDomain f x) y = kernelForm (fun i j => K (f i) j) x y := by
  classical
  unfold kernelForm
  rw [Finsupp.sum_mapDomain_index]
  · intro i
    simp
  · intro i a b
    simp only [star_add, add_mul, Finsupp.sum, Finset.sum_add_distrib]

lemma kernelForm_mapDomain_right (K : Matrix I I ℂ) (f : I → I) (x y : I →₀ ℂ) :
    kernelForm K x (Finsupp.mapDomain f y) = kernelForm (fun i j => K i (f j)) x y := by
  classical
  unfold kernelForm
  apply Finsupp.sum_congr
  intro i hi
  rw [Finsupp.sum_mapDomain_index]
  · intro j
    simp
  · intro j a b
    exact mul_add _ _ _

lemma kernelForm_mapDomain (K : Matrix I I ℂ) (f : I → I) (x y : I →₀ ℂ) :
    kernelForm K (Finsupp.mapDomain f x) (Finsupp.mapDomain f y) =
      kernelForm (fun i j => K (f i) (f j)) x y := by
  rw [kernelForm_mapDomain_left]
  exact kernelForm_mapDomain_right (K := (fun i j => K (f i) j)) f x y

lemma kernelPre_norm_sq (K : Matrix I I ℂ) (hK : K.PosSemidef)
    (x : PositiveKernelPreSpace K hK) : ‖x‖ ^ 2 = (kernelForm K x x).re :=
  norm_sq_eq_re_inner (𝕜 := ℂ) x

def kernelPreMap (K : Matrix I I ℂ) (hK : K.PosSemidef) (f : I → I)
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x : I →₀ ℂ, (kernelForm (fun i j => K (f i) (f j)) x x).re ≤
      C ^ 2 * (kernelForm K x x).re) :
    PositiveKernelPreSpace K hK →L[ℂ] PositiveKernelPreSpace K hK :=
  let L : PositiveKernelPreSpace K hK →ₗ[ℂ] PositiveKernelPreSpace K hK :=
    { toFun := Finsupp.mapDomain f
      map_add' _ _ := Finsupp.mapDomain_add
      map_smul' r x := Finsupp.mapDomain_smul r x }
  L.mkContinuous C (fun x => by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
    rw [mul_pow, kernelPre_norm_sq K hK, kernelPre_norm_sq K hK]
    change (kernelForm K (Finsupp.mapDomain f x) (Finsupp.mapDomain f x)).re ≤
      C ^ 2 * (kernelForm K x x).re
    exact (congrArg Complex.re (kernelForm_mapDomain K f
      (show I →₀ ℂ from x) (show I →₀ ℂ from x))).trans_le (hf x))

@[simp] lemma kernelPreMap_apply (K : Matrix I I ℂ) (hK : K.PosSemidef) (f : I → I)
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x : I →₀ ℂ, (kernelForm (fun i j => K (f i) (f j)) x x).re ≤
      C ^ 2 * (kernelForm K x x).re) (x : PositiveKernelPreSpace K hK) :
    kernelPreMap K hK f C hC hf x = Finsupp.mapDomain f x := rfl
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev StinespringPreSpace (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :=
  PositiveKernelPreSpace (stinespringKernel φ) (stinespringKernel_positive φ)

def stinespringLeftLabel (b : M) (p : M × H) : M × H := (b * p.1, p.2)

def stinespringShift (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (b : M)
    (x : StinespringPreSpace φ) : StinespringPreSpace φ :=
  Finsupp.mapDomain (stinespringLeftLabel b) x

lemma stinespringShift_one (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (x : StinespringPreSpace φ) : stinespringShift φ 1 x = x := by
  have he : stinespringLeftLabel (H := H) (1 : M) = id := by
    funext p
    simp only [stinespringLeftLabel, one_mul, id_eq]
  unfold stinespringShift
  dsimp only [StinespringPreSpace, PositiveKernelPreSpace] at x ⊢
  rw [he, Finsupp.mapDomain_id]

lemma stinespringShift_mul (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (a b : M) (x : StinespringPreSpace φ) :
    stinespringShift φ a (stinespringShift φ b x) = stinespringShift φ (a * b) x := by
  have he : stinespringLeftLabel (H := H) a ∘ stinespringLeftLabel b =
      stinespringLeftLabel (a * b) := by
    funext p
    simp only [Function.comp_apply, stinespringLeftLabel, mul_assoc]
  unfold stinespringShift
  dsimp only [StinespringPreSpace, PositiveKernelPreSpace] at x ⊢
  rw [← Finsupp.mapDomain_comp, he]

lemma stinespringLeft_bound (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (b : M)
    (x : (M × H) →₀ ℂ) :
    (kernelForm (fun p q => stinespringKernel φ (stinespringLeftLabel b p)
      (stinespringLeftLabel b q)) x x).re ≤ ‖b‖ ^ 2 * (kernelForm (stinespringKernel φ) x x).re := by
  classical
  change (kernelForm (fun p q : M × H => inner ℂ p.2
    (φ (star (b * p.1) * (b * q.1)) q.2)) x x).re ≤
      ‖b‖ ^ 2 * (kernelForm (fun p q : M × H => inner ℂ p.2
        (φ (star p.1 * q.1) q.2)) x x).re
  rw [kernelForm_coefficients, kernelForm_coefficients]
  exact completelyPositive_kernel_left_bound φ (fun p : x.support => p.val.1)
    (fun p : x.support => x p • p.val.2) b

def stinespringPreOperator (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (b : M) :
    StinespringPreSpace φ →L[ℂ] StinespringPreSpace φ :=
  kernelPreMap (stinespringKernel φ) (stinespringKernel_positive φ)
    (stinespringLeftLabel b) ‖b‖ (norm_nonneg _) (stinespringLeft_bound φ b)

def stinespringOperator (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (b : M) :
    StinespringSpace φ →L[ℂ] StinespringSpace φ :=
  (stinespringPreOperator φ b).completion

@[simp] lemma stinespringOperator_coe (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (b : M) (x : StinespringPreSpace φ) :
    stinespringOperator φ b x =
      (UniformSpace.Completion.coe' (stinespringShift φ b x)) := by
  exact ContinuousLinearMap.completion_apply_coe (stinespringPreOperator φ b) x
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace
open UniformSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma stinespringOperator_ext (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (A B : StinespringSpace φ →L[ℂ] StinespringSpace φ)
    (h : ∀ x y : StinespringPreSpace φ,
      inner ℂ (x : StinespringSpace φ) (A y) = inner ℂ (x : StinespringSpace φ) (B y)) :
    A = B := by
  apply ContinuousLinearMap.ext
  intro η
  apply ext_inner_left ℂ
  intro ξ
  induction ξ, η using Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y => exact h x y

lemma stinespringOperator_inner_coe (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (b : M) (x y : StinespringPreSpace φ) :
    inner ℂ (x : StinespringSpace φ) (stinespringOperator φ b y) =
      kernelForm (fun p q : M × H => inner ℂ p.2 (φ (star p.1 * b * q.1) q.2)) x y := by
  rw [stinespringOperator_coe, Completion.inner_coe]
  change kernelForm (stinespringKernel φ) x (Finsupp.mapDomain (stinespringLeftLabel b) y) = _
  have he := kernelForm_mapDomain_right (stinespringKernel φ) (stinespringLeftLabel b)
    (show (M × H) →₀ ℂ from x) (show (M × H) →₀ ℂ from y)
  refine he.trans ?_
  congr 1
  funext p q
  simp only [stinespringKernel, stinespringLeftLabel, mul_assoc]

lemma stinespringOperator_zero (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    stinespringOperator φ 0 = 0 := by
  apply stinespringOperator_ext φ
  intro x y
  rw [stinespringOperator_inner_coe]
  simp [kernelForm, Finsupp.sum]

lemma stinespringOperator_add (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a b : M) :
    stinespringOperator φ (a + b) = stinespringOperator φ a + stinespringOperator φ b := by
  apply stinespringOperator_ext φ
  intro x y
  simp only [add_apply, inner_add_right, stinespringOperator_inner_coe, kernelForm,
    mul_add, add_mul, map_add, Finsupp.sum, Finset.sum_add_distrib]

lemma stinespringOperator_one (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    stinespringOperator φ 1 = 1 := by
  apply stinespringOperator_ext φ
  intro x y
  rw [stinespringOperator_coe]
  rw [stinespringShift_one]
  rfl

lemma stinespringOperator_mul (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a b : M) :
    stinespringOperator φ (a * b) = stinespringOperator φ a * stinespringOperator φ b := by
  apply stinespringOperator_ext φ
  intro x y
  rw [mul_apply_eq_comp, stinespringOperator_coe, stinespringOperator_coe,
    stinespringOperator_coe, stinespringShift_mul]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace
open UniformSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma stinespringOperator_star (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (b : M) :
    stinespringOperator φ (star b) = star (stinespringOperator φ b) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro ξ η
  induction ξ, η using Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    rw [stinespringOperator_coe, stinespringOperator_coe, Completion.inner_coe, Completion.inner_coe]
    change kernelForm (stinespringKernel φ) (Finsupp.mapDomain (stinespringLeftLabel (star b)) x) y =
      kernelForm (stinespringKernel φ) x (Finsupp.mapDomain (stinespringLeftLabel b) y)
    have hl := kernelForm_mapDomain_left (stinespringKernel φ) (stinespringLeftLabel (star b))
      (show (M × H) →₀ ℂ from x) (show (M × H) →₀ ℂ from y)
    have hr := kernelForm_mapDomain_right (stinespringKernel φ) (stinespringLeftLabel b)
      (show (M × H) →₀ ℂ from x) (show (M × H) →₀ ℂ from y)
    refine hl.trans ((congrArg (fun K : Matrix (M × H) (M × H) ℂ => kernelForm K x y) ?_).trans hr.symm)
    funext p q
    simp only [stinespringKernel, stinespringLeftLabel, star_mul, star_star, mul_assoc]

lemma stinespringOperator_smul (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (z : ℂ) (b : M) :
    stinespringOperator φ (z • b) = z • stinespringOperator φ b := by
  apply stinespringOperator_ext φ
  intro x y
  rw [smul_apply, inner_smul_right, stinespringOperator_inner_coe, stinespringOperator_inner_coe]
  simp only [kernelForm, mul_smul_comm, smul_mul_assoc, map_smul,
    smul_apply, inner_smul_right, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

def stinespringRepresentation (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    M →⋆ₐ[ℂ] (StinespringSpace φ →L[ℂ] StinespringSpace φ) where
  toFun := stinespringOperator φ
  map_zero' := stinespringOperator_zero φ
  map_one' := stinespringOperator_one φ
  map_add' := stinespringOperator_add φ
  map_mul' := stinespringOperator_mul φ
  map_star' := stinespringOperator_star φ
  commutes' z := by
    rw [Algebra.algebraMap_eq_smul_one, stinespringOperator_smul, stinespringOperator_one]
    rfl
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace
open UniformSpace

namespace BoundedHochschild.KadisonRingrose

variable {M H : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def stinespringPreVector (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ : H) :
    StinespringPreSpace φ := Finsupp.single (1, ξ) 1

def stinespringVector (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ : H) :
    StinespringSpace φ := Completion.coe' (stinespringPreVector φ ξ)

lemma stinespringVector_pairing (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (x : StinespringPreSpace φ) (ξ : H) :
    inner ℂ (x : StinespringSpace φ) (stinespringVector φ ξ) =
      x.sum (fun p z => star z * inner ℂ p.2 (φ (star p.1) ξ)) := by
  classical
  rw [stinespringVector, Completion.inner_coe]
  change kernelForm (stinespringKernel φ) x (stinespringPreVector φ ξ) = _
  simp [kernelForm, stinespringKernel, stinespringPreVector]

lemma stinespringVector_add (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ η : H) :
    stinespringVector φ (ξ + η) = stinespringVector φ ξ + stinespringVector φ η := by
  apply ext_inner_left ℂ
  intro ω
  induction ω using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    simp only [inner_add_right, stinespringVector_pairing, map_add, mul_add,
      Finsupp.sum, Finset.sum_add_distrib]

lemma stinespringVector_smul (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (z : ℂ) (ξ : H) :
    stinespringVector φ (z • ξ) = z • stinespringVector φ ξ := by
  apply ext_inner_left ℂ
  intro ω
  induction ω using Completion.induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x =>
    simp only [inner_smul_right, stinespringVector_pairing, map_smul,
      Finsupp.sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring

lemma stinespringVector_norm_sq (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ : H) :
    ‖stinespringVector φ ξ‖ ^ 2 = (inner ℂ ξ (φ 1 ξ)).re := by
  classical
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change (inner ℂ ((stinespringPreVector φ ξ) : StinespringSpace φ) (stinespringVector φ ξ)).re = _
  rw [stinespringVector_pairing]
  simp [stinespringPreVector]

lemma stinespringVector_bound (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ : H) :
    ‖stinespringVector φ ξ‖ ≤ Real.sqrt ‖φ 1‖ * ‖ξ‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (norm_nonneg _), stinespringVector_norm_sq]
  calc
    _ ≤ ‖inner ℂ ξ (φ 1 ξ)‖ := Complex.re_le_norm _
    _ ≤ ‖ξ‖ * ‖φ 1 ξ‖ := norm_inner_le_norm _ _
    _ ≤ ‖ξ‖ * (‖φ 1‖ * ‖ξ‖) :=
      mul_le_mul_of_nonneg_left ((φ 1).le_opNorm ξ) (norm_nonneg _)
    _ = _ := by ring

def stinespringEmbedding (φ : CompletelyPositiveMap M (H →L[ℂ] H)) :
    H →L[ℂ] StinespringSpace φ :=
  LinearMap.mkContinuous
    { toFun := stinespringVector φ
      map_add' := stinespringVector_add φ
      map_smul' := stinespringVector_smul φ }
    (Real.sqrt ‖φ 1‖) (stinespringVector_bound φ)

@[simp] lemma stinespringEmbedding_apply (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (ξ : H) :
    stinespringEmbedding φ ξ = stinespringVector φ ξ := rfl

lemma stinespringVector_coefficient (φ : CompletelyPositiveMap M (H →L[ℂ] H))
    (a : M) (ξ η : H) :
    inner ℂ (stinespringVector φ ξ) (stinespringRepresentation φ a (stinespringVector φ η)) =
      inner ℂ ξ (φ a η) := by
  classical
  change inner ℂ ((stinespringPreVector φ ξ) : StinespringSpace φ)
    (stinespringOperator φ a (stinespringPreVector φ η)) = _
  rw [stinespringOperator_inner_coe]
  simp [kernelForm, stinespringPreVector]

theorem stinespring_factorization (φ : CompletelyPositiveMap M (H →L[ℂ] H)) (a : M) :
    φ a = (stinespringEmbedding φ).adjoint.comp
      ((stinespringRepresentation φ a).comp (stinespringEmbedding φ)) := by
  apply ContinuousLinearMap.ext
  intro η
  apply ext_inner_left ℂ
  intro ξ
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  exact (stinespringVector_coefficient φ a ξ η).symm
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma stinespringEmbedding_norm_le (φ : CompletelyPositiveMap A (H →L[ℂ] H)) :
    ‖stinespringEmbedding φ‖ ≤ Real.sqrt ‖φ 1‖ :=
  (stinespringEmbedding φ).opNorm_le_bound (Real.sqrt_nonneg _)
    (stinespringVector_bound φ)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev HilbertDouble (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  PiLp 2 (fun _ : Fin 2 => H)

abbrev doubleMatrixHom : Mat (H →L[ℂ] H) →⋆ₙₐ[ℂ]
    (HilbertDouble H →L[ℂ] HilbertDouble H) :=
  WeakPureInfiniteness.matrixOperatorHom (n := Fin 2) (H := H)

lemma matrixDouble_one :
    doubleMatrixHom (H := H) (1 : Mat (H →L[ℂ] H)) = 1 := by
  ext ξ i
  change (∑ j : Fin 2, (1 : Mat (H →L[ℂ] H)) i j (ξ j)) = ξ i
  fin_cases i <;> simp [CStarMatrix.one_apply, apply_ite]

def paulsenOperatorMap (f : A →ₗ[ℂ] ℂ) (T : A →ₗ[ℂ] (H →L[ℂ] H)) :
    paulsenSystem A →ₗ[ℂ] (HilbertDouble H →L[ℂ] HilbertDouble H) :=
  (doubleMatrixHom (H := H) : Mat (H →L[ℂ] H) →ₗ[ℂ]
    (HilbertDouble H →L[ℂ] HilbertDouble H)).comp (paulsenSystemMap f T)

omit [PartialOrder A] [StarOrderedRing A] in
lemma paulsenOperatorMap_one (f : A →ₗ[ℂ] ℂ) (hf : f 1 = 1)
    (T : A →ₗ[ℂ] (H →L[ℂ] H)) :
    paulsenOperatorMap f T ⟨1, paulsenSystem_one⟩ = 1 := by
  change doubleMatrixHom (H := H)
    (paulsenSystemMap f T ⟨1, paulsenSystem_one⟩) = 1
  rw [paulsenSystemMap_one f hf, matrixDouble_one]

variable [Nontrivial A]

lemma paulsenOperatorMap_positive (f : A →ₗ[ℂ] ℂ) (hf : f 1 = 1)
    (T : A →ₗ[ℂ] (H →L[ℂ] H))
    (hT : ∀ n (X : CStarMatrix (Fin n) (Fin n) A), ‖X.map T‖ ≤ ‖X‖)
    (n : ℕ) (X : operatorSystemMatrices (paulsenSystem A) n) (hX : 0 ≤ X.val) :
    0 ≤ operatorSystemAmplification (paulsenSystem A) (paulsenOperatorMap f T) n X := by
  have h := paulsenSystemMap_positive f hf T hT n X hX
  exact map_nonneg (CStarMatrix.mapₙₐ (doubleMatrixHom (H := H))) h

theorem exists_paulsen_extension [Nontrivial H] (f : A →ₗ[ℂ] ℂ) (hf : f 1 = 1)
    (T : A →ₗ[ℂ] (H →L[ℂ] H))
    (hT : ∀ n (X : CStarMatrix (Fin n) (Fin n) A), ‖X.map T‖ ≤ ‖X‖) :
    ∃ Φ : CompletelyPositiveMap (Mat A) (HilbertDouble H →L[ℂ] HilbertDouble H),
      Φ 1 = 1 ∧ ∀ X : paulsenSystem A, Φ (X : Mat A) = paulsenOperatorMap f T X := by
  obtain ⟨Φ, hΦ, _, hrest⟩ := exists_unital_completelyPositive_extension (paulsenSystem A)
    paulsenSystem_one paulsenSystem_star (paulsenOperatorMap f T)
    (paulsenOperatorMap_one f hf T) (paulsenOperatorMap_positive f hf T hT)
  exact ⟨Φ, hΦ, hrest⟩
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def doubleCoordinate (i : Fin 2) : H →ₗᵢ[ℂ] HilbertDouble H where
  toFun ξ := PiLp.single 2 i ξ
  map_add' ξ η := PiLp.single_add 2 i
  map_smul' z ξ := by
    apply PiLp.ext
    intro j
    simp [PiLp.single_apply]
  norm_map' ξ := by simp

omit [CompleteSpace H] in
lemma doubleCoordinate_inner (i : Fin 2) (ξ : H) (η : HilbertDouble H) :
    inner ℂ (doubleCoordinate i ξ) η = inner ℂ ξ (η i) := by
  fin_cases i
  all_goals
    simp [doubleCoordinate, PiLp.inner_apply, PiLp.single_apply]

@[simp] lemma doubleCoordinate_adjoint (i : Fin 2) (η : HilbertDouble H) :
    (doubleCoordinate i).toContinuousLinearMap.adjoint η = η i := by
  apply ext_inner_left ℂ
  intro ξ
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact doubleCoordinate_inner i ξ η

lemma doubleCoordinate_extract (i j : Fin 2) (Q : Mat (H →L[ℂ] H)) :
    (doubleCoordinate i).toContinuousLinearMap.adjoint.comp
      ((doubleMatrixHom (H := H) Q).comp
        (doubleCoordinate j).toContinuousLinearMap) = Q i j := by
  apply ContinuousLinearMap.ext
  intro ξ
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    doubleCoordinate_adjoint]
  exact WeakPureInfiniteness.matrixOperator_single Q i j ξ
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in
lemma paulsen_single_mem (a : A) :
    singleCStarMatrix (0 : Fin 2) 1 a ∈ paulsenSystem A := by
  refine ⟨0, 0, ?_, ?_⟩ <;> simp [singleCStarMatrix, Matrix.single]

omit [PartialOrder A] [StarOrderedRing A] in
lemma paulsenLinear_single (f : A →ₗ[ℂ] ℂ) (T : A →ₗ[ℂ] (H →L[ℂ] H)) (a : A) :
    paulsenLinear f T (singleCStarMatrix (0 : Fin 2) 1 a) =
      singleCStarMatrix (0 : Fin 2) 1 (T a) := by
  apply CStarMatrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [paulsenLinear, singleCStarMatrix, Matrix.single, starConjugateLinear]

lemma paulsenExtension_entry (f : A →ₗ[ℂ] ℂ) (T : A →ₗ[ℂ] (H →L[ℂ] H))
    (Φ : CompletelyPositiveMap (Mat A) (HilbertDouble H →L[ℂ] HilbertDouble H))
    (hΦ : ∀ X : paulsenSystem A, Φ (X : Mat A) = paulsenOperatorMap f T X) (a : A) :
    (doubleCoordinate (H := H) 0).toContinuousLinearMap.adjoint.comp
      ((Φ (singleCStarMatrix (0 : Fin 2) 1 a)).comp
        (doubleCoordinate 1).toContinuousLinearMap) = T a := by
  have he := hΦ ⟨singleCStarMatrix (0 : Fin 2) 1 a, paulsen_single_mem a⟩
  change Φ (singleCStarMatrix (0 : Fin 2) 1 a) =
    doubleMatrixHom (H := H) (paulsenLinear f T (singleCStarMatrix 0 1 a)) at he
  rw [he, paulsenLinear_single]
  rw [doubleCoordinate_extract]
  exact Matrix.single_apply_same _ _ _

omit [PartialOrder A] [StarOrderedRing A] in
lemma single_offDiagonal_factor (a : A) : singleCStarMatrix (0 : Fin 2) 1 a =
    matrixScalarHom 2 a * singleCStarMatrix (0 : Fin 2) 1 (1 : A) := by
  apply CStarMatrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [singleCStarMatrix, Matrix.single, CStarMatrix.mul_apply]

lemma single_offDiagonal_norm_le_one [Nontrivial A] :
    ‖singleCStarMatrix (0 : Fin 2) 1 (1 : A)‖ ≤ 1 := by
  let E := singleCStarMatrix (0 : Fin 2) 1 (1 : A)
  have he : star E * E = diag (0 : A) 1 := by
    apply CStarMatrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [E, singleCStarMatrix, Matrix.single, diag, CStarMatrix.mul_apply,
        CStarMatrix.star_apply]
  have hn : ‖E‖ ^ 2 ≤ 1 := by
    rw [pow_two, ← CStarRing.norm_star_mul_self, he]
    simpa using norm_diag_le (0 : A) 1
  exact (sq_le_one_iff₀ (norm_nonneg E)).mp hn
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

open HochschildMatrixDilation

universe u v
variable {A : Type u} {H : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [instance] OperatorFactorization.normed OperatorFactorization.innerSpace
  OperatorFactorization.complete

variable [Nontrivial A] [Nontrivial H]

theorem factorization_of_complete_contraction (T : A →ₗ[ℂ] (H →L[ℂ] H))
    (hT : ∀ n (X : CStarMatrix (Fin n) (Fin n) A), ‖X.map T‖ ≤ ‖X‖) :
    Nonempty (OperatorFactorization T 1) := by
  obtain ⟨f, hf, _⟩ := NaimarkZFC.exists_norming_state (1 : A)
  have hf1 : f 1 = 1 := ((NaimarkZFC.isState_iff f).mp hf).1
  obtain ⟨Φ, hΦ1, hΦ⟩ := exists_paulsen_extension f.toLinearMap hf1 T hT
  let V := stinespringEmbedding Φ
  let π := (stinespringRepresentation Φ).comp (matrixScalarHom 2)
  let J₀ := (doubleCoordinate (H := H) 0).toContinuousLinearMap
  let J₁ := (doubleCoordinate (H := H) 1).toContinuousLinearMap
  let E := singleCStarMatrix (0 : Fin 2) 1 (1 : A)
  let L := V.comp J₀
  let R := (stinespringRepresentation Φ E).comp (V.comp J₁)
  have hV : ‖V‖ ≤ 1 := by
    simpa only [V, hΦ1, CStarRing.norm_one, Real.sqrt_one] using stinespringEmbedding_norm_le Φ
  have hJ (i : Fin 2) : ‖(doubleCoordinate (H := H) i).toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro ξ
    simp
  have hL : ‖L‖ ≤ 1 := by
    exact (ContinuousLinearMap.opNorm_comp_le V J₀).trans
      (by simpa only [one_mul] using mul_le_mul hV (hJ 0) (norm_nonneg J₀) zero_le_one)
  have hR : ‖R‖ ≤ 1 := by
    have hE : ‖stinespringRepresentation Φ E‖ ≤ 1 :=
      (NonUnitalStarAlgHom.norm_apply_le _ _).trans single_offDiagonal_norm_le_one
    have hVJ : ‖V.comp J₁‖ ≤ 1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa only [one_mul] using mul_le_mul hV (hJ 1) (norm_nonneg J₁) zero_le_one)
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by simpa only [one_mul] using mul_le_mul hE hVJ (norm_nonneg (V.comp J₁)) zero_le_one)
  refine ⟨{
    K := StinespringSpace Φ
    representation := π
    leftMap := L
    rightMap := R
    bound := ?_
    factorization := ?_ }⟩
  · simpa only [one_mul] using mul_le_mul hL hR (norm_nonneg R) zero_le_one
  · intro a
    rw [← paulsenExtension_entry f.toLinearMap T Φ hΦ a, stinespring_factorization,
      single_offDiagonal_factor a, map_mul]
    dsimp only [L, R, π, V, E, StarAlgHom.comp_apply]
    rw [ContinuousLinearMap.adjoint_comp]
    rfl

theorem factorization_of_complete_bound (T : A →ₗ[ℂ] (H →L[ℂ] H))
    {C : ℝ} (hC : 0 < C)
    (hT : ∀ n (X : CStarMatrix (Fin n) (Fin n) A), ‖X.map T‖ ≤ C * ‖X‖) :
    Nonempty (OperatorFactorization T C) := by
  let U : A →ₗ[ℂ] (H →L[ℂ] H) := (C : ℂ)⁻¹ • T
  have hU : ∀ n (X : CStarMatrix (Fin n) (Fin n) A), ‖X.map U‖ ≤ ‖X‖ := by
    intro n X
    have he : X.map U = (C : ℂ)⁻¹ • X.map T := by
      apply CStarMatrix.ext
      intro i j
      rfl
    rw [he, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
    calc
      C⁻¹ * ‖X.map T‖ ≤ C⁻¹ * (C * ‖X‖) :=
        mul_le_mul_of_nonneg_left (hT n X) (inv_nonneg.mpr hC.le)
      _ = ‖X‖ := by rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]
  obtain ⟨F⟩ := factorization_of_complete_contraction U hU
  refine ⟨{
    K := F.K
    representation := F.representation
    leftMap := F.leftMap
    rightMap := (C : ℂ) • F.rightMap
    bound := ?_
    factorization := ?_ }⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC]
    calc
      ‖F.leftMap‖ * (C * ‖F.rightMap‖) = C * (‖F.leftMap‖ * ‖F.rightMap‖) := by ring
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left F.bound hC.le
      _ = C := mul_one C
  · intro a
    calc
      T a = (C : ℂ) • U a := by simp [U, hC.ne']
      _ = F.leftMap.adjoint.comp
          ((F.representation a).comp ((C : ℂ) • F.rightMap)) := by
        rw [F.factorization]
        simp only [ContinuousLinearMap.comp_smul]
end BoundedHochschild.KadisonRingrose
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

variable {I H K : Type*} [Fintype I]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem represented_factorization [Nontrivial M] [Nontrivial H]
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : M →L[ℂ] M)
    {C : ℝ} (hC : 0 < C) (hT : CompletelyBoundedEstimate T C) :
    Nonempty (OperatorFactorization (σ.toLinearMap.comp T.toLinearMap) C) := by
  apply factorization_of_complete_bound _ hC
  intro n A
  have he : A.map (σ.toLinearMap.comp T.toLinearMap) = (A.map T).map σ := by
    apply CStarMatrix.ext
    intro i j
    rfl
  rw [he]
  exact (NonUnitalStarAlgHom.norm_apply_le
    (CStarMatrix.mapₙₐ (n := Fin n) σ.toNonUnitalStarAlgHom) (A.map T)).trans (hT.2 n A)
end BoundedHochschild.KadisonRingrose
end
end OAI
end

theorem solution.{u,u_2} : type_of% @OAI.BoundedHochschild.KadisonRingrose.represented_factorization.{u,u_2} := @OAI.BoundedHochschild.KadisonRingrose.represented_factorization.{u,u_2}
