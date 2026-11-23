-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.mem_normGroup_iff_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:04:37.044656+00:00
-- url     : https://prove2.me/submissions/92b08a9a-5ddd-47f6-b1eb-c00a0bbf7d1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Theorems.Thm_GlobalTheory_QuadSymbol_mem_normGroup_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
namespace GlobalTheory.QuadSymbol
section Local
variable (K L : Type) [Field K] [Field L] [Algebra K L]
variable {K L}
open NumberField IsDedekindDomain in
open scoped TensorProduct in
variable (K L : Type) [Field K] [Field L] [Algebra K L] in
variable {K L} in
private theorem norm_smul_add_smul_basis_eq_sq_sub_mul_sq {A S : Type} [CommRing A] [CommRing S]
    [Algebra A S] (f : Module.Basis (Fin 2) A S) (h0 : f 0 = 1) {c : A}
    (h1 : f 1 * f 1 = algebraMap A S c) (a b : A) :
    Algebra.norm A (a • f 0 + b • f 1) = a ^ 2 - c * b ^ 2 := by
  have hm0 : (a • f 0 + b • f 1) * f 0 = a • f 0 + b • f 1 := by rw [h0, mul_one]
  have hm1 : (a • f 0 + b • f 1) * f 1 = (b * c) • f 0 + a • f 1 := by
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, h1, h0, one_mul, Algebra.algebraMap_eq_smul_one,
      smul_smul, add_comm]
  rw [Algebra.norm_eq_matrix_det f, Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, hm0, hm1, map_add, map_smul,
    Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply]
  simp
  ring
end Local
section Global
variable (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
end Global
end GlobalTheory.QuadSymbol
namespace GlobalTheory.Published
open GlobalTheory.QuadSymbol
end GlobalTheory.Published
end
end

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open GlobalTheory GlobalTheory.QuadSymbol
variable (K L : Type) [Field K] [Field L] [Algebra K L]
variable {K L}
open NumberField IsDedekindDomain
open scoped TensorProduct
variable (K L : Type) [Field K] [Field L] [Algebra K L]
variable {K L}
namespace GlobalTheory.QuadSymbol
namespace _root_.GlobalTheory.QuadSymbol
theorem _root_.solution (e : Module.Basis (Fin 2) K L)
    (h0 : e 0 = 1) {δ : K} (h1 : e 1 * e 1 = algebraMap K L δ) {A : Type} [CommRing A]
    [Algebra K A] {x : Aˣ} :
    x ∈ _root_.GlobalTheory.QuadSymbol.normGroup K L A ↔
      ∃ a b : A, (x : A) = a ^ 2 - algebraMap K A δ * b ^ 2 := by
  haveI : FiniteDimensional K L := Module.Finite.of_basis e
  set f := Algebra.TensorProduct.basis A e
  have hf0 : f 0 = 1 := by
    rw [Algebra.TensorProduct.basis_apply, h0]
    rfl
  have hf1 : f 1 * f 1 = algebraMap A (A ⊗[K] L) (algebraMap K A δ) := by
    simp only [f, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      h1, Algebra.TensorProduct.algebraMap_apply]
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
    congr 1
    simp [Algebra.smul_def]
  rw [_root_.GlobalTheory.QuadSymbol.mem_normGroup_iff]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨f.repr z 0, f.repr z 1, ?_⟩
    have hz' : z = f.repr z 0 • f 0 + f.repr z 1 • f 1 := by
      conv_lhs => rw [← f.sum_repr z]
      rw [Fin.sum_univ_two]
    have hn := norm_smul_add_smul_basis_eq_sq_sub_mul_sq f hf0 hf1 (f.repr z 0) (f.repr z 1)
    rw [← hz', hz] at hn
    exact hn
  · rintro ⟨a, b, h⟩
    exact ⟨a • f 0 + b • f 1, by rw [norm_smul_add_smul_basis_eq_sq_sub_mul_sq f hf0 hf1, h]⟩
end _root_.GlobalTheory.QuadSymbol
end GlobalTheory.QuadSymbol
