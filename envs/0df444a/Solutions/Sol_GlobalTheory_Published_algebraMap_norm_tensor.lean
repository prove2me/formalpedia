-- Prove2me | solution 1 for GlobalTheory.Published.algebraMap_norm_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:33:59.680879+00:00
-- url     : https://prove2.me/submissions/3a6a20bf-1958-4161-a789-00ef9bc90a05

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Theorems.Thm_GlobalTheory_Published_algebraMap_norm_of_basis_one_sqrt
import Theorems.Thm_GlobalTheory_Published_exists_cc_eq_neg
import Theorems.Thm_GlobalTheory_Published_exists_basis_one_imaginary
import Theorems.Thm_GlobalTheory_Published_exists_sq_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.Published
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable (A : Type*) [CommRing A] [Algebra (maximalRealSubfield E) A]
namespace GlobalTheory.Published
theorem _root_.solution (z : A ⊗[maximalRealSubfield E] E) :
    algebraMap A (A ⊗[maximalRealSubfield E] E) (Algebra.norm A z) =
      z * Algebra.TensorProduct.map (AlgHom.id A A) (IsCMField.complexConj E).toAlgHom z := by
  obtain ⟨θ, h0, hθ⟩ := exists_cc_eq_neg E
  obtain ⟨b, hb0, hb1⟩ := exists_basis_one_imaginary h0 hθ
  obtain ⟨d, hd⟩ := exists_sq_real hθ
  refine algebraMap_norm_of_basis_one_sqrt (Algebra.TensorProduct.basis A b)
    (by rw [Algebra.TensorProduct.basis_apply, hb0]; rfl) (algebraMap _ A d) ?_ _ ?_ z
  · rw [Algebra.TensorProduct.basis_apply, hb1, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hd,
      ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.algebraMap_apply' d).symm
  · rw [Algebra.TensorProduct.basis_apply, hb1, Algebra.TensorProduct.map_tmul,
      ← TensorProduct.tmul_neg, ← hθ]
    rfl
end GlobalTheory.Published
