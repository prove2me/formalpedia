-- Prove2me | solution 1 for GlobalTheory.Published.norm_tmul_add_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:37.050264+00:00
-- url     : https://prove2.me/submissions/1f92452e-7b47-4d26-93c7-8b61d73a4e98

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Theorems.Thm_GlobalTheory_Published_norm_of_basis_one_sqrt
import Theorems.Thm_GlobalTheory_Published_exists_basis_one_imaginary

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
theorem _root_.solution {θ : E} (h0 : θ ≠ 0) (hθ : cc θ = -θ) {d : maximalRealSubfield E}
    (hd : (d : E) = θ * θ) (x y : A) :
    Algebra.norm A (x ⊗ₜ[maximalRealSubfield E] (1 : E) + y ⊗ₜ[maximalRealSubfield E] θ) =
      x ^ 2 - algebraMap (maximalRealSubfield E) A d * y ^ 2 := by
  obtain ⟨b, hb0, hb1⟩ := exists_basis_one_imaginary h0 hθ
  have := norm_of_basis_one_sqrt (Algebra.TensorProduct.basis A b)
    (by rw [Algebra.TensorProduct.basis_apply, hb0]; rfl) (algebraMap _ A d)
    (by
      rw [Algebra.TensorProduct.basis_apply, hb1, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hd,
        ← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.algebraMap_apply' d).symm) x y
  rwa [Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply, hb0, hb1,
    TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one,
    mul_one] at this
end GlobalTheory.Published
