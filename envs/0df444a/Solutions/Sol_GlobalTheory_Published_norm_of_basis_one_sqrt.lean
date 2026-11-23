-- Prove2me | solution 1 for GlobalTheory.Published.norm_of_basis_one_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:20.22138+00:00
-- url     : https://prove2.me/submissions/eefb1c26-6cfb-48f2-9dc5-2567a29fef38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e

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
variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
namespace GlobalTheory.Published
theorem _root_.solution (b : Module.Basis (Fin 2) A S) (h0 : b 0 = 1) (d : A)
    (h1 : b 1 * b 1 = algebraMap A S d) (x y : A) :
    Algebra.norm A (x • b 0 + y • b 1) = x ^ 2 - d * y ^ 2 := by
  have e0 : (x • b 0 + y • b 1) * b 0 = x • b 0 + y • b 1 := by rw [h0, mul_one]
  have e1 : (x • b 0 + y • b 1) * b 1 = (y * d) • b 0 + x • b 1 := by
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, h1, h0, one_mul, Algebra.algebraMap_eq_smul_one,
      smul_smul, add_comm]
  rw [Algebra.norm_eq_matrix_det b, Matrix.det_fin_two]
  simp only [Algebra.leftMulMatrix_eq_repr_mul, e0, e1, map_add, map_smul, Module.Basis.repr_self,
    Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply]
  simp
  ring
end GlobalTheory.Published
