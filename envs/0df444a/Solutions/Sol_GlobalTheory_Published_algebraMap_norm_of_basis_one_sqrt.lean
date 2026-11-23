-- Prove2me | solution 1 for GlobalTheory.Published.algebraMap_norm_of_basis_one_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:25.484379+00:00
-- url     : https://prove2.me/submissions/cc975306-0b87-4305-8d6e-b19115a68613

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Theorems.Thm_GlobalTheory_Published_norm_of_basis_one_sqrt

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
    (h1 : b 1 * b 1 = algebraMap A S d) (σ : S →ₐ[A] S) (hσ : σ (b 1) = -b 1) (z : S) :
    algebraMap A S (Algebra.norm A z) = z * σ z := by
  have hz : z = b.repr z 0 • b 0 + b.repr z 1 • b 1 := by
    conv_lhs => rw [← b.sum_repr z, Fin.sum_univ_two]
  generalize b.repr z 0 = x, b.repr z 1 = y at hz
  subst hz
  rw [norm_of_basis_one_sqrt b h0 d h1, map_add, map_smul, map_smul, hσ, h0, map_one σ]
  simp only [Algebra.smul_def, map_sub, map_mul, map_pow, ← h1]
  ring
end GlobalTheory.Published
