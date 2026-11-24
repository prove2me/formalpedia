-- Prove2me | solution 1 for GlobalTheory.Published.coe_norm_eq_mul_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:40:00.365289+00:00
-- url     : https://prove2.me/submissions/c10bf547-df59-45ef-a01c-bda8cb95bd99

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
namespace GlobalTheory.Published
theorem _root_.solution (x : E) :
    ((Algebra.norm (maximalRealSubfield E) x : maximalRealSubfield E) : E) = x * cc x := by
  obtain ⟨θ, h0, hθ⟩ := exists_cc_eq_neg E
  obtain ⟨b, hb0, hb1⟩ := exists_basis_one_imaginary h0 hθ
  obtain ⟨d, hd⟩ := exists_sq_real hθ
  exact algebraMap_norm_of_basis_one_sqrt b hb0 d (by rw [hb1]; exact hd.symm)
    (IsCMField.complexConj E).toAlgHom (by rw [hb1]; exact hθ) x
end GlobalTheory.Published
