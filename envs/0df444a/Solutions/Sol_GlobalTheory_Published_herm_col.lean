-- Prove2me | solution 1 for GlobalTheory.Published.herm_col
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:09.609343+00:00
-- url     : https://prove2.me/submissions/6f59a9a6-42ff-45f4-b8c0-9359d5ddfe9f

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.Published
theorem _root_.solution (G P : Matrix (Fin r) (Fin r) E) (a b : Fin r) :
    herm G (fun k => P k a) (fun k => P k b) = (Pᵀ * G * P.map cc) a b := by
  simp only [herm, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm
end GlobalTheory.Published
