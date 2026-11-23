-- Prove2me | solution 1 for GlobalTheory.SemicharIndep.herm_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:41.461186+00:00
-- url     : https://prove2.me/submissions/d10f3b01-41d5-44ed-af9c-4c0c2f5ab1c2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TorusAtEpsIndep
import Theorems.Thm_GlobalTheory_SemicharIndep_cc_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.SemicharIndep
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.SemicharIndep
theorem _root_.solution (G : Matrix (Fin r) (Fin r) E) (a : E) (u v : Fin r → E) :
    herm G u (a • v) = cc a * herm G u v := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, cc_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end GlobalTheory.SemicharIndep
