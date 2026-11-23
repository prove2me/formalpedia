-- Prove2me | solution 1 for GlobalTheory.SemicharIndep.B_sub_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:42.849798+00:00
-- url     : https://prove2.me/submissions/229125b0-7671-4384-9e6e-d4cf8b119b45

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TorusAtEpsIndep
import Theorems.Thm_GlobalTheory_SemicharIndep_cc_sub
import Theorems.Thm_GlobalTheory_SemicharIndep_herm_smul_right

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
theorem _root_.solution (X : Data E r) (a b : E) (u v : Fin r → E) :
    B X u ((a - b) • v) = B X u (a • v) - B X u (b • v) := by
  unfold B
  rw [herm_smul_right, herm_smul_right, herm_smul_right, cc_sub, sub_mul, mul_sub, map_sub]
end GlobalTheory.SemicharIndep
