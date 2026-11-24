-- Prove2me | solution 1 for GlobalTheory.SemicharIndep.B_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:57:14.09538+00:00
-- url     : https://prove2.me/submissions/c6786bfc-e02b-4304-9a1c-2ac75cdcb0bb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TorusAtEpsIndep
import Theorems.Thm_GlobalTheory_SemicharIndep_cc_cc
import Theorems.Thm_GlobalTheory_SemicharIndep_herm_smul_left
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
theorem _root_.solution (X : Data E r) (a : E) (u v : Fin r → E) : B X (a • u) v = B X u (cc a • v) := by
  unfold B
  rw [herm_smul_left, herm_smul_right, cc_cc]
end GlobalTheory.SemicharIndep
