-- Prove2me | solution 1 for GlobalTheory.SemicharIndep.B_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:57:14.901954+00:00
-- url     : https://prove2.me/submissions/bf3672c4-5b65-45a3-82bc-3e60a1590909

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TorusAtEpsIndep
import Theorems.Thm_GlobalTheory_SemicharIndep_cc_mul
import Theorems.Thm_GlobalTheory_SemicharIndep_trace_conj
import Theorems.Thm_GlobalTheory_SemicharIndep_cc_herm

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
theorem _root_.solution (X : Data E r) (u v : Fin r → E) : B X u v = -B X v u := by
  unfold B
  rw [← trace_conj, ← map_neg, cc_mul, cc_herm X.Gm_herm, X.ξ0_im, neg_mul]
end GlobalTheory.SemicharIndep
