-- Prove2me | solution 1 for GlobalTheory.TorsionCoset.natCast_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:04:39.180919+00:00
-- url     : https://prove2.me/submissions/30c8366a-2a3b-4d48-a2b5-68350f453877

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TBNFinal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNeZeroPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsNeZeroOnCoset
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.TorsionCoset
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.TorsionCoset
theorem _root_.solution (X : PT E) {x : Vsp X.dim} (hx : x ∈ X.L) (k : ℕ) :
    (k : ℂ) • x ∈ X.L := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hx k
end GlobalTheory.TorsionCoset
