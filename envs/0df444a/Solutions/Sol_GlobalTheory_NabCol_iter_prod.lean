-- Prove2me | solution 1 for GlobalTheory.NabCol.iter_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:02:21.04819+00:00
-- url     : https://prove2.me/submissions/f25ee7a1-8a7d-4639-b201-cc3e4c7004c0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
import Theorems.Thm_GlobalTheory_NabCol_dofN_prod
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.PowGerm
open GlobalTheory GlobalTheory.NabCol
variable {k : Type} [CommRing k] {d n : ℕ}
namespace GlobalTheory.NabCol
theorem _root_.solution (F : Fin d → PS k 2 d) (c : Fin n) (u : Fin d → k) (r : ℕ) (g : Fin n → PS k 1 d) :
    (DofN F c u)^[r] (∏ b, inCol b (g b)) = ∏ b, inCol b ((colD F c u b)^[r] (g b)) := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [Function.iterate_succ_apply', ih, dofN_prod]
end GlobalTheory.NabCol
