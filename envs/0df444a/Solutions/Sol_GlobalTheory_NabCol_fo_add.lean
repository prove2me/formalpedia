-- Prove2me | solution 1 for GlobalTheory.NabCol.fo_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:17:26.540391+00:00
-- url     : https://prove2.me/submissions/895b05fa-6484-43cf-bbce-ebbbfb1911c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
import Theorems.Thm_GlobalTheory_NabCol_fo_comm
import Theorems.Thm_GlobalTheory_FormalLog_CZ_cons
import Theorems.Thm_GlobalTheory_FormalLog_CZ_nil


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
variable {ι β : Type}
namespace GlobalTheory.NabCol
theorem _root_.solution (D : ι → β → β) (hD : ∀ a b, Function.Commute (D a) (D b)) (L : List ι) (m m' : ι →₀ ℕ) (x : β) :
    fo D L (m + m') x = fo D L m (fo D L m' x) := by
  induction L generalizing x with
  | nil => rfl
  | cons a L ih =>
    show (D a)^[(m + m') a] (fo D L (m + m') x) = (D a)^[m a] (fo D L m ((D a)^[m' a] (fo D L m' x)))
    rw [ih, ← fo_comm D L m ((D a)^[m' a]) (fun b => (hD a b).iterate_left _), Finsupp.add_apply,
      Function.iterate_add_apply]
end GlobalTheory.NabCol
