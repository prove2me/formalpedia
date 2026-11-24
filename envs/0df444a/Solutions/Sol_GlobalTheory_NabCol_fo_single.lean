-- Prove2me | solution 1 for GlobalTheory.NabCol.fo_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:03:00.007968+00:00
-- url     : https://prove2.me/submissions/bbbc9ca9-d703-45d3-a50c-31eeeb597dfd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
import Theorems.Thm_GlobalTheory_NabCol_fo_of_zero
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
theorem _root_.solution (D : ι → β → β) (L : List ι) (hL : L.Nodup) (a : ι) (ha : a ∈ L) (r : ℕ) (x : β) :
    fo D L (Finsupp.single a r) x = (D a)^[r] x := by
  induction L with
  | nil => simp at ha
  | cons b L ih =>
    rw [List.nodup_cons] at hL
    show (D b)^[Finsupp.single a r b] (fo D L (Finsupp.single a r) x) = _
    by_cases hab : a = b
    · subst hab
      rw [Finsupp.single_eq_same, fo_of_zero]
      intro c hc
      exact Finsupp.single_eq_of_ne (fun h => hL.1 (h ▸ hc))
    · rw [Finsupp.single_eq_of_ne (Ne.symm hab), ih hL.2 (by simpa [hab] using ha)]
      rfl
end GlobalTheory.NabCol
