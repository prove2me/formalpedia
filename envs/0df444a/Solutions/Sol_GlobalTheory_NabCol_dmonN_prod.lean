-- Prove2me | solution 1 for GlobalTheory.NabCol.dmonN_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:16:15.605918+00:00
-- url     : https://prove2.me/submissions/f62c32aa-febb-497e-8b0d-dfc433bfdb68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
import Theorems.Thm_GlobalTheory_NabCol_iter_prod
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
variable {k : Type} [CommRing k] {d n : ℕ}
namespace GlobalTheory.NabCol
theorem _root_.solution (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k) (m : ι →₀ ℕ)
    (g : Fin n → PS k 1 d) :
    DmonN F cp u m (∏ b, inCol b (g b)) =
      ∏ b, inCol b (fo (fun l => colD F (cp l) (u l) b) Finset.univ.toList m (g b)) := by
  unfold DmonN fo
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons l L ih => simp only [List.foldr_cons, ih, iter_prod]
end GlobalTheory.NabCol
