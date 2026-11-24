-- Prove2me | solution 1 for GlobalTheory.NabCol.pderiv_prod_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:01:57.047944+00:00
-- url     : https://prove2.me/submissions/9c3b9da2-c7af-4a6e-bdce-18285429ad4e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
import Theorems.Thm_GlobalTheory_NabCol_pderiv_inCol

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
theorem _root_.solution (b : Fin n) (j : Fin d) (g : Fin n → PS k 1 d) (s : Finset (Fin n)) (hs : b ∉ s) :
    pderiv k (b, j) (∏ c ∈ s, inCol c (g c)) = 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert c s hc ih =>
    rw [Finset.mem_insert, not_or] at hs
    rw [Finset.prod_insert hc, Derivation.leibniz, ih hs.2, pderiv_inCol, if_neg (Ne.symm hs.1)]
    simp
end GlobalTheory.NabCol
