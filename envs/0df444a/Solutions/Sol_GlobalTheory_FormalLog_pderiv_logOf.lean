-- Prove2me | solution 1 for GlobalTheory.FormalLog.pderiv_logOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:30:52.987797+00:00
-- url     : https://prove2.me/submissions/846c1c3d-4f95-4d9f-bf62-e88cbb481284

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalFamilyConstantCoeffZeroZeroSecondVar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ConstantCoeffPrim
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PderivSecondEvFirstPointEqZero
import Theorems.Thm_GlobalTheory_FormalLog_om_closed
import Theorems.Thm_GlobalTheory_FormalLog_pderiv_prim


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalLog
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)
variable [Algebra ℚ k]
namespace GlobalTheory.FormalLog
theorem _root_.solution (i a : Fin d) : pderiv k ((0 : Fin 1), a) (logOf G i) = Om G i a := by
  have hcl : ∀ v w : Fin 1 × Fin d, pderiv k w (Om G i v.2) = pderiv k v (Om G i w.2) := by
    rintro ⟨v1, v⟩ ⟨w1, w⟩
    obtain rfl : v1 = 0 := Subsingleton.elim _ _
    obtain rfl : w1 = 0 := Subsingleton.elim _ _
    exact om_closed G i v w
  exact pderiv_prim _ hcl ((0 : Fin 1), a)
end GlobalTheory.FormalLog
