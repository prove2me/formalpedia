-- Prove2me | solution 1 for GlobalTheory.ActLimit.TendsS.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:43:48.653166+00:00
-- url     : https://prove2.me/submissions/d960a473-a20f-4581-a165-6a4ecc9826a2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupActionLimitsIntegralEndomorphisms
import Theorems.Thm_GlobalTheory_ActLimit_Tends_unique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.ActLimit
variable {C : Type} [Field C] {V : VF C}
namespace GlobalTheory.ActLimit
namespace TendsS
theorem _root_.solution {τ : Type} {f : ℕ → MvPowerSeries τ C} {g g' : MvPowerSeries τ C}
    (h : TendsS V f g) (h' : TendsS V f g') : g = g' := by
  ext μ; exact (h μ).unique (h' μ)
end TendsS
end GlobalTheory.ActLimit
