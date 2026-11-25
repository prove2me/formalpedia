-- Prove2me | solution 1 for GlobalTheory.ActLimit.TendsS.sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:18:18.945406+00:00
-- url     : https://prove2.me/submissions/c453ad86-5ab8-45c2-a2a2-5a7969479459

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupActionLimitsIntegralEndomorphisms
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_neg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_neg


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
theorem _root_.solution {τ : Type} {f f' : ℕ → MvPowerSeries τ C} {g g' : MvPowerSeries τ C}
    (h : TendsS V f g) (h' : TendsS V f' g') : TendsS V (fun n => f n - f' n) (g - g') := fun μ => by
  simpa [sub_eq_add_neg] using (h μ).add (h' μ).neg
end TendsS
end GlobalTheory.ActLimit
