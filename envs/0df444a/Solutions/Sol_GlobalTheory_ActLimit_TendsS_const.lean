-- Prove2me | solution 1 for GlobalTheory.ActLimit.TendsS.const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:16:26.697192+00:00
-- url     : https://prove2.me/submissions/f221e4ba-3c42-4912-a5b7-ba2dac49b41d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupActionLimitsIntegralEndomorphisms

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
theorem _root_.solution {τ : Type} (g : MvPowerSeries τ C) : TendsS V (fun _ => g) g := fun _ => Tends.const _
end TendsS
end GlobalTheory.ActLimit
