-- Prove2me | solution 1 for GlobalTheory.ActLimit.Tends.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:34:13.066172+00:00
-- url     : https://prove2.me/submissions/a37e9fd1-f0f5-47e0-8ca9-a33a02f32d3e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupActionLimitsIntegralEndomorphisms
import Theorems.Thm_GlobalTheory_ActLimit_eq_zero_of_ge
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sub
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sub


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
namespace Tends
theorem _root_.solution {s : ℕ → C} {x y : C} (hx : Tends V s x) (hy : Tends V s y) : x = y := by
  apply sub_eq_zero.1
  refine eq_zero_of_ge (V := V) fun w => ?_
  obtain ⟨n, h1, h2⟩ := ((hx w).and (hy w)).exists
  simpa using h1.sub h2
end Tends
end GlobalTheory.ActLimit
