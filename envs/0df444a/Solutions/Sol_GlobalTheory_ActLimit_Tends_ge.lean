-- Prove2me | solution 1 for GlobalTheory.ActLimit.Tends.ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:26:43.00159+00:00
-- url     : https://prove2.me/submissions/48336eee-6f75-4497-af53-0b12fa2b6fa0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupActionLimitsIntegralEndomorphisms
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_add
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_add


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
theorem _root_.solution {s : ℕ → C} {x : C} {w : ℝ} (hx : Tends V s x) (hs : ∀ n, V.Ge w (s n)) : V.Ge w x := by
  obtain ⟨n, h1⟩ := (hx w).exists
  simpa using h1.add (hs n)
end Tends
end GlobalTheory.ActLimit
