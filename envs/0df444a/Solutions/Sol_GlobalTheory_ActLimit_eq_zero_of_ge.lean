-- Prove2me | solution 1 for GlobalTheory.ActLimit.eq_zero_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:16:20.706362+00:00
-- url     : https://prove2.me/submissions/08a4cbca-d624-4c4e-b531-3a11ec6e9ccf

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
theorem _root_.solution {x : C} (h : ∀ w : ℝ, V.Ge w x) : x = 0 := by
  by_contra hx
  have hv : V.v x ≠ ⊤ := by rwa [Ne, AddValuation.top_iff]
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hv
  have h1 := h (t + 1)
  unfold VF.Ge at h1
  rw [← ht] at h1
  have : t + 1 ≤ t := by exact_mod_cast h1
  linarith
end GlobalTheory.ActLimit
