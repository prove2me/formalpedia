-- Prove2me | solution 1 for GlobalTheory.ActLimit.TendsS.const_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:52:57.753007+00:00
-- url     : https://prove2.me/submissions/640893a9-9b50-40ee-ad4f-7924af486239

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupActionLimitsIntegralEndomorphisms
import Theorems.Thm_GlobalTheory_ActLimit_Tends_unique
import Theorems.Thm_GlobalTheory_ActLimit_TendsS_const
import Theorems.Thm_GlobalTheory_ActLimit_TendsS_unique

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
theorem _root_.solution {τ : Type} {f : ℕ → MvPowerSeries τ C} {g : MvPowerSeries τ C}
    (h : TendsS V f g) (hf : ∀ n, MvPowerSeries.constantCoeff (f n) = 0) : MvPowerSeries.constantCoeff g = 0 := by
  have h0 := h 0
  simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf] at h0
  exact h0.unique (Tends.const 0)
end TendsS
end GlobalTheory.ActLimit
