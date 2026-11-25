-- Prove2me | solution 1 for GlobalTheory.ActLimit.const_of_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:35:06.311721+00:00
-- url     : https://prove2.me/submissions/54ab96e3-6a01-449f-9a78-50bb74dd913f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupActionLimitsIntegralEndomorphisms
import Theorems.Thm_GlobalTheory_ActLimit_const_ev

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
variable {dd : ℕ}
namespace GlobalTheory.ActLimit
theorem _root_.solution {m n : ℕ} {a : Fin m → Pt C n dd} (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0)
    {f : PS C m dd} (hf : ev a f = 0) : MvPowerSeries.constantCoeff f = 0 := by
  have h := const_ev ha (f := f - MvPowerSeries.C (MvPowerSeries.constantCoeff f)) (by simp)
  unfold ev at h hf
  rw [MvPowerSeries.subst_sub (a := fun p : Fin m × Fin dd => a p.1 p.2)
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => ha p.1 p.2), hf,
    MvPowerSeries.subst_C] at h
  simpa using h
end GlobalTheory.ActLimit
