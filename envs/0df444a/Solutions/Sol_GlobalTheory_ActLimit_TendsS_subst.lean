-- Prove2me | solution 1 for GlobalTheory.ActLimit.TendsS.subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:01:50.032239+00:00
-- url     : https://prove2.me/submissions/3b412f9e-78eb-4839-a5b4-fa837f482f92

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupActionLimitsIntegralEndomorphisms
import Theorems.Thm_GlobalTheory_ActLimit_TendsS_const_zero

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
theorem _root_.solution {σ τ : Type} [Finite σ] {a : ℕ → σ → MvPowerSeries τ C} {b : σ → MvPowerSeries τ C}
    (ha : ∀ n s, MvPowerSeries.constantCoeff (a n s) = 0) (hab : ∀ s, TendsS V (fun n => a n s) (b s))
    {f : ℕ → MvPowerSeries σ C} {g : MvPowerSeries σ C} (h : TendsS V f g) :
    TendsS V (fun n => MvPowerSeries.subst (a n) (f n)) (MvPowerSeries.subst b g) := by
  have hA : MvPowerSeries.HasSubst fun s => (hab s).lift := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => ?_
    apply Subtype.ext
    refine Prod.ext (funext fun n => ha n s) ((hab s).const_zero fun n => ha n s)
  have h1 : ∀ n, MvPowerSeries.map (term V n) (MvPowerSeries.subst (fun s => (hab s).lift) h.lift) =
      MvPowerSeries.subst (a n) (f n) := fun n => MvPowerSeries.map_subst hA _
  have h2 : MvPowerSeries.map (lim V) (MvPowerSeries.subst (fun s => (hab s).lift) h.lift) =
      MvPowerSeries.subst b g := MvPowerSeries.map_subst hA _
  intro μ
  simp only [← h1, ← h2, MvPowerSeries.coeff_map]
  exact (MvPowerSeries.coeff μ (MvPowerSeries.subst (fun s => (hab s).lift) h.lift)).2
end TendsS
end GlobalTheory.ActLimit
