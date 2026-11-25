-- Prove2me | solution 1 for GlobalTheory.GaugeGermIntegral.intS_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:47:53.037798+00:00
-- url     : https://prove2.me/submissions/88294911-c572-48d4-8f4f-4c37a51771a6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_SigmaDefectEvalPhaseOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivEvSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_InvariantDerivIntegral
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_ig_of_intAA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_Nab_intAA_of_ig


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
open MvPowerSeries Formalism.L2.FormalSeriesBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
  ReciprocityTheory.ChartRestriction.G.TB.LogPf ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
open GlobalTheory GlobalTheory.GaugeGermIntegral
variable {K : Type} [Field K]
namespace GlobalTheory.GaugeGermIntegral
theorem _root_.solution (V : VF K) {σ : Type} (f : MvPowerSeries σ K) :
    IntS V f ↔ f ∈ Ig (intRing V) K σ := by
  constructor
  · intro h
    exact ig_of_intAA fun n => ⟨⟨_, h n⟩, rfl⟩
  · intro h n
    obtain ⟨r, hr⟩ := intAA_of_ig h n
    rw [← hr]
    exact r.2
end GlobalTheory.GaugeGermIntegral
