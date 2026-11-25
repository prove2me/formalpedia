-- Prove2me | solution 1 for GlobalTheory.GaugeGermIntegral.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:14:53.742961+00:00
-- url     : https://prove2.me/submissions/13802ecc-c6f5-46c8-acb5-9f40f69739ce

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_SigmaDefectEvalPhaseOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PderivEvSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_InvariantDerivIntegral
import Theorems.Thm_GlobalTheory_GaugeGermIntegral_cocycle_integral
import Theorems.Thm_GlobalTheory_GaugeGermIntegral_invariant_deriv_integral

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
variable [CharZero K] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {V : VF K}
namespace GlobalTheory.GaugeGermIntegral
theorem _root_.solution : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O]
    (dd : ℕ) (Y : FBChart C V O dd), GermISt Y ∧ GermIISt Y :=
  fun _ _ _ _ _ _ _ _ Y => ⟨cocycle_integral Y, invariant_deriv_integral Y⟩
end GlobalTheory.GaugeGermIntegral
