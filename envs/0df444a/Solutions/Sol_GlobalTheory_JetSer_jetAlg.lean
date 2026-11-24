-- Prove2me | solution 1 for GlobalTheory.JetSer.jetAlg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:41:31.103135+00:00
-- url     : https://prove2.me/submissions/2a6fc0b8-8b5d-46b0-887d-a412be21e9fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsToJetEq
import Theorems.Thm_GlobalTheory_JetSer_jetTruncR_toJet
import Theorems.Thm_GlobalTheory_JetSer_jetAug_toJet
import Theorems.Thm_GlobalTheory_JetSer_eq_of_toJet_eq
import Theorems.Thm_GlobalTheory_JetSer_exists_toJet_eq
import Theorems.Thm_GlobalTheory_JetSer_exists_jetHom
import Theorems.Thm_GlobalTheory_JetSer_jetHom_toJet
import Theorems.Thm_GlobalTheory_JetSer_toJet_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart
open GlobalTheory GlobalTheory.JetSer
variable {R : Type} [CommRing R] {κ : Type}
variable [Finite κ]
namespace GlobalTheory.JetSer
theorem _root_.solution : JetAlgSt := fun R _ κ _ =>
  ⟨fun m => ⟨toJetHom R κ m, fun _ => rfl, fun j => toJet_X m j⟩,
    fun m g => ⟨jetTruncR_toJet m g, jetAug_toJet m g⟩,
    fun _ _ h => eq_of_toJet_eq h, exists_toJet_eq,
    fun _ _ a ha m => ⟨exists_jetHom a ha m, jetHom_toJet a ha m⟩⟩
end GlobalTheory.JetSer
