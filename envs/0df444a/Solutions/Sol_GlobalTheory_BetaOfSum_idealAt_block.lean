-- Prove2me | solution 1 for GlobalTheory.BetaOfSum.idealAt_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:01:44.971485+00:00
-- url     : https://prove2.me/submissions/b9675943-dbb8-4c4e-9331-b8f619c862c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BlockHarmLevOfBlockHarm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsBetaUnitBlock
import Theorems.Thm_GlobalTheory_BetaOfSum_detSpan_block
import Theorems.Thm_GlobalTheory_BetaEx_span_image_span


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
open GlobalTheory GlobalTheory.BetaOfSum
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BetaEx GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility GlobalTheory.ShortLawsCompare
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l) {n₁ n₂ : ℕ}
namespace GlobalTheory.BetaOfSum
theorem _root_.solution (M₁ : Submodule (𝓞 E) (Fin n₁ → E)) (M₂ : Submodule (𝓞 E) (Fin n₂ → E)) (τ : E →+* ℂ) :
    idealAt c (blockLat ⟨M₁⟩ ⟨M₂⟩).La τ = idealAt c M₁ τ * idealAt c M₂ τ := by
  have e := detSpan_block M₁ M₂
  unfold detSpan at e
  unfold idealAt
  rw [← span_image_span, e, Submodule.span_mul_span, span_image_span, Submodule.span_mul_span, Set.image_mul]
end GlobalTheory.BetaOfSum
