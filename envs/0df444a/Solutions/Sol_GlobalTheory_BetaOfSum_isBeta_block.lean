-- Prove2me | solution 1 for GlobalTheory.BetaOfSum.isBeta_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:11:35.87586+00:00
-- url     : https://prove2.me/submissions/e76edd64-e776-4197-803a-da6298750c4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BlockHarmLevOfBlockHarm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsBetaUnitBlock
import Theorems.Thm_GlobalTheory_BetaOfSum_block_Ln
import Theorems.Thm_GlobalTheory_BetaOfSum_index_block
import Theorems.Thm_GlobalTheory_BetaOfSum_idealAt_block

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
theorem _root_.solution {Λ₁ : GenLat E n₁} {Λ₂ : GenLat E n₂} {β₁ β₂ : c.F} (b₁ : IsBeta Dw c Λ₁ β₁)
    (b₂ : IsBeta Dw c Λ₂ β₂) : IsBeta Dw c (blockLat Λ₁ Λ₂) (β₁ * β₂) := by
  refine ⟨mul_ne_zero b₁.1 b₂.1, ?_, fun σ => ?_⟩
  · have e₁ := b₁.2.1
    have e₂ := b₂.2.1
    unfold BetaIs at e₁ e₂ ⊢
    rw [block_Ln]
    simp only [idealAt_block c Λ₁.La Λ₂.La, idealAt_block c Λ₁.Ln Λ₂.Ln, mul_pow, Finset.prod_mul_distrib]
    rw [← e₁, ← e₂, ← Set.singleton_mul_singleton, ← Submodule.span_mul_span, mul_mul_mul_comm]
  · rw [index_block, map_mul, norm_mul, mul_pow, b₁.2.2 σ, b₂.2.2 σ, Nat.cast_mul, mul_pow]
end GlobalTheory.BetaOfSum
