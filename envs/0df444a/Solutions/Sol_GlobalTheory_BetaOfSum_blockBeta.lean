-- Prove2me | solution 1 for GlobalTheory.BetaOfSum.blockBeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:29:07.259586+00:00
-- url     : https://prove2.me/submissions/fc05e298-7c72-4f9e-8f91-a6ff5cef9ba9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BlockHarmLevOfBlockHarm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsBetaUnitBlock
import Theorems.Thm_GlobalTheory_BetaOfSum_isBeta_block
import Theorems.Thm_GlobalTheory_BetaOfSum_isBeta_unit_block
import Theorems.Thm_GlobalTheory_ShortLawsCompare_isBeta_mul
import Theorems.Thm_GlobalTheory_ShortLawsCompare_isBeta_ratio
import Theorems.Thm_GlobalTheory_ShortLawsCompare_latOK_block
import Theorems.Thm_GlobalTheory_Survey_BaseClassMove_isBeta_unit


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
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (c : Coeff l) (bad : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility.BlockBeta Dw c bad := by
  intro E _ _ _ H Dw l c bad
  refine ⟨fun n₁ n₂ Λ₁ Λ₂ h₁ h₂ β₁ β₂ β b₁ b₂ => ⟨fun b => ?_, ?_⟩,
    fun n₁ n₂ Λ₂ _ => ⟨GlobalTheory.Survey.BaseClassMove.isBeta_unit c n₁, isBeta_unit_block c n₁ Λ₂⟩⟩
  · have hB := latOK_block h₁ h₂
    exact isBeta_ratio c hB.1 hB.2.2 (isBeta_block c b₁ b₂) b
  · rintro ⟨ζ, hζ, rfl⟩
    exact isBeta_mul c (isBeta_block c b₁ b₂) hζ
end GlobalTheory.BetaOfSum
