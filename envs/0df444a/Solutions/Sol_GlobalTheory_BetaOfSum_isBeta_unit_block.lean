-- Prove2me | solution 1 for GlobalTheory.BetaOfSum.isBeta_unit_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:11:39.256261+00:00
-- url     : https://prove2.me/submissions/b425effc-0ce7-4479-a76d-6b5fbd14b748

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BlockHarmLevOfBlockHarm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsBetaUnitBlock
import Theorems.Thm_GlobalTheory_BetaOfSum_block_Ln
import Theorems.Thm_GlobalTheory_BetaOfSum_index_block
import Theorems.Thm_GlobalTheory_BetaOfSum_idealAt_block
import Theorems.Thm_GlobalTheory_ShortLawsCompare_isUnit_idealAt
import Theorems.Thm_GlobalTheory_ShortLawsCompare_trivAt_std
import Theorems.Thm_GlobalTheory_ShortLawsCompare_unimod_std


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
theorem _root_.solution (n₁ : ℕ) (Λ₂ : GenLat E n₂) (β : c.F) :
    IsBeta Dw c (blockLat (unitLat E n₁) Λ₂) β ↔ IsBeta Dw c Λ₂ β := by
  have e : (unitLat E n₁).Ln = (unitLat E n₁).La := inf_idem _
  have hu : IsUnit (∏ τ : E →+* ℂ, idealAt c (unitLat E n₁).La τ ^ Dw.mult τ) :=
    IsUnit.prod_univ_iff.2 fun τ =>
      (isUnit_idealAt c (trivAt_std n₁ 0) (unimod_std n₁) zero_ne_one τ).pow _
  refine and_congr_right fun _ => and_congr ?_ (forall_congr' fun σ => ?_)
  · unfold BetaIs
    rw [block_Ln, e]
    simp only [idealAt_block c (unitLat E n₁).La Λ₂.La, idealAt_block c (unitLat E n₁).La Λ₂.Ln, mul_pow,
      Finset.prod_mul_distrib]
    rw [mul_left_comm, hu.mul_right_inj]
  · rw [index_block, e]
    simp
end GlobalTheory.BetaOfSum
