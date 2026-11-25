-- Prove2me | solution 1 for GlobalTheory.BetaOfSum.index_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:51:06.439741+00:00
-- url     : https://prove2.me/submissions/abf4629b-2092-4b26-bbb8-84203dec0a08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BlockHarmLevOfBlockHarm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsBetaUnitBlock
import Theorems.Thm_GlobalTheory_BetaOfSum_mem_block
import Theorems.Thm_GlobalTheory_BetaOfSum_block_Ln

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
variable {E : Type} [Field E] [NumberField E] {n₁ n₂ : ℕ}
namespace GlobalTheory.BetaOfSum
theorem _root_.solution (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) :
    ((blockLat Λ₁ Λ₂).Ln.toAddSubgroup.addSubgroupOf (blockLat Λ₁ Λ₂).La.toAddSubgroup).index =
      (Λ₁.Ln.toAddSubgroup.addSubgroupOf Λ₁.La.toAddSubgroup).index *
        (Λ₂.Ln.toAddSubgroup.addSubgroupOf Λ₂.La.toAddSubgroup).index := by
  let φ : (blockLat Λ₁ Λ₂).La.toAddSubgroup →+ Λ₁.La.toAddSubgroup × Λ₂.La.toAddSubgroup :=
    { toFun := fun v => (⟨fun i => v.1 (Fin.castAdd n₂ i), v.2.1⟩, ⟨fun j => v.1 (Fin.natAdd n₁ j), v.2.2⟩)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hφ : Function.Surjective φ := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨⟨Fin.append x y, (mem_block _ _ _).2 ⟨by simpa using hx, by simpa using hy⟩⟩, ?_⟩
    ext j <;> simp [φ]
  rw [← AddSubgroup.index_prod, ← AddSubgroup.index_comap_of_surjective _ hφ, block_Ln]
  rfl
end GlobalTheory.BetaOfSum
