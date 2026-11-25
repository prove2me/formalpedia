-- Prove2me | solution 1 for GlobalTheory.BetaOfSum.mem_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:33:34.955258+00:00
-- url     : https://prove2.me/submissions/a4d0823c-95e6-4ad9-bcf3-b791fecb0004

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_BlockPolyLevelMove
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BlockHarmLevOfBlockHarm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsBetaUnitBlock

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
theorem _root_.solution (M₁ : Submodule (𝓞 E) (Fin n₁ → E)) (M₂ : Submodule (𝓞 E) (Fin n₂ → E))
    (v : Fin (n₁ + n₂) → E) : v ∈ (blockLat ⟨M₁⟩ ⟨M₂⟩).La ↔
      (fun i => v (Fin.castAdd n₂ i)) ∈ M₁ ∧ (fun j => v (Fin.natAdd n₁ j)) ∈ M₂ := Iff.rfl
end GlobalTheory.BetaOfSum
