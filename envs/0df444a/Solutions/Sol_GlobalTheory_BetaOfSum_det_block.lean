-- Prove2me | solution 1 for GlobalTheory.BetaOfSum.det_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:33:27.169795+00:00
-- url     : https://prove2.me/submissions/ec17c36c-2afd-4184-9089-51ecb1530777

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
omit [NumberField E]
namespace GlobalTheory.BetaOfSum
theorem _root_.solution (u : Matrix (Fin (n₁ + n₂)) (Fin (n₁ + n₂)) E)
    (h : ∀ i j, u (Fin.castAdd n₂ i) (Fin.natAdd n₁ j) = 0) :
    u.det = (Matrix.of fun i j => u (Fin.castAdd n₂ i) (Fin.castAdd n₂ j)).det *
      (Matrix.of fun i j => u (Fin.natAdd n₁ i) (Fin.natAdd n₁ j)).det := by
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, ← Matrix.det_fromBlocks_zero₁₂ _
    (Matrix.of fun i j => u (Fin.natAdd n₁ i) (Fin.castAdd n₂ j))]
  congr 1
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [h]
end GlobalTheory.BetaOfSum
