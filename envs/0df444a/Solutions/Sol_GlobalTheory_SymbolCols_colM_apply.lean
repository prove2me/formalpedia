-- Prove2me | solution 1 for GlobalTheory.SymbolCols.colM_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:59:52.919079+00:00
-- url     : https://prove2.me/submissions/8b1e8401-d19e-4023-a7db-34bdf74cbb26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfCongrJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfProdLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumProdConstantCoeffDmonOfCols

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.SymbolCols
namespace GlobalTheory.SymbolCols
theorem _root_.solution {ι : Type} [Finite ι] {n : ℕ} (m : ι × Fin n →₀ ℕ) (b : Fin n) (l : ι) :
    colM m b l = m (l, b) := by
  simp [colM]
end GlobalTheory.SymbolCols
