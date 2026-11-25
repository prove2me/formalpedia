-- Prove2me | solution 1 for GlobalTheory.SymbolCols.sum_degree_colM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:06:06.438871+00:00
-- url     : https://prove2.me/submissions/c6bc6520-5330-472e-a314-2ee2fe3a61f9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfCongrJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfProdLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumProdConstantCoeffDmonOfCols
import Theorems.Thm_GlobalTheory_SymbolCols_colM_apply

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
theorem _root_.solution {ι : Type} [Fintype ι] {n : ℕ} (m : ι × Fin n →₀ ℕ) :
    ∑ b, (colM m b).degree = m.degree := by
  simp only [Finsupp.degree_eq_sum, colM_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
end GlobalTheory.SymbolCols
