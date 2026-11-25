-- Prove2me | solution 1 for GlobalTheory.SymbolCols.exists_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:18:44.433373+00:00
-- url     : https://prove2.me/submissions/ced692d1-209a-4278-9fb8-5a0cdc36050b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfCongrJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfProdLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumProdConstantCoeffDmonOfCols
import Theorems.Thm_GlobalTheory_SymbolCols_colM_apply
import Theorems.Thm_GlobalTheory_SymbolCols_sum_degree_colM

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
theorem _root_.solution {ι : Type} [Fintype ι] {n : ℕ} (m a : ι × Fin n →₀ ℕ)
    (hdeg : m.degree = a.degree) (hne : m ≠ a) :
    ∃ b, (colM m b).degree ≤ (colM a b).degree ∧ colM m b ≠ colM a b := by
  by_contra hcon
  push Not at hcon
  have hle : ∀ b, (colM a b).degree ≤ (colM m b).degree := fun b => by
    by_contra h
    have := hcon b (by omega)
    rw [this] at h
    exact h le_rfl
  have hs : ∑ b, (colM a b).degree = ∑ b, (colM m b).degree := by
    rw [sum_degree_colM, sum_degree_colM, hdeg]
  have heq := (Finset.sum_eq_sum_iff_of_le fun b _ => hle b).1 hs
  refine hne (Finsupp.ext fun ⟨l, b⟩ => ?_)
  rw [← colM_apply, ← colM_apply, hcon b (heq b (Finset.mem_univ b)).ge]
end GlobalTheory.SymbolCols
