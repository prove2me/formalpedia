-- Prove2me | solution 1 for GlobalTheory.T.hecke_series_cell_has_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:57:49.943478+00:00
-- url     : https://prove2.me/submissions/571f8c37-db07-433d-8ad6-4b1bb86deaf9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeckeSeriesCellHasSum
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeckeSeriesCellHasSumStatement
import Theorems.Thm_GlobalTheory_LatticePair_hasSum_pair


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (e : Fin n → ℤ), ∀ g ∈ cell k (Fin n) ϖ e, ∀ X : ℂ, (∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * X ^ 2‖ < 1) → HasSum (fun h : {h : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) ∧ (∀ i j, (h.out⁻¹ * g : GL (Fin n) k).1 i j ∈ 𝒪[k])} => X ^ ((-ord k (Matrix.GeneralLinearGroup.det h.1.out)).toNat + (ord k (Matrix.GeneralLinearGroup.det (h.1.out⁻¹ * g))).toNat)) (X ^ (∑ i, |e i|).toNat * ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2)⁻¹) := by
  first | exact @GlobalTheory.LatticePair.hasSum_pair | exact GlobalTheory.LatticePair.hasSum_pair | (intros; apply GlobalTheory.LatticePair.hasSum_pair <;> assumption)
end _root_.GlobalTheory.T
