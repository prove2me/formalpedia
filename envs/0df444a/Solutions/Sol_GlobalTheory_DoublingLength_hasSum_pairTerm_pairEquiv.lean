-- Prove2me | solution 1 for GlobalTheory.DoublingLength.hasSum_pairTerm_pairEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:04:16.336711+00:00
-- url     : https://prove2.me/submissions/22f9752a-a66c-4658-b9a6-acb00d7bcea8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalEigenfunctionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeckeSeriesCellHasSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumSphericalFunctionDoublingLength
import Theorems.Thm_GlobalTheory_DoublingLength_hasSum_of_subtype
import Theorems.Thm_GlobalTheory_DoublingLength_pairTerm_pairEquiv
import Theorems.Thm_GlobalTheory_GLDoubling_iUnion_cell
import Theorems.Thm_GlobalTheory_T_hecke_series_cell_has_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling
noncomputable section
open GlobalTheory GlobalTheory.DoublingLength
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
namespace GlobalTheory.DoublingLength
theorem _root_.solution {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (hφ : IsBorelSph k γ φ)
    {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) {len : GL (Fin n) k → ℕ}
    (hlen : ∀ e : Fin n → ℤ, Antitone e → ∀ g ∈ cell k (Fin n) ϖ e, len g = (∑ i, |e i|).toNat)
    {X : ℂ} (hX : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * X ^ 2‖ < 1) (g : GL (Fin n) k ⧸ KO k (Fin n)) :
    HasSum (fun h => pairTerm X φ (pairEquiv k n (g, h)))
      (X ^ len g.out * (∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * X ^ 2)⁻¹) * φ g.out) := by
  obtain ⟨e, he⟩ := Set.mem_iUnion.1 (show g.out ∈ ⋃ e : {e : Fin n → ℤ // Antitone e}, cell k (Fin n) ϖ e by
    rw [iUnion_cell hϖ]; trivial)
  rw [hlen e.1 e.2 g.out he]
  refine hasSum_of_subtype
    (P := fun h : GL (Fin n) k ⧸ KO k (Fin n) => (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) ∧
      (∀ i j, (h.out⁻¹ * g.out : GL (Fin n) k).1 i j ∈ 𝒪[k]))
    (fun h => X ^ ((-ord k (Matrix.GeneralLinearGroup.det h.out)).toNat +
      (ord k (Matrix.GeneralLinearGroup.det (h.out⁻¹ * g.out))).toNat)) (φ g.out)
    (GlobalTheory.T.hecke_series_cell_has_sum k n ϖ hϖ e.1 g.out he X hX) (fun h hB => ?_) (fun h hB => ?_) rfl
  · rw [pairTerm_pairEquiv hφ, if_pos hB]
  · rw [pairTerm_pairEquiv hφ, if_neg hB]
end GlobalTheory.DoublingLength
