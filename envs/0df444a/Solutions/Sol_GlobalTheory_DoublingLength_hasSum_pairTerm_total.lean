-- Prove2me | solution 1 for GlobalTheory.DoublingLength.hasSum_pairTerm_total
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:49:52.18654+00:00
-- url     : https://prove2.me/submissions/8e568afc-462a-4e06-878a-48e9978d440b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalEigenfunctionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeckeSeriesCellHasSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumSphericalFunctionDoublingLength
import Theorems.Thm_GlobalTheory_DoublingLength_hasSum_of_subtype
import Theorems.Thm_GlobalTheory_T_hasSum_hecke_series_spherical_integral_inverse


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
open scoped Classical
namespace GlobalTheory.DoublingLength
theorem _root_.solution {γ : Fin n → ℂ} {φ : GL (Fin n) k → ℂ} (hφ : IsBorelSph k γ φ) (hγ : ∀ i, γ i ≠ 0)
    {X : ℂ} (hX : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X‖ < 1) (a : ℂ) :
    HasSum (fun h : GL (Fin n) k ⧸ KO k (Fin n) =>
      if (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) then
        X ^ (-ord k (Matrix.GeneralLinearGroup.det h.out)).toNat * φ h.out * a else 0)
      (a * ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (i : ℕ) * (γ i)⁻¹ * X)⁻¹) := by
  exact hasSum_of_subtype
    (P := fun c : GL (Fin n) k ⧸ KO k (Fin n) => ∀ i j, (c.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k])
    (fun c => X ^ (-ord k (Matrix.GeneralLinearGroup.det c.out)).toNat * φ c.out) a
    (GlobalTheory.T.hasSum_hecke_series_spherical_integral_inverse k n γ φ hφ hγ X hX) (fun c hB => if_pos hB) (fun c hB => if_neg hB) (mul_comm _ _)
end GlobalTheory.DoublingLength
