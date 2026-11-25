-- Prove2me | solution 1 for GlobalTheory.DoublingLength.hasSum_pairTerm_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:57:57.469829+00:00
-- url     : https://prove2.me/submissions/139cdf6f-0d3f-41be-ae23-f9691cf5a236

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalIntegralInverseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalEigenfunctionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HeckeSeriesCellHasSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumSphericalFunctionDoublingLength
import Theorems.Thm_GlobalTheory_DoublingLength_hasSum_of_subtype
import Theorems.Thm_GlobalTheory_T_hasSum_hecke_series_spherical_eigenfunction


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
    {X : ℂ} (hX : ∀ i : Fin n, ‖(resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X‖ < 1)
    (h : GL (Fin n) k ⧸ KO k (Fin n)) :
    HasSum (fun c => pairTerm X φ (h, c))
      (if (∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]) then
        X ^ (-ord k (Matrix.GeneralLinearGroup.det h.out)).toNat * φ h.out *
          ∏ i : Fin n, (1 - (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X)⁻¹ else 0) := by
  by_cases hA : ∀ i j, (h.out⁻¹ : GL (Fin n) k).1 i j ∈ 𝒪[k]
  · rw [if_pos hA]
    refine hasSum_of_subtype (P := fun c : GL (Fin n) k ⧸ KO k (Fin n) => ∀ i j, (c.out : GL (Fin n) k).1 i j ∈ 𝒪[k])
      (fun c => X ^ (ord k (Matrix.GeneralLinearGroup.det c.out)).toNat * φ (h.out * c.out))
      (X ^ (-ord k (Matrix.GeneralLinearGroup.det h.out)).toNat)
      (GlobalTheory.T.hasSum_hecke_series_spherical_eigenfunction k n γ φ hφ hγ X hX h.out) (fun c hB => ?_) (fun c hB => ?_) (by ring)
    · rw [pairTerm, if_pos ⟨hA, hB⟩]
      ring
    · rw [pairTerm, if_neg fun H => hB H.2]
  · rw [if_neg hA]
    have : (fun c => pairTerm X φ (h, c)) = fun _ => 0 := funext fun c => by
      rw [pairTerm, if_neg fun H => hA H.1]
    rw [this]
    exact hasSum_zero
end GlobalTheory.DoublingLength
