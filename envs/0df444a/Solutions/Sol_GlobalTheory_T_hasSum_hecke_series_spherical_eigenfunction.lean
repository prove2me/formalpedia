-- Prove2me | solution 1 for GlobalTheory.T.hasSum_hecke_series_spherical_eigenfunction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:49:49.548307+00:00
-- url     : https://prove2.me/submissions/1f13d00d-34be-4781-b87e-7fd9f777884a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalEigenfunction
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasBoundedSumsOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HasSumHeckeSeriesSphericalEigenfunctionStatement
import Theorems.Thm_GlobalTheory_HeckeShift_hasSum_hecke_shift


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
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (γ : Fin n → ℂ) (φ : GL (Fin n) k → ℂ), IsBorelSph k γ φ → (∀ i, γ i ≠ 0) → ∀ X : ℂ, (∀ i : Fin n, ‖(resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X‖ < 1) → ∀ g : GL (Fin n) k, HasSum (fun c : {c : GL (Fin n) k ⧸ KO k (Fin n) // (∀ i j, (c.out : GL (Fin n) k).1 i j ∈ 𝒪[k])} => X ^ (ord k (Matrix.GeneralLinearGroup.det c.1.out)).toNat * φ (g * c.1.out)) ((∏ i : Fin n, (1 - (resCard k : ℂ) ^ (n - 1 - (i : ℕ)) * γ i * X)⁻¹) * φ g) := by
  first | exact @GlobalTheory.HeckeShift.hasSum_hecke_shift | exact GlobalTheory.HeckeShift.hasSum_hecke_shift | (intros; apply GlobalTheory.HeckeShift.hasSum_hecke_shift <;> assumption)
end _root_.GlobalTheory.T
