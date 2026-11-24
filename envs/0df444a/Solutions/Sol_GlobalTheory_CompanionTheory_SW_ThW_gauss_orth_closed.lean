-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThW.gauss_orth_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:14:10.136912+00:00
-- url     : https://prove2.me/submissions/fb4c0803-6cd1-497b-b10f-91a11243e764

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianChangeOfVariablesIsometry
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_GaussOrth_gauss_orth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.ThW
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (ρ : NumberField.InfinitePlace F → (F →+* ℝ)) (P : NumberField.InfinitePlace F → Matrix ι ι ℝ) (gi : NumberField.InfinitePlace F → Matrix ι ι ℝ), B.det ≠ 0 → (∀ w, (gi w).transpose * B.map (ρ w) * gi w = B.map (ρ w)) → (∀ (τ : NumberField.InfinitePlace F → ℂ) (x : NumberField.InfinitePlace F → ι → ℝ), GlobalTheory.CompanionTheory.SW.Core.gauss B ρ P τ (fun w => (gi w).mulVec (x w)) = GlobalTheory.CompanionTheory.SW.Core.gauss B ρ (fun w => (gi w).transpose * P w * gi w) τ x) ∧ ∀ τ : NumberField.InfinitePlace F → ℂ, GlobalTheory.CompanionTheory.SW.Core.cG B ρ (fun w => (gi w).transpose * P w * gi w) τ = GlobalTheory.CompanionTheory.SW.Core.cG B ρ P τ :=
  fun _ _ _ _ _ _ B ρ P gi hB hg => GlobalTheory.CompanionTheory.SW.ThW.GaussOrth.gauss_orth B ρ P gi hB hg
end GlobalTheory.CompanionTheory.SW.ThW
