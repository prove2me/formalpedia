-- Prove2me | solution 1 for GlobalTheory.T.theta_function_modularity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:29:04.399035+00:00
-- url     : https://prove2.me/submissions/496fef4a-bb7e-4e61-afd0-f0373054e92f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ThetaFunctionModularity
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ThetaFunctionModularityStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThetaUD_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ), IsOrth B ρ gf gi → ∀ (φ : (ι → A F) → ℂ) (τ : InfinitePlace F → ℂ), (∀ b : F, theta B ρ P gf gi (opU ψ (hf F) (Bf B) (algebraMap F (A F) b) φ) (fun w => τ w + (ρ w b : ℝ)) = theta B ρ P gf gi φ τ) ∧ (∀ a : F, a ≠ 0 → theta B ρ P gf gi (opD 1 (algebraMap F (A F) a) φ) (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) = theta B ρ P gf gi φ τ) ∧ ∀ c : ℂ, theta B ρ P gf gi (c • φ) τ = c * theta B ρ P gf gi φ τ := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThetaUD.main | exact GlobalTheory.CompanionTheory.SW.ThetaUD.main | (intros; apply GlobalTheory.CompanionTheory.SW.ThetaUD.main <;> assumption)
end _root_.GlobalTheory.T
