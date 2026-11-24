-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThetaUD.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:12:32.874095+00:00
-- url     : https://prove2.me/submissions/f6f28ea6-ef84-4b6f-a265-67aaa8dd3972

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ThetaFunctionModularity
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThetaUD_term_U
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThetaUD_term_D

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThetaUD
variable {F : Type} [Field F] [NumberField F]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.SW.ThetaUD
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ), IsOrth B ρ gf gi → ∀ (φ : (ι → A F) → ℂ) (τ : InfinitePlace F → ℂ), (∀ b : F, theta B ρ P gf gi (opU ψ (hf F) (Bf B) (algebraMap F (A F) b) φ) (fun w => τ w + (ρ w b : ℝ)) = theta B ρ P gf gi φ τ) ∧ (∀ a : F, a ≠ 0 → theta B ρ P gf gi (opD 1 (algebraMap F (A F) a) φ) (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) = theta B ρ P gf gi φ τ) ∧ ∀ c : ℂ, theta B ρ P gf gi (c • φ) τ = c * theta B ρ P gf gi φ τ := by
  intro F _ _ ψ hψ ι _ _ M B ρ P hQ gf gi hO φ τ
  refine ⟨fun b => ?_, fun a ha => ?_, fun c => ?_⟩
  · unfold theta
    exact tsum_congr fun x => term_U ψ hψ M B ρ P hQ gf gi hO φ τ b x
  · unfold theta
    simp only [term_D]
    exact (MulAction.toPerm (Units.mk0 a ha) : Equiv.Perm (ι → F)).tsum_eq (thTerm B ρ P gf gi φ τ)
  · unfold theta
    rw [← tsum_mul_left]
    refine tsum_congr fun x => ?_
    simp [thTerm, mul_assoc]
end GlobalTheory.CompanionTheory.SW.ThetaUD
