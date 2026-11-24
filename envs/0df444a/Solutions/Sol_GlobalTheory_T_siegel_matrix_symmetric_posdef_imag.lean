-- Prove2me | solution 1 for GlobalTheory.T.siegel_matrix_symmetric_posdef_imag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:22:24.251253+00:00
-- url     : https://prove2.me/submissions/11440f5e-54b4-4b66-baf5-092df81e3a8f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SiegelMatrixSymmetricPosdefImag
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SiegelMatrixSymmetricPosdefImagStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_ZM_symm_posDef_gauss


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → (ZM B ρ P τ).IsSymm ∧ ((ZM B ρ P τ).map Complex.im).PosDef ∧ ∀ x : ι × InfinitePlace F → ℝ, Complex.exp ((Real.pi : ℂ) * Complex.I * ((fun i => (x i : ℂ)) ⬝ᵥ (ZM B ρ P τ *ᵥ fun i => (x i : ℂ)))) = gauss B ρ P τ (cur x) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.ZM_symm_posDef_gauss | exact GlobalTheory.CompanionTheory.SW.ThW.ZM_symm_posDef_gauss | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.ZM_symm_posDef_gauss <;> assumption)
end _root_.GlobalTheory.T
