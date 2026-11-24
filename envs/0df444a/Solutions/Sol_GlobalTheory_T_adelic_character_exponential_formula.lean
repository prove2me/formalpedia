-- Prove2me | solution 1 for GlobalTheory.T.adelic_character_exponential_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:02:46.825452+00:00
-- url     : https://prove2.me/submissions/090dccdd-8427-43eb-bbcc-aaa828630b55

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicCharacterExponentialFormula
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicCharacterExponentialFormulaStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_chiB_toA_eq_exp


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (A F) ℂ), IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ a y : ι → F, chiB ψ (Bf B) (toA a) (toA y) = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((emb ρ a ⬝ᵥ (DM B ρ *ᵥ emb ρ y) : ℝ) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.chiB_toA_eq_exp | exact GlobalTheory.CompanionTheory.SW.ThW.chiB_toA_eq_exp | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.chiB_toA_eq_exp <;> assumption)
end _root_.GlobalTheory.T
