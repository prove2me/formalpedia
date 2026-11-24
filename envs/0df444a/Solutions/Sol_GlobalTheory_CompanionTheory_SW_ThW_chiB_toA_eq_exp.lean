-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThW.chiB_toA_eq_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:09:22.620908+00:00
-- url     : https://prove2.me/submissions/e7ed9658-641d-4228-af75-f81d88f73eaf

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicCharacterExponentialFormula
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_emb_dotProduct_DM
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_toA_dotProduct_Bf
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_sum_rho_eq_trace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker
namespace GlobalTheory.CompanionTheory.SW.ThW
theorem _root_.solution (F : Type) [Field F] [NumberField F] (ψ : AddChar (A F) ℂ)
    (hψ : IsStdChar F ψ) (ι : Type) [Fintype ι] [DecidableEq ι]
    [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F)
    (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ)
    (hQ : QSetup M B ρ P) (a y : ι → F) :
    chiB ψ (Bf B) (toA a) (toA y) = Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) *
      ((emb ρ a ⬝ᵥ (DM B ρ *ᵥ emb ρ y) : ℝ) : ℂ)) := by
  obtain ⟨hT, -, -, -, hρ, -, -⟩ := hQ
  rw [chiB, toA_dotProduct_Bf, hψ.2, emb_dotProduct_DM, sum_rho_eq_trace hT hρ]
  norm_cast
end GlobalTheory.CompanionTheory.SW.ThW
