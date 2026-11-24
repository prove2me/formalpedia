-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThW.gM_DM_emb_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:56:12.449793+00:00
-- url     : https://prove2.me/submissions/7bd56159-33f0-4889-b5c9-27eca9cbfcba

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramTransposeDualTraceIdentity
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_DM_mulVec_emb
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_gM_transpose_mulVec
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
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
namespace GlobalTheory.CompanionTheory.SW.ThW
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (b : InfinitePlace F → 𝓞 F) (N : ℕ) (y : ι → F), (gM ρ b N)ᵀ *ᵥ (DM B ρ *ᵥ emb ρ y) = fun p => (((N : ℚ) * Algebra.trace ℚ F ((b p.2 : F) * (B *ᵥ y) p.1) : ℚ) : ℝ) := by
  intro F _ _ ι _ _ _ M B ρ P hQ b N y
  obtain ⟨hT, -, -, -, hρ, -, -⟩ := hQ
  funext p
  obtain ⟨i, v⟩ := p
  rw [DM_mulVec_emb, gM_transpose_mulVec]
  have h := sum_rho_eq_trace hT hρ ((b v : F) * (B *ᵥ y) i)
  simp only [emb, ← map_mul]
  rw [h]
  push_cast
  rfl
end GlobalTheory.CompanionTheory.SW.ThW
