-- Prove2me | solution 1 for GlobalTheory.T.gram_transpose_dual_trace_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:11:04.492772+00:00
-- url     : https://prove2.me/submissions/81591fb1-ce19-4061-b336-1d935992696e

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramTransposeDualTraceIdentity
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramTransposeDualTraceIdentityStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_gM_DM_emb_eq_trace


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (b : InfinitePlace F → 𝓞 F) (N : ℕ) (y : ι → F), (gM ρ b N)ᵀ *ᵥ (DM B ρ *ᵥ emb ρ y) = fun p => (((N : ℚ) * Algebra.trace ℚ F ((b p.2 : F) * (B *ᵥ y) p.1) : ℚ) : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.gM_DM_emb_eq_trace | exact GlobalTheory.CompanionTheory.SW.ThW.gM_DM_emb_eq_trace | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.gM_DM_emb_eq_trace <;> assumption)
end _root_.GlobalTheory.T
