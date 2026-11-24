-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.TraceFormGram.trGram_isSymm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:54:55.592118+00:00
-- url     : https://prove2.me/submissions/0818a6e1-6d13-44b8-a88b-500edee6c5c8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EtaleAwayQuotientEqLocalization
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceFormGram_sig_sig
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceFormGram_trace_sig

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TraceFormGram
open HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable [NumberField F] [NumberField E]
namespace GlobalTheory.CompanionTheory.SW.TraceFormGram
theorem _root_.solution {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {M d : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (b : Module.Basis (Fin d) F E) :
    (trGram σ J b).IsSymm := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [Matrix.transpose_apply, trGram]
  rw [← trace_sig h (σ (b l) * J j i * b k)]
  simp only [map_mul, sig_sig h, hJ.1]
  congr 1
  ring
end GlobalTheory.CompanionTheory.SW.TraceFormGram
