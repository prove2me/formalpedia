-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.TraceFormGram.trace_sig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:34:38.849354+00:00
-- url     : https://prove2.me/submissions/4f911d89-d8ea-48cc-92b8-b86e52fbcb68

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EtaleAwayQuotientEqLocalization
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceFormGram_sig_sig

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
theorem _root_.solution {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) :
    Algebra.trace F E (σ x) = Algebra.trace F E x :=
  Algebra.trace_eq_of_algEquiv
    (AlgEquiv.ofAlgHom σ σ (AlgHom.ext (sig_sig h)) (AlgHom.ext (sig_sig h))) x
end GlobalTheory.CompanionTheory.SW.TraceFormGram
