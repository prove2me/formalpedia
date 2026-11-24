-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.TraceFormGram.expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:37:43.30282+00:00
-- url     : https://prove2.me/submissions/72d56a29-485c-4628-a7cc-23399c53660f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EtaleAwayQuotientEqLocalization

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
namespace GlobalTheory.CompanionTheory.SW.TraceFormGram
theorem _root_.solution {d : ℕ} (b : Module.Basis (Fin d) F E) (R : Type) [CommRing R] [Algebra F R]
    (u : R ⊗[F] E) :
    u = ∑ k, ((Algebra.TensorProduct.basis R b).repr u k) ⊗ₜ[F] b k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr u]
  simp [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
end GlobalTheory.CompanionTheory.SW.TraceFormGram
