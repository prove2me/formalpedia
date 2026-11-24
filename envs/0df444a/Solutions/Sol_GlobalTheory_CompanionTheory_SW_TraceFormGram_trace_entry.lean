-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.TraceFormGram.trace_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:58:35.204648+00:00
-- url     : https://prove2.me/submissions/a923d4da-aa73-4115-ba62-d6375ae0956e

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EtaleAwayQuotientEqLocalization
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceFormGram_trace_tmul
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceFormGram_expand

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
theorem _root_.solution [FiniteDimensional F E] (σ : E →ₐ[F] E) {d : ℕ} (b : Module.Basis (Fin d) F E)
    (R : Type) [CommRing R] [Algebra F R] (u v : R ⊗[F] E) (e : E) :
    Algebra.trace R (R ⊗[F] E) (sigR R σ u * ((1 : R) ⊗ₜ[F] e) * v) =
      ∑ k, ∑ l, (Algebra.TensorProduct.basis R b).repr u k *
        (algebraMap F R (Algebra.trace F E (σ (b k) * e * b l)) *
          (Algebra.TensorProduct.basis R b).repr v l) := by
  conv_lhs => rw [expand b R u, expand b R v]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have : sigR R σ (((Algebra.TensorProduct.basis R b).repr u k) ⊗ₜ[F] b k) =
      ((Algebra.TensorProduct.basis R b).repr u k) ⊗ₜ[F] σ (b k) := by
    simp [sigR]
  rw [this, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, trace_tmul]
  simp only [mul_one]
  ring
end GlobalTheory.CompanionTheory.SW.TraceFormGram
