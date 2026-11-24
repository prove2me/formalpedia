-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LatSum.finite_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:30:35.240888+00:00
-- url     : https://prove2.me/submissions/72585cc9-2c2c-4d8d-8639-75d79b4d82d4

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EisensteinLatticeSumBound

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatSum
namespace GlobalTheory.CompanionTheory.SW.LatSum
theorem _root_.solution (F : Type) [Field F] [NumberField F] (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) :
    {α : 𝓞 F | ∀ w, |ρ w (α : F)| < 1}.Finite := by
  have hf := Embeddings.finite_of_norm_le F ℂ 1
  refine (hf.preimage (f := fun α : 𝓞 F => (α : F)) ?_).subset ?_
  · exact (RingOfIntegers.coe_injective).injOn
  · intro α hα
    refine ⟨RingOfIntegers.isIntegral_coe α, fun φ => ?_⟩
    have h1 : ‖φ (α : F)‖ = InfinitePlace.mk φ (α : F) := (InfinitePlace.apply φ _).symm
    have h2 := InfinitePlace.norm_embedding_eq (InfinitePlace.mk φ) (α : F)
    rw [h1, ← h2, ← hρ, Complex.norm_real, Real.norm_eq_abs]
    exact (hα _).le
end GlobalTheory.CompanionTheory.SW.LatSum
