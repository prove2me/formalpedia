-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimInf.exists_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:29:32.287531+00:00
-- url     : https://prove2.me/submissions/f8b1c680-a85c-4813-a00e-4b33fdb71703

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanPrimitiveVectorCompactRescale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimInf
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.PrimInf
theorem _root_.solution (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ δ : E, σ δ = -δ ∧ δ ≠ 0 := by
  obtain ⟨-, hC, -, hτ⟩ := h
  let τ₀ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  have hnr : ¬ ComplexEmbedding.IsReal τ₀ := fun hr =>
    InfinitePlace.not_isReal_iff_isComplex.mpr (hC.isComplex (InfinitePlace.mk τ₀))
      (InfinitePlace.isReal_mk_iff.mpr hr)
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra hall
    push_neg at hall
    apply hnr
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := hτ τ₀ x
    rw [hall x] at this
    exact this.symm
  have hσσ : ∀ x, σ (σ x) = x := fun x => τ₀.injective (by rw [hτ, hτ, star_star])
  refine ⟨x - σ x, by simp [hσσ], sub_ne_zero.mpr (Ne.symm hx)⟩
end GlobalTheory.CompanionTheory.SW.PrimInf
