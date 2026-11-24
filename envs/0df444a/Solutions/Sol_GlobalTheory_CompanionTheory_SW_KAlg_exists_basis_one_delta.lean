-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.KAlg.exists_basis_one_delta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:26:37.921749+00:00
-- url     : https://prove2.me/submissions/e6b2cc7a-08a8-4594-9f7d-1f95a57eb576

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.KAlg
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.KAlg
theorem _root_.solution (σ : E →ₐ[F] E) {δ : E} (hδ : σ δ = -δ) (h0 : δ ≠ 0)
    (hfr : Module.finrank F E = 2) (h2 : (2 : F) ≠ 0) :
    ∃ b : Module.Basis (Fin 2) F E, b 0 = 1 ∧ b 1 = δ := by
  have li : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : s • (1 : E) + t • (-δ) = 0 := by
      have := congrArg σ hst
      simpa [map_add, map_smul, hδ] using this
    have hs : (2 * s) • (1 : E) = 0 := by
      have : (2 * s) • (1 : E) = (s • (1 : E) + t • δ) + (s • (1 : E) + t • (-δ)) := by module
      rw [this, hst, h1, add_zero]
    have hs0 : s = 0 := by
      rcases smul_eq_zero.1 hs with h | h
      · exact (mul_eq_zero.1 h).resolve_left h2
      · exact absurd h one_ne_zero
    subst hs0
    refine ⟨rfl, ?_⟩
    rcases smul_eq_zero.1 (by simpa using hst : t • δ = 0) with h | h
    · exact h
    · exact absurd h h0
  refine ⟨basisOfLinearIndependentOfCardEqFinrank li (by simp [hfr]), ?_, ?_⟩
  · simp
  · simp
end GlobalTheory.CompanionTheory.SW.KAlg
