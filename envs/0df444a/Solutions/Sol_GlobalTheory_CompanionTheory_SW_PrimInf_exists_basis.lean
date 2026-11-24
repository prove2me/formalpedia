-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.PrimInf.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:29:31.607175+00:00
-- url     : https://prove2.me/submissions/792a43ef-d1a1-4d62-bbc9-c4a918671e13

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
theorem _root_.solution (σ : E →ₐ[F] E) (h : IsCMExt F E σ) {δ : E} (hδ : σ δ = -δ) (h0 : δ ≠ 0) :
    ∃ b : Module.Basis (Fin 2) F E, b 0 = 1 ∧ b 1 = δ := by
  have hli : LinearIndependent F ![(1 : E), δ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h2 : s • (1 : E) - t • δ = 0 := by
      have := congrArg σ.toLinearMap hst
      rw [map_add, LinearMap.map_smul, LinearMap.map_smul, map_zero] at this
      simp only [AlgHom.toLinearMap_apply, map_one, hδ, smul_neg] at this
      rwa [sub_eq_add_neg]
    have h3 : (2 * t) • δ = 0 := by
      have : (2 * t) • δ = (s • (1 : E) + t • δ) - (s • (1 : E) - t • δ) := by
        rw [mul_smul, two_smul]
        abel
      rw [this, hst, h2, sub_zero]
    have ht : t = 0 := by
      rcases smul_eq_zero.mp h3 with h4 | h4
      · simpa using h4
      · exact absurd h4 h0
    subst ht
    refine ⟨?_, rfl⟩
    simpa using hst
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by
    rw [h.2.2.1]
    rfl
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard, ?_, ?_⟩
  · simp
  · simp
end GlobalTheory.CompanionTheory.SW.PrimInf
