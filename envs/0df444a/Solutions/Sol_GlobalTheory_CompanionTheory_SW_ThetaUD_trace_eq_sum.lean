-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.ThetaUD.trace_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:35:06.281687+00:00
-- url     : https://prove2.me/submissions/bc947d82-dbb9-4e44-a1d8-9319840ae9a0

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ThetaFunctionModularity

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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThetaUD
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.SW.ThetaUD
theorem _root_.solution (hT : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (y : F) :
    ((Algebra.trace ℚ F y : ℚ) : ℂ) = ∑ w, ((ρ w y : ℝ) : ℂ) := by
  have h1 := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := y)
  have h2 : ((Algebra.trace ℚ F y : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ F y) := by simp
  rw [h2, h1]
  symm
  refine Fintype.sum_bijective (fun w : InfinitePlace F => (w.embedding).toRatAlgHom) ?_ _ _ ?_
  · constructor
    · intro w w' h
      have : w.embedding = w'.embedding := by
        ext x
        exact DFunLike.congr_fun h x
      rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding w', this]
    · intro σ
      have hr : (InfinitePlace.mk (σ : F →+* ℂ)).IsReal := hT.isReal _
      have hc : ComplexEmbedding.IsReal (σ : F →+* ℂ) := InfinitePlace.isReal_mk_iff.1 hr
      refine ⟨InfinitePlace.mk (σ : F →+* ℂ), ?_⟩
      ext x
      have := InfinitePlace.embedding_mk_eq_of_isReal hc
      simp [this]
  · intro w
    simp [hρ]
end GlobalTheory.CompanionTheory.SW.ThetaUD
