-- Prove2me | solution 1 for GlobalTheory.T.totally_real_continuous_embedding_infinite_adeles
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:24:44.398472+00:00
-- url     : https://prove2.me/submissions/211eb73d-16ba-49e5-bd28-4611ac5b5362

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TotallyRealContinuousEmbeddingInfiniteAdeles
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TotallyRealContinuousEmbeddingInfiniteAdelesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_AdelicRealLine_exists_continuous_real_embedding


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → (∃ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ) ∧ ∀ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ → ∀ (t : ℝ) (w : InfinitePlace F), ‖θ t w‖ = |t| := by
  first | exact @GlobalTheory.CompanionTheory.AdelicRealLine.exists_continuous_real_embedding | exact GlobalTheory.CompanionTheory.AdelicRealLine.exists_continuous_real_embedding | (intros; apply GlobalTheory.CompanionTheory.AdelicRealLine.exists_continuous_real_embedding <;> assumption)
end _root_.GlobalTheory.T
