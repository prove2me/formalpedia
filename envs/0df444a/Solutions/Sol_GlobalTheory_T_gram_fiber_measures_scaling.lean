-- Prove2me | solution 1 for GlobalTheory.T.gram_fiber_measures_scaling
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:10:58.536366+00:00
-- url     : https://prove2.me/submissions/f5f68bf2-9f42-45c0-b9f4-d4f14a16fac0

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresScaling
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresScalingStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Rescale_isGramFib_rescale


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ a c : ℝ≥0, a ≠ 0 → c ≠ 0 → IsGramFib R σ J n (a • μ) (c • ν) (fun S => (a / c) • m S) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Rescale.isGramFib_rescale | exact GlobalTheory.CompanionTheory.SW.Rescale.isGramFib_rescale | (intros; apply GlobalTheory.CompanionTheory.SW.Rescale.isGramFib_rescale <;> assumption)
end _root_.GlobalTheory.T
