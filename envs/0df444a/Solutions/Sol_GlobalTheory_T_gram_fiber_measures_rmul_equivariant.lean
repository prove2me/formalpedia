-- Prove2me | solution 1 for GlobalTheory.T.gram_fiber_measures_rmul_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:04:55.044345+00:00
-- url     : https://prove2.me/submissions/c02ee8f1-6445-4af8-ab62-f53d2d6ba250

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresSupport
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresSupportStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibScale_fib_rmul


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)), IsUnit g.det → ∀ τ : HermR R σ n → HermR R σ n, (∀ S, (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = cT (sigR R σ) g * S * g) → ∀ a c : ℝ≥0, μ.map (fun X => rmul R X g) = a • μ → ν.map τ = c • ν → ∀ S, a • m (τ S) = c • (m S).map (fun X => rmul R X g) := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibScale.fib_rmul | exact GlobalTheory.CompanionTheory.SW.FibScale.fib_rmul | (intros; apply GlobalTheory.CompanionTheory.SW.FibScale.fib_rmul <;> assumption)
end _root_.GlobalTheory.T
