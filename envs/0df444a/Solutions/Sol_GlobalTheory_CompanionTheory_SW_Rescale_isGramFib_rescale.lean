-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Rescale.isGramFib_rescale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:53:21.336741+00:00
-- url     : https://prove2.me/submissions/a192c4e3-082d-4025-89d3-c8522f654bff

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FibreFamilySmul
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresScaling
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_Rescale_isFibreFamily_rescale


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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Rescale
namespace GlobalTheory.CompanionTheory.SW.Rescale
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ a c : ℝ≥0, a ≠ 0 → c ≠ 0 → IsGramFib R σ J n (a • μ) (c • ν) (fun S => (a / c) • m S) := by
  intro F E _ _ _ _ _ σ _ M J _ R _ _ _ _ _ _ n μ ν m _ _ h a c _ hc
  exact isFibreFamily_rescale _ _ _ μ ν _ _ _ _ m h a c hc
end GlobalTheory.CompanionTheory.SW.Rescale
