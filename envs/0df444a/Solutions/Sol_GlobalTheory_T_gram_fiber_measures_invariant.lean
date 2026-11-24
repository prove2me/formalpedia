-- Prove2me | solution 1 for GlobalTheory.T.gram_fiber_measures_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:37:59.507132+00:00
-- url     : https://prove2.me/submissions/0fc84468-cb5f-4c09-a31d-a21eb46bf621

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresInvariant
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresInvariantStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreInv_map_actW_fibre


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (h : HA R σ J) (S : HermR R σ n), (m S).map (actW R σ J h) = m S := by
  first | exact @GlobalTheory.CompanionTheory.SW.FibreInv.map_actW_fibre | exact GlobalTheory.CompanionTheory.SW.FibreInv.map_actW_fibre | (intros; apply GlobalTheory.CompanionTheory.SW.FibreInv.map_actW_fibre <;> assumption)
end _root_.GlobalTheory.T
