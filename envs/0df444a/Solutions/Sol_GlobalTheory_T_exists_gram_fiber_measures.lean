-- Prove2me | solution 1 for GlobalTheory.T.exists_gram_fiber_measures
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:17:52.14181+00:00
-- url     : https://prove2.me/submissions/59545705-dbd4-4a6c-9d80-ee85e92c33bc

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsGramFiberMeasures
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsGramFiberMeasuresStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramExist_exists_gramFib


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∃ m, IsGramFib R σ J n μ ν m := by
  first | exact @GlobalTheory.CompanionTheory.SW.GramExist.exists_gramFib | exact GlobalTheory.CompanionTheory.SW.GramExist.exists_gramFib | (intros; apply GlobalTheory.CompanionTheory.SW.GramExist.exists_gramFib <;> assumption)
end _root_.GlobalTheory.T
