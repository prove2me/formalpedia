-- Prove2me | solution 1 for GlobalTheory.T.gram_fiber_measures_change_of_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:10:55.750644+00:00
-- url     : https://prove2.me/submissions/ea579eb1-902c-4b4e-943b-f377db265ff0

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresChangeOfForm
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresChangeOfFormStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocIsom_fibre_map_isometry


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (J' : Matrix (Fin M) (Fin M) E), IsHermND σ J' → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ (μ' : Measure (Fin n → Fin M → R ⊗[F] E)) m', μ'.IsAddHaarMeasure → IsGramFib R σ J' n μ' ν m' → ∀ g : GL (Fin M) (R ⊗[F] E), JR R J' = cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) → ∀ a : ℝ≥0, μ'.map (actTup R g) = a • μ → ∀ S, (m' S).map (actTup R g) = a • m S := by
  first | exact @GlobalTheory.CompanionTheory.SW.LocIsom.fibre_map_isometry | exact GlobalTheory.CompanionTheory.SW.LocIsom.fibre_map_isometry | (intros; apply GlobalTheory.CompanionTheory.SW.LocIsom.fibre_map_isometry <;> assumption)
end _root_.GlobalTheory.T
