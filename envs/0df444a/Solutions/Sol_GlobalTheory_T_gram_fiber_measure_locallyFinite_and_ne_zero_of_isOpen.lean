-- Prove2me | solution 1 for GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:36:50.066237+00:00
-- url     : https://prove2.me/submissions/659a1dcb-5a1e-4a69-acff-6f5b3ea3bb33

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresContinuity
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresContinuityStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocFin_fibre_loc_fin


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ), ∀ (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)) (m : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib R σ J n μ ν m → ∀ S : HermR R σ n, IsLocallyFiniteMeasure (m S) ∧ ∀ U : Set (Fin n → Fin M → R ⊗[F] E), IsOpen U → (∃ X ∈ U, gramR R σ J X = S ∧ IsUnit (gramR R σ J X).det) → m S U ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.LocFin.fibre_loc_fin | exact GlobalTheory.CompanionTheory.SW.LocFin.fibre_loc_fin | (intros; apply GlobalTheory.CompanionTheory.SW.LocFin.fibre_loc_fin <;> assumption)
end _root_.GlobalTheory.T
