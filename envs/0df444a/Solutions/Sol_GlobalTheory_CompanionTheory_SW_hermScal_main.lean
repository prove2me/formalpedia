-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.hermScal_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:50:37.901952+00:00
-- url     : https://prove2.me/submissions/171be4a7-6935-4c34-913d-d3732dd2f021

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousHermScal
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_OneHerm_map_hermScal

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
noncomputable section
namespace GlobalTheory.CompanionTheory.SW
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), IsHomeomorph (hermScal R σ) ∧ (∀ S : HermR R σ 1, hermScal R σ (algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) ((S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0)) = S) ∧ ∀ (lam : Measure R), lam.IsAddHaarMeasure → lam.map (hermScal R σ) = coordHerm R σ b lam 1 := by
  intro F E _ _ _ _ _ σ hσ R _ _ _ _ _ _ _ _ _ d b
  refine ⟨(GlobalTheory.CompanionTheory.SW.OneHerm.hermHomeo R hσ).isHomeomorph, GlobalTheory.CompanionTheory.SW.OneHerm.hermScal_hermHalf R hσ, ?_⟩
  intro lam hlam
  exact GlobalTheory.CompanionTheory.SW.OneHerm.map_hermScal R hσ b lam
end GlobalTheory.CompanionTheory.SW
