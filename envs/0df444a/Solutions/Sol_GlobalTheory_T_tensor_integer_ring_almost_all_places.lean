-- Prove2me | solution 1 for GlobalTheory.T.tensor_integer_ring_almost_all_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:22:23.428395+00:00
-- url     : https://prove2.me/submissions/5950648f-3751-42d3-8d47-fbaa4acf2c74

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorIntegerRingAlmostAllPlaces
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorIntegerRingAlmostAllPlacesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_good_ring


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ O : Subring (Fv F v ⊗[F] E), (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) ∧ (∀ y ∈ O, sigR (Fv F v) σ y ∈ O) ∧ Finite (MaximalSpectrum O) ∧ IsUnit (2 : O) ∧ (∃ δ : O, IsUnit δ ∧ sigR (Fv F v) σ δ = -δ) ∧ (∀ s β : O, IsUnit β → sigR (Fv F v) σ β = β → ∃ ε z : O, (ε : Fv F v ⊗[F] E) * sigR (Fv F v) σ ε = 1 ∧ ((β : Fv F v ⊗[F] E) - sigR (Fv F v) σ ε * s) * z = 1) ∧ ∀ β : O, IsUnit β → sigR (Fv F v) σ β = β → ∃ a : O, (a : Fv F v ⊗[F] E) * sigR (Fv F v) σ a = β := by
  first | exact @GlobalTheory.CompanionTheory.SW.GoodRing.good_ring | exact GlobalTheory.CompanionTheory.SW.GoodRing.good_ring | (intros; apply GlobalTheory.CompanionTheory.SW.GoodRing.good_ring <;> assumption)
end _root_.GlobalTheory.T
