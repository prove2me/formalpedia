-- Prove2me | solution 1 for GlobalTheory.T.integral_almost_all_places
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:25.170993+00:00
-- url     : https://prove2.me/submissions/c08daadf-ecdd-44d5-9195-d1cb57b2cb89

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlacesStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodInt_rational_integral_units


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), (∀ x : E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (Fv F v) x) k ∈ v.adicCompletionIntegers F) ∧ ∀ x : F, x ≠ 0 → ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, Valued.v (algebraMap F (Fv F v) x) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units | exact GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units | (intros; apply GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units <;> assumption)
end _root_.GlobalTheory.T
