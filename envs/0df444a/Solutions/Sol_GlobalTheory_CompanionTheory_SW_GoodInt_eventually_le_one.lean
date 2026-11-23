-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GoodInt.eventually_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:57:58.822185+00:00
-- url     : https://prove2.me/submissions/fcae30d6-4634-419c-99eb-cfb23c8e47a2

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GoodInt
namespace GlobalTheory.CompanionTheory.SW.GoodInt
theorem _root_.solution {F : Type} [Field F] [NumberField F] (x : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v.valuation F x ≤ 1 := by
  have h := HeightOneSpectrum.Support.finite (𝓞 F) x
  rw [Filter.eventually_cofinite]
  refine h.subset fun v hv => ?_
  exact not_le.mp hv
end GlobalTheory.CompanionTheory.SW.GoodInt
