-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GoodInt.valued_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:04.539947+00:00
-- url     : https://prove2.me/submissions/43979400-d403-4be5-92bc-6a371c11a3a5

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
theorem _root_.solution {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    Valued.v (algebraMap F (Fv F v) x) = v.valuation F x := by
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
end GlobalTheory.CompanionTheory.SW.GoodInt
