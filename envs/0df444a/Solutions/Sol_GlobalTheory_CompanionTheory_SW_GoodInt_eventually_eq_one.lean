-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GoodInt.eventually_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:57.373608+00:00
-- url     : https://prove2.me/submissions/7a7e6db3-4384-4e91-a6df-5ae44ad1d830

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodInt_eventually_le_one

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
theorem _root_.solution {F : Type} [Field F] [NumberField F] (x : F) (hx : x ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, v.valuation F x = 1 := by
  filter_upwards [eventually_le_one x, eventually_le_one x⁻¹] with v h1 h2
  refine le_antisymm h1 ?_
  rw [map_inv₀] at h2
  have h0 : v.valuation F x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  exact (inv_le_one₀ (zero_lt_iff.mpr h0)).mp h2
end GlobalTheory.CompanionTheory.SW.GoodInt
