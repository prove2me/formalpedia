-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LatRat.eventually_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:38.139243+00:00
-- url     : https://prove2.me/submissions/2e29945e-69cb-4920-a2b0-ea894d1f1cae

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeStableAlmostEverywhere

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatRat
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.LatRat
theorem _root_.solution (x : F) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F := by
  have h := HeightOneSpectrum.Support.finite (𝓞 F) x
  filter_upwards [h.compl_mem_cofinite] with v hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have h2 : Valued.v (algebraMap F (Fv F v) x) = v.valuation F x :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  rw [h2]
  exact not_lt.mp hv
end GlobalTheory.CompanionTheory.SW.LatRat
