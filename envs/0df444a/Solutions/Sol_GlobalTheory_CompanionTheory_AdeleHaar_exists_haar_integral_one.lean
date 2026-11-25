-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:21:46.418867+00:00
-- url     : https://prove2.me/submissions/4b8c06c5-d646-4820-93d8-226a6bd50763

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsFiniteAdeleHaarNormalized
import Theorems.Thm_GroundTheory_Global_mem_integralFiniteAdeles


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdeleHaar
namespace GlobalTheory.CompanionTheory.AdeleHaar
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F],
    ∃ lf : Measure (Af F), lf.IsAddHaarMeasure ∧
      lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 := by
  intro F _ _
  have : BorelSpace (Af F) := ⟨rfl⟩
  have hset : ({x | ∀ v, x v ∈ v.adicCompletionIntegers F} : Set (Af F)) =
      (GroundTheory.Global.integralFiniteAdelesPositiveCompacts F :
        Set (FiniteAdeleRing (𝓞 F) F)) := by
    ext x
    exact GroundTheory.Global.mem_integralFiniteAdeles.symm
  refine ⟨Measure.addHaarMeasure (GroundTheory.Global.integralFiniteAdelesPositiveCompacts F),
    inferInstance, ?_⟩
  rw [hset]
  exact Measure.addHaarMeasure_self
end GlobalTheory.CompanionTheory.AdeleHaar
