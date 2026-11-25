-- Prove2me | solution 1 for GlobalTheory.T.exists_finite_adele_haar_normalized
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:19:01.824366+00:00
-- url     : https://prove2.me/submissions/b019d652-6745-4418-af78-665313ae5696

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsFiniteAdeleHaarNormalized
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsFiniteAdeleHaarNormalizedStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_AdeleHaar_exists_haar_integral_one


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F], ∃ lf : Measure (Af F), lf.IsAddHaarMeasure ∧ lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 := by
  first | exact @GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one | exact GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one | (intros; apply GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one <;> assumption)
end _root_.GlobalTheory.T
