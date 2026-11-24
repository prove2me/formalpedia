-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GramLocal.adele_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:21:21.549911+00:00
-- url     : https://prove2.me/submissions/9d52efbc-5420-4d07-bb57-78305ac6cad2

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramMatrixLocalGlobal

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramLocal
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.GramLocal
theorem _root_.solution (x y : AF F) (h1 : fstA F x = fstA F y)
    (h2 : ∀ v, evalV F v (sndA F x) = evalV F v (sndA F y)) : x = y := by
  refine Prod.ext h1 ?_
  exact Subtype.ext (funext h2)
end GlobalTheory.CompanionTheory.SW.GramLocal
