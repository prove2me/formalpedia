-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TfLoc.Iw.val_algebraMap_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:41:40.296411+00:00
-- url     : https://prove2.me/submissions/9be28f2c-9b36-4964-b19d-a53bc3e864d9

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_val_algebraMap_le_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel PositivityTheory.Rg.Tf.Loc Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TfLoc GlobalTheory.CompanionTheory.TfLoc.Iw
variable {k E : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E]
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [FiniteDimensional k E]
namespace GlobalTheory.CompanionTheory.TfLoc.Iw
theorem _root_.solution (a : k) :
    valuation E (algebraMap k E a) ≤ 1 ↔ valuation k a ≤ 1 := by
  simpa using val_algebraMap_le_iff (E := E) a 1
end GlobalTheory.CompanionTheory.TfLoc.Iw
