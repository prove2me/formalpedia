-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TfLoc.Iw.continuous_inv_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:41:31.276794+00:00
-- url     : https://prove2.me/submissions/94c6a208-d48d-47fd-abca-9ad9f9a8fc08

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_continuous_entry

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
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {m : ℕ}
namespace GlobalTheory.CompanionTheory.TfLoc.Iw
theorem _root_.solution (i j : Fin m) :
    Continuous fun g : GL (Fin m) F => ((g⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) i j :=
  (continuous_entry i j).comp continuous_inv
end GlobalTheory.CompanionTheory.TfLoc.Iw
