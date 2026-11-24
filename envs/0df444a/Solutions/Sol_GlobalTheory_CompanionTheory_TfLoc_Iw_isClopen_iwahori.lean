-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TfLoc.Iw.isClopen_iwahori
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:02:53.699417+00:00
-- url     : https://prove2.me/submissions/82c5bd75-f42d-4dd0-8f6e-8fa5071bea9d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_isClopen_lt_one
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_isClopen_le_one
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_continuous_entry
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_continuous_inv_entry
import Theorems.Thm_GlobalTheory_CompanionTheory_TfLoc_Iw_iwahori_eq

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
theorem _root_.solution : IsClopen (iwahori (m := m) F) := by
  rw [iwahori_eq]
  refine (IsClopen.inter ?_ ?_).inter ?_
  · exact isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j =>
      isClopen_le_one.preimage (continuous_entry i j)
  · exact isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j =>
      isClopen_le_one.preimage (continuous_inv_entry i j)
  · exact isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j =>
      isClopen_iInter_of_finite fun _ => isClopen_lt_one.preimage (continuous_entry i j)
end GlobalTheory.CompanionTheory.TfLoc.Iw
