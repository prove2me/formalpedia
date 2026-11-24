-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TfLoc.Iw.torusO_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:41:39.418026+00:00
-- url     : https://prove2.me/submissions/57ccc5ff-bd59-4c49-8605-ea09e1ce6b7e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization

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
variable {F : Type*} [Field F] [ValuativeRel F] {m : ℕ}
namespace GlobalTheory.CompanionTheory.TfLoc.Iw
theorem _root_.solution : torusO (n := m) F ⊆ iwahori (m := m) F := fun _ ht =>
  ⟨ht.1, fun i j hij => by rw [ht.2 i j (ne_of_gt hij)]; simp⟩
end GlobalTheory.CompanionTheory.TfLoc.Iw
