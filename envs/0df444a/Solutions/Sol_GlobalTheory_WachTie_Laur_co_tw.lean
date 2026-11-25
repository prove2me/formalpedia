-- Prove2me | solution 1 for GlobalTheory.WachTie.Laur.co_tw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:31:09.079051+00:00
-- url     : https://prove2.me/submissions/a7a79e26-f757-4b87-9847-bbd420611f31

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_NonGaloisCusps_GradedSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfSumSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries
open GlobalTheory GlobalTheory.WachTie
open GlobalTheory.WachTie.Laur
variable {L M M' : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module L M']
namespace GlobalTheory.WachTie.Laur
theorem _root_.solution (c : L) (g : M →ₗ[L] M') (x : Laur L M) (k : ℤ) :
    co (tw c g x) k = c ^ k • g (co x k) := rfl
end GlobalTheory.WachTie.Laur
