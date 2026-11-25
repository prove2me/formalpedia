-- Prove2me | solution 1 for GlobalTheory.KTypeCompare.UJset_allPos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:18:03.891035+00:00
-- url     : https://prove2.me/submissions/6deb7c97-00f7-4e76-b329-5170b8dfc039

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HarishChandraParameters
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsWtOnIffOfTorus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.KTypeCompare
open GlobalTheory.IndefiniteRowSideFullHecke
variable {n : ℕ}
namespace GlobalTheory.KTypeCompare
theorem _root_.solution (k : ℕ) : PI.UpqRep.UJset (PI.UpqRep.allPos k) =
    (Matrix.unitaryGroup (Fin k) ℂ : Set (Matrix (Fin k) (Fin k) ℂ)) := by
  have hJ : PI.UpqRep.Jm (PI.UpqRep.allPos k) = 1 := by
    simp [PI.UpqRep.Jm, PI.UpqRep.allPos, Matrix.diagonal_one]
  ext g
  simp only [PI.UpqRep.UJset, PI.UpqRep.inUJ, Set.mem_ofPred_eq, hJ, Matrix.mul_one,
    SetLike.mem_coe, Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
end GlobalTheory.KTypeCompare
