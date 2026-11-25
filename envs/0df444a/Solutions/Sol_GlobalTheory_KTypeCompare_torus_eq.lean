-- Prove2me | solution 1 for GlobalTheory.KTypeCompare.torus_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:18:12.699977+00:00
-- url     : https://prove2.me/submissions/aa0a3052-0768-4ec2-81e1-0ae1caa43543

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
theorem _root_.solution (θ : Fin n → ℝ) :
    (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) = HarishChandraRootData.torus θ := by
  unfold HarishChandraRootData.torus
  congr 1
  funext a
  rw [mul_comm]
end GlobalTheory.KTypeCompare
