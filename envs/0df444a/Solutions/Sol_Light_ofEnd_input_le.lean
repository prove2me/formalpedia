-- Prove2me | solution 1 for Light.ofEnd_input_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:30:53.945017+00:00
-- url     : https://prove2.me/submissions/82953415-08b1-49c8-b1c8-aa1574294bb6

import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
import Definitions.Def_Submission_ThreeSumApsp_Lang_TopProcedure
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_ThreeSumApsp_WordRam_Bounded_abs_le


set_option autoImplicit false
section
open Light
open ThreeSumApsp ThreeSumApsp.WordRam
variable {lim : Limits} {P : Program} {d : ℕ}
variable {Q : EndStatement.Problem} (x : Bounded Q)
namespace Light
theorem _root_.solution : ∀ a ∈ (ofEnd Q).input x, |a| ≤ ((x.n + x.U + 1 : ℕ) : ℤ) := by
  intro a ha
  rcases List.mem_cons.1 ha with rfl | ha
  · rw [abs_of_nonneg (by positivity)]
    push_cast
    omega
  · have := Bounded.abs_le ha
    push_cast
    omega
end Light
