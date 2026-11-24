-- Prove2me | solution 1 for GlobalTheory.JR.NormalFormL.mom_sec_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:35:09.921876+00:00
-- url     : https://prove2.me/submissions/411091b6-9a2e-412a-af2a-f3aaf27c6818

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
import Theorems.Thm_P2M_GlobalTheory_JR_NormalFormL_inv_sec__4f2b1984a7c3
import Theorems.Thm_GlobalTheory_JR_NormalFormL_charpoly_companion_inv
import Theorems.Thm_GlobalTheory_JR_NormalFormL_dot_pow_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NormalFormL
variable {k : Type} [Field k] {r : ℕ}
namespace GlobalTheory.JR.NormalFormL
theorem _root_.solution (Y : Gl r k) (n : ℕ) : mom (sec (inv Y)) n = mom Y n := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp [mom, dotProduct]
  have hs := inv_sec' (inv Y)
  simp only [mom]
  rw [dot_pow_eq_sum _ hr, dot_pow_eq_sum _ hr]
  have hc : (sec (inv Y)).1.charpoly = Y.1.charpoly := charpoly_companion_inv Y
  rw [hc]
  refine Finset.sum_congr rfl fun i hi => ?_
  congr 1
  have := congrFun (congrArg (fun a : Inv r k => a.2.1) hs) ⟨i, Finset.mem_range.mp hi⟩
  simpa [inv, mom] using this
end GlobalTheory.JR.NormalFormL
