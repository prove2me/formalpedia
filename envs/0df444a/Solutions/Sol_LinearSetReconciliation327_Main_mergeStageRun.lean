-- Prove2me | solution 1 for LinearSetReconciliation327.Main.mergeStageRun
-- status  : ACCEPTED   (prove)
-- author  : @djwj233
-- created : 2026-11-22T04:12:00.728384+00:00
-- url     : https://prove2.me/submissions/44cf2aa3-0119-4ee2-b11b-66309438c6ac

import Definitions.Def_LinearSetReconciliation327_Main_MergeStep20261121

set_option autoImplicit false
set_option maxHeartbeats 400000

open LinearSetReconciliation327.Main

theorem solution {P : Program} {E : RAMEnv} {base ab al bb bl ob : ℕ} (A B : List ℕ)
    (hAt : At P base (RMR.mrgStmtFull.compile base)) (hW : 1 < 2 ^ E.W) :
    StageRun P E base (base + RMR.mrgStmtFull.len) (RMR.mrgCost al bl)
      (fun s => s.regs r10 = ab ∧ s.regs r11 = al ∧ s.regs r12 = bb ∧ s.regs r13 = bl ∧
        s.regs r14 = ob ∧
        RMR.mList s.mem ab al = A ∧ RMR.mList s.mem bb bl = B ∧
        A.Nodup ∧ B.Nodup ∧
        (∀ p, p < al → s.mem (ab + p) < 2 ^ E.W) ∧
        (∀ p, p < bl → s.mem (bb + p) < 2 ^ E.W) ∧
        al < 2 ^ E.W ∧ bl < 2 ^ E.W ∧
        ab + al ≤ 2 ^ E.W ∧ bb + bl ≤ 2 ^ E.W ∧
        ob + (al + bl) + 1 < 2 ^ E.W ∧
        (ab + al ≤ ob ∨ ob + (al + bl) ≤ ab) ∧ (bb + bl ≤ ob ∨ ob + (al + bl) ≤ bb))
      (fun s' => (outList s').Nodup ∧
        (outList s').toFinset = symmDiff A.toFinset B.toFinset) :=
  LinearSetReconciliation327.Main.RMR.mergeStageRun A B hAt hW
