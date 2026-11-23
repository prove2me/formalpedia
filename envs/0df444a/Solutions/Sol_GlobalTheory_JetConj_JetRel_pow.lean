-- Prove2me | solution 1 for GlobalTheory.JetConj.JetRel.pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:40.245035+00:00
-- url     : https://prove2.me/submissions/f40a2564-28e5-4421-9cff-d2780ca1650b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_JetRelOfWeierstrassSystem
import Theorems.Thm_GlobalTheory_JetConj_JetRel_zero
import Theorems.Thm_GlobalTheory_JetConj_JetRel_const
import Theorems.Thm_GlobalTheory_JetConj_JetRel_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.JetConj
variable {S : Subring (ℂ × ℂ)} {f f' g g' h h' : ℂ → ℂ}
namespace GlobalTheory.JetConj
namespace JetRel
theorem _root_.solution (H : JetRel S f f') (k : ℕ) : JetRel S (fun z => f z ^ k) (fun z => f' z ^ k) := by
  induction k with
  | zero => simpa using JetRel.const (S := S) (a := 1) (b := 1) S.one_mem
  | succ k ih => simpa [pow_succ] using ih.mul H
end JetRel
end GlobalTheory.JetConj
