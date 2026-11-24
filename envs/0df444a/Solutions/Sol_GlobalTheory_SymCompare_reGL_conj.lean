-- Prove2me | solution 1 for GlobalTheory.SymCompare.reGL_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:21:16.725209+00:00
-- url     : https://prove2.me/submissions/54e6e551-30d5-409c-aa7e-7756305b504a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsReindexIff
import Theorems.Thm_GlobalTheory_StepData_LatFrame_conj_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.SymCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}
namespace GlobalTheory.SymCompare
theorem _root_.solution {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (F : LatFrame k ι n) (F' : LatFrame k ι' m) (a : ι ≃ ι') (b : n ≃ m) (ho : a.trans F'.ord = F.ord.trans b)
    (hb : F'.bas = reGL b F.bas) (g : GL ι k) : F'.conj (reGL a g) = reGL b (F.conj g) := by
  have : reGL F'.ord (reGL a g) = reGL b (reGL F.ord g) := by
    change reGL (a.trans F'.ord) g = reGL (F.ord.trans b) g
    rw [ho]
  rw [LatFrame.conj_apply, LatFrame.conj_apply, this, hb, map_mul, map_mul, map_inv]
end GlobalTheory.SymCompare
