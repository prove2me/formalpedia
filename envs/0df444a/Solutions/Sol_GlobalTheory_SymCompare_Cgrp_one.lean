-- Prove2me | solution 1 for GlobalTheory.SymCompare.Cgrp_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:13:09.450063+00:00
-- url     : https://prove2.me/submissions/e22d7bab-3d40-41cb-89fc-ab759e7c137c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsReindexIff
import Theorems.Thm_GlobalTheory_StepData_mem_Cgrp


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
theorem _root_.solution (J : Subgroup (GL (n ⊕ Fin c) k)) : Cgrp J 1 = R k n c 1 ⊓ J := by
  ext x; simp [mem_Cgrp]
end GlobalTheory.SymCompare
