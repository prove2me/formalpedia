-- Prove2me | solution 1 for GlobalTheory.BadShare.SqCount.monic_divX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:47:42.678853+00:00
-- url     : https://prove2.me/submissions/a910624e-9ccb-4241-9581-d40647d1a23f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardMonicSquarefreeUnitConstPolysGe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare GlobalTheory.BadShare.SqCount
variable (g : ℕ) [Fact g.Prime]
variable {g}
namespace GlobalTheory.BadShare.SqCount
theorem _root_.solution {k : Type} [Field k] {a : k[X]} (ha : a.Monic) (hd : 1 ≤ a.natDegree) : a.divX.Monic := by
  rw [Monic, leadingCoeff, natDegree_divX_eq_natDegree_tsub_one, coeff_divX, Nat.sub_add_cancel hd]
  exact ha
end GlobalTheory.BadShare.SqCount
