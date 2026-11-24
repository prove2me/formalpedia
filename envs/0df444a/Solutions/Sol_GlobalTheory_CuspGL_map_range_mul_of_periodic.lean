-- Prove2me | solution 1 for GlobalTheory.CuspGL.map_range_mul_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:05:37.439881+00:00
-- url     : https://prove2.me/submissions/be1e4a29-e5ae-4377-b5de-901594312ccd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FrobeniusTorusMinpolyDegreeRootPowerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatDegreeMulEsymmRootsPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution {β : Type} (g : ℕ → β) (e : ℕ) (hg : ∀ i, g (e + i) = g i) (m : ℕ) :
    (Multiset.range (e * m)).map g = m • (Multiset.range e).map g := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, add_comm (e * m), Multiset.range_add, Multiset.map_add, Multiset.map_map,
      succ_nsmul', ← ih]
    congr 1
    exact Multiset.map_congr rfl fun i _ => hg i
end GlobalTheory.CuspGL
