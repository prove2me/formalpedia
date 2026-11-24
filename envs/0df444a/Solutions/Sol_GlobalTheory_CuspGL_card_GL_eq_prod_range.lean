-- Prove2me | solution 1 for GlobalTheory.CuspGL.card_GL_eq_prod_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:04:03.394775+00:00
-- url     : https://prove2.me/submissions/e34a6d5b-cde3-41fd-8c73-36b2141cb9f3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesOfFinrankMulCardBasesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CardSubspacesMulGeneralLinearGroupCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution (F : Type) [Field F] [Finite F] (n : ℕ) :
    Nat.card (GL (Fin n) F) = ∏ i ∈ Finset.range n, (Nat.card F ^ n - Nat.card F ^ i) := by
  classical
  haveI := Fintype.ofFinite F
  rw [Matrix.card_GL_field, Nat.card_eq_fintype_card,
    ← Fin.prod_univ_eq_prod_range (fun i => Fintype.card F ^ n - Fintype.card F ^ i)]
end GlobalTheory.CuspGL
