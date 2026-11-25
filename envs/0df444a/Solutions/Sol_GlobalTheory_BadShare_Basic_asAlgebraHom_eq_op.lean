-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.asAlgebraHom_eq_op
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:33:29.828989+00:00
-- url     : https://prove2.me/submissions/3346dce6-7136-4100-91e5-c3e3605c28bd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Theorems.Thm_GlobalTheory_BadShare_Basic_alg_coeff
import Theorems.Thm_GlobalTheory_BadShare_Basic_op_eq_asAlgebraHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime] (N : ℕ)
variable {g N}
open GlobalTheory.BadShare.Basic
variable {G : Type} [Group G] [Fintype G]
namespace GlobalTheory.BadShare.Basic
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (a : MonoidAlgebra ℂ G) :
    ρ.asAlgebraHom a = op ρ (fun x => a.coeff x) := by
  rw [op_eq_asAlgebraHom, alg_coeff]
end GlobalTheory.BadShare.Basic
