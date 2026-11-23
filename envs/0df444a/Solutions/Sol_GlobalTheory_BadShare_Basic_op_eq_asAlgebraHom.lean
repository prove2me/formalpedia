-- Prove2me | solution 1 for GlobalTheory.BadShare.Basic.op_eq_asAlgebraHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:00.122075+00:00
-- url     : https://prove2.me/submissions/3bef4257-a21f-4977-a70e-597c825074ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial

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
theorem _root_.solution {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (e : G → ℂ) :
    op ρ e = ρ.asAlgebraHom (alg e) := by
  simp [op, alg, Representation.asAlgebraHom_single]
end GlobalTheory.BadShare.Basic
