-- Prove2me | solution 1 for GlobalTheory.T.charpolyEndomorphismDensityGL_recursion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:34:47.268489+00:00
-- url     : https://prove2.me/submissions/f4b734aa-ec77-441c-9bc6-e93252972339

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyEndomorphismDensityGLRecursion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharpolyEndomorphismDensityGLRecursionStatement
import Theorems.Thm_GlobalTheory_CuspGL_mu_rec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (P : F[X]), P.Monic → (Nat.card F : ℂ) ^ P.natDegree * mu P = conv (fun _ => 1) mu P ∧ mu (1 : F[X]) = 1 := by
  first | exact @GlobalTheory.CuspGL.mu_rec | exact GlobalTheory.CuspGL.mu_rec | (intros; apply GlobalTheory.CuspGL.mu_rec <;> assumption)
end _root_.GlobalTheory.T
