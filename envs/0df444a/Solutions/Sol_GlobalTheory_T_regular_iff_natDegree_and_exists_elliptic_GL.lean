-- Prove2me | solution 1 for GlobalTheory.T.regular_iff_natDegree_and_exists_elliptic_GL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:44:51.329166+00:00
-- url     : https://prove2.me/submissions/1de4c4c8-ed87-4bf1-9007-8e72f6375f4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RegularIffNatDegreeAndExistsEllipticGL
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RegularIffNatDegreeAndExistsEllipticGLStatement
import Theorems.Thm_GlobalTheory_CuspGL_regular_iff_natDegree_and_exists_elliptic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 0 < n → ∀ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, ((∀ e : ℕ, 0 < e → e < n → α ^ Nat.card F ^ e ≠ α) ↔ (minpoly F α).natDegree = n) ∧ ((minpoly F α).natDegree = n → ∃ x : GL (Fin n) F, Matrix.charpoly (x : Matrix (Fin n) (Fin n) F) = minpoly F α) := by
  first | exact @GlobalTheory.CuspGL.regular_iff_natDegree_and_exists_elliptic | exact GlobalTheory.CuspGL.regular_iff_natDegree_and_exists_elliptic | (intros; apply GlobalTheory.CuspGL.regular_iff_natDegree_and_exists_elliptic <;> assumption)
end _root_.GlobalTheory.T
