-- Prove2me | solution 1 for GlobalTheory.T.modularGroup_rowVec_and_conj_rightActions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:37:14.26645+00:00
-- url     : https://prove2.me/submissions/c246cb7f-d132-482d-a03f-73e1993f6623

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModularGroupRowVecAndConjRightActions
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModularGroupRowVecAndConjRightActionsStatement
import Theorems.Thm_GlobalTheory_WpFam_Act_rightActions


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (N : ℕ), IsRAct (vact N) ∧ (∀ D, IsRAct (gact N D)) ∧ (∀ (x : Fin 2 → ZMod N) α β, vmul (vmul x α) β = vmul x (α * β)) ∧ (∀ x : Fin 2 → ZMod N, vmul x 1 = x) ∧ (∀ (x : Fin 2 → ZMod N) α, vmul x α = 0 ↔ x = 0) ∧ (∀ (M : ℕ) (x : Fin 2 → ZMod N) α, vmul (M • x) α = M • vmul x α) ∧ (∀ (x : Fin 2 → ZMod N) (a : (ZMod N)ˣ), vmul x (dg a) = ![x 0, (a : ZMod N) * x 1]) ∧ (∀ γ δ, redGL N (γ * δ) = redGL N γ * redGL N δ) ∧ redGL N 1 = 1 := by
  first | exact @GlobalTheory.WpFam.Act.rightActions | exact GlobalTheory.WpFam.Act.rightActions | (intros; apply GlobalTheory.WpFam.Act.rightActions <;> assumption)
end _root_.GlobalTheory.T
