-- Prove2me | solution 1 for GlobalTheory.T.eq_of_weierstrassP_derivWeierstrassP_torsion_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:53:59.690919+00:00
-- url     : https://prove2.me/submissions/da2d9054-0c92-486f-ab02-7fae203bf89b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqOfWeierstrassPDerivWeierstrassPTorsionEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqOfWeierstrassPDerivWeierstrassPTorsionEqStatement
import Theorems.Thm_GlobalTheory_WpFam_wp_wpd_separate


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
theorem _root_.solution : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (x y : Fin 2 → ZMod N), x ≠ 0 → y ≠ 0 → wp N x τ = wp N y τ → wpd N x τ = wpd N y τ → x = y := by
  first | exact @GlobalTheory.WpFam.wp_wpd_separate | exact GlobalTheory.WpFam.wp_wpd_separate | (intros; apply GlobalTheory.WpFam.wp_wpd_separate <;> assumption)
end _root_.GlobalTheory.T
