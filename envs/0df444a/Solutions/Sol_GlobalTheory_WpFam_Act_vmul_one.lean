-- Prove2me | solution 1 for GlobalTheory.WpFam.Act.vmul_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:17:54.242825+00:00
-- url     : https://prove2.me/submissions/69b2ad3b-d8a1-4146-9c61-4bdf551153a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModularGroupRowVecAndConjRightActions

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
open GlobalTheory GlobalTheory.WpFam GlobalTheory.WpFam.Act
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
namespace GlobalTheory.WpFam.Act
namespace _root_.GlobalTheory.WpFam.Act
theorem _root_.solution {N : ℕ} (x : Fin 2 → ZMod N) : _root_.GlobalTheory.WpFam.vmul x 1 = x := by
  unfold _root_.GlobalTheory.WpFam.vmul
  simp
end _root_.GlobalTheory.WpFam.Act
end GlobalTheory.WpFam.Act
