-- Prove2me | solution 1 for GlobalTheory.WpFam.Act.vmul_vmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:21:40.143322+00:00
-- url     : https://prove2.me/submissions/631a454f-3ffc-4a5f-8555-0e0ccf858fe9

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
theorem _root_.solution {N : ℕ} (x : Fin 2 → ZMod N) (α β : GL (Fin 2) (ZMod N)) :
    _root_.GlobalTheory.WpFam.vmul (_root_.GlobalTheory.WpFam.vmul x α) β = _root_.GlobalTheory.WpFam.vmul x (α * β) := by
  unfold _root_.GlobalTheory.WpFam.vmul
  simp [Matrix.vecMul_vecMul]
end _root_.GlobalTheory.WpFam.Act
end GlobalTheory.WpFam.Act
