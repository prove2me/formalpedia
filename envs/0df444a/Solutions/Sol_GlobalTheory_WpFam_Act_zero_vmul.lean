-- Prove2me | solution 1 for GlobalTheory.WpFam.Act.zero_vmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:36:11.39737+00:00
-- url     : https://prove2.me/submissions/ebf76a23-24a6-48a6-8a84-c9d5ad5f37b1

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
namespace GlobalTheory.WpFam.Act
theorem _root_.solution {N : ℕ} (α : GL (Fin 2) (ZMod N)) : vmul (0 : Fin 2 → ZMod N) α = 0 := by
  simp only [vmul, Matrix.zero_vecMul]
end GlobalTheory.WpFam.Act
