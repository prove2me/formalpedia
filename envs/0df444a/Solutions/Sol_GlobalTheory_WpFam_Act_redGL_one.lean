-- Prove2me | solution 1 for GlobalTheory.WpFam.Act.redGL_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:05.961885+00:00
-- url     : https://prove2.me/submissions/eb2cba8c-d420-4bd3-94fd-fff9386990ec

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
theorem _root_.solution (N : ℕ) : _root_.GlobalTheory.WpFam.redGL N 1 = 1 := by
  unfold _root_.GlobalTheory.WpFam.redGL
  simp
end _root_.GlobalTheory.WpFam.Act
end GlobalTheory.WpFam.Act
