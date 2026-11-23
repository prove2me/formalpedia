-- Prove2me | solution 1 for GlobalTheory.WpFam.Act.redGL_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:05.319517+00:00
-- url     : https://prove2.me/submissions/9b3a25d6-1ccb-4274-943f-4100a84b32cb

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
theorem _root_.solution (N : ℕ) (γ δ : SL(2, ℤ)) :
    _root_.GlobalTheory.WpFam.redGL N (γ * δ) = _root_.GlobalTheory.WpFam.redGL N γ * _root_.GlobalTheory.WpFam.redGL N δ := by
  unfold _root_.GlobalTheory.WpFam.redGL
  simp [map_mul]
end _root_.GlobalTheory.WpFam.Act
end GlobalTheory.WpFam.Act
