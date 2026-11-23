-- Prove2me | solution 1 for GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:02.7858+00:00
-- url     : https://prove2.me/submissions/aef872ce-b060-4863-b323-debb9b445c1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_RootPowerSumCharacterAdditiveAndXSubOnePow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution :
    ∀ (F : Type) [Field F] (θ : AlgebraicClosure F →* ℂ) (k : ℕ),
      IsAdditive (rootSum θ k) ∧ ∀ j : ℕ, rootSum θ k ((X - C 1 : F[X]) ^ j) = j := by
  intro F _ θ k
  refine ⟨fun P Q hP hQ => ?_, fun j => ?_⟩
  · unfold rootSum
    rw [Polynomial.map_mul, Polynomial.roots_mul ((hP.map _).mul (hQ.map _)).ne_zero,
      Multiset.map_add, Multiset.sum_add]
  · unfold rootSum
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      Polynomial.roots_pow, Polynomial.roots_X_sub_C, Multiset.map_nsmul, Multiset.sum_nsmul]
    simp
end GlobalTheory.CuspGL
