-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.exists_zsmul_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:42:48.858813+00:00
-- url     : https://prove2.me/submissions/7faa74c7-d14b-41c5-9495-6b658629ac86

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Theorems.Thm_P2M_GroundTheory_Arith_Abelian_exists_equation_of___Sq_ne_zero_539fa7a3f801
import Theorems.Thm_GroundTheory_Arith_Abelian_infinite_of_isSepClosed
import Theorems.Thm_P2M_GroundTheory_Arith_Abelian__Sq_ne_zero_of_ne_zero_fd3fba5d47fb
import Theorems.Thm_P2M_GroundTheory_Arith_Abelian___Sq_ne_zero_d2a733e9e1e7
import Theorems.Thm_GroundTheory_Arith_Abelian_zsmul_eq_zero_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
variable {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution [IsSepClosed F] [DecidableEq F] {n : ℤ} (hn : n ≠ 0) :
    ∃ P : W.toAffine.Point, n • P ≠ 0 := by
  have := infinite_of_isSepClosed F
  have hprod : W.ΨSq n * W.Ψ₂Sq ≠ 0 := mul_ne_zero (ΨSq_ne_zero_of_ne_zero W hn) (Ψ₂Sq_ne_zero W)
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (W.ΨSq n * W.Ψ₂Sq).roots.toFinset
  rw [Multiset.mem_toFinset, mem_roots hprod, IsRoot, eval_mul, mul_eq_zero, not_or] at hx
  obtain ⟨y, hy⟩ := exists_equation_of_Ψ₂Sq_ne_zero W hx.2
  have h : W.toAffine.Nonsingular x y := equation_iff_nonsingular.mp hy
  exact ⟨.some x y h, fun h0 => hx.1 ((zsmul_eq_zero_iff W h n).mp h0)⟩
end GroundTheory.Arith.Abelian
