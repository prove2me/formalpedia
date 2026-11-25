-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.card_torsionBy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:17:22.562809+00:00
-- url     : https://prove2.me/submissions/525aa8a0-7699-4370-94f6-6438cf97b26b

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Torsion
import Theorems.Thm_GroundTheory_Arith_Abelian_card_zsmul_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open AddSubgroup
variable {F : Type*} [Field F] [IsSepClosed F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {n : ℕ} (hn : (n : F) ≠ 0) :
    Nat.card (torsionBy W.toAffine.Point n) = n ^ 2 := by
  classical
  have h := card_zsmul_eq_zero W (n := (n : ℤ)) (by exact_mod_cast hn)
  rw [Int.natAbs_natCast] at h
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun P => Submodule.mem_torsionBy_iff _ _)
end GroundTheory.Arith.Abelian
