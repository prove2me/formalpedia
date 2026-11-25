-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.nonempty_torsionBy_addEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:28:37.908975+00:00
-- url     : https://prove2.me/submissions/f71b2641-2e45-4d36-ae1a-248ce6f0be11

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_KernelCard
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Torsion
import Theorems.Thm_GroundTheory_Arith_Abelian_nonempty_addEquiv_zmod_prod
import Theorems.Thm_GroundTheory_Arith_Abelian_card_torsionBy
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.Abelian.xOf_neg
attribute [local simp] GroundTheory.Arith.Abelian.xOf_some



set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open AddSubgroup
variable {F : Type*} [Field F] [IsSepClosed F] [DecidableEq F] (W : WeierstrassCurve F) [W.IsElliptic]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {n : ℕ} (hn : (n : F) ≠ 0) :
    Nonempty (torsionBy W.toAffine.Point n ≃+ ZMod n × ZMod n) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  refine nonempty_addEquiv_zmod_prod hn0 (fun x => torsionBy.nsmul x) (card_torsionBy W hn) ?_
  intro m hm
  have hmF : (m : F) ≠ 0 := by
    obtain ⟨k, rfl⟩ := hm
    intro h
    exact hn (by push_cast; rw [h, zero_mul])
  have hm0 : m ≠ 0 := by rintro rfl; simp at hmF
  have : Finite (torsionBy W.toAffine.Point m) :=
    Nat.finite_of_card_ne_zero (by rw [card_torsionBy W hmF]; exact pow_ne_zero _ hm0)
  rw [← card_torsionBy W hmF]
  refine Nat.card_le_card_of_injective (fun x => ⟨x.1.1, torsionBy.nsmul_iff.mpr ?_⟩) ?_
  · have := congrArg Subtype.val x.2
    simpa using this
  · intro x y h
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val h
end GroundTheory.Arith.Abelian
