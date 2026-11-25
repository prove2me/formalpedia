-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.card_zsmul_eq_zero_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:05:18.480727+00:00
-- url     : https://prove2.me/submissions/795ada54-5020-4e74-b110-0f78887698f7

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Isogeny
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius
import Theorems.Thm_GroundTheory_Arith_Abelian_natDegree_yPoly
import Theorems.Thm_GroundTheory_Arith_Abelian_yPoly_ne_zero
import Theorems.Thm_GroundTheory_Arith_Abelian_isRoot_yPoly
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_neg
import Theorems.Thm_GroundTheory_Arith_Abelian_xOf_some
import Theorems.Thm_P2M_GroundTheory_Arith_Abelian_zsmul_eq_zero_iff__Sq_274c34b39eaa
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
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F)
namespace GroundTheory.Arith.Abelian
theorem _root_.solution {n : ℤ} (hn : E.ΨSq n ≠ 0) :
    Nat.card {P : E.toAffine.Point // n • P = 0} ≤ 1 + 2 * (E.ΨSq n).roots.toFinset.card := by
  classical
  set S := (E.ΨSq n).roots.toFinset
  set T : Finset (F × F) := S.biUnion fun x => ((yPoly E x).roots.toFinset).image fun y => (x, y)
  have hT : T.card ≤ 2 * S.card := by
    refine (Finset.card_biUnion_le).trans ?_
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun x _ => ?_
    refine Finset.card_image_le.trans ?_
    refine (Multiset.toFinset_card_le _).trans ?_
    exact (card_roots' _).trans (natDegree_yPoly E x).le
  let f : {P : E.toAffine.Point // n • P = 0} → Option (F × F) := fun P =>
    match P.1 with
    | .zero => none
    | .some x y _ => some (x, y)
  have hf : Function.Injective f := by
    rintro ⟨P, hP⟩ ⟨Q, hQ⟩ h
    cases P with
    | zero =>
      cases Q with
      | zero => rfl
      | some x y _ => exact absurd h (by simp [f])
    | some x y hxy =>
      cases Q with
      | zero => exact absurd h (by simp [f])
      | some x' y' _ =>
        simp only [f, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
  have hrange : Set.range f ⊆ (T.insertNone : Set (Option (F × F))) := by
    rintro _ ⟨⟨P, hP⟩, rfl⟩
    cases P with
    | zero => exact Finset.none_mem_insertNone
    | some x y hxy =>
      have hx : (E.ΨSq n).eval x = 0 := by
        rcases (zsmul_eq_zero_iff_ΨSq E n _).mp hP with h0 | ⟨x', y', h', he, hx'⟩
        · exact absurd h0 (Point.some_ne_zero hxy)
        · rw [Point.some.injEq] at he; rw [he.1]; exact hx'
      show some (x, y) ∈ (T.insertNone : Set _)
      rw [Finset.mem_coe, Finset.some_mem_insertNone]
      simp only [T, S, Finset.mem_biUnion, Finset.mem_image, Multiset.mem_toFinset]
      refine ⟨x, (mem_roots hn).mpr hx, y, ?_, rfl⟩
      exact (mem_roots (yPoly_ne_zero E x)).mpr (isRoot_yPoly E hxy.1)
  calc Nat.card {P : E.toAffine.Point // n • P = 0}
      = Nat.card (Set.range f) := (Nat.card_range_of_injective hf).symm
    _ ≤ Nat.card (T.insertNone : Set (Option (F × F))) :=
        Nat.card_mono (Finset.finite_toSet _) hrange
    _ = T.card + 1 := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_insertNone]
    _ ≤ 1 + 2 * S.card := by omega
end GroundTheory.Arith.Abelian
