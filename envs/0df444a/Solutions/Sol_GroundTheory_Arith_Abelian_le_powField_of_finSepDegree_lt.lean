-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.le_powField_of_finSepDegree_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:44:16.218077+00:00
-- url     : https://prove2.me/submissions/c3092e9d-b003-4688-8a20-67fe97b11419

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobenius
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_IsogenyFrobeniusSep
import Theorems.Thm_GroundTheory_Arith_Abelian_powAdjoin_succ_eq_top
import Theorems.Thm_GroundTheory_Arith_Abelian_finrank_powField
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
open Polynomial WeierstrassCurve WeierstrassCurve.Affine IntermediateField
variable {F : Type*} [Field F] (E : WeierstrassCurve F) (p : ℕ) [hp : Fact p.Prime] [CharP F p]
variable [PerfectRing F p]
namespace GroundTheory.Arith.Abelian
theorem _root_.solution (M : IntermediateField F E.toAffine.FunctionField)
    [FiniteDimensional M E.toAffine.FunctionField]
    (h : Field.finSepDegree M E.toAffine.FunctionField <
      Module.finrank M E.toAffine.FunctionField) : M ≤ powField E p := by
  by_contra hM
  set N := M ⊔ powField E p
  have t := relfinrank_mul_relfinrank (le_sup_right : powField E p ≤ N) (le_top : N ≤ ⊤)
  have hp' : relfinrank (powField E p) ⊤ = p := by rw [relfinrank_top_right, finrank_powField]
  rw [hp'] at t
  rcases (Nat.prime_mul_iff.mp (t ▸ hp.out)) with ⟨-, h1⟩ | ⟨-, h1⟩
  · have hN : N = ⊤ := top_le_iff.mp ((relfinrank_eq_one_iff).mp h1)
    have hT1 : powAdjoin E p M 1 = ⊤ := by
      rw [← IntermediateField.restrictScalars_eq_top_iff (K := F)]
      refine top_le_iff.mp ?_
      rw [← hN]
      refine sup_le ?_ ?_
      · intro m hm
        exact (powAdjoin E p M 1).algebraMap_mem ⟨m, hm⟩
      · rw [powField, adjoin_le_iff]
        rintro w (rfl | rfl)
        · exact (subset_adjoin _ _ (by simp) : genX E ^ p ∈ powAdjoin E p M 1)
        · exact (subset_adjoin _ _ (by simp) : genY E ^ p ∈ powAdjoin E p M 1)
    have hall : ∀ a, 1 ≤ a → powAdjoin E p M a = ⊤ := fun a ha =>
      Nat.le_induction hT1 (fun n _ ih => powAdjoin_succ_eq_top E p M hT1 ih) a ha
    set S := separableClosure M E.toAffine.FunctionField
    haveI : CharP S p := charP_of_injective_algebraMap (algebraMap F S).injective p
    haveI : ExpChar S p := ExpChar.prime hp.out
    obtain ⟨nx, hnx⟩ := IsPurelyInseparable.pow_mem S p (genX E)
    obtain ⟨ny, hny⟩ := IsPurelyInseparable.pow_mem S p (genY E)
    have hmem : ∀ (z : E.toAffine.FunctionField) (n a : ℕ),
        z ^ p ^ n ∈ (algebraMap S E.toAffine.FunctionField).range → n ≤ a → z ^ p ^ a ∈ S := by
      intro z n a hz hn
      obtain ⟨s, hs⟩ := hz
      have e : z ^ p ^ a = (z ^ p ^ n) ^ p ^ (a - n) := by
        rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' hn]
      rw [e, ← hs]
      exact pow_mem s.2 _
    have hle : powAdjoin E p M (nx + ny + 1) ≤ S := by
      rw [powAdjoin, adjoin_le_iff]
      rintro w (rfl | rfl)
      · exact hmem _ nx _ hnx (by omega)
      · exact hmem _ ny _ hny (by omega)
    rw [hall _ (by omega), top_le_iff, separableClosure.eq_top_iff] at hle
    rw [Field.finSepDegree_eq_finrank_of_isSeparable] at h
    exact lt_irrefl _ h
  · exact hM (le_sup_left.trans ((relfinrank_eq_one_iff).mp h1))
end GroundTheory.Arith.Abelian
