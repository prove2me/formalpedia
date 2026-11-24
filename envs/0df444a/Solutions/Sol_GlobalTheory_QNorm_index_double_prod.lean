-- Prove2me | solution 1 for GlobalTheory.QNorm.index_double_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:43:53.822958+00:00
-- url     : https://prove2.me/submissions/239d8ce4-772e-48a4-a9ba-83a20589c0b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexSqsTopOfFg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution (L T : Type) [AddCommGroup L] [AddCommGroup T] [Module.Free ℤ L]
    [Module.Finite ℤ L] [Finite T] :
    (nsmulAddMonoidHom (α := L × T) 2).range.index =
      2 ^ Module.finrank ℤ (L × T) * Nat.card (nsmulAddMonoidHom (α := L × T) 2).ker := by
  have h1 : (nsmulAddMonoidHom (α := L × T) 2).range =
      ((nsmulAddMonoidHom (α := L) 2).range).prod (nsmulAddMonoidHom (α := T) 2).range := by
    ext ⟨x, y⟩
    simp only [AddMonoidHom.mem_range, AddSubgroup.mem_prod, nsmulAddMonoidHom_apply]
    constructor
    · rintro ⟨⟨a, b⟩, h⟩
      exact ⟨⟨a, congrArg Prod.fst h⟩, ⟨b, congrArg Prod.snd h⟩⟩
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      exact ⟨(a, b), Prod.ext ha hb⟩
  have h2 : (nsmulAddMonoidHom (α := L × T) 2).ker =
      (⊥ : AddSubgroup L).prod (nsmulAddMonoidHom (α := T) 2).ker := by
    ext ⟨x, y⟩
    have hx : 2 • x = 0 ↔ x = 0 := by
      rw [← natCast_zsmul, smul_eq_zero]; simp
    simp [AddMonoidHom.mem_ker, AddSubgroup.mem_prod, hx]
  have h3 : Module.finrank ℤ (L × T) = Module.finrank ℤ L := by
    have hT : Module.rank ℤ T = 0 := by
      rw [rank_eq_zero_iff]
      intro x
      refine ⟨(Nat.card T : ℤ), by exact_mod_cast Nat.card_pos.ne', ?_⟩
      simp
    have hq := Submodule.rank_quotient_add_rank (LinearMap.ker (LinearMap.fst ℤ L T))
    have e1 := (LinearMap.quotKerEquivOfSurjective (LinearMap.fst ℤ L T)
      LinearMap.fst_surjective).rank_eq
    have e2 : Module.rank ℤ (LinearMap.ker (LinearMap.fst ℤ L T)) = 0 := by
      rw [LinearMap.ker_fst, rank_range_of_injective _ LinearMap.inr_injective, hT]
    unfold Module.finrank
    rw [← hq, e1, e2, add_zero]
  have h4 : (nsmulAddMonoidHom (α := T) 2).range.index =
      Nat.card (nsmulAddMonoidHom (α := T) 2).ker := by
    have a := AddSubgroup.card_mul_index (nsmulAddMonoidHom (α := T) 2).range
    have b := AddSubgroup.card_mul_index (nsmulAddMonoidHom (α := T) 2).ker
    rw [AddSubgroup.index_ker] at b
    have hpos : 0 < Nat.card (nsmulAddMonoidHom (α := T) 2).range := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [a, mul_comm, b]
  rw [h1, h2, h3, AddSubgroup.index_prod, AddSubgroup.index_range_nsmul, h4,
    Nat.card_congr (AddSubgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
  simp
end GlobalTheory.QNorm
