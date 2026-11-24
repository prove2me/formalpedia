-- Prove2me | solution 1 for GlobalTheory.HeckeTate.mem_of_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:20:43.4567+00:00
-- url     : https://prove2.me/submissions/f0ae7054-f573-4ed1-a29b-7de1f65d0e55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.HeckeTate
namespace GlobalTheory.HeckeTate
theorem _root_.solution {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] (B : M →+ M →+ ℤ)
    (hB : Function.Bijective B) {m c : ℕ} (hm : m ≠ 0) (hg : m ^ Module.finrank ℤ M = c * c) (C : AddSubgroup M)
    (hC : (nsmulAddMonoidHom (α := M) m).range ≤ C)
    (hc : (nsmulAddMonoidHom (α := M) m).range.relIndex C = c)
    (hiso : ∀ x ∈ C, ∀ y ∈ C, (m : ℤ) ∣ B x y) (x : M) (hx : ∀ y ∈ C, (m : ℤ) ∣ B x y) : x ∈ C := by
  classical
  have : NeZero m := ⟨hm⟩
  set K := (nsmulAddMonoidHom (α := M) m).range with hK
  have hKi : K.index = c * c := by rw [hK, AddSubgroup.index_range_nsmul, hg]
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact pow_ne_zero _ hm (by simpa using hg)
  have hCi : C.index = c := by
    have := AddSubgroup.relIndex_mul_index hC
    rw [hc, hKi] at this
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hc0) this
  have : C.FiniteIndex := ⟨hCi ▸ hc0⟩
  let D : AddSubgroup M :=
    { carrier := {x | ∀ y ∈ C, (m : ℤ) ∣ B x y}
      add_mem' := fun {a b} ha hb y hy => by
        rw [map_add, AddMonoidHom.add_apply]; exact (ha y hy).add (hb y hy)
      zero_mem' := fun y _ => by simp
      neg_mem' := fun {a} ha y hy => by
        rw [map_neg, AddMonoidHom.neg_apply]; exact (ha y hy).neg_right }
  have hCD : C ≤ D := fun x hx => hiso x hx
  let f : D → (M ⧸ C →+ ZMod m) := fun x =>
    QuotientAddGroup.lift C ((Int.castAddHom (ZMod m)).comp (B x)) fun y hy =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (x.2 y hy)
  have hf : ∀ (x : D) (y : M), f x (y : M ⧸ C) = (B x y : ZMod m) := fun _ _ => rfl
  let F : D →+ (M ⧸ C →+ ZMod m) := AddMonoidHom.mk' f fun a b => by
    ext y
    simp [hf]
  have hker : F.ker = K.addSubgroupOf D := by
    ext x
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
    constructor
    · intro h
      have h1 : ∀ y, (m : ℤ) ∣ B x y := fun y =>
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by rw [← hf]; exact DFunLike.congr_fun h _)
      choose t ht using h1
      have hm' : (m : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hm
      obtain ⟨z, hz⟩ := hB.2 (AddMonoidHom.mk' t fun a b => mul_left_cancel₀ hm' (by
        rw [← ht, map_add, ht, ht, mul_add]))
      refine ⟨z, hB.1 (AddMonoidHom.ext fun y => ?_)⟩
      rw [ht, nsmulAddMonoidHom_apply, map_nsmul, hz]
      simp
    · rintro ⟨z, hz⟩
      ext y
      change f x y = 0
      rw [hf, ← hz, nsmulAddMonoidHom_apply, map_nsmul]
      simp
  have := Fintype.ofFinite (M ⧸ C)
  let T : (M ⧸ C →+ ZMod m) → AddChar (M ⧸ C) ℂ := fun φ => ZMod.stdAddChar.compAddMonoidHom φ
  have hT : Function.Injective T := fun φ ψ h => AddMonoidHom.ext fun x =>
    ZMod.injective_stdAddChar (DFunLike.congr_fun h x)
  have : Finite (M ⧸ C →+ ZMod m) := Finite.of_injective T hT
  have h1 : K.relIndex D ≤ c := by
    rw [AddSubgroup.relIndex, ← hker, AddSubgroup.index_ker]
    refine (Nat.card_le_card_of_injective _ Subtype.val_injective).trans
      ((Nat.card_le_card_of_injective T hT).trans_eq ?_)
    rw [← hCi, AddSubgroup.index, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]
  have h2 := AddSubgroup.relIndex_mul_relIndex K C D hC hCD
  have h3 : C.relIndex D ≠ 0 := AddSubgroup.FiniteIndex.index_ne_zero
  have h4 : C.relIndex D = 1 := by
    rw [hc] at h2
    have := Nat.pos_of_ne_zero hc0
    have := Nat.pos_of_ne_zero h3
    nlinarith
  exact (AddSubgroup.relIndex_eq_one.1 h4) hx
end GlobalTheory.HeckeTate
