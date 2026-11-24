-- Prove2me | solution 1 for GlobalTheory.HeckeTate.exists_unimod_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:19:11.300114+00:00
-- url     : https://prove2.me/submissions/0ebfd8c2-693b-4dbc-8bfa-8c8bad5a4512

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUnimodDiv
import Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_adj
import Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_bij
import Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_ext
import Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_skew


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
theorem _root_.solution {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] {σ : R ≃+* R}
    {B : M →+ M →+ ℤ} (h : IsUnimod σ B) {m : ℕ} (hm : m ≠ 0) (C : Submodule R M) (hC : ∀ a, m • a ∈ C)
    (hiso : ∀ x ∈ C, ∀ y ∈ C, (m : ℤ) ∣ B x y) (horth : ∀ x, (∀ y ∈ C, (m : ℤ) ∣ B x y) → x ∈ C) :
    ∃ B' : C →+ C →+ ℤ, IsUnimod σ B' ∧ ∀ x y : C, B x y = m * B' x y := by
  have hm' : (m : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hm
  choose t ht using fun x y : C => hiso x x.2 y y.2
  let B' : C →+ C →+ ℤ := AddMonoidHom.mk'
    (fun x => AddMonoidHom.mk' (t x) fun a b => mul_left_cancel₀ hm' (by
      rw [mul_add, ← ht, ← ht, ← ht, Submodule.coe_add, map_add]))
    fun a b => AddMonoidHom.ext fun y => mul_left_cancel₀ hm' (by
      change m * t (a + b) y = m * (t a y + t b y)
      rw [mul_add, ← ht, ← ht, ← ht, Submodule.coe_add, map_add, AddMonoidHom.add_apply])
  have hB' : ∀ x y : C, B x y = m * B' x y := ht
  refine ⟨B', ⟨fun x y => mul_left_cancel₀ hm' ?_, fun a x y => mul_left_cancel₀ hm' ?_, ?_, fun f => ?_⟩, hB'⟩
  · rw [mul_neg, ← hB', ← hB', h.skew]
  · rw [← hB', ← hB', Submodule.coe_smul, Submodule.coe_smul, h.adj]
  · rw [injective_iff_map_eq_zero]
    intro x hx
    apply Subtype.ext
    apply (injective_iff_map_eq_zero _).1 h.bij.1
    ext a
    have := hB' x ⟨m • a, hC a⟩
    rw [hx, map_nsmul] at this
    simpa [hm] using this
  · let u : M →+ C := AddMonoidHom.mk' (fun a => ⟨m • a, hC a⟩) fun a b => Subtype.ext (smul_add _ _ _)
    obtain ⟨x, hx⟩ := h.bij.2 (f.comp u)
    have key : ∀ y : C, B x y = m * f y := fun y => by
      rw [hx, ← nsmul_eq_mul, ← map_nsmul]
      rfl
    refine ⟨⟨x, horth x fun y hy => ⟨_, key ⟨y, hy⟩⟩⟩, AddMonoidHom.ext fun y => mul_left_cancel₀ hm' ?_⟩
    rw [← hB', key]
end GlobalTheory.HeckeTate
