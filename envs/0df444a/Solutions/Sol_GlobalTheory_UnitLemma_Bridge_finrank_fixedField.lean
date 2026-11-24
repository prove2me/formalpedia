-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Bridge.finrank_fixedField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:05:10.690331+00:00
-- url     : https://prove2.me/submissions/b71aba69-dbef-46db-b8c5-51d20c9b6b9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyCompactOfComplete
import Theorems.Thm_GlobalTheory_UnitLemma_Bridge_mem_fixedField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Bridge
namespace GlobalTheory.UnitLemma.Bridge
theorem _root_.solution {E : Type} [Field E] [CharZero E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x)
    (hne : ∃ y, c y ≠ y) : Module.finrank (fixedField c) E = 2 := by
  obtain ⟨y, hy⟩ := hne
  set d := y - c y with hd
  have hd0 : d ≠ 0 := sub_ne_zero.2 hy.symm
  have hcd : c d = -d := by rw [hd, map_sub, hc]; ring
  let f : (fixedField c × fixedField c) →ₗ[fixedField c] E :=
    { toFun := fun p => (p.1 : E) + (p.2 : E) * d
      map_add' := by intro p q; simp; ring
      map_smul' := by
        intro a p
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply, Subfield.coe_mul]
        change _ = (a : E) * _
        ring }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨a, b⟩ h
    have h1 : (a : E) + (b : E) * d = 0 := h
    have h2 := congrArg c h1
    rw [map_add, map_mul, (mem_fixedField c _).1 a.2, (mem_fixedField c _).1 b.2, hcd, map_zero] at h2
    have ha : (a : E) = 0 := by linear_combination (h1 + h2) / 2
    have hb : (b : E) * d = 0 := by linear_combination (h1 - h2) / 2
    have hb' : (b : E) = 0 := (mul_eq_zero.1 hb).resolve_right hd0
    exact Prod.ext (Subtype.ext ha) (Subtype.ext hb')
  have hsurj : Function.Surjective f := by
    intro z
    refine ⟨(⟨(z + c z) / 2, ?_⟩, ⟨(z - c z) / (2 * d), ?_⟩), ?_⟩
    · rw [mem_fixedField, map_div₀, map_add, hc, map_ofNat, add_comm]
    · rw [mem_fixedField, map_div₀, map_sub, hc, map_mul, map_ofNat, hcd]
      field_simp
      ring
    · change (z + c z) / 2 + (z - c z) / (2 * d) * d = z
      field_simp
      ring
  rw [← (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).finrank_eq]
  simp
end GlobalTheory.UnitLemma.Bridge
