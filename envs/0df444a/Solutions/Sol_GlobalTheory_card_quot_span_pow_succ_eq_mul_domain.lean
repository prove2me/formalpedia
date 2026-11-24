-- Prove2me | solution 1 for GlobalTheory.card_quot_span_pow_succ_eq_mul_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:25:55.344968+00:00
-- url     : https://prove2.me/submissions/f0f33007-e153-4f1f-bdfe-07e64f409536

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardQuotSpanPowEqCardPowDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (O : Type) [CommRing O] [IsDomain O] (t : O) (ht : t ≠ 0)
    (r : ℕ) :
    Nat.card (O ⧸ Ideal.span {t ^ (r + 1)}) =
      Nat.card (O ⧸ Ideal.span {t}) * Nat.card (O ⧸ Ideal.span {t ^ r}) := by
  set H := (Ideal.span {t ^ (r + 1)}).toAddSubgroup with hH
  set K := (Ideal.span {t ^ r}).toAddSubgroup with hK
  have hHK : H ≤ K := by
    intro x hx
    simp only [hH, hK, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton] at hx ⊢
    exact (pow_dvd_pow t (Nat.le_succ r)).trans hx
  have e1 : Nat.card (O ⧸ Ideal.span {t ^ (r + 1)}) = H.index := rfl
  have e2 : Nat.card (O ⧸ Ideal.span {t ^ r}) = K.index := rfl
  have e3 : Nat.card (O ⧸ Ideal.span {t}) = (Ideal.span {t}).toAddSubgroup.index := rfl
  rw [e1, e2, e3, ← AddSubgroup.relIndex_mul_index hHK]
  congr 1
  let φ : O →+ K :=
    { toFun := fun x => ⟨t ^ r * x, by
        simp only [hK, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]
        exact dvd_mul_right _ _⟩
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp [mul_add] }
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ Ideal.span {t ^ r} := hy
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hy'
    exact ⟨a, rfl⟩
  have hc : (H.addSubgroupOf K).comap φ = (Ideal.span {t}).toAddSubgroup := by
    ext x
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, hH,
      Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]
    change t ^ (r + 1) ∣ t ^ r * x ↔ t ∣ x
    rw [pow_succ]
    exact mul_dvd_mul_iff_left (pow_ne_zero r ht)
  rw [AddSubgroup.relIndex, ← hc, AddSubgroup.index_comap_of_surjective _ hφ]
end GlobalTheory
