-- Prove2me | solution 1 for GlobalTheory.exists_primitive_idempotent_map_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:46:54.944717+00:00
-- url     : https://prove2.me/submissions/e650a3e2-bccf-4988-90c3-ada7205167b4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StAvDefs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsPrimitiveIdempotentMapEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A R : Type*} [CommRing A] [IsNoetherianRing A]
    [CommRing R] [IsDomain R] (φ : A →+* R) :
    ∃ e : A, e * e = e ∧ e ≠ 0 ∧ (∀ f : A, f * f = f → f * e = f → f = 0 ∨ f = e) ∧ φ e = 1 := by
  let S : Set (Ideal A) := {I | ∃ e : A, e * e = e ∧ φ e = 1 ∧ I = Ideal.span {1 - e}}
  have hS : S.Nonempty := ⟨_, 1, by simp, by simp, rfl⟩
  obtain ⟨I, ⟨e, he, hφe, rfl⟩, hmax⟩ :=
    (set_has_maximal_iff_noetherian.2 (inferInstance : IsNoetherian A A)) S hS
  have key : ∀ f : A, f * f = f → f * e = f → φ f = 1 → f = e := by
    intro f hf hfe hφf
    have hle : Ideal.span {1 - e} ≤ Ideal.span {1 - f} := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton']
      exact ⟨1 - e, by linear_combination hfe⟩
    have heq : Ideal.span {1 - e} = Ideal.span {1 - f} := by
      by_contra hne
      exact hmax _ ⟨f, hf, hφf, rfl⟩ (lt_of_le_of_ne hle hne)
    have hmem : 1 - f ∈ Ideal.span {1 - e} := heq ▸ Ideal.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
    linear_combination e * hc - hfe + c * he
  refine ⟨e, he, ?_, ?_, hφe⟩
  · rintro rfl
    simp at hφe
  · intro f hf hfe
    have hid : IsIdempotentElem (φ f) := by
      change φ f * φ f = φ f
      rw [← map_mul, hf]
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 hid with h | h
    · left
      have := key (e - f) (by linear_combination he + hf - 2 * hfe)
        (by linear_combination he - hfe) (by rw [map_sub, h, hφe, sub_zero])
      linear_combination -this
    · exact Or.inr (key f hf hfe h)
end GlobalTheory
