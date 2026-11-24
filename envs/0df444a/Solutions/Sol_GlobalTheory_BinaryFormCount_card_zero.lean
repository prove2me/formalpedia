-- Prove2me | solution 1 for GlobalTheory.BinaryFormCount.card_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:08:22.27553+00:00
-- url     : https://prove2.me/submissions/0969d2c0-be81-43e8-ae8f-f75d01e7900d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_SelfDualUnramifiedPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NcardSumBinaryFormNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory GlobalTheory.BinaryFormCount
open Finset
variable {k : Type} [Field k] [Fintype k] [DecidableEq k]
namespace GlobalTheory.BinaryFormCount
theorem _root_.solution {t n : k} (hD : t ^ 2 - 4 * n ≠ 0) {η : ℝ}
    (h1 : (∃ r : k, r ^ 2 - t * r + n = 0) → η = 1)
    (h2 : (¬ ∃ r : k, r ^ 2 - t * r + n = 0) → η = -1) :
    (#{p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = 0} : ℝ)
      = Fintype.card k - η + η * Fintype.card k := by
  by_cases h : ∃ r : k, r ^ 2 - t * r + n = 0
  · rw [h1 h]
    obtain ⟨r, hr⟩ := h
    have hne : t - 2 * r ≠ 0 := by
      intro h0
      apply hD
      linear_combination (t - 2 * r) * h0 - 4 * hr
    have e : ({p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = 0} : Finset (k × k))
        = (univ.image fun b : k => (-r * b, b)) ∪ (univ.image fun b : k => (-(t - r) * b, b)) := by
      ext ⟨a, b⟩
      simp only [mem_filter, mem_univ, true_and, mem_union, mem_image, Prod.mk.injEq,
        exists_eq_right]
      constructor
      · intro hab
        have : (-r * b - a) * (-(t - r) * b - a) = 0 := by linear_combination hab - b ^ 2 * hr
        rcases mul_eq_zero.1 this with h | h
        · exact Or.inl (sub_eq_zero.1 h)
        · exact Or.inr (sub_eq_zero.1 h)
      · rintro (rfl | rfl) <;> linear_combination b ^ 2 * hr
    have i : (univ.image fun b : k => (-r * b, b)) ∩ (univ.image fun b : k => (-(t - r) * b, b))
        = {((0 : k), (0 : k))} := by
      ext ⟨a, b⟩
      simp only [mem_univ, true_and, mem_inter, mem_image, Prod.mk.injEq,
        exists_eq_right, mem_singleton]
      constructor
      · rintro ⟨rfl, h⟩
        have : (t - 2 * r) * b = 0 := by linear_combination -h
        have hb := (mul_eq_zero.1 this).resolve_left hne
        simp [hb]
      · rintro ⟨rfl, rfl⟩; simp
    have := Finset.card_union_add_card_inter (univ.image fun b : k => (-r * b, b))
      (univ.image fun b : k => (-(t - r) * b, b))
    rw [i, ← e, card_image_of_injective _ (fun a b h => congrArg Prod.snd h),
      card_image_of_injective _ (fun a b h => congrArg Prod.snd h), card_singleton,
      card_univ] at this
    have h3 := congrArg (Nat.cast : ℕ → ℝ) this
    push_cast at h3
    linarith
  · rw [h2 h]
    have e : ({p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = 0} : Finset (k × k))
        = {((0 : k), (0 : k))} := by
      ext ⟨a, b⟩
      simp only [mem_filter, mem_univ, true_and, Prod.mk.injEq, mem_singleton]
      constructor
      · intro hab
        by_cases hb : b = 0
        · subst hb
          simpa using hab
        · refine (h ⟨-a / b, ?_⟩).elim
          field_simp
          linear_combination hab
      · rintro ⟨rfl, rfl⟩; simp
    rw [e, card_singleton]
    push_cast
    ring
end GlobalTheory.BinaryFormCount
