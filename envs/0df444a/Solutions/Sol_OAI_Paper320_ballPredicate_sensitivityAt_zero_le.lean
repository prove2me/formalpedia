-- Prove2me | solution 1 for OAI.Paper320.ballPredicate_sensitivityAt_zero_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T02:17:53.642317+00:00
-- url     : https://prove2.me/submissions/fff2919f-8e7c-4a73-a541-1aeda0b6da41

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/HammingBase.lean:L91-L113
-- (upload_full_project.md Phase 4): solution for node OAI.Paper320.ballPredicate_sensitivityAt_zero_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase

-- ---- from OAI.Combinatorics.Sensitivity.HammingBase ----
namespace OAI

/-! Hamming balls used by the initial nested predicates. -/

noncomputable section
open scoped Classical

namespace Paper320

variable {I C : Type} [Fintype I]

theorem hammingDist_flip_self (x : I → Bool) (i : I) :
    hammingDist x (flip x {i}) = 1 := by
  have h : (Finset.univ.filter fun j => x j ≠ flip x {i} j) = {i} := by
    ext j
    by_cases hj : j = i
    · subst j
      cases x i <;> simp [flip]
    · simp [flip, hj]
  rw [hammingDist, h]
  simp

theorem hammingDist_le_flip_add_one (x z : I → Bool) (i : I) :
    hammingDist x z ≤ hammingDist (flip x {i}) z + 1 := by
  have h := hammingDist_triangle x (flip x {i}) z
  rw [hammingDist_flip_self] at h
  omega

theorem hammingDist_flip_eq_add_one (x z : I → Bool) (i : I) (hi : x i = z i) :
    hammingDist (flip x {i}) z = hammingDist x z + 1 := by
  have h : (Finset.univ.filter fun j => flip x {i} j ≠ z j) =
      insert i (Finset.univ.filter fun j => x j ≠ z j) := by
    ext j
    by_cases hj : j = i
    · subst j
      cases hx : x i <;> simp_all [flip]
    · simp [flip, hj]
  rw [hammingDist, h, Finset.card_insert_of_notMem]
  · rfl
  · simp [hi]

theorem ballPredicate_eq_true [Fintype C] (centers : C → I → Bool) (R : ℕ)
    (x : I → Bool) :
    ballPredicate centers R x = true ↔ ∃ c, hammingDist x (centers c) ≤ R := by
  simp [ballPredicate]

theorem ballPredicate_zero_flip [Fintype C] (centers : C → I → Bool) (R : ℕ)
    (x : I → Bool) (i : I) (hx : ballPredicate centers R x = false)
    (hi : ballPredicate centers R (flip x {i}) = true) :
    ∃ c, hammingDist x (centers c) = R + 1 ∧ x i ≠ centers c i := by
  rcases (ballPredicate_eq_true centers R (flip x {i})).1 hi with ⟨c, hc⟩
  have hn : ¬ hammingDist x (centers c) ≤ R := by
    intro h
    have := (ballPredicate_eq_true centers R x).2 ⟨c, h⟩
    simp_all
  have hd := hammingDist_le_flip_add_one x (centers c) i
  refine ⟨c, by omega, ?_⟩
  intro heq
  rw [hammingDist_flip_eq_add_one x (centers c) i heq] at hc
  omega

theorem near_center_unique (centers : C → I → Bool) (R : ℕ)
    (hsep : ∀ a b, a ≠ b → 2 * (R + 1) < hammingDist (centers a) (centers b))
    (x : I → Bool) {a b : C} (ha : hammingDist x (centers a) ≤ R + 1)
    (hb : hammingDist x (centers b) ≤ R + 1) : a = b := by
  by_contra h
  have hs := hsep a b h
  have ht := hammingDist_triangle (centers a) x (centers b)
  rw [hammingDist_comm (centers a) x] at ht
  omega

theorem ballPredicate_sensitivityAt_zero_le [Fintype C]
    (centers : C → I → Bool) (R : ℕ)
    (hsep : ∀ a b, a ≠ b → 2 * (R + 1) < hammingDist (centers a) (centers b))
    (x : I → Bool) (hx : ballPredicate centers R x = false) :
    sensitivityAt (ballPredicate centers R) x ≤ R + 1 := by
  let A := Finset.univ.filter fun i =>
    ballPredicate centers R (flip x {i}) ≠ ballPredicate centers R x
  change A.card ≤ R + 1
  by_cases hA : A.Nonempty
  · obtain ⟨i, hi⟩ := hA
    have hi' : ballPredicate centers R (flip x {i}) = true := by
      simpa [A, hx] using hi
    obtain ⟨c, hc, _⟩ := ballPredicate_zero_flip centers R x i hx hi'
    have hsub : A ⊆ Finset.univ.filter fun j => x j ≠ centers c j := by
      intro j hj
      have hj' : ballPredicate centers R (flip x {j}) = true := by
        simpa [A, hx] using hj
      obtain ⟨c', hc', hjc⟩ := ballPredicate_zero_flip centers R x j hx hj'
      have heq : c' = c := near_center_unique centers R hsep x (by omega) (by omega)
      simpa [heq] using hjc
    exact (Finset.card_le_card hsub).trans_eq hc
  · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
    simp

end Paper320

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper320
open scoped Classical
variable {I C : Type} [Fintype I]

theorem solution [Fintype C]
    (centers : C → I → Bool) (R : ℕ)
    (hsep : ∀ a b, a ≠ b → 2 * (R + 1) < hammingDist (centers a) (centers b))
    (x : I → Bool) (hx : ballPredicate centers R x = false) :
    sensitivityAt (ballPredicate centers R) x ≤ R + 1 := by
  first
    | exact OAI.Paper320.ballPredicate_sensitivityAt_zero_le centers R hsep x hx
    | exact OAI.Paper320.ballPredicate_sensitivityAt_zero_le
    | (apply OAI.Paper320.ballPredicate_sensitivityAt_zero_le <;> assumption)
    | (intros; apply OAI.Paper320.ballPredicate_sensitivityAt_zero_le <;> assumption)
