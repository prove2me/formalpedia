-- Prove2me | solution 1 for OAI.LaughlinGap.RealOccupation.Certificate21.fibers_checked
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T03:36:05.618359+00:00
-- url     : https://prove2.me/submissions/3fcd427c-44aa-4069-8fcc-78c067a0eb09

import Mathlib
import Definitions.Def_OAIQ030L028
import Definitions.Def_OAIQ030L031

section
-- module Solutions.OAIQ030_LG.LaughlinGap_FastFourKeys
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fast Four Keys. -/

noncomputable section


namespace LaughlinGap.RealOccupation

lemma checkFourTerms_sound {D : ℕ} (P : FourTerm D → Prop) [DecidablePred P]
    (h : checkFourTerms D (fun b => decide (P b)) = true) : ∀ b, P b := by
  rintro ⟨n,j,x⟩
  have hn := List.all_eq_true.mp h n (List.mem_finRange n)
  have hj := List.all_eq_true.mp hn j (List.mem_finRange j)
  exact of_decide_eq_true (List.all_eq_true.mp hj x (List.mem_finRange x))

end LaughlinGap.RealOccupation

namespace LaughlinGap.RealOccupation

lemma fourFibers_of_index {D K : ℕ} (hD : D ≤ 23)
    (keys : Fin K → Finset (Fin 25)) (index : FourTerm D → Fin K)
    (fibers : Fin K → Finset (FourTerm D))
    (hi : Function.Injective keys) (hcard : ∀ a, (keys a).card=4)
    (cover : ∀ b, (fourTermLabels hD b).Nodup → (fourTermLabels hD b).toFinset=keys (index b))
    (fiberCover : ∀ b, (fourTermLabels hD b).Nodup → b ∈ fibers (index b))
    (fiberSound : ∀ a, ∀ b ∈ fibers a, (fourTermLabels hD b).toFinset=keys a) :
    ∀ a b, (fourTermLabels hD b).toFinset=keys a ↔ b ∈ fibers a := by
  intro a b
  constructor
  · intro h
    have hn : (fourTermLabels hD b).Nodup := by
      apply (Multiset.toFinset_card_eq_card_iff_nodup (m := (↑(fourTermLabels hD b) : Multiset (Fin 25)))).mp
      change (fourTermLabels hD b).toFinset.card=(fourTermLabels hD b).length
      rw [h,hcard]
      rfl
    have hind : index b=a := hi ((cover b hn).symm.trans h)
    simpa only [hind] using fiberCover b hn
  · exact fiberSound a b

end LaughlinGap.RealOccupation

namespace LaughlinGap.RealOccupation

lemma checkFourFibersSound_sound {D K : ℕ} (hD : D ≤ 23)
    (keys : Fin K → Finset (Fin 25)) (fibers : Fin K → Finset (FourTerm D))
    (h : checkFourFibersSound hD keys fibers=true) :
    ∀ a b, b ∈ fibers a → (fourTermLabels hD b).toFinset=keys a := by
  intro a b hb
  have ha := List.all_eq_true.mp h a (List.mem_finRange a)
  exact @of_decide_eq_true _ (Finset.decidableDforallFinset (s := fibers a)) ha b hb

end LaughlinGap.RealOccupation

end

end OAI
end

section
-- module Solutions.OAIQ030_LG.LaughlinGap_Certificate21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate21. -/

noncomputable section


namespace LaughlinGap.RealOccupation
open scoped BigOperators ComplexOrder
open Spin
namespace Certificate21

lemma cover_0 : ∀ j : Fin 0, ∀ x : Fin 11,
  (fourTermLabels (by omega : 21 ≤ 23) ⟨0,j,x⟩).Nodup →
    (fourTermLabels (by omega : 21 ≤ 23) ⟨0,j,x⟩).toFinset=keys (keyIndex 0 j x) := by decide +kernel
lemma cover_1 : ∀ j : Fin 1, ∀ x : Fin 11,
  (fourTermLabels (by omega : 21 ≤ 23) ⟨1,j,x⟩).Nodup →
    (fourTermLabels (by omega : 21 ≤ 23) ⟨1,j,x⟩).toFinset=keys (keyIndex 1 j x) := by decide +kernel
lemma cover_2 : ∀ j : Fin 1, ∀ x : Fin 10,
  (fourTermLabels (by omega : 21 ≤ 23) ⟨2,j,x⟩).Nodup →
    (fourTermLabels (by omega : 21 ≤ 23) ⟨2,j,x⟩).toFinset=keys (keyIndex 2 j x) := by decide +kernel
lemma cover_3 : ∀ j : Fin 2, ∀ x : Fin 10,
  (fourTermLabels (by omega : 21 ≤ 23) ⟨3,j,x⟩).Nodup →
    (fourTermLabels (by omega : 21 ≤ 23) ⟨3,j,x⟩).toFinset=keys (keyIndex 3 j x) := by decide +kernel
lemma cover_4 : ∀ j : Fin 2, ∀ x : Fin 9,
  (fourTermLabels (by omega : 21 ≤ 23) ⟨4,j,x⟩).Nodup →
    (fourTermLabels (by omega : 21 ≤ 23) ⟨4,j,x⟩).toFinset=keys (keyIndex 4 j x) := by decide +kernel
lemma cover_5 : ∀ j : Fin 3, ∀ x : Fin 9,
  (fourTermLabels (by omega : 21 ≤ 23) ⟨5,j,x⟩).Nodup →
    (fourTermLabels (by omega : 21 ≤ 23) ⟨5,j,x⟩).toFinset=keys (keyIndex 5 j x) := by decide +kernel
lemma cover_6 : ∀ j : Fin 3, ∀ x : Fin 8,
  (fourTermLabels (by omega : 21 ≤ 23) ⟨6,j,x⟩).Nodup →
    (fourTermLabels (by omega : 21 ≤ 23) ⟨6,j,x⟩).toFinset=keys (keyIndex 6 j x) := by decide +kernel
lemma cover_7 : ∀ j : Fin 4, ∀ x : Fin 8,
  (fourTermLabels (by omega : 21 ≤ 23) ⟨7,j,x⟩).Nodup →
    (fourTermLabels (by omega : 21 ≤ 23) ⟨7,j,x⟩).toFinset=keys (keyIndex 7 j x) := by decide +kernel
lemma cover_8 : ∀ j : Fin 4, ∀ x : Fin 7,
  (fourTermLabels (by omega : 21 ≤ 23) ⟨8,j,x⟩).Nodup →
    (fourTermLabels (by omega : 21 ≤ 23) ⟨8,j,x⟩).toFinset=keys (keyIndex 8 j x) := by decide +kernel
lemma cover_9 : ∀ j : Fin 5, ∀ x : Fin 7,
  (fourTermLabels (by omega : 21 ≤ 23) ⟨9,j,x⟩).Nodup →
    (fourTermLabels (by omega : 21 ≤ 23) ⟨9,j,x⟩).toFinset=keys (keyIndex 9 j x) := by decide +kernel
lemma cover_10 : ∀ j : Fin 5, ∀ x : Fin 6,
  (fourTermLabels (by omega : 21 ≤ 23) ⟨10,j,x⟩).Nodup →
    (fourTermLabels (by omega : 21 ≤ 23) ⟨10,j,x⟩).toFinset=keys (keyIndex 10 j x) := by decide +kernel
lemma cover_11 : ∀ j : Fin 6, ∀ x : Fin 6,
  (fourTermLabels (by omega : 21 ≤ 23) ⟨11,j,x⟩).Nodup →
    (fourTermLabels (by omega : 21 ≤ 23) ⟨11,j,x⟩).toFinset=keys (keyIndex 11 j x) := by decide +kernel
lemma cover_12 : ∀ j : Fin 6, ∀ x : Fin 5,
  (fourTermLabels (by omega : 21 ≤ 23) ⟨12,j,x⟩).Nodup →
    (fourTermLabels (by omega : 21 ≤ 23) ⟨12,j,x⟩).toFinset=keys (keyIndex 12 j x) := by decide +kernel
lemma cover_13 : ∀ j : Fin 7, ∀ x : Fin 5,
  (fourTermLabels (by omega : 21 ≤ 23) ⟨13,j,x⟩).Nodup →
    (fourTermLabels (by omega : 21 ≤ 23) ⟨13,j,x⟩).toFinset=keys (keyIndex 13 j x) := by decide +kernel
lemma cover_14 : ∀ j : Fin 7, ∀ x : Fin 4,
  (fourTermLabels (by omega : 21 ≤ 23) ⟨14,j,x⟩).Nodup →
    (fourTermLabels (by omega : 21 ≤ 23) ⟨14,j,x⟩).toFinset=keys (keyIndex 14 j x) := by decide +kernel
lemma cover_15 : ∀ j : Fin 8, ∀ x : Fin 4,
  (fourTermLabels (by omega : 21 ≤ 23) ⟨15,j,x⟩).Nodup →
    (fourTermLabels (by omega : 21 ≤ 23) ⟨15,j,x⟩).toFinset=keys (keyIndex 15 j x) := by decide +kernel
lemma cover_16 : ∀ j : Fin 8, ∀ x : Fin 3,
  (fourTermLabels (by omega : 21 ≤ 23) ⟨16,j,x⟩).Nodup →
    (fourTermLabels (by omega : 21 ≤ 23) ⟨16,j,x⟩).toFinset=keys (keyIndex 16 j x) := by decide +kernel
lemma cover_17 : ∀ j : Fin 9, ∀ x : Fin 3,
  (fourTermLabels (by omega : 21 ≤ 23) ⟨17,j,x⟩).Nodup →
    (fourTermLabels (by omega : 21 ≤ 23) ⟨17,j,x⟩).toFinset=keys (keyIndex 17 j x) := by decide +kernel
lemma cover_18 : ∀ j : Fin 9, ∀ x : Fin 2,
  (fourTermLabels (by omega : 21 ≤ 23) ⟨18,j,x⟩).Nodup →
    (fourTermLabels (by omega : 21 ≤ 23) ⟨18,j,x⟩).toFinset=keys (keyIndex 18 j x) := by decide +kernel
lemma cover_19 : ∀ j : Fin 10, ∀ x : Fin 2,
  (fourTermLabels (by omega : 21 ≤ 23) ⟨19,j,x⟩).Nodup →
    (fourTermLabels (by omega : 21 ≤ 23) ⟨19,j,x⟩).toFinset=keys (keyIndex 19 j x) := by decide +kernel
lemma cover_20 : ∀ j : Fin 10, ∀ x : Fin 1,
  (fourTermLabels (by omega : 21 ≤ 23) ⟨20,j,x⟩).Nodup →
    (fourTermLabels (by omega : 21 ≤ 23) ⟨20,j,x⟩).toFinset=keys (keyIndex 20 j x) := by decide +kernel
lemma cover_21 : ∀ j : Fin 11, ∀ x : Fin 1,
  (fourTermLabels (by omega : 21 ≤ 23) ⟨21,j,x⟩).Nodup →
    (fourTermLabels (by omega : 21 ≤ 23) ⟨21,j,x⟩).toFinset=keys (keyIndex 21 j x) := by decide +kernel
lemma cover : ∀ b : FourTerm 21, (fourTermLabels (by omega : 21 ≤ 23) b).Nodup →
    (fourTermLabels (by omega : 21 ≤ 23) b).toFinset=keys (keyIndex b.1 b.2.1 b.2.2) := by
  rintro ⟨n,j,x⟩
  fin_cases n
  · exact cover_0 j x
  · exact cover_1 j x
  · exact cover_2 j x
  · exact cover_3 j x
  · exact cover_4 j x
  · exact cover_5 j x
  · exact cover_6 j x
  · exact cover_7 j x
  · exact cover_8 j x
  · exact cover_9 j x
  · exact cover_10 j x
  · exact cover_11 j x
  · exact cover_12 j x
  · exact cover_13 j x
  · exact cover_14 j x
  · exact cover_15 j x
  · exact cover_16 j x
  · exact cover_17 j x
  · exact cover_18 j x
  · exact cover_19 j x
  · exact cover_20 j x
  · exact cover_21 j x
lemma keys_injective : Function.Injective keys := by decide +kernel
lemma keys_card : ∀ a : Fin 64, (keys a).card=4 := by decide +kernel
lemma fibers_cover : ∀ b : FourTerm 21,
    (fourTermLabels (by omega : 21 ≤ 23) b).Nodup →
      b ∈ fibers (keyIndex b.1 b.2.1 b.2.2) := by
  apply checkFourTerms_sound
  decide +kernel
lemma fibers_sound : ∀ a : Fin 64, ∀ b ∈ fibers a,
    (fourTermLabels (by omega : 21 ≤ 23) b).toFinset=keys a := by
  apply checkFourFibersSound_sound
  decide +kernel
lemma fibers_checked_oai : ∀ a : Fin 64, ∀ b : FourTerm 21,
    (fourTermLabels (by omega : 21 ≤ 23) b).toFinset=keys a ↔ b ∈ fibers a :=
  fourFibers_of_index (by omega : 21 ≤ 23) keys
    (fun b => keyIndex b.1 b.2.1 b.2.2) fibers keys_injective keys_card cover fibers_cover fibers_sound
end Certificate21
end LaughlinGap.RealOccupation

end

end OAI
end

theorem solution : type_of% @OAI.LaughlinGap.RealOccupation.Certificate21.fibers_checked_oai := @OAI.LaughlinGap.RealOccupation.Certificate21.fibers_checked_oai
