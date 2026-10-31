-- Prove2me | solution 1 for OAI.LaughlinGap.RealOccupation.Certificate21.keys_checked
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T03:37:55.258453+00:00
-- url     : https://prove2.me/submissions/ff6604a4-53ef-48b0-aaf8-4d69406d5f0e

import Mathlib
import Definitions.Def_OAIQ030L028
import Definitions.Def_OAIQ030L029

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

lemma fourKeys_of_index {D K : ℕ} (hD : D ≤ 23)
    (keys : Fin K → Finset (Fin 25)) (index : FourTerm D → Fin K)
    (rep : Fin K → FourTerm D)
    (cover : ∀ b, (fourTermLabels hD b).Nodup → (fourTermLabels hD b).toFinset=keys (index b))
    (hrep : ∀ a, (fourTermLabels hD (rep a)).Nodup ∧ (fourTermLabels hD (rep a)).toFinset=keys a) :
    fourKeys hD = Finset.univ.image keys := by
  ext A
  constructor
  · intro h
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_image.mpr ⟨index b,Finset.mem_univ _,(cover b (Finset.mem_filter.mp hb).2).symm⟩
  · intro h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_image.mpr ⟨rep a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hrep a).1⟩,(hrep a).2⟩

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
lemma representatives_checked : ∀ a : Fin 64,
  (fourTermLabels (by omega : 21 ≤ 23) (representatives a)).Nodup ∧
  (fourTermLabels (by omega : 21 ≤ 23) (representatives a)).toFinset=keys a := by decide +kernel
lemma keys_checked_oai : fourKeys (by omega : 21 ≤ 23) = Finset.univ.image keys :=
  fourKeys_of_index (by omega : 21 ≤ 23) keys (fun b => keyIndex b.1 b.2.1 b.2.2)
    representatives cover representatives_checked
end Certificate21
end LaughlinGap.RealOccupation

end

end OAI
end

theorem solution : type_of% @OAI.LaughlinGap.RealOccupation.Certificate21.keys_checked_oai := @OAI.LaughlinGap.RealOccupation.Certificate21.keys_checked_oai
