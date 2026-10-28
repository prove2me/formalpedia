-- Prove2me | solution 1 for OAI.Problem337.every_exact_marker_occurs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:03:49.832677+00:00
-- url     : https://prove2.me/submissions/8a6431b6-dcc0-40c7-a315-2f86d83233fa

import Mathlib
import Definitions.Def_EgyptianFractions
import Definitions.Def_OAIQ8EF000

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_FiniteExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- A finite collection of denominators has a canonical increasing enumeration. -/
theorem finset_increasing_enumeration (s : Finset ℕ) :
    ∃ n : Fin s.card → ℕ, StrictMono n ∧
      (∀ m, (∃ i, n i = m) ↔ m ∈ s) ∧
      (∀ f : ℕ → ℚ, (∑ i, f (n i)) = ∑ m ∈ s, f m) := by
  refine ⟨s.orderEmbOfFin rfl, (s.orderEmbOfFin rfl).strictMono, ?_, ?_⟩
  · intro m
    change m ∈ Set.range (s.orderEmbOfFin rfl) ↔ m ∈ s
    rw [Finset.range_orderEmbOfFin]
    rfl
  · intro f
    calc
      (∑ i, f ((s.orderEmbOfFin rfl) i)) =
          ∑ m ∈ Finset.univ.image (s.orderEmbOfFin rfl), f m := by
        rw [Finset.sum_image (fun a _ b _ h => (s.orderEmbOfFin rfl).injective h)]
      _ = ∑ m ∈ s, f m := by rw [Finset.image_orderEmbOfFin_univ]

/-- Enumeration preserves a lower bound and the sum of unit fractions. -/
theorem finset_unit_fraction_representation (s : Finset ℕ) (a : ℕ) (x : ℚ)
    (hpos : ∀ m ∈ s, a ≤ m) (hsum : (∑ m ∈ s, (1 : ℚ) / m) = x) :
    ∃ n : Fin s.card → ℕ, (∀ i, a ≤ n i) ∧ StrictMono n ∧
      (∑ i, (1 : ℚ) / n i) = x ∧
      (∀ m, (∃ i, n i = m) ↔ m ∈ s) := by
  obtain ⟨n, hmono, hmem, hsum'⟩ := finset_increasing_enumeration s
  refine ⟨n, ?_, hmono, ?_, hmem⟩
  · intro i
    exact hpos (n i) ((hmem _).mp ⟨i, rfl⟩)
  · exact (hsum' (fun m => (1 : ℚ) / m)).trans hsum

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MarkerOccurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

private theorem pronic_strictMono : StrictMono pronic := by
  intro a b hab
  unfold pronic
  nlinarith

private theorem pronic_pos (j : ℕ) : 0 < pronic j := by
  unfold pronic
  positivity

private theorem reciprocal_pronic (j : ℕ) :
    (1 : ℚ) / pronic j = 1 / (j + 1 : ℚ) - 1 / (j + 2 : ℚ) := by
  have h1 : (j + 1 : ℚ) ≠ 0 := by positivity
  have h2 : (j + 2 : ℚ) ≠ 0 := by positivity
  simp only [pronic, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  field_simp
  ring

private theorem sum_reciprocal_pronic (t : ℕ) :
    (∑ j ∈ Finset.range t, (1 : ℚ) / pronic j) = 1 - 1 / (t + 1 : ℚ) := by
  induction t with
  | zero => norm_num
  | succ t ih =>
    rw [Finset.sum_range_succ, ih, reciprocal_pronic]
    push_cast
    ring

private theorem pronicSet_pos {m d : ℕ} (hd : d ∈ pronicSet m) : 1 ≤ d := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hd
  exact pronic_pos j

private theorem pronicSet_sum {m : ℕ} (hm : 1 ≤ m) :
    (∑ d ∈ pronicSet m, (1 : ℚ) / d) = 1 - 1 / (m : ℚ) := by
  unfold pronicSet
  rw [Finset.sum_image]
  · rw [sum_reciprocal_pronic]
    congr 2
    norm_cast
    omega
  · intro a ha b hb hab
    exact pronic_strictMono.injective hab

private theorem pronic_succ_not_pronic {a b : ℕ} : pronic a + 1 ≠ pronic b := by
  intro h
  rcases lt_trichotomy a b with hab | hab | hab
  · have : a + 1 ≤ b := hab
    unfold pronic at h
    nlinarith
  · subst b
    omega
  · have := pronic_strictMono hab
    omega

private theorem insert_pronicSet_one {m : ℕ} (hm : 1 ≤ m)
    (hmem : m ∉ pronicSet m) :
    (∀ d ∈ insert m (pronicSet m), 1 ≤ d) ∧
      (∑ d ∈ insert m (pronicSet m), (1 : ℚ) / d) = 1 := by
  constructor
  · intro d hd
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact hm
    · exact pronicSet_pos hd
  · rw [Finset.sum_insert hmem, pronicSet_sum hm]
    ring

private theorem insert_pronicSet_card {m : ℕ} (hm : 1 ≤ m)
    (hmem : m ∉ pronicSet m) : (insert m (pronicSet m)).card = m := by
  rw [Finset.card_insert_of_notMem hmem]
  unfold pronicSet
  rw [Finset.card_image_of_injective _ pronic_strictMono.injective, Finset.card_range]
  omega

/-- Every integer at least two occurs in a finite distinct unit fraction expansion of one.
The construction telescopes consecutive reciprocal differences. -/
theorem exists_finset_one_with_marker_bounded (m : ℕ) (hm : 2 ≤ m) :
    ∃ s : Finset ℕ, (∀ d ∈ s, 1 ≤ d) ∧ m ∈ s ∧
      (∑ d ∈ s, (1 : ℚ) / d) = 1 ∧ s.card ≤ m + 1 := by
  classical
  by_cases hmem : m ∈ pronicSet m
  · obtain ⟨a, ha, ham⟩ := Finset.mem_image.mp hmem
    have hnext : m + 1 ∉ pronicSet (m + 1) := by
      intro h
      obtain ⟨b, hb, hbm⟩ := Finset.mem_image.mp h
      apply pronic_succ_not_pronic (a := a) (b := b)
      omega
    obtain ⟨hpos, hsum⟩ := insert_pronicSet_one (by omega : 1 ≤ m + 1) hnext
    refine ⟨insert (m + 1) (pronicSet (m + 1)), hpos, ?_, hsum, ?_⟩
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨a, ?_, ham⟩
      apply Finset.mem_range.mpr
      have := Finset.mem_range.mp ha
      omega
    · exact (insert_pronicSet_card (by omega : 1 ≤ m + 1) hnext).le
  · obtain ⟨hpos, hsum⟩ := insert_pronicSet_one (by omega : 1 ≤ m) hmem
    refine ⟨insert m (pronicSet m), hpos, by simp, hsum, ?_⟩
    rw [insert_pronicSet_card (by omega : 1 ≤ m) hmem]
    omega

/-- The finite-set version of exact-marker occurrence. -/
theorem exists_finset_one_with_marker (m : ℕ) (hm : 2 ≤ m) :
    ∃ s : Finset ℕ, (∀ d ∈ s, 1 ≤ d) ∧ m ∈ s ∧
      (∑ d ∈ s, (1 : ℚ) / d) = 1 := by
  obtain ⟨s, hpos, hmem, hsum, _⟩ := exists_finset_one_with_marker_bounded m hm
  exact ⟨s, hpos, hmem, hsum⟩

/-- Unconditional exact-marker occurrence, in the qualified expansion model. -/
theorem every_exact_marker_occurs_proof :
    ∀ m : ℕ, 2 ≤ m → ∃ k : ℕ, m ∈ D k := by
  intro m hm
  obtain ⟨s, hpos, hmem, hsum⟩ := exists_finset_one_with_marker m hm
  obtain ⟨n, hnpos, hnmono, hnsum, hnmem⟩ :=
    finset_unit_fraction_representation s 1 1 hpos hsum
  exact ⟨s.card, hm, n, ⟨hnpos, hnmono, hnsum⟩, (hnmem m).mpr hmem⟩

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

open scoped BigOperators

namespace Problem337

theorem every_exact_marker_occurs_oai :
    ∀ m : ℕ, 2 ≤ m → ∃ k : ℕ, m ∈ D k := by
  exact every_exact_marker_occurs_proof

end Problem337

end

end OAI
end

theorem solution : type_of% @OAI.Problem337.every_exact_marker_occurs_oai := @OAI.Problem337.every_exact_marker_occurs_oai
