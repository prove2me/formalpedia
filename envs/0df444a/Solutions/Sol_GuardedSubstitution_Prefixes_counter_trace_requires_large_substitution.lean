-- Prove2me | solution 1 for GuardedSubstitution.Prefixes.counter_trace_requires_large_substitution
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T19:40:35.879458+00:00
-- url     : https://prove2.me/submissions/86770832-6331-4320-be3e-a5d36fdcfee5

import Definitions.Def_GuardedSubstitutionReadout

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace SubstitutionFactorBound

open GuardedSubstitution.Prefixes (expansion)

variable {α σ : Type*} [DecidableEq α]

/-- Distinct exact-width contiguous factors, indexed by valid starting offsets. -/
def factors (width : ℕ) (word : List α) : Finset (List α) :=
  (Finset.range (word.length + 1 - width)).image (fun i => (word.drop i).take width)

theorem mem_factors {width : ℕ} {word factor : List α} :
    factor ∈ factors width word ↔
      ∃ i, i + width ≤ word.length ∧ factor = (word.drop i).take width := by
  unfold factors
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by omega, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by omega, rfl⟩

/-- A width-w factor crossing a given cut starts in the last w-1 letters
on the left. This set may also contain irrelevant candidates. -/
def cutCandidates (width : ℕ) (left right : List α) : Finset (List α) :=
  (Finset.range (width - 1)).image
    (fun j => ((left.drop (left.length - (j+1))) ++ right).take width)

theorem card_cutCandidates (width : ℕ) (left right : List α) :
    (cutCandidates width left right).card ≤ width - 1 := by
  simpa [cutCandidates] using
    (Finset.card_image_le (s := Finset.range (width - 1))
      (f := fun j => ((left.drop (left.length - (j+1))) ++ right).take width))

theorem factors_append_subset (width : ℕ) (left right : List α) :
    factors width (left ++ right) ⊆
      (factors width left ∪ factors width right) ∪ cutCandidates width left right := by
  intro factor present
  obtain ⟨i, fits, rfl⟩ := mem_factors.mp present
  simp only [List.length_append] at fits
  by_cases beyond : left.length ≤ i
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply mem_factors.mpr
    refine ⟨i-left.length, by omega, ?_⟩
    rw [List.drop_append, List.drop_eq_nil_of_le beyond, List.nil_append]
  · have inLeft : i ≤ left.length := by omega
    rw [List.drop_append_of_le_length inLeft]
    by_cases contained : i + width ≤ left.length
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply mem_factors.mpr
      refine ⟨i, contained, ?_⟩
      rw [List.take_append_of_le_length]
      simpa only [List.length_drop] using (show width ≤ left.length - i from by omega)
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨left.length-i-1, Finset.mem_range.mpr (by omega), ?_⟩
      have h : left.length - (left.length-i-1+1) = i := by omega
      rw [h]

/-- Candidates at each ordered cut of the right-hand side of one rule. -/
def ruleCandidates (width : ℕ) (value : σ → List α) : List σ → Finset (List α)
  | [] => ∅
  | a :: tail => cutCandidates width (value a) (tail.flatMap value) ∪
      ruleCandidates width value tail

theorem card_ruleCandidates (width : ℕ) (value : σ → List α) (rhs : List σ) :
    (ruleCandidates width value rhs).card ≤ rhs.length * (width - 1) := by
  induction rhs with
  | nil => simp [ruleCandidates]
  | cons a tail ih =>
    simp only [ruleCandidates, List.length_cons, Nat.add_mul, Nat.one_mul]
    exact (Finset.card_union_le _ _).trans (by
      simpa [Nat.add_comm] using Nat.add_le_add (card_cutCandidates width (value a)
        (tail.flatMap value)) ih)

theorem factors_flatMap_subset (width : ℕ) (positive : 0 < width) (value : σ → List α)
    (pool : Finset (List α)) (rhs : List σ)
    (children : ∀ a ∈ rhs, factors width (value a) ⊆ pool) :
    factors width (rhs.flatMap value) ⊆ pool ∪ ruleCandidates width value rhs := by
  induction rhs with
  | nil => simp [ruleCandidates, factors, show 1 - width = 0 by omega]
  | cons a tail ih =>
    intro factor present
    simp only [List.flatMap_cons] at present
    have remaining := ih (fun b hb => children b (List.mem_cons_of_mem a hb))
    rcases Finset.mem_union.mp (factors_append_subset width (value a)
        (tail.flatMap value) present) with inChild | cut
    · rcases Finset.mem_union.mp inChild with first | rest
      · exact Finset.mem_union_left _ (children a (List.mem_cons_self) first)
      · rcases Finset.mem_union.mp (remaining rest) with old | r
        · exact Finset.mem_union_left _ old
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ r)
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ cut)

variable {k : ℕ}

/-- Size of the substitution table, counting one entry per child occurrence. -/
def rhsSize (rule : Fin k → List (Fin k)) : ℕ := ∑ a, (rule a).length

def levelCandidates (width : ℕ) (rule : Fin k → List (Fin k)) (decode : Fin k → List α)
    (depth : ℕ) : Finset (List α) :=
  Finset.univ.biUnion fun a =>
    ruleCandidates width (fun b => (expansion rule depth b).flatMap decode) (rule a)

theorem card_levelCandidates (width : ℕ) (rule : Fin k → List (Fin k))
    (decode : Fin k → List α) (depth : ℕ) :
    (levelCandidates width rule decode depth).card ≤ rhsSize rule * (width - 1) := by
  unfold levelCandidates rhsSize
  rw [Finset.sum_mul]
  exact Finset.card_biUnion_le.trans
    (Finset.sum_le_sum fun a _ => card_ruleCandidates width _ (rule a))

/-- Lower levels contribute one shared set of candidates per depth, even
when the same subexpansion is reused exponentially many times. -/
def allCandidates (width : ℕ) (rule : Fin k → List (Fin k)) (decode : Fin k → List α) :
    ℕ → Finset (List α)
  | 0 => ∅
  | depth+1 => allCandidates width rule decode depth ∪ levelCandidates width rule decode depth

theorem card_allCandidates (width : ℕ) (rule : Fin k → List (Fin k)) (decode : Fin k → List α)
    (depth : ℕ) :
    (allCandidates width rule decode depth).card ≤ depth * rhsSize rule * (width - 1) := by
  induction depth with
  | zero => simp [allCandidates]
  | succ depth ih =>
    simp only [allCandidates, Nat.succ_mul, Nat.add_mul]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add ih (card_levelCandidates width rule decode depth))

theorem factors_expansion_subset (width : ℕ) (wide : 2 ≤ width)
    (rule : Fin k → List (Fin k)) (decode : Fin k → List α)
    (short : ∀ a, (decode a).length ≤ 1) (depth : ℕ) (a : Fin k) :
    factors width ((expansion rule depth a).flatMap decode) ⊆
      allCandidates width rule decode depth := by
  induction depth generalizing a with
  | zero =>
    have small : (decode a).length + 1 - width = 0 := by have := short a; omega
    simp [expansion, factors, allCandidates, small]
  | succ depth ih =>
    rw [expansion, List.flatMap_assoc]
    intro factor present
    rcases Finset.mem_union.mp
        (factors_flatMap_subset width (by omega) _ _ (rule a) (fun b _ => ih b) present)
        with fromChild | fromCut
    · exact Finset.mem_union_left _ fromChild
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, fromCut⟩)

/-- A depth-d substitution with total right-hand-side size s has at most
d*s*(width-1) distinct width-letter factors after decoding each leaf as at
most one output letter. Erasing leaves is allowed. -/
theorem factor_count_le (width : ℕ) (wide : 2 ≤ width)
    (rule : Fin k → List (Fin k)) (decode : Fin k → List α)
    (short : ∀ a, (decode a).length ≤ 1) (depth : ℕ) (a : Fin k) :
    (factors width ((expansion rule depth a).flatMap decode)).card ≤
      depth * rhsSize rule * (width - 1) :=
  (Finset.card_le_card (factors_expansion_subset width wide rule decode short depth a)).trans
    (card_allCandidates width rule decode depth)

theorem factors_append_left_subset (width : ℕ) (left right : List α) :
    factors width left ⊆ factors width (left ++ right) := by
  intro factor present
  obtain ⟨i, fits, rfl⟩ := mem_factors.mp present
  apply mem_factors.mpr
  refine ⟨i, by simp only [List.length_append]; omega, ?_⟩
  rw [List.drop_append_of_le_length (show i ≤ left.length by omega),
    List.take_append_of_le_length (show width ≤ (left.drop i).length by simp; omega)]

/-- Even when the reported run stops partway through the expansion,
its decoded prefix satisfies the same bound. -/
theorem prefix_factor_count_le (width : ℕ) (wide : 2 ≤ width)
    (rule : Fin k → List (Fin k)) (decode : Fin k → List α)
    (short : ∀ a, (decode a).length ≤ 1) (depth : ℕ) (a : Fin k) (T : ℕ) :
    (factors width (((expansion rule depth a).take T).flatMap decode)).card ≤
      depth * rhsSize rule * (width - 1) := by
  refine (Finset.card_le_card ?_).trans (factor_count_le width wide rule decode short depth a)
  let word := expansion rule depth a
  change factors width ((word.take T).flatMap decode) ⊆ factors width (word.flatMap decode)
  have append : (word.take T).flatMap decode ++ (word.drop T).flatMap decode = word.flatMap decode := by
    rw [← List.flatMap_append, List.take_append_drop]
  simpa only [append] using factors_append_left_subset width ((word.take T).flatMap decode)
    ((word.drop T).flatMap decode)

end SubstitutionFactorBound

namespace SubstitutionCounter

/-- The low `m` bits of a numeral, least significant bit first. -/
def numeralBits (m : ℕ) (i : Fin (2 ^ m)) : List Bool :=
  List.ofFn (fun j : Fin m => i.val.testBit j.val)

@[simp] theorem numeralBits_length (m : ℕ) (i : Fin (2 ^ m)) :
    (numeralBits m i).length = m := by
  simp [numeralBits]

theorem numeralBits_injective (m : ℕ) : Function.Injective (numeralBits m) := by
  intro x y same
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases small : i < m
  · have atX : i < (numeralBits m x).length := by simpa using small
    have equal := List.getElem_of_eq same (i := i) atX
    simpa only [numeralBits, List.getElem_ofFn] using equal
  · have enough : 2 ^ m ≤ 2 ^ i := Nat.pow_le_pow_right (by decide)
      (Nat.le_of_not_gt small)
    rw [Nat.testBit_eq_false_of_lt (x.isLt.trans_le enough),
      Nat.testBit_eq_false_of_lt (y.isLt.trans_le enough)]

/-- Successive blocks list all numerals. Positions beyond the low `m`
bits inside each block are zero. A query uses one division, one
remainder, and one bit extraction. -/
def counterTrace (m block : ℕ) : List Bool :=
  List.ofFn (fun t : Fin (block * 2 ^ m) => (t.val / block).testBit (t.val % block))

@[simp] theorem counterTrace_length (m block : ℕ) :
    (counterTrace m block).length = block * 2 ^ m := by
  simp [counterTrace]

theorem counterTrace_getElem {m block t : ℕ} (inTrace : t < (counterTrace m block).length) :
    (counterTrace m block)[t] = (t / block).testBit (t % block) :=
  List.getElem_ofFn inTrace

theorem counterTrace_window_fits {m block : ℕ} (hm : m ≤ block) (i : Fin (2 ^ m)) :
    i.val * block + m ≤ (counterTrace m block).length := by
  rw [counterTrace_length, Nat.mul_comm block]
  calc
    i.val * block + m ≤ i.val * block + block := Nat.add_le_add_left hm _
    _ = (i.val + 1) * block := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ 2 ^ m * block := Nat.mul_le_mul_right _ i.isLt

theorem counterTrace_window {m block : ℕ} (hm : m ≤ block) (i : Fin (2 ^ m)) :
    ((counterTrace m block).drop (i.val * block)).take m = numeralBits m i := by
  have fits := counterTrace_window_fits hm i
  have sufficient : m ≤ (counterTrace m block).length - i.val * block := by omega
  apply List.ext_getElem
  · rw [List.length_take, List.length_drop, numeralBits_length, Nat.min_eq_left sufficient]
  · intro j _ hright
    have jlt : j < m := by simpa using hright
    have jblock := jlt.trans_le hm
    have blockPos := Nat.zero_lt_of_lt jblock
    rw [List.getElem_take, List.getElem_drop, counterTrace_getElem]
    simp only [numeralBits, List.getElem_ofFn]
    rw [Nat.mul_comm i.val block, Nat.mul_add_div blockPos, Nat.mul_add_mod,
      Nat.div_eq_of_lt jblock, Nat.mod_eq_of_lt jblock, Nat.add_zero]

end SubstitutionCounter

namespace SubstitutionClockSeparation

open SubstitutionCounter SubstitutionFactorBound
open GuardedSubstitution.Prefixes (expansion)

theorem counterTrace_num_factors (m block : ℕ) (fits : m ≤ block) :
    2^m ≤ (factors m (counterTrace m block)).card := by
  let numerals := (Finset.univ : Finset (Fin (2^m))).image (numeralBits m)
  have includes : numerals ⊆ factors m (counterTrace m block) := by
    intro word found
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp found
    exact mem_factors.mpr ⟨i.val * block, counterTrace_window_fits fits i,
      (counterTrace_window fits i).symm⟩
  have number : numerals.card = 2^m := by
    rw [Finset.card_image_of_injective _ (numeralBits_injective m), Finset.card_univ, Fintype.card_fin]
  rw [← number]
  exact Finset.card_le_card includes

theorem counterTrace_budget {k : ℕ} (m block : ℕ) (wide : 2 ≤ m) (fits : m ≤ block)
    (rule : Fin k → List (Fin k)) (decode : Fin k → List Bool)
    (short : ∀ a, (decode a).length ≤ 1) (depth : ℕ) (a : Fin k) (T : ℕ)
    (tail : List Bool)
    (observed : counterTrace m block ++ tail =
      ((expansion rule depth a).take T).flatMap decode) :
    2^m ≤ depth * rhsSize rule * (m-1) := by
  have sub := factors_append_left_subset m (counterTrace m block) tail
  rw [observed] at sub
  exact (counterTrace_num_factors m block fits).trans
    ((Finset.card_le_card sub).trans (prefix_factor_count_le m wide rule decode short depth a T))

end SubstitutionClockSeparation

theorem solution {k : ℕ}
    (m block : ℕ) (wide : 2 ≤ m) (fits : m ≤ block)
    (rule : Fin k → List (Fin k)) (decode : Fin k → List Bool)
    (short : ∀ a, (decode a).length ≤ 1)
    (depth : ℕ) (a : Fin k) (T : ℕ) (tail : List Bool) :
    let trace : List Bool :=
      List.ofFn (fun t : Fin (block * 2 ^ m) => (t.val / block).testBit (t.val % block))
    trace ++ tail = ((GuardedSubstitution.Prefixes.expansion rule depth a).take T).flatMap decode →
      2 ^ m ≤ depth * (∑ b, (rule b).length) * (m - 1) := by
  dsimp only
  intro observed
  exact SubstitutionClockSeparation.counterTrace_budget m block wide fits rule decode short
    depth a T tail observed

#print axioms solution
