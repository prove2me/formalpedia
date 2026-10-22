-- Prove2me | solution 1 for HardyCapset20261020.Cert.boolean_check_completion_bound
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-20T16:59:02.887915+00:00
-- url     : https://prove2.me/submissions/84fd43a0-229b-47e0-ae6f-356848b16772

import Theorems.Thm_HardyCapset20261020_Cert_certificate_checker_sound
import Definitions.Def_HardyCapsetBooleanVerifier20261020
import Mathlib.Algebra.BigOperators.Fin
namespace HardyCapset20261020.Cert
theorem binaryBlockers_size (s : Array Nat) : (binaryBlockers s).size = 6561 := by
  simp [binaryBlockers]

theorem binaryBlockers_get (s : Array Nat) (i : ℕ) (hi : i < 6561) :
    (binaryBlockers s)[i]! = binaryPair s i := by
  simp [binaryBlockers, hi]

end HardyCapset20261020.Cert
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace HardyCapset20261020.Cert

theorem lineB_iff (a b c : ℕ) : lineB a b c = true ↔ LineCode a b c := by
  simp only [lineB, List.all_eq_true, beq_iff_eq, List.mem_range, LineCode]
  constructor
  · intro h i
    exact h i.val i.isLt
  · intro h i hi
    exact h ⟨i, hi⟩

theorem fixedB_iff (c : Certificate) (a : ℕ) : fixedB c a = true ↔ FixedAnchor c a := by
  simp [fixedB, FixedAnchor]

theorem blockB_iff (c : Certificate) (q : ℕ) (ab : ℕ × ℕ) :
    blockB c q ab = true ↔ BlockOK c q ab := by
  unfold blockB BlockOK
  split_ifs <;> simp [fixedB_iff, lineB_iff, and_assoc]

theorem edgeB_iff (c : Certificate) (r : Row) (e : Edge) :
    edgeB c r e = true ↔ EdgeOK c r e := by
  simp [edgeB, EdgeOK, fixedB_iff, lineB_iff, and_assoc]

theorem tripleB_iff (c : Certificate) (r : Row) (e : Triple) :
    tripleB c r e = true ↔ TripleOK c r e := by
  simp [tripleB, TripleOK, lineB_iff, and_assoc]

theorem mem_assignments (xs : List Bool) (n : ℕ) (h : xs.length = n) : xs ∈ assignments n := by
  induction n generalizing xs with
  | zero =>
      cases xs with
      | nil => simp [assignments]
      | cons b xs => simp at h
  | succ n ih =>
      cases xs with
      | nil => simp at h
      | cons b xs =>
          have ht : xs.length = n := by simpa using h
          have hm := ih xs ht
          apply List.mem_flatMap.mpr
          refine ⟨xs, hm, ?_⟩
          cases b <;> simp

theorem readBit_ofFn {n : ℕ} (s : Fin n → Bool) (i : ℕ) :
    readBit (List.ofFn s) i = bit s i := by
  by_cases hi : i < n
  · simp [readBit, bit, hi]
  · have hx : (List.ofFn s)[i]? = none := by
      apply List.getElem?_eq_none
      simpa using Nat.le_of_not_gt hi
    simp [readBit, bit, hi, hx]

theorem bool_not_pair (a b : Bool) :
    (Bool.not (a && b) = true) ↔ ¬ (a = true ∧ b = true) := by
  cases a <;> cases b <;> decide

theorem bool_not_triple (a b c : Bool) :
    (Bool.not (a && b && c) = true) ↔ ¬ (a = true ∧ b = true ∧ c = true) := by
  cases a <;> cases b <;> cases c <;> decide

theorem legalB_ofFn {r : Row} (s : Fin r.vars.size → Bool) :
    legalB r (List.ofFn s) = true ↔ LegalPattern r s := by
  simp only [legalB, LegalPattern, Bool.and_eq_true, List.all_eq_true,
    readBit_ofFn]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro e he
      exact (bool_not_pair _ _).mp (h1 e he)
    · intro e he
      exact (bool_not_triple _ _ _).mp (h2 e he)
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro e he
      exact (bool_not_pair _ _).mpr (h1 e he)
    · intro e he
      exact (bool_not_triple _ _ _).mpr (h2 e he)

theorem list_range_sum (n : ℕ) (f : ℕ → ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

theorem selectedCost_ofFn (r : Row) (s : Fin r.vars.size → Bool) :
    selectedCost r (List.ofFn s) =
    ∑ k : Fin r.vars.size, if s k then entry r.coeff k.val else 0 := by
  unfold selectedCost
  rw [list_range_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  simp [readBit_ofFn, bit, k.isLt]

theorem patternB_sound (r : Row) (h : patternB r = true) : PatternBound r := by
  intro s hs
  have hm : List.ofFn s ∈ assignments r.vars.size :=
    mem_assignments _ _ (by simp)
  have hp := (List.all_eq_true.mp h) (List.ofFn s) hm
  have hl : legalB r (List.ofFn s) = true := (legalB_ofFn s).mpr hs
  have hc : selectedCost r (List.ofFn s) ≤ r.bound := by simpa [hl] using hp
  simpa only [selectedCost_ofFn] using hc

theorem rowB_sound (c : Certificate) (r : Row) (h : rowB c r = true) : RowOK c r := by
  have hh : r.coeff.size = r.vars.size ∧
      (∀ j ∈ r.vars.toList, j < c.pool.size) ∧
      (∀ e ∈ r.edges.toList, EdgeOK c r e) ∧
      (∀ e ∈ r.triples.toList, TripleOK c r e) ∧ patternB r = true := by
    simpa only [rowB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
      List.all_eq_true, edgeB_iff, tripleB_iff, and_assoc] using h
  exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, patternB_sound r hh.2.2.2.2⟩

theorem localCoverB_iff (c : Certificate) (j : ℕ) :
    localCoverB c j = true ↔ LocalCoverOK c j := by
  simp only [localCoverB, LocalCoverOK, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, and_assoc]

theorem verifyB_sound (c : Certificate) (h : verifyB c = true) : Check c := by
  have hh : c.normal < 6561 ∧ c.level < 3 ∧ 0 < c.denominator ∧
      (∀ q ∈ c.pool.toList, q < 6561) ∧ c.blockers.size = 6561 ∧
      (∀ q < 6561, BlockOK c q c.blockers[q]!) ∧
      (∀ r ∈ c.rows.toList, rowB c r = true) ∧ c.coverRows.size = c.pool.size ∧
      (∀ j < c.pool.size, LocalCoverOK c j) ∧
      cost c < c.denominator * (deletedCount c + 1) := by
    simpa only [verifyB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      List.all_eq_true, List.mem_range, blockB_iff, localCoverB_iff, and_assoc] using h
  refine ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2.1, ?_, ?_,
    hh.2.2.2.2.2.2.2.1, ?_, hh.2.2.2.2.2.2.2.2.2⟩
  · intro q
    exact hh.2.2.2.2.2.1 q.val q.isLt
  · intro r hr
    exact rowB_sound c r (hh.2.2.2.2.2.2.1 r hr)
  · intro j
    exact hh.2.2.2.2.2.2.2.2.1 j.val j.isLt

theorem verifyDataB_sound (c : Certificate) (chunks : Array Nat)
    (he : c.blockers = binaryBlockers chunks) (h : verifyDataB c chunks = true) : Check c := by
  have hh : c.normal < 6561 ∧ c.level < 3 ∧ 0 < c.denominator ∧
      (∀ q ∈ c.pool.toList, q < 6561) ∧ 6561 = 6561 ∧
      (∀ q < 6561, BlockOK c q (binaryPair chunks q)) ∧
      (∀ r ∈ c.rows.toList, rowB c r = true) ∧ c.coverRows.size = c.pool.size ∧
      (∀ j < c.pool.size, LocalCoverOK c j) ∧
      cost c < c.denominator * (deletedCount c + 1) := by
    simpa only [verifyDataB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
      List.all_eq_true, List.mem_range, blockB_iff, localCoverB_iff, and_assoc] using h
  refine ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, (by rw [he]; simp [binaryBlockers]), ?_, ?_,
    hh.2.2.2.2.2.2.2.1, ?_, hh.2.2.2.2.2.2.2.2.2⟩
  · intro q
    simpa only [he, binaryBlockers_get chunks q.val q.isLt] using hh.2.2.2.2.2.1 q.val q.isLt
  · intro r hr
    exact rowB_sound c r (hh.2.2.2.2.2.2.1 r hr)
  · intro j
    exact hh.2.2.2.2.2.2.2.2.1 j.val j.isLt

end HardyCapset20261020.Cert

open HardyCapset20261020 HardyCapset20261020.Cert
theorem solution (c : Certificate) (h : verifyB c = true) :
    CompletionBound (decode c.normal) c.level :=
  certificate_checker_sound c (verifyB_sound c h)
#print axioms solution
