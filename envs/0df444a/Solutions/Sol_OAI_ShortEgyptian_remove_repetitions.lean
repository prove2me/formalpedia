-- Prove2me | solution 1 for OAI.ShortEgyptian.remove_repetitions
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T01:04:31.223798+00:00
-- url     : https://prove2.me/submissions/1f4bd4e2-7cf1-4370-ab93-08e17cb47bde

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/Distinctness.lean:L63-L129
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.remove_repetitions. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Theorems.Thm_OAI_ShortEgyptian_denominator_bound_aux

-- ---- from OAI.NumberTheory.ShortEgyptian.Basic ----
namespace OAI

namespace ShortEgyptian

theorem isExpansion_iff (a b : ℕ) (ns : List ℕ) :
    IsExpansion a b ns ↔ ns.Pairwise (· < ·) ∧
      (∀ n ∈ ns, 2 ≤ n) ∧ unitSum ns = (a : ℚ) / b := by
  have heq : (ns.map (fun n => (1 : ℚ) / (n : ℚ))).sum = unitSum ns := by
    induction ns with
    | nil => rfl
    | cons n ns ih => simpa [unitSum] using congrArg ((1 : ℚ) / (n : ℚ) + ·) ih
  simp only [IsExpansion, heq]

theorem unitSum_nonneg (ns : List ℕ) : 0 ≤ unitSum ns := by
  unfold unitSum
  apply List.sum_nonneg
  intro x hx
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp hx
  positivity

theorem unit_le_sum {n : ℕ} {ns : List ℕ} (hn : n ∈ ns) :
    (1 : ℚ) / n ≤ unitSum ns := by
  unfold unitSum
  apply List.single_le_sum _ _ (List.mem_map.mpr ⟨n, hn, rfl⟩)
  intro x hx
  obtain ⟨m, _, rfl⟩ := List.mem_map.mp hx
  positivity

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.Distinctness ----
namespace OAI

namespace ShortEgyptian

theorem unitSum_perm {xs ys : List ℕ} (hp : xs.Perm ys) : unitSum xs = unitSum ys :=
  (hp.map (fun n : ℕ => (1 : ℚ) / n)).sum_eq

theorem fraction_denominator_bound {A P : ℕ} (hA : 0 < A) (hP : 0 < P)
    (ns : List ℕ) (hpos : ∀ n ∈ ns, 0 < n) (heq : unitSum ns = (A : ℚ) / P)
    {n : ℕ} (hn : n ∈ ns) : n ≤ (ns.length * P) ^ (2 ^ (ns.length - 1)) := by
  let sorted := ns.mergeSort (fun a b => decide (a ≤ b))
  have hperm : sorted.Perm ns := List.mergeSort_perm ns _
  have hpair : sorted.Pairwise (· ≤ ·) := by
    simpa only [decide_eq_true_eq] using
      List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
        (by intros; simp_all; omega) (by intros; simp; omega) ns
  have hh := denominator_bound_aux sorted hpair
    (fun d hd => hpos d (hperm.mem_iff.mp hd)) A P ns.length hA hP
    (by simp [sorted]) ((unitSum_perm hperm).trans heq) n (hperm.mem_iff.mpr hn)
  simpa [sorted] using hh

theorem duplicate_replacement {d : ℕ} (hd : 3 ≤ d) :
    ∃ v w : ℕ, 0 < v ∧ 0 < w ∧
      (1 : ℚ) / v + 1 / w = 2 / d ∧ 2 * d < v + w := by
  let p := d / 2
  have heq : d = 2 * p + d % 2 := by dsimp [p]; omega
  have hp : 1 ≤ p := by dsimp [p]; omega
  rcases Nat.mod_two_eq_zero_or_one d with heven | hodd
  · have hd' : d = 2 * p := by omega
    have hp2 : 2 ≤ p := by omega
    refine ⟨p + 1, p * (p + 1), by omega, by positivity, ?_, ?_⟩
    · have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
      have hp1Q : ((p : ℚ) + 1) ≠ 0 := by positivity
      rw [hd']
      push_cast
      field_simp
    · rw [hd']
      nlinarith [Nat.mul_le_mul_left p hp2]
  · have hd' : d = 2 * p + 1 := by omega
    refine ⟨p + 1, (p + 1) * (2 * p + 1), by omega, by positivity, ?_, ?_⟩
    · have hp1Q : ((p : ℚ) + 1) ≠ 0 := by positivity
      have hp2Q : (2 * (p : ℚ) + 1) ≠ 0 := by positivity
      rw [hd']
      push_cast
      field_simp
      ring
    · rw [hd']
      nlinarith

theorem duplicate_extract {d : ℕ} {ns : List ℕ} (hd : List.Duplicate d ns) :
    ∃ xs, ns.Perm (d :: d :: xs) := by
  have h1 := List.perm_cons_erase hd.mem
  have hcnt : 2 ≤ ns.count d := List.duplicate_iff_two_le_count.mp hd
  have hcnt' : 1 ≤ (ns.erase d).count d := by
    have hh := h1.count_eq d
    simp only [List.count_cons_self] at hh
    omega
  have hmem : d ∈ ns.erase d := List.count_pos_iff.mp (by omega)
  exact ⟨(ns.erase d).erase d, h1.trans ((List.perm_cons_erase hmem).cons d)⟩

theorem remove_repetitions {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (ns : List ℕ) (hpos : ∀ n ∈ ns, 0 < n) (heq : unitSum ns = (a : ℚ) / b) :
    ∃ xs : List ℕ, IsExpansion a b xs ∧ xs.length = ns.length := by
  have hb : 0 < b := lt_trans ha hab
  let S : Set ℕ := {v | ∃ xs : List ℕ, (∀ n ∈ xs, 0 < n) ∧
    xs.length = ns.length ∧ unitSum xs = (a : ℚ) / b ∧ xs.sum = v}
  have hSne : S.Nonempty := ⟨ns.sum, ns, hpos, rfl, heq, rfl⟩
  have hSbdd : BddAbove S := by
    refine ⟨ns.length * (ns.length * b) ^ (2 ^ (ns.length - 1)), ?_⟩
    intro v hv
    obtain ⟨xs, hxpos, hxlen, hxeq, rfl⟩ := hv
    have hh := xs.sum_le_card_nsmul ((ns.length * b) ^ (2 ^ (ns.length - 1))) (by
      intro n hn
      have hh := fraction_denominator_bound ha hb xs hxpos hxeq hn
      simpa only [hxlen] using hh)
    simpa [hxlen] using hh
  obtain ⟨xs, hxpos, hxlen, hxeq, hxsum⟩ := Nat.sSup_mem hSne hSbdd
  have hxlt : unitSum xs < 1 := by
    rw [hxeq]
    exact (div_lt_one (by exact_mod_cast hb : (0 : ℚ) < b)).mpr (by exact_mod_cast hab)
  have hnodup : xs.Nodup := by
    by_contra hdup
    obtain ⟨d, hdup⟩ := List.exists_duplicate_iff_not_nodup.mpr hdup
    obtain ⟨ys, hperm⟩ := duplicate_extract hdup
    have hypos : ∀ n ∈ ys, 0 < n := fun n hn =>
      hxpos n (hperm.mem_iff.mpr (by simp [hn]))
    have hdpos := hxpos d hdup.mem
    have hdsum : unitSum xs = 2 / (d : ℚ) + unitSum ys := by
      rw [unitSum_perm hperm, unitSum_cons, unitSum_cons]
      ring
    have hd3 : 3 ≤ d := by
      have hh : (2 : ℚ) / d < 1 := by linarith [unitSum_nonneg ys]
      have hdQ : (0 : ℚ) < d := by exact_mod_cast hdpos
      have hh' := (div_lt_iff₀ hdQ).mp hh
      norm_num at hh'
      exact hh'
    obtain ⟨v, w, hv, hw, hrep, hincr⟩ := duplicate_replacement hd3
    have hnew : (v :: w :: ys).sum ∈ S := by
      refine ⟨v :: w :: ys, ?_, ?_, ?_, rfl⟩
      · intro n hn
        rcases List.mem_cons.mp hn with rfl | hn
        · exact hv
        rcases List.mem_cons.mp hn with rfl | hn
        · exact hw
        · exact hypos n hn
      · simpa only [List.length_cons] using hperm.length_eq.symm.trans hxlen
      · rw [unitSum_cons, unitSum_cons, ← add_assoc, hrep, ← hdsum, hxeq]
    have hle := le_csSup hSbdd hnew
    have hsumperm := hperm.sum_eq
    simp only [List.sum_cons] at hle hsumperm
    omega
  let sorted := xs.mergeSort (fun a b => decide (a ≤ b))
  have hperm : sorted.Perm xs := List.mergeSort_perm xs _
  have hpair : sorted.Pairwise (· ≤ ·) := by
    simpa only [decide_eq_true_eq] using
      List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
        (by intros; simp_all; omega) (by intros; simp; omega) xs
  have hne : sorted.Pairwise (· ≠ ·) := hperm.nodup_iff.mpr hnodup
  refine ⟨sorted, (isExpansion_iff _ _ _).mpr ⟨?_, ?_, ?_⟩, hperm.length_eq.trans hxlen⟩
  · exact (hpair.and hne).imp (fun h => lt_of_le_of_ne h.1 h.2)
  · intro n hn
    have hn' := hperm.mem_iff.mp hn
    have hnpos := hxpos n hn'
    have hh : (1 : ℚ) / n < 1 := lt_of_le_of_lt (unit_le_sum hn') hxlt
    have hh' := (div_lt_iff₀ (by exact_mod_cast hnpos : (0 : ℚ) < n)).mp hh
    exact_mod_cast (show (1 : ℚ) < n by simpa using hh')
  · exact (unitSum_perm hperm).trans hxeq

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian


theorem solution : type_of% @_root_.OAI.ShortEgyptian.remove_repetitions := @_root_.OAI.ShortEgyptian.remove_repetitions
