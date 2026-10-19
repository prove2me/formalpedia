-- Prove2me | solution 1 for OAI.SeparableQuotient.InfiniteRamsey.homogeneous_subset
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T20:50:10.71817+00:00
-- url     : https://prove2.me/submissions/32b3666a-9a86-4edd-8891-60cc8258155c

import Mathlib

section
-- module Solutions.OAIQW_SeparableQuotient.RamseyThinning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.InfiniteRamsey
open Filter
open scoped Classical

variable {χ : Type*} [Finite χ]

lemma eventually_constant (U : Ultrafilter ℕ) (f : ℕ → χ) :
    ∃ b, ∀ᶠ m in U, f m = b :=
  U.eventually_exists_iff.mp (Eventually.of_forall (fun m => ⟨f m, rfl⟩))

def limitColor (U : Ultrafilter ℕ) (c : Finset ℕ → χ) : ℕ → Finset ℕ → χ
  | 0, s => c s
  | k+1, s => (eventually_constant U (fun m => limitColor U c k (insert m s))).choose

lemma limitColor_eventually (U : Ultrafilter ℕ) (c : Finset ℕ → χ)
    (k : ℕ) (s : Finset ℕ) :
    ∀ᶠ m in U, limitColor U c k (insert m s) = limitColor U c (k+1) s :=
  (eventually_constant U (fun m => limitColor U c k (insert m s))).choose_spec

/-- The finite-set form of the infinite Ramsey theorem, proved by iterated
ultrafilter colors. Used only for the four-hit thinning in exact-pairs. -/
theorem homogeneous (n : ℕ) (c : Finset ℕ → χ) :
    ∃ (M : Set ℕ) (b : χ), M.Infinite ∧
      ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ M → s.card = n → c s = b := by
  let U := Ultrafilter.of (atTop : Filter ℕ)
  let b := limitColor U c n ∅
  let Good : Finset ℕ → Prop := fun S => ∀ s ⊆ S, s.card ≤ n → limitColor U c (n-s.card) s = b
  have hempty : Good ∅ := by
    intro s hs _
    have he : s = ∅ := Finset.subset_empty.mp hs
    subst s
    rfl
  have hstep (S : Finset ℕ) (hS : Good S) : ∃ m > S.sup id, Good (insert m S) := by
    have hev (s : Finset ℕ) (hs : s ⊆ S) : ∀ᶠ m in U,
        s.card < n → limitColor U c (n-s.card-1) (insert m s) = b := by
      by_cases hlt : s.card < n
      · have he : n-s.card-1+1 = n-s.card := by omega
        exact (limitColor_eventually U c (n-s.card-1) s).mono
          (fun _ h _ => h.trans (by rw [he]; exact hS s hs hlt.le))
      · exact Eventually.of_forall (fun _ h => (hlt h).elim)
    have hall : ∀ᶠ m in U, ∀ s ∈ S.powerset,
        s.card < n → limitColor U c (n-s.card-1) (insert m s) = b :=
      (eventually_all_finset S.powerset).mpr (fun s hs => hev s (Finset.mem_powerset.mp hs))
    have hlarge : ∀ᶠ m in U, S.sup id < m :=
      (eventually_gt_atTop (S.sup id)).filter_mono (Ultrafilter.of_le atTop)
    obtain ⟨m, hm, hall⟩ := (hlarge.and hall).exists
    have hmS : m ∉ S := by
      intro h
      exact (not_le_of_gt hm) (Finset.le_sup (f := id) h)
    refine ⟨m, hm, fun s hs hcard => ?_⟩
    by_cases hms : m ∈ s
    · let t := s.erase m
      have hts : t ⊆ S := by
        intro a ha
        have hh := Finset.mem_of_subset hs (Finset.mem_of_mem_erase ha)
        exact (Finset.mem_insert.mp hh).resolve_left (Finset.ne_of_mem_erase ha)
      have htc : t.card+1 = s.card := by
        exact Finset.card_erase_add_one hms
      have he : insert m t = s := Finset.insert_erase hms
      have hh := hall t (Finset.mem_powerset.mpr hts) (by omega)
      simpa only [he, show n-t.card-1 = n-s.card by omega] using hh
    · have hss : s ⊆ S := by
        intro a ha
        exact (Finset.mem_insert.mp (hs ha)).resolve_left (fun h => hms (h ▸ ha))
      exact hS s hss hcard
  let next (S : {S : Finset ℕ // Good S}) : ℕ := (hstep S.val S.property).choose
  have hn (S : {S : Finset ℕ // Good S}) : S.val.sup id < next S ∧ Good (insert (next S) S.val) :=
    (hstep S.val S.property).choose_spec
  let seq : ℕ → {S : Finset ℕ // Good S} := Nat.rec ⟨∅, hempty⟩
    (fun _ S => ⟨insert (next S) S.val, (hn S).2⟩)
  have hseq (i : ℕ) : (seq (i+1)).val = insert (next (seq i)) (seq i).val := rfl
  have hmono : Monotone (fun i => (seq i).val) := monotone_nat_of_le_succ
    (fun i => by rw [hseq]; exact Finset.subset_insert _ _)
  let v : ℕ → ℕ := fun i => next (seq i)
  have hvmem (i : ℕ) : v i ∈ (seq (i+1)).val := by rw [hseq]; exact Finset.mem_insert_self _ _
  have hv : StrictMono v := by
    apply strictMono_nat_of_lt_succ
    intro i
    exact (Finset.le_sup (f := id) (hvmem i)).trans_lt (hn (seq (i+1))).1
  let M : Set ℕ := ⋃ i, ↑(seq i).val
  have hM : M.Infinite := (Set.infinite_range_of_injective hv.injective).mono (by
    rintro _ ⟨i, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i+1, hvmem i⟩)
  refine ⟨M, b, hM, fun s hs hcard => ?_⟩
  have hex : ∀ a : s, ∃ i, a.val ∈ (seq i).val :=
    fun a => Set.mem_iUnion.mp (hs a.property)
  choose k hk using hex
  let N := Finset.univ.sup k
  have hsub : s ⊆ (seq N).val := by
    intro a ha
    exact hmono (Finset.le_sup (f := k) (Finset.mem_univ ⟨a, ha⟩)) (hk ⟨a, ha⟩)
  have hh := (seq N).property s hsub hcard.le
  simpa only [hcard, Nat.sub_self, limitColor] using hh

/-- Relative version for any infinite subset of the natural numbers. -/
theorem homogeneous_subset_oai (n : ℕ) (c : Finset ℕ → χ) (A : Set ℕ) (hA : A.Infinite) :
    ∃ (M : Set ℕ) (b : χ), M ⊆ A ∧ M.Infinite ∧
      ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ M → s.card = n → c s = b := by
  let f : ℕ → ℕ := Nat.nth (· ∈ A)
  have hf : StrictMono f := Nat.nth_strictMono hA
  obtain ⟨B, b, hB, hb⟩ := homogeneous n (fun s => c (s.image f))
  refine ⟨f '' B, b, ?_, hB.image hf.injective.injOn, ?_⟩
  · rintro _ ⟨i, _, rfl⟩
    exact Nat.nth_mem_of_infinite hA i
  · intro s hs hcard
    let t := s.preimage f (hf.injective.injOn)
    have him : t.image f = s := by
      ext a
      constructor
      · intro ha
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        exact Finset.mem_preimage.mp hi
      · intro ha
        obtain ⟨i, _, rfl⟩ := hs ha
        exact Finset.mem_image.mpr ⟨i, Finset.mem_preimage.mpr ha, rfl⟩
    have hts : (↑t : Set ℕ) ⊆ B := by
      intro i hi
      have hfi : f i ∈ s := (Finset.mem_preimage.mp hi)
      obtain ⟨j, hj, he⟩ := hs hfi
      exact hf.injective he ▸ hj
    have htcard : t.card = n := by rw [← hcard, ← him, Finset.card_image_of_injective _ hf.injective]
    simpa only [him] using hb t hts htcard

end SeparableQuotient.InfiniteRamsey

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.SeparableQuotient.InfiniteRamsey.homogeneous_subset_oai.{u_1} := @OAI.SeparableQuotient.InfiniteRamsey.homogeneous_subset_oai.{u_1}
