-- Prove2me | solution 1 for GrothendieckLB.Supplement.cq_head_cutoff_invariance
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T19:41:24.247354+00:00
-- url     : https://prove2.me/submissions/99496302-1cc2-4a81-9ae4-b72e0d8e43ca

import Definitions.Def_GrothendieckLB_Supplement_cqNonlinearHeadCheck
open GrothendieckLB.Supplement GrothendieckLB.Supplement.CQHeadArithmetic
namespace CQCutoff
set_option maxHeartbeats 1000000

private theorem tabSize {α : Type} (n : Nat) (f : Nat → α) : (tab n f).size=n := by simp [tab]
private theorem tabGet {α : Type} (d : α) {n i : Nat} {f : Nat → α} (hi : i < n) :
    entry d (tab n f) i = f i := by simp [entry,tab,hi]
private theorem pushGet {α : Type} (d : α) (xs : Array α) (x : α) (i : Nat) :
    entry d (xs.push x) i = if i=xs.size then x else entry d xs i := by
  by_cases h : i=xs.size <;> simp [entry,Array.getElem?_push,h]
private theorem rawSize (n : Nat) : (momentRows n).size = n+6 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [momentRows,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private def agrees {α : Type} (d : α) (n : Nat) (xs ys : Array α) : Prop :=
  ∀ i, i < n → entry d xs i = entry d ys i

private theorem rawAgrees {n N : Nat} (h : n ≤ N) :
    agrees zeroCombination (n+6) (momentRows n) (momentRows N) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => intro i hi; rfl
  | succ k ih =>
    intro i hi
    rw [Nat.add_succ,momentRows,pushGet,rawSize,if_neg (by omega : i ≠ n+k+6)]
    exact ih i hi

private theorem sumC {f g : Nat → MomentCombination} (n : Nat)
    (h : ∀ k, k < n → f k=g k) : sumCombinations f n = sumCombinations g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumCombinations, ih (fun i hi => h i (by omega)),h n (by omega)]

private theorem startSize (n : Nat) : (startAt n).size = 3*n+1 := tabSize _ _
private theorem startAgrees {n N : Nat} (h : n ≤ N) :
    agrees zeroCombination (3*n+1) (startAt n) (startAt N) := by
  intro b hb
  simp only [startAt,tabGet _ hb,tabGet _ (show b<3*N+1 by omega),hStart]
  split
  · apply sumC
    intro k hk
    rw [rawAgrees (show 3*n-5 ≤ 3*N-5 by omega) k (by omega : k < 3*n-5+6)]
  · rfl

private theorem shiftSize (x : Array MomentCombination) : (shift x).size=x.size-1 := tabSize _ _
private theorem shiftAgrees {k : Nat} {x y : Array MomentCombination}
    (hx : k ≤ x.size) (hy : k ≤ y.size) (h : agrees zeroCombination k x y) :
    agrees zeroCombination (k-1) (shift x) (shift y) := by
  intro b hb
  rw [shift,tabGet _ (show b<x.size-1 by omega),shift,tabGet _ (show b<y.size-1 by omega),
    h (b+1) (by omega),h (b-1) (by omega)]

private theorem nextSize (p : Nat) (x y : Array MomentCombination) :
    (nextRow p x y).size=y.size-3 := by
  simp only [nextRow,tabSize,shiftSize] <;> omega

private theorem nextAgrees {p k : Nat} {x y v w : Array MomentCombination}
    (hv : k ≤ v.size) (hw : k ≤ w.size)
    (hp : agrees zeroCombination (k-3) x y) (hc : agrees zeroCombination k v w) :
    agrees zeroCombination (k-3) (nextRow p x v) (nextRow p y w) := by
  have h1 := shiftAgrees hv hw hc
  have h2 := shiftAgrees (by rw [shiftSize] <;> omega) (by rw [shiftSize] <;> omega) h1
  have h3 := shiftAgrees (by simp only [shiftSize] <;> omega) (by simp only [shiftSize] <;> omega) h2
  intro b hb
  simp only [nextRow]
  rw [tabGet _ (by simp only [shiftSize] <;> omega), tabGet _ (by simp only [shiftSize] <;> omega),
    hp b hb,h1 b (by omega),h3 b (by omega)]

private def G (n p : Nat) := grid n (startAt n) p
private def W (n p a : Nat) := entry (#[] : Array Interval) (G n p).weights a
private theorem wSize (n p : Nat) : (G n p).weights.size=p+1 := by
  induction p with
  | zero => rfl
  | succ p ih => change ((G n p).weights.push _).size = _; simp [ih]
private theorem wStable {n a p P : Nat} (ha : a ≤ p) (hp : p ≤ P) :
    W n P a = W n p a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp
  clear hp
  induction k with
  | zero => rfl
  | succ k ih =>
    change entry #[] ((G n (p+k)).weights.push _) a = _
    rw [pushGet,wSize,if_neg (by omega : a ≠ p+k+1)]; exact ih

private theorem curSize (n p : Nat) : (G n p).cur.size=3*n+1-3*p := by
  induction p with
  | zero => exact startSize n
  | succ p ih =>
    change (nextRow p _ (G n p).cur).size=_
    rw [nextSize,ih] <;> omega

private structure Compatible (n N p : Nat) : Prop where
  cur : agrees zeroCombination (3*n+1-3*p) (G n p).cur (G N p).cur
  prev : agrees zeroCombination (3*n+1-3*p) (G n p).prev (G N p).prev
  weights : ∀ a, a ≤ p → agrees zeroInterval (n+1-a) (W n p a) (W N p a)

private theorem compatible {n N : Nat} (hn : n ≤ N) (p : Nat) (hp : p ≤ n) :
    Compatible n N p := by
  induction p with
  | zero =>
    refine ⟨startAgrees hn,startAgrees hn,?_⟩
    intro a ha
    obtain rfl : a=0 := by omega
    intro b hb
    change entry zeroInterval (zeroWeights n (startAt n)) b = entry zeroInterval (zeroWeights N (startAt N)) b
    have hc := startAgrees hn
    have h1 := shiftAgrees (show 3*n+1 ≤ (startAt n).size by simp only [startSize] <;> omega) (by rw [startSize] <;> omega) hc
    have h2 := shiftAgrees (by rw [shiftSize,startSize] <;> omega) (by rw [shiftSize,startSize] <;> omega) h1
    rw [zeroWeights,tabGet _ (by omega),zeroWeights,tabGet _ (by omega)]
    by_cases he : b=0
    · simp [he]
    · rw [if_neg he,if_neg he,hc (b-1) (by omega),h2 (b-1) (by omega)]
  | succ p ih =>
    have hi := ih (by omega)
    have hc := hi.cur
    have hp' := hi.prev
    have step := nextAgrees (p:=p) (by simp only [curSize] <;> omega) (by rw [curSize] <;> omega)
      (fun b (hb : b < 3*n+1-3*p-3) => hp' b (by omega)) hc
    refine ⟨?_,?_,?_⟩
    · intro b hb
      apply step b; omega
    · intro b hb
      apply hc b; omega
    · intro a ha
      by_cases hva : a=p+1
      · subst a
        intro b hb
        change entry zeroInterval (entry #[] ((G n p).weights.push _) (p+1)) b =
          entry zeroInterval (entry #[] ((G N p).weights.push _) (p+1)) b
        rw [pushGet,pushGet,wSize,wSize,if_pos rfl,if_pos rfl,
          tabGet _ (by omega),tabGet _ (by omega)]
        exact congrArg (toWeight (p+1) b) (hc b (by omega))
      · rw [wStable (show a≤p by omega) (show p≤p+1 by omega),
            wStable (n:=N) (show a≤p by omega) (show p≤p+1 by omega)]
        exact hi.weights a (by omega)

private theorem singletonEntry {α : Type} (d x : α) : entry d #[x] 0 = x := rfl
private def R (n p a : Nat) := entry (#[] : Array Interval) (rhoPowers n p) a
private theorem rSize (n p : Nat) : (rhoPowers n p).size=p+1 := by
  induction p with
  | zero => rfl
  | succ p ih => simp [rhoPowers,ih]
private theorem rStable {n a p P : Nat} (ha : a ≤ p) (hp : p ≤ P) : R n P a=R n p a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp
  clear hp
  induction k with
  | zero => rfl
  | succ k ih =>
    change entry #[] ((rhoPowers n (p+k)).push _) a = _
    rw [pushGet,rSize,if_neg (by omega : a ≠ p+k+1)]; exact ih

private theorem rhoAgrees {n N : Nat} (hn : n ≤ N) (p : Nat) :
    ∀ a, a ≤ p → agrees zeroInterval (n+1) (R n p a) (R N p a) := by
  induction p with
  | zero =>
    intro a ha
    obtain rfl : a=0 := by omega
    intro j hj
    simp only [R,rhoPowers,singletonEntry]
    rw [tabGet _ hj,tabGet _ (by omega)]
  | succ p ih =>
    intro a ha
    by_cases he : a = p+1
    · subst a
      have h := ih p (Nat.le_refl p)
      intro j hj
      change entry zeroInterval (entry #[] ((rhoPowers n p).push _) (p+1)) j =
        entry zeroInterval (entry #[] ((rhoPowers N p).push _) (p+1)) j
      rw [pushGet,pushGet,rSize,rSize,if_pos rfl,if_pos rfl,rhoNext,tabGet _ hj,rhoNext,tabGet _ (by omega)]
      have sh (k : Nat) : shifted (R n p p) k j = shifted (R N p p) k j := by
        unfold shifted
        split
        · exact h _ (by omega)
        · rfl
      unfold R at sh
      rw [sh 1,sh 3,sh 5]
    · rw [rStable (show a≤p by omega) (show p≤p+1 by omega),
          rStable (n:=N) (show a≤p by omega) (show p≤p+1 by omega)]
      exact ih a (by omega)

private theorem sumI {f g : Nat → Interval} (n : Nat) (h : ∀ k, k<n → f k=g k) :
    sumIntervals f n = sumIntervals g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumIntervals,ih (fun i hi => h i (by omega)),h n (by omega)]

private theorem sum_cutoff {m n N : Nat} (hm : m ≤ n) (hn : n ≤ N) :
    fullSum (grid n (startAt n) n).weights (rhoPowers n n) m =
      fullSum (grid N (startAt N) N).weights (rhoPowers N N) m := by
  unfold fullSum
  apply sumI
  intro a ha
  apply sumI
  intro b hb
  have hwa := (compatible hn n (Nat.le_refl n)).weights a (by omega) b (by omega)
  rw [← wStable (n:=N) (show a≤n by omega) hn] at hwa
  have hra := rhoAgrees hn n a (by omega) (m-b) (by omega)
  rw [← rStable (n:=N) (show a≤n by omega) hn] at hra
  change scaleInterval _ (mulInterval _ (entry _ (W n n a) b) (entry _ (R n n a) (m-b))) =
    scaleInterval _ (mulInterval _ (entry _ (W N N a) b) (entry _ (R N N a) (m-b)))
  rw [hwa,hra]

private theorem allMatch {α : Type} (xs : List α) {f g : α → Bool}
    (h : ∀ x ∈ xs, f x=g x) : xs.all f = xs.all g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.all_cons,List.all_cons,h x (by simp),ih (fun y hy => h y (by simp [hy]))]

end CQCutoff

open CQCutoff

theorem solution {n N : Nat} (hn : n ≤ N) (indices : List Nat)
    (h : ∀ j ∈ indices, 2*j+3 ≤ n) :
    verifyList n indices = verifyList N indices := by
  apply allMatch indices
  intro j hj
  exact congrArg (fun v : Interval =>
    decide (max (-v.lo) v.hi * 10^40 ≤ coefficientScale*2*314159265358979323846*(cqHeadUnits[j]?.getD 0)))
      (sum_cutoff (h j hj) hn)
