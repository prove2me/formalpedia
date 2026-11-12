-- Prove2me | solution 1 for GreedySuperstring.LowerBound.binary_greedy_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:12:59.612661+00:00
-- url     : https://prove2.me/submissions/b31c7f25-88fa-471f-8743-65e8b096e966

import Mathlib
import Definitions.Def_GreedySuperstring_LowerBound_WordModel
import Definitions.Def_GreedySuperstring_LowerBound_GapModel
import Definitions.Def_GreedySuperstring_LowerBound_Construction
import Theorems.Thm_GreedySuperstring_LowerBound_gap_word_overlap
import Theorems.Thm_GreedySuperstring_LowerBound_greedy_invariants
import Theorems.Thm_GreedySuperstring_LowerBound_large_overlap_pairs
universe word_u

section
set_option autoImplicit false


namespace GreedySuperstring.Dev.GapOverlap

open GreedySuperstring.LowerBound

abbrev Pos (u : List ℕ) : Prop := ∀ g ∈ u, 0 < g

/-- bit version of the gap blocks -/
def bd (u : List ℕ) : List Bool :=
  u.flatMap (fun g => List.replicate (g - 1) false ++ [true])

/-- bit version of `gapWord` -/
def bw (L : ℕ) (u : List ℕ) (R : ℕ) : List Bool :=
  List.replicate L false ++ true :: (bd u ++ List.replicate R false)

@[simp] theorem bd_nil : bd [] = [] := rfl

@[simp] theorem bd_cons (g : ℕ) (u : List ℕ) :
    bd (g :: u) = List.replicate (g - 1) false ++ true :: bd u := by
  simp [bd]

def sym (b : Bool) : OAI.Superstring.Symbol := [b]

theorem sym_inj : Function.Injective sym := by
  intro a b h
  simpa [sym] using h

theorem gapWord_eq_map (L : ℕ) (u : List ℕ) (R : ℕ) :
    gapWord L u R = (bw L u R).map sym := by
  simp [gapWord, bw, bd, zeroSymbol, oneSymbol, sym, List.map_flatMap, List.map_replicate]

theorem rep_true_inj {a c : ℕ} {X Y : List Bool}
    (h : List.replicate a false ++ true :: X = List.replicate c false ++ true :: Y) :
    a = c ∧ X = Y := by
  induction a generalizing c with
  | zero =>
    cases c with
    | zero => simpa using h
    | succ c => simp [List.replicate_succ] at h
  | succ a ih =>
    cases c with
    | zero => simp [List.replicate_succ] at h
    | succ c =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      have := ih h
      exact ⟨by omega, this.2⟩

theorem rep_prefix_le {b c : ℕ} {t r : List Bool}
    (h : List.replicate b false ++ t = List.replicate c false ++ true :: r) : b ≤ c := by
  induction b generalizing c with
  | zero => omega
  | succ b ih =>
    cases c with
    | zero => simp [List.replicate_succ] at h
    | succ c =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      have := ih h
      omega

theorem allfalse_eq_rep {s : List Bool} (hs : ∀ x ∈ s, x = false) :
    s = List.replicate s.length false := by
  rw [List.eq_replicate_iff]
  exact ⟨rfl, hs⟩

theorem lemA2 {s : List Bool} (hs : ∀ x ∈ s, x = false) {a L : ℕ} {X Y : List Bool}
    (h : s ++ List.replicate a false ++ true :: X = List.replicate L false ++ true :: Y) :
    s ++ List.replicate a false = List.replicate L false ∧ X = Y := by
  have h' : List.replicate (s.length + a) false ++ true :: X =
      List.replicate L false ++ true :: Y := by
    rw [List.replicate_add, ← allfalse_eq_rep hs]; simpa using h
  have := rep_true_inj h'
  refine ⟨?_, this.2⟩
  rw [allfalse_eq_rep hs, ← List.replicate_add, this.1]

theorem lemB : ∀ (w u : List ℕ) (b R : ℕ) (t : List Bool), Pos w → Pos u →
    bd w ++ List.replicate b false ++ t = bd u ++ List.replicate R false →
    ∃ q, u = w ++ q ∧ (q = [] → b ≤ R) ∧ (∀ y, q.head? = some y → b < y) ∧
      (t = [] → q = [] ∧ b = R) := by
  intro w
  induction w with
  | nil =>
    intro u b R t _ hu h
    cases u with
    | nil =>
      have hl := congrArg List.length h
      simp at hl
      refine ⟨[], by simp, fun _ => by omega, by simp, fun ht => ⟨rfl, ?_⟩⟩
      subst ht; simpa using hl
    | cons g u' =>
      have hg : 0 < g := hu g (by simp)
      simp only [bd_nil, List.nil_append, bd_cons, List.append_assoc] at h
      have := rep_prefix_le h
      refine ⟨g :: u', by simp, fun h => by simp at h, fun y hy => ?_, fun ht => ?_⟩
      · simp at hy; omega
      · subst ht
        exfalso
        have : true ∈ List.replicate b false ++ ([] : List Bool) := by
          rw [h]; simp
        simp at this
  | cons g w' ih =>
    intro u b R t hw hu h
    cases u with
    | nil =>
      simp only [bd_cons, bd_nil, List.nil_append, List.append_assoc] at h
      have : true ∈ List.replicate R false := by rw [← h]; simp
      simp at this
    | cons g2 u2 =>
      simp only [bd_cons, List.append_assoc, List.cons_append] at h
      have h1 := rep_true_inj h
      have hg : 0 < g := hw g (by simp)
      have hg2 : 0 < g2 := hu g2 (by simp)
      have hgg : g = g2 := by omega
      subst hgg
      obtain ⟨q, hq, h2, h3, h4⟩ := ih u2 b R t (fun x hx => hw x (by simp [hx]))
        (fun x hx => hu x (by simp [hx])) (by simpa [List.append_assoc] using h1.2)
      exact ⟨q, by simp [hq], h2, h3, h4⟩

theorem exists_first_true {s : List Bool} (h : true ∈ s) :
    ∃ s1 s2, s = s1 ++ true :: s2 ∧ ∀ x ∈ s1, x = false := by
  induction s with
  | nil => simp at h
  | cons x s ih =>
    cases x with
    | true => exact ⟨[], s, by simp, by simp⟩
    | false =>
      have : true ∈ s := by simpa using h
      obtain ⟨s1, s2, h1, h2⟩ := ih this
      exact ⟨false :: s1, s2, by simp [h1], by simpa using h2⟩

theorem lemQ (R : ℕ) (u : List ℕ) (hu : Pos u) : ∀ (L : ℕ) (s : List Bool) (a : ℕ)
    (w : List ℕ) (b : ℕ) (t : List Bool), Pos w →
    s ++ List.replicate a false ++ true :: (bd w ++ List.replicate b false ++ t) =
      List.replicate L false ++ true :: (bd u ++ List.replicate R false) →
    ∃ p q : List ℕ, u = p ++ w ++ q ∧ (p = [] → a ≤ L) ∧
      (∀ x, p.getLast? = some x → a < x) ∧
      (q = [] → b ≤ R) ∧ (∀ y, q.head? = some y → b < y) ∧
      (s = [] → p = [] ∧ a = L) ∧ (t = [] → q = [] ∧ b = R) := by
  induction u with
  | nil =>
    intro L s a w b t hw h
    by_cases hs : ∀ x ∈ s, x = false
    · obtain ⟨h1, h2⟩ := lemA2 hs h
      obtain ⟨q, hq, h3, h4, h5⟩ := lemB w [] b R t hw hu (by simpa using h2)
      have hl := congrArg List.length h1
      simp at hl
      refine ⟨[], q, by simpa using hq, fun _ => by omega, by simp, h3, h4, ?_, h5⟩
      intro hs0
      subst hs0
      simp at hl
      exact ⟨rfl, hl⟩
    · push Not at hs
      obtain ⟨x, hx, hxf⟩ := hs
      have hxt : x = true := by simpa using hxf
      subst hxt
      obtain ⟨s1, s2, hs12, hs1⟩ := exists_first_true hx
      subst hs12
      have h' : List.replicate s1.length false ++ true :: (s2 ++ List.replicate a false ++ true ::
          (bd w ++ List.replicate b false ++ t)) =
          List.replicate L false ++ true :: (bd [] ++ List.replicate R false) := by
        rw [← allfalse_eq_rep hs1] ; simpa [List.append_assoc] using h
      have h2 := (rep_true_inj h').2
      have : true ∈ List.replicate R false := by
        rw [bd_nil, List.nil_append] at h2
        rw [← h2]; simp
      simp at this
  | cons g u' ih =>
    intro L s a w b t hw h
    have hg : 0 < g := hu g (by simp)
    have hu' : Pos u' := fun x hx => hu x (by simp [hx])
    by_cases hs : ∀ x ∈ s, x = false
    · obtain ⟨h1, h2⟩ := lemA2 hs h
      obtain ⟨q, hq, h3, h4, h5⟩ := lemB w (g :: u') b R t hw hu h2
      have hl := congrArg List.length h1
      simp at hl
      refine ⟨[], q, by simpa using hq, fun _ => by omega, by simp, h3, h4, ?_, h5⟩
      intro hs0
      subst hs0
      simp at hl
      exact ⟨rfl, hl⟩
    · push Not at hs
      obtain ⟨x, hx, hxf⟩ := hs
      have hxt : x = true := by simpa using hxf
      subst hxt
      obtain ⟨s1, s2, hs12, hs1⟩ := exists_first_true hx
      subst hs12
      have h' : List.replicate s1.length false ++ true :: (s2 ++ List.replicate a false ++ true ::
          (bd w ++ List.replicate b false ++ t)) =
          List.replicate L false ++ true :: (bd (g :: u') ++ List.replicate R false) := by
        rw [← allfalse_eq_rep hs1] ; simpa [List.append_assoc] using h
      have h2 := (rep_true_inj h').2
      rw [bd_cons, List.append_assoc] at h2
      obtain ⟨p', q, hpq, e1, e2, e3, e4, -, e6⟩ := ih hu' (g - 1) s2 a w b t hw
        (by simpa [List.append_assoc] using h2)
      refine ⟨g :: p', q, by simp [hpq], by simp, ?_, e3, e4, by simp, e6⟩
      intro x hx
      cases p' with
      | nil => simp at hx; have := e1 rfl; omega
      | cons y p'' =>
        have := e2 x (by simpa [List.getLast?_cons_cons] using hx)
        exact this

theorem infix_bits {a b L R : ℕ} {w u : List ℕ} (hw : Pos w) (hu : Pos u)
    (h : bw a w b <:+: bw L u R) :
    ∃ p q : List ℕ, u = p ++ w ++ q ∧ (p = [] → a ≤ L) ∧
      (∀ x, p.getLast? = some x → a < x) ∧
      (q = [] → b ≤ R) ∧ (∀ y, q.head? = some y → b < y) := by
  obtain ⟨s, t, hst⟩ := h
  obtain ⟨p, q, h1, h2, h3, h4, h5, -, -⟩ := lemQ R u hu L s a w b t hw
    (by simpa [bw, List.append_assoc] using hst)
  exact ⟨p, q, h1, h2, h3, h4, h5⟩


theorem bd_length {u : List ℕ} (hu : Pos u) : (bd u).length = u.sum := by
  induction u with
  | nil => simp
  | cons g u ih =>
    have hg : 0 < g := hu g (by simp)
    have := ih (fun x hx => hu x (by simp [hx]))
    simp only [bd_cons, List.length_append, List.length_replicate, List.length_cons, List.sum_cons]
    omega

theorem bw_length {L R : ℕ} {u : List ℕ} (hu : Pos u) :
    (bw L u R).length = L + 1 + u.sum + R := by
  simp [bw, bd_length hu]
  omega

end GreedySuperstring.Dev.GapOverlap

namespace GreedySuperstring.LowerBound

open GreedySuperstring.Dev.GapOverlap

theorem infix_gapWord {a b L R : ℕ} {w u : List ℕ} (hw : ∀ g ∈ w, 0 < g) (hu : ∀ g ∈ u, 0 < g)
    (h : gapWord a w b <:+: gapWord L u R) :
    ∃ p q : List ℕ, u = p ++ w ++ q ∧ (p = [] → a ≤ L) ∧ (∀ x, p.getLast? = some x → a < x) ∧
      (q = [] → b ≤ R) ∧ (∀ y, q.head? = some y → b < y) := by
  rw [gapWord_eq_map, gapWord_eq_map, List.infix_map_iff] at h
  obtain ⟨l, hl, he⟩ := h
  have := List.map_injective_iff.mpr sym_inj he
  subst this
  exact infix_bits hw hu hl


theorem gapWord_length {L R : ℕ} {u : List ℕ} (hu : ∀ g ∈ u, 0 < g) :
    (gapWord L u R).length = L + 1 + u.sum + R := by
  rw [gapWord_eq_map, List.length_map, bw_length hu]

end GreedySuperstring.LowerBound
end

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace GreedySuperstring.Dev.Family

open GreedySuperstring.LowerBound OAI.Superstring

/-- gap lists of the five kinds, in order X Y U V Z -/
def gp (k : Fin 5) (c m : ℕ) : List ℕ :=
  match k with
  | 0 => [m, c, m, c]
  | 1 => [c, m, c, m]
  | 2 => [c, c, m, c]
  | 3 => [c, m, c, c]
  | 4 => [c, c, m]

def lpad (k : Fin 5) (r P : ℕ) : ℕ :=
  match k with
  | 0 => P + 2 * r
  | 1 => P
  | 2 => P
  | 3 => P
  | 4 => P + r

def rpad (k : Fin 5) (r P : ℕ) : ℕ :=
  match k with
  | 0 => P
  | 1 => P + 4 * r
  | 2 => P
  | 3 => P + r
  | 4 => 0

def W (k : Fin 5) (r P i : ℕ) : Word :=
  gapWord (lpad k r P) (gp k (commonGap r P) (privateGap r P i)) (rpad k r P)

theorem mem_iff_W (r P : ℕ) (s : Word) :
    s ∈ inputFamily r P ↔ ∃ k i, 1 ≤ i ∧ i ≤ r ∧ s = W k r P i := by
  simp only [inputFamily, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨i, ⟨h1, h2⟩, h⟩
    rcases h with h | h | h | h | h
    · exact ⟨0, i, h1, h2, h⟩
    · exact ⟨1, i, h1, h2, h⟩
    · exact ⟨2, i, h1, h2, h⟩
    · exact ⟨3, i, h1, h2, h⟩
    · exact ⟨4, i, h1, h2, h⟩
  · rintro ⟨k, i, h1, h2, h⟩
    refine ⟨i, ⟨h1, h2⟩, ?_⟩
    fin_cases k
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem gp_pos (k : Fin 5) {c m : ℕ} (hc : 0 < c) (hm : 0 < m) : ∀ g ∈ gp k c m, 0 < g := by
  intro g hg
  fin_cases k <;> simp [gp] at hg <;> omega

/-- a segment decomposition is a decomposition by `take` -/
theorem seg_take {w u : List ℕ} {C : List ℕ → List ℕ → Prop}
    (h : ∃ p q, u = p ++ w ++ q ∧ C p q) :
    ∃ k, k ≤ u.length ∧ ∃ q, u = u.take k ++ w ++ q ∧ C (u.take k) q := by
  obtain ⟨p, q, hu, hC⟩ := h
  refine ⟨p.length, ?_, q, ?_, ?_⟩
  · rw [hu]; simp
  · have : u.take p.length = p := by rw [hu]; simp
    rw [this]; exact hu
  · have : u.take p.length = p := by rw [hu]; simp
    rw [this]; exact hC

theorem not_infix (k l : Fin 5) (r P i j : ℕ) (hr : 1 ≤ r)
    (hi1 : 1 ≤ i) (hi2 : i ≤ r) (hj1 : 1 ≤ j) (hj2 : j ≤ r)
    (hne : k ≠ l ∨ i ≠ j) : ¬ W k r P i <:+: W l r P j := by
  intro h
  have hc : 0 < commonGap r P := by unfold commonGap; omega
  have hm : ∀ i, 0 < privateGap r P i := by intro i; unfold privateGap; omega
  obtain ⟨p, q, hu, h1, h2, h3, h4⟩ := infix_gapWord (gp_pos k hc (hm i)) (gp_pos l hc (hm j)) h
  have key := seg_take (w := gp k (commonGap r P) (privateGap r P i))
    (u := gp l (commonGap r P) (privateGap r P j))
    (C := fun p q => (p = [] → lpad k r P ≤ lpad l r P) ∧ (∀ x, p.getLast? = some x → lpad k r P < x) ∧
      (q = [] → rpad k r P ≤ rpad l r P) ∧ (∀ y, q.head? = some y → rpad k r P < y))
    ⟨p, q, hu, h1, h2, h3, h4⟩
  obtain ⟨n, hn, q', hu', c1, c2, c3, c4⟩ := key
  unfold commonGap privateGap at *
  fin_cases k <;> fin_cases l <;> simp [gp, lpad, rpad] at hn hu' c1 c2 c3 c4 hne <;>
    interval_cases n <;> simp at hu' c1 c2 c3 c4 <;> omega

/-! ### converse of `infix_gapWord` -/

def blk (g : ℕ) : Word := List.replicate (g - 1) zeroSymbol ++ [oneSymbol]

theorem gapWord_eq (L : ℕ) (u : List ℕ) (R : ℕ) :
    gapWord L u R = (List.replicate L zeroSymbol ++ [oneSymbol]) ++ u.flatMap blk ++
      List.replicate R zeroSymbol := rfl

theorem rep_split (n a : ℕ) (h : a ≤ n) :
    List.replicate n zeroSymbol = List.replicate (n - a) zeroSymbol ++ List.replicate a zeroSymbol := by
  rw [← List.replicate_add]; congr 1; omega

theorem rep_split' (n a : ℕ) (h : a ≤ n) :
    List.replicate n zeroSymbol = List.replicate a zeroSymbol ++ List.replicate (n - a) zeroSymbol := by
  rw [← List.replicate_add]; congr 1; omega

theorem pre_split {a L : ℕ} {p : List ℕ} (h1 : p = [] → a ≤ L)
    (h2 : ∀ x, p.getLast? = some x → a < x) :
    ∃ A : Word, List.replicate L zeroSymbol ++ [oneSymbol] ++ p.flatMap blk =
      A ++ (List.replicate a zeroSymbol ++ [oneSymbol]) := by
  rcases List.eq_nil_or_concat p with rfl | ⟨p', x, rfl⟩
  · refine ⟨List.replicate (L - a) zeroSymbol, ?_⟩
    rw [rep_split L a (h1 rfl)]
    simp only [List.flatMap_nil, List.append_nil, List.append_assoc]
  · have hx := h2 x (by simp)
    refine ⟨List.replicate L zeroSymbol ++ [oneSymbol] ++ p'.flatMap blk ++
      List.replicate (x - 1 - a) zeroSymbol, ?_⟩
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, blk, List.concat_eq_append]
    rw [rep_split (x - 1) a (by omega)]
    simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem suf_split {b R : ℕ} {q : List ℕ} (h1 : q = [] → b ≤ R)
    (h2 : ∀ y, q.head? = some y → b < y) :
    ∃ B : Word, q.flatMap blk ++ List.replicate R zeroSymbol =
      List.replicate b zeroSymbol ++ B := by
  rcases q with _ | ⟨y, q'⟩
  · refine ⟨List.replicate (R - b) zeroSymbol, ?_⟩
    rw [rep_split' R b (h1 rfl)]
    simp only [List.flatMap_nil, List.nil_append]
  · have hy := h2 y (by simp)
    refine ⟨List.replicate (y - 1 - b) zeroSymbol ++ [oneSymbol] ++ q'.flatMap blk ++
      List.replicate R zeroSymbol, ?_⟩
    simp only [List.flatMap_cons, blk]
    rw [rep_split' (y - 1) b (by omega)]
    simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem gapWord_infix_of {a b L R : ℕ} {w u : List ℕ} (p q : List ℕ) (hu : u = p ++ w ++ q)
    (h1 : p = [] → a ≤ L) (h2 : ∀ x, p.getLast? = some x → a < x)
    (h3 : q = [] → b ≤ R) (h4 : ∀ y, q.head? = some y → b < y) :
    gapWord a w b <:+: gapWord L u R := by
  obtain ⟨A, hA⟩ := pre_split h1 h2
  obtain ⟨B, hB⟩ := suf_split h3 h4
  refine ⟨A, B, ?_⟩
  rw [gapWord_eq, gapWord_eq, hu]
  simp only [List.flatMap_append, List.append_assoc] at hA hB ⊢
  have e1 : List.replicate L zeroSymbol ++ ([oneSymbol] ++ (p.flatMap blk ++ (w.flatMap blk ++
      (q.flatMap blk ++ List.replicate R zeroSymbol)))) =
      (List.replicate L zeroSymbol ++ ([oneSymbol] ++ p.flatMap blk)) ++ (w.flatMap blk ++
        (q.flatMap blk ++ List.replicate R zeroSymbol)) := by simp
  rw [e1, hA, hB]
  simp

/-! ### the short word -/

def sb (c P r : ℕ) (j : ℕ) : List ℕ := [c, c, P + r + (j + 1), c, P + r + (j + 1)]

theorem shortList_eq (r P : ℕ) :
    ((List.range r).flatMap (fun j =>
      [commonGap r P, commonGap r P, privateGap r P (j + 1),
       commonGap r P, privateGap r P (j + 1)])) ++ [commonGap r P, commonGap r P] =
    ((List.range r).flatMap (sb (commonGap r P) P r)) ++ [commonGap r P, commonGap r P] := by
  rfl

theorem pre_prop (c P r k : ℕ) :
    ((List.range k).flatMap (sb c P r) = [] ∨
      ((List.range k).flatMap (sb c P r)).getLast? = some (P + r + k)) ∧
    (k = 0 → (List.range k).flatMap (sb c P r) = []) ∧
    (1 ≤ k → ((List.range k).flatMap (sb c P r)).getLast? = some (P + r + k)) := by
  rcases k with _ | k
  · simp
  · refine ⟨Or.inr ?_, by simp, fun _ => ?_⟩ <;>
    · rw [List.range_succ, List.flatMap_append]
      simp [sb]

theorem split_short (r P i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ r) :
    ∃ pre post : List ℕ,
      ((List.range (r)).flatMap (sb (commonGap r P) P r)) ++ [commonGap r P, commonGap r P] =
        pre ++ [commonGap r P, commonGap r P, privateGap r P i, commonGap r P, privateGap r P i]
          ++ (commonGap r P :: commonGap r P :: post) ∧
      (i = 1 → pre = []) ∧ (2 ≤ i → pre.getLast? = some (P + r + (i - 1))) ∧
      (i = r → post = []) ∧ (i < r → post.head? = some (P + r + (i + 1))) := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  obtain ⟨n, hn⟩ : ∃ n, r = k + 1 + n := ⟨r - (k + 1), by omega⟩
  have hr : List.range r = List.range k ++ (List.range (n + 1)).map (fun j => k + j) := by
    rw [show r = k + (n + 1) by omega, List.range_add]
  have hs : ∀ c : ℕ, (List.range r).flatMap (sb c P r) =
      (List.range k).flatMap (sb c P r) ++ (sb c P r k ++
        ((List.range n).map (fun j => k + (j + 1))).flatMap (sb c P r)) := by
    intro c
    rw [hr, List.range_succ_eq_map]
    simp [List.flatMap_append, Function.comp_def]
  obtain ⟨hp1, hp2, hp3⟩ := pre_prop (commonGap r P) P r k
  rcases n with _ | n
  · refine ⟨(List.range k).flatMap (sb (commonGap r P) P r), [], ?_, ?_, ?_, ?_, ?_⟩
    · rw [hs]; simp [sb, privateGap]
    · intro h; exact hp2 (by omega)
    · intro h; have := hp3 (by omega); simpa using this
    · intro; rfl
    · intro h; omega
  · refine ⟨(List.range k).flatMap (sb (commonGap r P) P r),
      (P + r + (k + 1 + 1)) :: commonGap r P :: (P + r + (k + 1 + 1)) ::
        (((List.range n).map (fun j => k + (j + 1 + 1))).flatMap (sb (commonGap r P) P r) ++
          [commonGap r P, commonGap r P]), ?_, ?_, ?_, ?_, ?_⟩
    · rw [hs, List.range_succ_eq_map]
      simp [sb, privateGap, List.flatMap_append, Function.comp_def]
    · intro h; exact hp2 (by omega)
    · intro h; have := hp3 (by omega); simpa using this
    · intro h; omega
    · intro h; simp

theorem shortWord_eq (r P : ℕ) :
    shortWord r P = gapWord (P + r) (((List.range r).flatMap (sb (commonGap r P) P r)) ++
      [commonGap r P, commonGap r P]) (P + r) := by
  unfold shortWord
  rw [← shortList_eq]

theorem W_infix_short (r P : ℕ) (hr : 1 ≤ r) (k : Fin 5) (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ r) :
    W k r P i <:+: shortWord r P := by
  obtain ⟨pre, post, hS, hp1, hp2, hq1, hq2⟩ := split_short r P i hi1 hi2
  rw [shortWord_eq]
  have hc : commonGap r P = P + 8 * r := rfl
  have hm : privateGap r P i = P + r + i := rfl
  have hpl : ∀ x, pre.getLast? = some x → x = P + r + (i - 1) ∧ 2 ≤ i := by
    intro x hx
    by_cases h1 : i = 1
    · rw [hp1 h1] at hx; simp at hx
    · rw [hp2 (by omega)] at hx
      cases hx; exact ⟨rfl, by omega⟩
  have hpn : pre = [] → i = 1 := by
    intro h
    by_contra h1
    have := hp2 (by omega)
    rw [h] at this; simp at this
  have hql : ∀ y, post.head? = some y → y = P + r + (i + 1) ∧ i < r := by
    intro y hy
    by_cases h1 : i = r
    · rw [hq1 h1] at hy; simp at hy
    · rw [hq2 (by omega)] at hy
      cases hy; exact ⟨rfl, by omega⟩
  have hqn : post = [] → i = r := by
    intro h
    by_contra h1
    have := hq2 (by omega)
    rw [h] at this; simp at this
  fin_cases k
  · -- X
    refine gapWord_infix_of (pre ++ [commonGap r P, commonGap r P]) (commonGap r P :: post) ?_ ?_ ?_ ?_ ?_
    · rw [hS]; simp [gp]
    · intro h; simp at h
    · intro x hx; simp at hx; subst hx; simp [W, lpad, hc]; omega
    · intro h; simp at h
    · intro y hy; simp at hy; subst hy; simp [W, rpad, hc]; omega
  · -- Y
    refine gapWord_infix_of (pre ++ [commonGap r P]) (commonGap r P :: commonGap r P :: post) ?_ ?_ ?_ ?_ ?_
    · rw [hS]; simp [gp]
    · intro h; simp at h
    · intro x hx; simp at hx; subst hx; simp [W, lpad, hc]; omega
    · intro h; simp at h
    · intro y hy; simp at hy; subst hy; simp [W, rpad, hc]; omega
  · -- U
    refine gapWord_infix_of pre (privateGap r P i :: commonGap r P :: commonGap r P :: post) ?_ ?_ ?_ ?_ ?_
    · rw [hS]; simp [gp]
    · intro h; have := hpn h; simp [W, lpad]
    · intro x hx; have := hpl x hx; simp [W, lpad]; omega
    · intro h; simp at h
    · intro y hy; simp at hy; subst hy; simp [W, rpad, hm]; omega
  · -- V
    refine gapWord_infix_of (pre ++ [commonGap r P, commonGap r P, privateGap r P i]) post ?_ ?_ ?_ ?_ ?_
    · rw [hS]; simp [gp]
    · intro h; simp at h
    · intro x hx; simp at hx; subst hx; simp [W, lpad, hm]; omega
    · intro h; have := hqn h; simp [rpad]
    · intro y hy; have := hql y hy; simp [W, rpad]; omega
  · -- Z
    refine gapWord_infix_of pre (commonGap r P :: privateGap r P i :: commonGap r P :: commonGap r P :: post)
      ?_ ?_ ?_ ?_ ?_
    · rw [hS]; simp [gp]
    · intro h; have := hpn h; simp [W, lpad]
    · intro x hx; have := hpl x hx; simp [W, lpad]; omega
    · intro h; simp at h
    · intro y hy; simp at hy; subst hy; simp [W, rpad]; omega

theorem gapWord_binary (L : ℕ) (u : List ℕ) (R : ℕ) : IsBinary (gapWord L u R) := by
  intro a ha
  simp only [gapWord, List.mem_append, List.mem_replicate, List.mem_flatMap, List.mem_singleton]
    at ha
  rcases ha with ((⟨_, rfl⟩ | rfl) | ⟨g, _, ⟨_, rfl⟩ | rfl⟩) | ⟨_, rfl⟩ <;>
    simp [zeroSymbol, oneSymbol]

theorem W_ne_nil (k : Fin 5) (r P i : ℕ) : W k r P i ≠ [] := by
  simp [W, gapWord]

theorem W_inj (k l : Fin 5) (r P i j : ℕ) (hr : 1 ≤ r) (hi1 : 1 ≤ i) (hi2 : i ≤ r)
    (hj1 : 1 ≤ j) (hj2 : j ≤ r) (h : W k r P i = W l r P j) : k = l ∧ i = j := by
  by_contra hne
  have := not_infix k l r P i j hr hi1 hi2 hj1 hj2 (by tauto)
  exact this (h ▸ List.infix_refl _)

theorem sum_sb (c P r n : ℕ) :
    ((List.range n).flatMap (sb c P r)).sum = n * (3 * c) + n * (2 * (P + r)) + n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.sum_append, ih]
    simp only [sb, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.sum_cons,
      List.sum_nil]
    ring

theorem shortWord_len (r P : ℕ) (hr : 1 ≤ r) :
    (shortWord r P).length = 5 * P * r + 27 * r ^ 2 + 4 * P + 19 * r + 1 := by
  rw [shortWord_eq, gapWord_length]
  · rw [List.sum_append, sum_sb]
    simp only [commonGap, List.sum_cons, List.sum_nil]
    ring
  · intro g hg
    simp only [List.mem_append, List.mem_flatMap, List.mem_range, sb, List.mem_cons,
      List.not_mem_nil, or_false] at hg
    rcases hg with ⟨j, _, h⟩ | h
    · simp [commonGap] at h
      rcases h with rfl | rfl | rfl | rfl | rfl <;> omega
    · rcases h with rfl | rfl <;> simp [commonGap] <;> omega

end GreedySuperstring.Dev.Family

namespace GreedySuperstring.LowerBound
open GreedySuperstring.Dev.Family OAI.Superstring

theorem mem_inputFamily_iff (r P : ℕ) (s : Word) :
    s ∈ inputFamily r P ↔ ∃ i, 1 ≤ i ∧ i ≤ r ∧
      (s = X r P i ∨ s = Y r P i ∨ s = U r P i ∨ s = V r P i ∨ s = Z r P i) := by
  rw [mem_iff_W]
  constructor
  · rintro ⟨k, i, h1, h2, h⟩
    refine ⟨i, h1, h2, ?_⟩
    fin_cases k
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · rintro ⟨i, h1, h2, h | h | h | h | h⟩
    · exact ⟨0, i, h1, h2, h⟩
    · exact ⟨1, i, h1, h2, h⟩
    · exact ⟨2, i, h1, h2, h⟩
    · exact ⟨3, i, h1, h2, h⟩
    · exact ⟨4, i, h1, h2, h⟩

theorem inputFamily_substringFree (r P : ℕ) (hr : 1 ≤ r) (hP : r ≤ P + 1) :
    SubstringFree (inputFamily r P) := by
  intro s hs t ht hne hinf
  obtain ⟨k, i, hi1, hi2, rfl⟩ := (mem_iff_W r P s).mp hs
  obtain ⟨l, j, hj1, hj2, rfl⟩ := (mem_iff_W r P t).mp ht
  refine not_infix k l r P i j hr hi1 hi2 hj1 hj2 ?_ hinf
  by_contra h
  push Not at h
  obtain ⟨rfl, rfl⟩ := h
  exact hne rfl

theorem inputFamily_card (r P : ℕ) (hr : 1 ≤ r) (hP : r ≤ P + 1) :
    (inputFamily r P).card = 5 * r := by
  have : inputFamily r P = ((Finset.univ : Finset (Fin 5)) ×ˢ Finset.Icc 1 r).image
      (fun x => W x.1 r P x.2) := by
    ext s
    rw [mem_iff_W]
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, Finset.mem_Icc, true_and,
      Prod.exists]
    constructor
    · rintro ⟨k, i, h1, h2, h⟩; exact ⟨k, i, ⟨h1, h2⟩, h.symm⟩
    · rintro ⟨k, i, ⟨h1, h2⟩, h⟩; exact ⟨k, i, h1, h2, h.symm⟩
  rw [this, Finset.card_image_of_injOn]
  · simp [mul_comm]
  · rintro ⟨k, i⟩ hk ⟨l, j⟩ hl h
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_univ, Set.mem_univ, Finset.coe_Icc,
      Set.mem_Icc, true_and] at hk hl
    obtain ⟨rfl, rfl⟩ := W_inj k l r P i j hr hk.1 hk.2 hl.1 hl.2 h
    rfl

theorem inputFamily_ne_nil (r P : ℕ) (hr : 1 ≤ r) (hP : r ≤ P + 1) :
    ∀ s ∈ inputFamily r P, s ≠ [] := by
  intro s hs
  obtain ⟨k, i, _, _, rfl⟩ := (mem_iff_W r P s).mp hs
  exact W_ne_nil k r P i

theorem inputFamily_binary (r P : ℕ) (hr : 1 ≤ r) (hP : r ≤ P + 1) :
    ∀ s ∈ inputFamily r P, IsBinary s := by
  intro s hs
  obtain ⟨k, i, _, _, rfl⟩ := (mem_iff_W r P s).mp hs
  exact gapWord_binary _ _ _

theorem shortWord_binary (r P : ℕ) : IsBinary (shortWord r P) := by
  rw [shortWord_eq]; exact gapWord_binary _ _ _

/-- NOTE: needs `1 ≤ r`; for `r = P = 0` the word is `[1,1,1]` (length 3, formula gives 1). -/
theorem shortWord_length (r P : ℕ) (hr : 1 ≤ r) :
    (shortWord r P).length = 5 * P * r + 27 * r ^ 2 + 4 * P + 19 * r + 1 :=
  shortWord_len r P hr

theorem shortWord_superstring (r P : ℕ) (hr : 1 ≤ r) (hP : r ≤ P + 1) :
    IsCommonSuperstring (inputFamily r P).toList (shortWord r P) := by
  intro s hs
  rw [Finset.mem_toList] at hs
  obtain ⟨k, i, hi1, hi2, rfl⟩ := (mem_iff_W r P s).mp hs
  exact W_infix_short r P hr k i hi1 hi2

end GreedySuperstring.LowerBound
end

section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace GreedySuperstring.Dev.Table

open GreedySuperstring.LowerBound OAI.Superstring GreedySuperstring.Dev.Family

theorem mem_gapMatches {L R L' R' : ℕ} {u v : List ℕ} {j : ℕ} :
    j ∈ gapMatches L R u L' R' v ↔
      j < min u.length v.length + 1 ∧ gapTests L R u L' R' v j = true := by
  simp [gapMatches]

theorem overlapLength_le_length {α : Type} [DecidableEq α] (s t : List α) :
    overlapLength s t ≤ t.length := by
  unfold overlapLength
  apply Finset.sup_le
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn
  simp only [id]
  have := hn.1
  have := min_le_right s.length t.length
  omega

theorem take_sum_mono (v : List ℕ) {j j' : ℕ} (h : j ≤ j') : (v.take j).sum ≤ (v.take j').sum := by
  have : v.take j <+: v.take j' := List.take_prefix_take_left (l := v) h
  obtain ⟨t, ht⟩ := this
  rw [← ht, List.sum_append]
  omega

/-- the overlap length of two gap words, in numbers -/
theorem ovlLen_formula (L R L' R' : ℕ) (u v : List ℕ)
    (hu : ∀ g ∈ u, 0 < g) (hv : ∀ g ∈ v, 0 < g)
    (hst : ¬ gapWord L u R <:+: gapWord L' v R')
    (hts : ¬ gapWord L' v R' <:+: gapWord L u R) :
    overlapLength (gapWord L u R) (gapWord L' v R') =
      if (gapMatches L R u L' R' v).Nonempty then
        L' + 1 + (v.take ((gapMatches L R u L' R' v).sup id)).sum + R
      else min R L' := by
  have h := GreedySuperstring.LowerBound.gap_word_overlap L R L' R' u v hu hv hst hts
  have hlen : overlapLength (gapWord L u R) (gapWord L' v R') =
      (overlap (gapWord L u R) (gapWord L' v R')).length := by
    unfold overlap
    rw [List.length_take, Nat.min_eq_left (overlapLength_le_length _ _)]
  rw [hlen, h]
  split_ifs
  · rw [gapWord_length]
    intro g hg
    exact hv g (List.mem_of_mem_take hg)
  · simp

theorem ovl_le_core (L R L' R' : ℕ) (u v : List ℕ)
    (hu : ∀ g ∈ u, 0 < g) (hv : ∀ g ∈ v, 0 < g)
    (hst : ¬ gapWord L u R <:+: gapWord L' v R')
    (hts : ¬ gapWord L' v R' <:+: gapWord L u R) (B : ℕ) (hB : min R L' ≤ B)
    (h : ∀ j, j < min u.length v.length + 1 → gapTests L R u L' R' v j = true →
      L' + 1 + (v.take j).sum + R ≤ B) :
    overlapLength (gapWord L u R) (gapWord L' v R') ≤ B := by
  rw [ovlLen_formula L R L' R' u v hu hv hst hts]
  split_ifs with hne
  · obtain ⟨j0, hj0, hjsup⟩ := Finset.exists_mem_eq_sup _ hne id
    rw [hjsup]
    simp only [id]
    have := mem_gapMatches.mp hj0
    exact h _ this.1 this.2
  · exact hB

theorem ovl_ge_core (L R L' R' : ℕ) (u v : List ℕ)
    (hu : ∀ g ∈ u, 0 < g) (hv : ∀ g ∈ v, 0 < g)
    (hst : ¬ gapWord L u R <:+: gapWord L' v R')
    (hts : ¬ gapWord L' v R' <:+: gapWord L u R) (j : ℕ)
    (hj : j < min u.length v.length + 1) (ht : gapTests L R u L' R' v j = true) :
    L' + 1 + (v.take j).sum + R ≤ overlapLength (gapWord L u R) (gapWord L' v R') := by
  rw [ovlLen_formula L R L' R' u v hu hv hst hts]
  have hmem : j ∈ gapMatches L R u L' R' v := mem_gapMatches.mpr ⟨hj, ht⟩
  rw [if_pos ⟨j, hmem⟩]
  have := Finset.le_sup (f := id) hmem
  have := take_sum_mono v (show j ≤ (gapMatches L R u L' R' v).sup id from this)
  omega


theorem W_le (k l : Fin 5) (r P i j : ℕ) (hr : 1 ≤ r)
    (hi1 : 1 ≤ i) (hi2 : i ≤ r) (hj1 : 1 ≤ j) (hj2 : j ≤ r) (hne : k ≠ l ∨ i ≠ j) (B : ℕ)
    (hB : min (rpad k r P) (lpad l r P) ≤ B)
    (h : ∀ jj, jj < min (gp k (commonGap r P) (privateGap r P i)).length
        (gp l (commonGap r P) (privateGap r P j)).length + 1 →
      gapTests (lpad k r P) (rpad k r P) (gp k (commonGap r P) (privateGap r P i))
        (lpad l r P) (rpad l r P) (gp l (commonGap r P) (privateGap r P j)) jj = true →
      lpad l r P + 1 + ((gp l (commonGap r P) (privateGap r P j)).take jj).sum + rpad k r P ≤ B) :
    overlapLength (W k r P i) (W l r P j) ≤ B := by
  have hc : 0 < commonGap r P := by unfold commonGap; omega
  have hm : ∀ i, 0 < privateGap r P i := by intro i; unfold privateGap; omega
  exact ovl_le_core _ _ _ _ _ _ (gp_pos k hc (hm i)) (gp_pos l hc (hm j))
    (not_infix k l r P i j hr hi1 hi2 hj1 hj2 hne)
    (not_infix l k r P j i hr hj1 hj2 hi1 hi2 (by tauto)) B hB h

theorem W_ge (k l : Fin 5) (r P i j : ℕ) (hr : 1 ≤ r)
    (hi1 : 1 ≤ i) (hi2 : i ≤ r) (hj1 : 1 ≤ j) (hj2 : j ≤ r) (hne : k ≠ l ∨ i ≠ j) (jj : ℕ)
    (hjj : jj < min (gp k (commonGap r P) (privateGap r P i)).length
        (gp l (commonGap r P) (privateGap r P j)).length + 1)
    (ht : gapTests (lpad k r P) (rpad k r P) (gp k (commonGap r P) (privateGap r P i))
        (lpad l r P) (rpad l r P) (gp l (commonGap r P) (privateGap r P j)) jj = true) :
    lpad l r P + 1 + ((gp l (commonGap r P) (privateGap r P j)).take jj).sum + rpad k r P ≤
      overlapLength (W k r P i) (W l r P j) := by
  have hc : 0 < commonGap r P := by unfold commonGap; omega
  have hm : ∀ i, 0 < privateGap r P i := by intro i; unfold privateGap; omega
  exact ovl_ge_core _ _ _ _ _ _ (gp_pos k hc (hm i)) (gp_pos l hc (hm j))
    (not_infix k l r P i j hr hi1 hi2 hj1 hj2 hne)
    (not_infix l k r P j i hr hj1 hj2 hi1 hi2 (by tauto)) jj hjj ht

end GreedySuperstring.Dev.Table

namespace GreedySuperstring.LowerBound

open GreedySuperstring.Dev.Family GreedySuperstring.Dev.Table

/- Table of exact overlap lengths (Table 2 and the step (ii)-(iv) bounds), `overlapLength` form. -/
section Table
variable (r P : ℕ) (hr : 1 ≤ r) (hP : r ≤ P + 1)
include hr hP

theorem ovl_XY {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ r) :
    overlapLength (X r P i) (Y r P i) = alpha r P i := by
  show overlapLength (W 0 r P i) (W 1 r P i) = alpha r P i
  have hle : overlapLength (W 0 r P i) (W 1 r P i) ≤ alpha r P i := by
    apply W_le 0 1 r P i i hr h1 h2 h1 h2 (Or.inl (by decide))
    · simp [lpad, rpad, alpha, beta, gamma] <;> omega
    · intro jj' hjj ht
      simp only [commonGap, privateGap, alpha, beta, gamma] at *
      simp [gp, lpad, rpad] at hjj ht ⊢
      interval_cases jj' <;> simp [gapTests] at ht ⊢ <;> omega
  have hge := W_ge 0 1 r P i i hr h1 h2 h1 h2 (Or.inl (by decide)) 3 (by simp [gp])
    (by unfold commonGap privateGap; simp only [lpad, rpad, gp]; simp [gapTests]; omega)
  simp only [commonGap, privateGap, alpha, beta, gamma] at *
  simp [gp, lpad, rpad] at hge ⊢
  omega

theorem ovl_XV {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ r) :
    overlapLength (X r P i) (V r P i) = alpha r P i := by
  show overlapLength (W 0 r P i) (W 3 r P i) = alpha r P i
  have hle : overlapLength (W 0 r P i) (W 3 r P i) ≤ alpha r P i := by
    apply W_le 0 3 r P i i hr h1 h2 h1 h2 (Or.inl (by decide))
    · simp [lpad, rpad, alpha, beta, gamma] <;> omega
    · intro jj' hjj ht
      simp only [commonGap, privateGap, alpha, beta, gamma] at *
      simp [gp, lpad, rpad] at hjj ht ⊢
      interval_cases jj' <;> simp [gapTests] at ht ⊢ <;> omega
  have hge := W_ge 0 3 r P i i hr h1 h2 h1 h2 (Or.inl (by decide)) 3 (by simp [gp])
    (by unfold commonGap privateGap; simp only [lpad, rpad, gp]; simp [gapTests]; omega)
  simp only [commonGap, privateGap, alpha, beta, gamma] at *
  simp [gp, lpad, rpad] at hge ⊢
  omega

theorem ovl_UY {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ r) :
    overlapLength (U r P i) (Y r P i) = alpha r P i := by
  show overlapLength (W 2 r P i) (W 1 r P i) = alpha r P i
  have hle : overlapLength (W 2 r P i) (W 1 r P i) ≤ alpha r P i := by
    apply W_le 2 1 r P i i hr h1 h2 h1 h2 (Or.inl (by decide))
    · simp [lpad, rpad, alpha, beta, gamma] <;> omega
    · intro jj' hjj ht
      simp only [commonGap, privateGap, alpha, beta, gamma] at *
      simp [gp, lpad, rpad] at hjj ht ⊢
      interval_cases jj' <;> simp [gapTests] at ht ⊢ <;> omega
  have hge := W_ge 2 1 r P i i hr h1 h2 h1 h2 (Or.inl (by decide)) 3 (by simp [gp])
    (by unfold commonGap privateGap; simp only [lpad, rpad, gp]; simp [gapTests]; omega)
  simp only [commonGap, privateGap, alpha, beta, gamma] at *
  simp [gp, lpad, rpad] at hge ⊢
  omega

theorem ovl_UV {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ r) :
    overlapLength (U r P i) (V r P i) = alpha r P i := by
  show overlapLength (W 2 r P i) (W 3 r P i) = alpha r P i
  have hle : overlapLength (W 2 r P i) (W 3 r P i) ≤ alpha r P i := by
    apply W_le 2 3 r P i i hr h1 h2 h1 h2 (Or.inl (by decide))
    · simp [lpad, rpad, alpha, beta, gamma] <;> omega
    · intro jj' hjj ht
      simp only [commonGap, privateGap, alpha, beta, gamma] at *
      simp [gp, lpad, rpad] at hjj ht ⊢
      interval_cases jj' <;> simp [gapTests] at ht ⊢ <;> omega
  have hge := W_ge 2 3 r P i i hr h1 h2 h1 h2 (Or.inl (by decide)) 3 (by simp [gp])
    (by unfold commonGap privateGap; simp only [lpad, rpad, gp]; simp [gapTests]; omega)
  simp only [commonGap, privateGap, alpha, beta, gamma] at *
  simp [gp, lpad, rpad] at hge ⊢
  omega

theorem ovl_VZ {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ r) :
    overlapLength (V r P i) (Z r P i) = beta r P := by
  show overlapLength (W 3 r P i) (W 4 r P i) = beta r P
  have hle : overlapLength (W 3 r P i) (W 4 r P i) ≤ beta r P := by
    apply W_le 3 4 r P i i hr h1 h2 h1 h2 (Or.inl (by decide))
    · simp [lpad, rpad, alpha, beta, gamma] <;> omega
    · intro jj' hjj ht
      simp only [commonGap, privateGap, alpha, beta, gamma] at *
      simp [gp, lpad, rpad] at hjj ht ⊢
      interval_cases jj' <;> simp [gapTests] at ht ⊢ <;> omega
  have hge := W_ge 3 4 r P i i hr h1 h2 h1 h2 (Or.inl (by decide)) 2 (by simp [gp])
    (by unfold commonGap privateGap; simp only [lpad, rpad, gp]; simp [gapTests]; omega)
  simp only [commonGap, privateGap, alpha, beta, gamma] at *
  simp [gp, lpad, rpad] at hge ⊢
  omega

theorem ovl_YX_le {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ r) :
    overlapLength (Y r P i) (X r P i) ≤ alpha r P i := by
  show overlapLength (W 1 r P i) (W 0 r P i) ≤ alpha r P i
  have hle : overlapLength (W 1 r P i) (W 0 r P i) ≤ alpha r P i := by
    apply W_le 1 0 r P i i hr h1 h2 h1 h2 (Or.inl (by decide))
    · simp [lpad, rpad, alpha, beta, gamma] <;> omega
    · intro jj' hjj ht
      simp only [commonGap, privateGap, alpha, beta, gamma] at *
      simp [gp, lpad, rpad] at hjj ht ⊢
      interval_cases jj' <;> simp [gapTests] at ht ⊢ <;> omega
  exact hle

theorem ovl_YU {i j : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ r) (h3 : 1 ≤ j) (h4 : j ≤ r) :
    overlapLength (Y r P i) (U r P j) = gamma r P := by
  show overlapLength (W 1 r P i) (W 2 r P j) = gamma r P
  have hle : overlapLength (W 1 r P i) (W 2 r P j) ≤ gamma r P := by
    apply W_le 1 2 r P i j hr h1 h2 h3 h4 (Or.inl (by decide))
    · simp [lpad, rpad, alpha, beta, gamma] <;> omega
    · intro jj' hjj ht
      simp only [commonGap, privateGap, alpha, beta, gamma] at *
      simp [gp, lpad, rpad] at hjj ht ⊢
      interval_cases jj' <;> simp [gapTests] at ht ⊢ <;> omega
  have hge := W_ge 1 2 r P i j hr h1 h2 h3 h4 (Or.inl (by decide)) 0 (by simp [gp])
    (by unfold commonGap privateGap; simp only [lpad, rpad, gp]; simp [gapTests]; omega)
  simp only [commonGap, privateGap, alpha, beta, gamma] at *
  simp [gp, lpad, rpad] at hge ⊢
  omega

theorem ovl_YX_ne_le {i j : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ r) (h3 : 1 ≤ j) (h4 : j ≤ r) (hij : i ≠ j) :
    overlapLength (Y r P i) (X r P j) ≤ gamma r P := by
  show overlapLength (W 1 r P i) (W 0 r P j) ≤ gamma r P
  have hle : overlapLength (W 1 r P i) (W 0 r P j) ≤ gamma r P := by
    apply W_le 1 0 r P i j hr h1 h2 h3 h4 (Or.inl (by decide))
    · simp [lpad, rpad, alpha, beta, gamma] <;> omega
    · intro jj' hjj ht
      simp only [commonGap, privateGap, alpha, beta, gamma] at *
      simp [gp, lpad, rpad] at hjj ht ⊢
      interval_cases jj' <;> simp [gapTests] at ht ⊢ <;> omega
  exact hle

theorem ovl_ZU_ne_le {i j : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ r) (h3 : 1 ≤ j) (h4 : j ≤ r) (hij : i ≠ j) :
    overlapLength (Z r P i) (U r P j) ≤ gamma r P := by
  show overlapLength (W 4 r P i) (W 2 r P j) ≤ gamma r P
  have hle : overlapLength (W 4 r P i) (W 2 r P j) ≤ gamma r P := by
    apply W_le 4 2 r P i j hr h1 h2 h3 h4 (Or.inl (by decide))
    · simp [lpad, rpad, alpha, beta, gamma] <;> omega
    · intro jj' hjj ht
      simp only [commonGap, privateGap, alpha, beta, gamma] at *
      simp [gp, lpad, rpad] at hjj ht ⊢
      interval_cases jj' <;> simp [gapTests] at ht ⊢ <;> omega
  exact hle

theorem ovl_ZX_le {i j : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ r) (h3 : 1 ≤ j) (h4 : j ≤ r) :
    overlapLength (Z r P i) (X r P j) ≤ gamma r P := by
  show overlapLength (W 4 r P i) (W 0 r P j) ≤ gamma r P
  have hle : overlapLength (W 4 r P i) (W 0 r P j) ≤ gamma r P := by
    apply W_le 4 0 r P i j hr h1 h2 h3 h4 (Or.inl (by decide))
    · simp [lpad, rpad, alpha, beta, gamma] <;> omega
    · intro jj' hjj ht
      simp only [commonGap, privateGap, alpha, beta, gamma] at *
      simp [gp, lpad, rpad] at hjj ht ⊢
      interval_cases jj' <;> simp [gapTests] at ht ⊢ <;> omega
  exact hle

theorem ovl_ZX_ne {i j : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ r) (h3 : 1 ≤ j) (h4 : j ≤ r) (hij : i ≠ j) :
    overlapLength (Z r P i) (X r P j) = 0 := by
  show overlapLength (W 4 r P i) (W 0 r P j) = 0
  have hle : overlapLength (W 4 r P i) (W 0 r P j) ≤ 0 := by
    apply W_le 4 0 r P i j hr h1 h2 h3 h4 (Or.inl (by decide))
    · simp [lpad, rpad, alpha, beta, gamma] <;> omega
    · intro jj' hjj ht
      simp only [commonGap, privateGap, alpha, beta, gamma] at *
      simp [gp, lpad, rpad] at hjj ht ⊢
      interval_cases jj' <;> simp [gapTests] at ht ⊢ <;> omega
  exact Nat.le_zero.mp hle

end Table
end GreedySuperstring.LowerBound
end

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace GreedySuperstring.Dev.Goal

open GreedySuperstring.LowerBound OAI.Superstring

/-! ### Overlap and merge basics -/
section Basics
variable {α : Type} [DecidableEq α]

lemma ol_cases (s t : List α) : overlapLength s t = 0 ∨
    (overlapLength s t < s.length ∧ overlapLength s t < t.length ∧
      s.drop (s.length - overlapLength s t) = t.take (overlapLength s t)) := by
  unfold overlapLength
  by_cases h : ((Finset.range (min s.length t.length)).filter
      (fun n => s.drop (s.length - n) = t.take n)).Nonempty
  · obtain ⟨n, hn, hmax⟩ := Finset.exists_mem_eq_sup _ h id
    right
    rw [hmax]
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff] at hn
    exact ⟨hn.1.1, hn.1.2, hn.2⟩
  · left
    rw [Finset.not_nonempty_iff_eq_empty.mp h]
    simp

lemma ovl_le_right (s t : List α) : overlapLength s t ≤ t.length := by
  rcases ol_cases s t with h | h
  · omega
  · omega

lemma overlap_length_eq (s t : List α) : (overlap s t).length = overlapLength s t := by
  unfold overlap
  rw [List.length_take]
  exact min_eq_left (ovl_le_right s t)

lemma merge_length (s t : List α) :
    (merge s t).length = s.length + t.length - overlapLength s t := by
  unfold merge
  rw [List.length_append, List.length_drop]
  have := ovl_le_right s t
  omega

lemma merge_length' (s t : List α) :
    (merge s t).length + overlapLength s t = s.length + t.length := by
  have := ovl_le_right s t
  rw [merge_length]
  omega

lemma suffix_merge (s t : List α) : t <:+ merge s t := by
  have hm : merge s t = s ++ t.drop (overlapLength s t) := rfl
  rcases ol_cases s t with h | ⟨h1, h2, h3⟩
  · rw [hm, h]
    simp
  · refine ⟨s.take (s.length - overlapLength s t), ?_⟩
    rw [hm]
    generalize overlapLength s t = n at h3 ⊢
    conv_rhs => rw [← List.take_append_drop (s.length - n) s]
    rw [List.append_assoc, h3, List.take_append_drop]

lemma prefix_merge (s t : List α) : s <+: merge s t := List.prefix_append _ _

lemma mem_merge {s t : List α} {x : α} (h : x ∈ merge s t) : x ∈ s ∨ x ∈ t := by
  unfold merge at h
  rcases List.mem_append.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (List.mem_of_mem_drop h)

end Basics

/-! ### Labelled words -/
section Family
variable (r P : ℕ)

def wd (k i : ℕ) : Word :=
  match k with
  | 0 => X r P i
  | 1 => Y r P i
  | 2 => U r P i
  | 3 => V r P i
  | _ => Z r P i

def Listed (k l : ℕ) : Prop :=
  (k = 0 ∧ l = 1) ∨ (k = 0 ∧ l = 3) ∨ (k = 2 ∧ l = 1) ∨ (k = 2 ∧ l = 3) ∨ (k = 1 ∧ l = 0)

variable (hr : 1 ≤ r) (hP : r ≤ P + 1)
include hr hP

lemma wd_mem {k i : ℕ} (hk : k < 5) (h1 : 1 ≤ i) (h2 : i ≤ r) : wd r P k i ∈ inputFamily r P := by
  rw [mem_inputFamily_iff]
  refine ⟨i, h1, h2, ?_⟩
  interval_cases k <;> simp [wd]

lemma family_eq_image :
    inputFamily r P = (Finset.Icc 1 r ×ˢ Finset.range 5).image (fun p => wd r P p.2 p.1) := by
  ext s
  rw [mem_inputFamily_iff, Finset.mem_image]
  constructor
  · rintro ⟨i, h1, h2, h⟩
    rcases h with h | h | h | h | h
    · exact ⟨(i, 0), by simp [h1, h2], by simp [wd, h]⟩
    · exact ⟨(i, 1), by simp [h1, h2], by simp [wd, h]⟩
    · exact ⟨(i, 2), by simp [h1, h2], by simp [wd, h]⟩
    · exact ⟨(i, 3), by simp [h1, h2], by simp [wd, h]⟩
    · exact ⟨(i, 4), by simp [h1, h2], by simp [wd, h]⟩
  · rintro ⟨⟨i, k⟩, hm, rfl⟩
    simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hm
    refine ⟨i, hm.1.1, hm.1.2, ?_⟩
    obtain ⟨⟨_, _⟩, hk⟩ := hm
    interval_cases k <;> simp [wd]

lemma wd_inj {k l i j : ℕ} (hk : k < 5) (hl : l < 5) (hi1 : 1 ≤ i) (hi2 : i ≤ r)
    (hj1 : 1 ≤ j) (hj2 : j ≤ r) (h : wd r P k i = wd r P l j) : k = l ∧ i = j := by
  have hc := inputFamily_card r P hr hP
  rw [family_eq_image r P hr hP] at hc
  have hinj : Set.InjOn (fun p : ℕ × ℕ => wd r P p.2 p.1) (Finset.Icc 1 r ×ˢ Finset.range 5 : Finset (ℕ × ℕ)) := by
    rw [← Finset.card_image_iff, hc]
    simp [mul_comm]
  have := @hinj (i, k) (by simp [hi1, hi2, hk]) (j, l) (by simp [hj1, hj2, hl]) h
  simp only [Prod.mk.injEq] at this
  exact ⟨this.2, this.1⟩

lemma big_ovl {k l i j : ℕ} (hk : k < 5) (hl : l < 5) (hi1 : 1 ≤ i) (hi2 : i ≤ r)
    (hj1 : 1 ≤ j) (hj2 : j ≤ r) (hne : wd r P k i ≠ wd r P l j)
    (h : beta r P < overlapLength (wd r P k i) (wd r P l j)) : i = j ∧ Listed k l := by
  have hov : beta r P < (overlap (wd r P k i) (wd r P l j)).length := by
    rw [overlap_length_eq]; exact h
  obtain ⟨i', h1, h2, hh⟩ := large_overlap_pairs r P hr hP _ _ (wd_mem r P hr hP hk hi1 hi2)
    (wd_mem r P hr hP hl hj1 hj2) hne hov
  have key : ∀ (a b : ℕ), a < 5 → b < 5 → wd r P k i = wd r P a i' → wd r P l j = wd r P b i' →
      k = a ∧ l = b ∧ i = i' ∧ j = i' := by
    intro a b ha hb e1 e2
    have x1 := wd_inj r P hr hP hk ha hi1 hi2 h1 h2 e1
    have x2 := wd_inj r P hr hP hl hb hj1 hj2 h1 h2 e2
    exact ⟨x1.1, x2.1, x1.2, x2.2⟩
  rcases hh with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · obtain ⟨a1, a2, a3, a4⟩ := key 0 1 (by omega) (by omega) e1 e2
    exact ⟨by omega, Or.inl ⟨a1, a2⟩⟩
  · obtain ⟨a1, a2, a3, a4⟩ := key 0 3 (by omega) (by omega) e1 e2
    exact ⟨by omega, Or.inr (Or.inl ⟨a1, a2⟩)⟩
  · obtain ⟨a1, a2, a3, a4⟩ := key 2 1 (by omega) (by omega) e1 e2
    exact ⟨by omega, Or.inr (Or.inr (Or.inl ⟨a1, a2⟩))⟩
  · obtain ⟨a1, a2, a3, a4⟩ := key 2 3 (by omega) (by omega) e1 e2
    exact ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inl ⟨a1, a2⟩)))⟩
  · obtain ⟨a1, a2, a3, a4⟩ := key 1 0 (by omega) (by omega) e1 e2
    exact ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inr ⟨a1, a2⟩)))⟩

lemma ovl_cross {k l i j : ℕ} (hk : k < 5) (hl : l < 5) (hi1 : 1 ≤ i) (hi2 : i ≤ r)
    (hj1 : 1 ≤ j) (hj2 : j ≤ r) (hij : i ≠ j) :
    overlapLength (wd r P k i) (wd r P l j) ≤ beta r P := by
  by_contra hcon
  have hne : wd r P k i ≠ wd r P l j := fun h => hij (wd_inj r P hr hP hk hl hi1 hi2 hj1 hj2 h).2
  exact hij (big_ovl r P hr hP hk hl hi1 hi2 hj1 hj2 hne (by omega)).1

lemma ovl_nl {k l i : ℕ} (hk : k < 5) (hl : l < 5) (hi1 : 1 ≤ i) (hi2 : i ≤ r)
    (hkl : k ≠ l) (hnl : ¬ Listed k l) :
    overlapLength (wd r P k i) (wd r P l i) ≤ beta r P := by
  by_contra hcon
  have hne : wd r P k i ≠ wd r P l i := fun h => hkl (wd_inj r P hr hP hk hl hi1 hi2 hi1 hi2 h).1
  exact hnl (big_ovl r P hr hP hk hl hi1 hi2 hi1 hi2 hne (by omega)).2

lemma beta_le_alpha {i : ℕ} (h1 : 1 ≤ i) : beta r P ≤ alpha r P i := by
  unfold beta alpha; omega

lemma ovl_same {k l i : ℕ} (hk : k < 5) (hl : l < 5) (hi1 : 1 ≤ i) (hi2 : i ≤ r)
    (hkl : k ≠ l) : overlapLength (wd r P k i) (wd r P l i) ≤ alpha r P i := by
  by_cases hli : Listed k l
  · rcases hli with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (ovl_XY r P hr hP hi1 hi2).le
    · exact (ovl_XV r P hr hP hi1 hi2).le
    · exact (ovl_UY r P hr hP hi1 hi2).le
    · exact (ovl_UV r P hr hP hi1 hi2).le
    · exact ovl_YX_le r P hr hP hi1 hi2
  · exact (ovl_nl r P hr hP hk hl hi1 hi2 hkl hli).trans (beta_le_alpha r P hr hP hi1)

end Family

/-! ### Greedy-run machinery -/
section Machinery
variable {α : Type} [DecidableEq α]

lemma run_append {B B' B'' : Finset (Block α)} {ls ls' : List ℕ}
    (h : GreedyRun B ls B') (h' : GreedyRun B' ls' B'') : GreedyRun B (ls ++ ls') B'' := by
  induction h with
  | nil B => simpa using h'
  | cons hs _ ih => exact GreedyRun.cons hs (ih h')

def Reach (S : Finset (List α)) (B : Finset (Block α)) : Prop :=
  ∃ ls, GreedyRun (initialBlocks S) ls B

lemma reach_step {S : Finset (List α)} {B B' : Finset (Block α)} {l : ℕ}
    (hB : Reach S B) (hs : GreedyStep B l B') : Reach S B' := by
  obtain ⟨ls, h⟩ := hB
  exact ⟨ls ++ [l], run_append h (GreedyRun.cons hs (GreedyRun.nil _))⟩

def Bnd (B : Finset (Block α)) (l : ℕ) : Prop :=
  ∀ c ∈ B, ∀ d ∈ B, c.word ≠ d.word → ∀ x y : List α,
    c.history.getLast? = some x → d.history.head? = some y → overlapLength x y ≤ l

lemma step_gen {S : Finset (List α)} (hne : ∀ s ∈ S, s ≠ []) (hsf : SubstringFree S)
    {B : Finset (Block α)} (hB : Reach S B) {a b : Block α} (ha : a ∈ B) (hb : b ∈ B)
    (hab : a ≠ b) {x y : List α} {l : ℕ}
    (hx : a.history.getLast? = some x) (hy : b.history.head? = some y)
    (hl : overlapLength x y = l) (hbnd : Bnd B l) :
    GreedyStep B l (insert (mergeBlocks a b) ((B.erase a).erase b)) ∧
      overlapLength a.word b.word = l := by
  obtain ⟨ls, hrun⟩ := hB
  obtain ⟨h1, h2, h3, -⟩ := greedy_invariants S hne hsf ls B hrun
  have key : ∀ c ∈ B, ∀ d ∈ B, c ≠ d → ∀ x y : List α, c.history.getLast? = some x →
      d.history.head? = some y → overlapLength c.word d.word = overlapLength x y := by
    intro c hc d hd hcd x y hx hy
    have := congrArg List.length (h3 c hc d hd hcd x y hx hy)
    rwa [overlap_length_eq, overlap_length_eq] at this
  have hw : a.word ≠ b.word := fun h =>
    h1 a ha b hb hab (h ▸ List.infix_refl _)
  have hab' := key a ha b hb hab x y hx hy
  refine ⟨⟨a, ha, b, hb, hw, ?_, hl.symm.trans hab'.symm, rfl⟩, hab'.trans hl⟩
  intro c hc d hd hcd
  have hcd' : c ≠ d := fun h => hcd (h ▸ rfl)
  obtain ⟨x', hx'⟩ : ∃ x', c.history.getLast? = some x' := by
    have := (h2 c hc).1
    exact ⟨_, List.getLast?_eq_getLast_of_ne_nil this⟩
  obtain ⟨y', hy'⟩ : ∃ y', d.history.head? = some y' := by
    have := (h2 d hd).1
    exact ⟨_, List.head?_eq_some_head this⟩
  rw [key c hc d hd hcd' x' y' hx' hy', hab', hl]
  exact hbnd c hc d hd hcd x' y' hx' hy'

end Machinery

/-! ### The blocks of the schedule -/
section Blocks
variable (r P : ℕ)

abbrev Blk := Block Symbol

def sg (k i : ℕ) : Blk := ⟨wd r P k i, [wd r P k i]⟩
def bA (i : ℕ) : Blk := mergeBlocks (sg r P 0 i) (sg r P 1 i)
def bB (i : ℕ) : Blk := mergeBlocks (sg r P 2 i) (sg r P 3 i)
def bC (i : ℕ) : Blk := mergeBlocks (bB r P i) (sg r P 4 i)
def bT (i : ℕ) : Blk := mergeBlocks (bA r P i) (bC r P i)

def size (s : ℕ) : ℕ :=
  match s with
  | 0 => 5
  | 1 => 4
  | 2 => 3
  | 3 => 2
  | _ => 1

/-- (first label, last label) of the `n`-th block of status `s`. -/
def fl (s n : ℕ) : ℕ × ℕ :=
  match s, n with
  | 0, 0 => (0, 0)
  | 0, 1 => (1, 1)
  | 0, 2 => (2, 2)
  | 0, 3 => (3, 3)
  | 0, _ => (4, 4)
  | 1, 0 => (0, 1)
  | 1, 1 => (2, 2)
  | 1, 2 => (3, 3)
  | 1, _ => (4, 4)
  | 2, 0 => (0, 1)
  | 2, 1 => (2, 3)
  | 2, _ => (4, 4)
  | 3, 0 => (0, 1)
  | 3, _ => (2, 4)
  | _, _ => (0, 4)

def blk (s j n : ℕ) : Blk :=
  match s, n with
  | 0, 0 => sg r P 0 j
  | 0, 1 => sg r P 1 j
  | 0, 2 => sg r P 2 j
  | 0, 3 => sg r P 3 j
  | 0, _ => sg r P 4 j
  | 1, 0 => bA r P j
  | 1, 1 => sg r P 2 j
  | 1, 2 => sg r P 3 j
  | 1, _ => sg r P 4 j
  | 2, 0 => bA r P j
  | 2, 1 => bB r P j
  | 2, _ => sg r P 4 j
  | 3, 0 => bA r P j
  | 3, _ => bC r P j
  | _, _ => bT r P j

lemma blk_ends {s : ℕ} (hs : s ≤ 4) {n : ℕ} (hn : n < size s) (j : ℕ) :
    (blk r P s j n).history.head? = some (wd r P (fl s n).1 j) ∧
    (blk r P s j n).history.getLast? = some (wd r P (fl s n).2 j) := by
  interval_cases s <;> simp only [size] at hn <;> interval_cases n <;>
    simp [blk, fl, sg, bA, bB, bC, bT, mergeBlocks]

lemma fl_lt {s : ℕ} (hs : s ≤ 4) {n : ℕ} (hn : n < size s) : (fl s n).1 < 5 ∧ (fl s n).2 < 5 := by
  interval_cases s <;> simp only [size] at hn <;> interval_cases n <;> simp [fl]

lemma fl_pairs {s : ℕ} (hs : 3 ≤ s) (hs' : s ≤ 4) {n : ℕ} (hn : n < size s) :
    ((fl s n).2 = 1 ∨ (fl s n).2 = 4) ∧ ((fl s n).1 = 0 ∨ (fl s n).1 = 2) := by
  interval_cases s <;> simp only [size] at hn <;> interval_cases n <;> simp [fl]

variable (hr : 1 ≤ r) (hP : r ≤ P + 1)
include hr hP

lemma blk_first {s s' : ℕ} (hs : s ≤ 4) (hs' : s' ≤ 4) {n m : ℕ} (hn : n < size s)
    (hm : m < size s') {i j : ℕ} (hi1 : 1 ≤ i) (hi2 : i ≤ r) (hj1 : 1 ≤ j) (hj2 : j ≤ r)
    (h : blk r P s i n = blk r P s' j m) : (fl s n).1 = (fl s' m).1 ∧ i = j := by
  have e := (blk_ends r P hs hn i).1
  rw [h, (blk_ends r P hs' hm j).1] at e
  have e' := Option.some.inj e
  exact wd_inj r P hr hP (fl_lt hs' hm).1 (fl_lt hs hn).1 hj1 hj2 hi1 hi2 e' |>.imp
    (fun x => x.symm) (fun x => x.symm)

end Blocks

/-! ### States -/
section States
variable (r P : ℕ)

def bl (s j : ℕ) : Finset Blk := (Finset.range (size s)).image (blk r P s j)

def state (st : ℕ → ℕ) : Finset Blk := (Finset.Icc 1 r).biUnion (fun j => bl r P (st j) j)

lemma mem_bl {s j : ℕ} {x : Blk} : x ∈ bl r P s j ↔ ∃ n < size s, blk r P s j n = x := by
  simp [bl]

lemma mem_state {st : ℕ → ℕ} {x : Blk} :
    x ∈ state r P st ↔ ∃ i, (1 ≤ i ∧ i ≤ r) ∧ x ∈ bl r P (st i) i := by
  simp [state, and_assoc]

lemma state_congr {st st' : ℕ → ℕ} (h : ∀ j, 1 ≤ j → j ≤ r → st j = st' j) :
    state r P st = state r P st' := by
  unfold state
  refine Finset.biUnion_congr rfl ?_
  intro j hj
  rw [Finset.mem_Icc] at hj
  rw [h j hj.1 hj.2]

variable (hr : 1 ≤ r) (hP : r ≤ P + 1)
include hr hP

lemma state_zero : state r P (fun _ => 0) = initialBlocks (inputFamily r P) := by
  ext x
  rw [mem_state, initialBlocks, Finset.mem_image]
  constructor
  · rintro ⟨i, ⟨hi1, hi2⟩, hx⟩
    rw [mem_bl] at hx
    obtain ⟨n, hn, rfl⟩ := hx
    simp only [size] at hn
    exact ⟨wd r P n i, wd_mem r P hr hP (by omega) hi1 hi2, by
      interval_cases n <;> rfl⟩
  · rintro ⟨w, hw, rfl⟩
    rw [mem_inputFamily_iff] at hw
    obtain ⟨i, h1, h2, h⟩ := hw
    refine ⟨i, ⟨h1, h2⟩, ?_⟩
    rw [mem_bl]
    rcases h with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by simp [size], rfl⟩
    · exact ⟨1, by simp [size], rfl⟩
    · exact ⟨2, by simp [size], rfl⟩
    · exact ⟨3, by simp [size], rfl⟩
    · exact ⟨4, by simp [size], rfl⟩

lemma state_update {st : ℕ → ℕ} (hst : ∀ i, st i ≤ 4) {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ r)
    {s' : ℕ} (hs' : s' ≤ 4) {a b M : Blk}
    (ha : a ∈ bl r P (st j) j) (hb : b ∈ bl r P (st j) j)
    (hEq : bl r P s' j = insert M (((bl r P (st j) j).erase a).erase b)) :
    state r P (Function.update st j s') = insert M (((state r P st).erase a).erase b) := by
  obtain ⟨pa, hpa, rfl⟩ := (mem_bl r P).1 ha
  obtain ⟨pb, hpb, rfl⟩ := (mem_bl r P).1 hb
  have disj : ∀ i, 1 ≤ i → i ≤ r → i ≠ j → ∀ x ∈ bl r P (st i) i,
      x ≠ blk r P (st j) j pa ∧ x ≠ blk r P (st j) j pb := by
    intro i hi1 hi2 hij x hx
    obtain ⟨n, hn, rfl⟩ := (mem_bl r P).1 hx
    exact ⟨fun h => hij (blk_first r P hr hP (hst i) (hst j) hn hpa hi1 hi2 hj1 hj2 h).2,
      fun h => hij (blk_first r P hr hP (hst i) (hst j) hn hpb hi1 hi2 hj1 hj2 h).2⟩
  ext x
  rw [mem_state, Finset.mem_insert, Finset.mem_erase, Finset.mem_erase, mem_state]
  constructor
  · rintro ⟨i, ⟨hi1, hi2⟩, hx⟩
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self, hEq, Finset.mem_insert, Finset.mem_erase, Finset.mem_erase] at hx
      rcases hx with hx | ⟨h1, h2, h3⟩
      · exact Or.inl hx
      · exact Or.inr ⟨h1, h2, i, ⟨hi1, hi2⟩, h3⟩
    · rw [Function.update_of_ne hij] at hx
      have := disj i hi1 hi2 hij x hx
      exact Or.inr ⟨this.2, this.1, i, ⟨hi1, hi2⟩, hx⟩
  · rintro (rfl | ⟨h1, h2, i, ⟨hi1, hi2⟩, hx⟩)
    · refine ⟨j, ⟨hj1, hj2⟩, ?_⟩
      rw [Function.update_self, hEq]
      exact Finset.mem_insert_self _ _
    · by_cases hij : i = j
      · subst hij
        refine ⟨i, ⟨hi1, hi2⟩, ?_⟩
        rw [Function.update_self, hEq]
        exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨h1, Finset.mem_erase.2 ⟨h2, hx⟩⟩)
      · exact ⟨i, ⟨hi1, hi2⟩, by rw [Function.update_of_ne hij]; exact hx⟩

end States

/-! ### Local transitions -/
section Trans
variable (r P : ℕ) (hr : 1 ≤ r) (hP : r ≤ P + 1)
include hr hP

lemma blk_ne {s s' n m j : ℕ} (hs : s ≤ 4) (hs' : s' ≤ 4) (hn : n < size s) (hm : m < size s')
    (hj1 : 1 ≤ j) (hj2 : j ≤ r) (hne : (fl s n).1 ≠ (fl s' m).1) :
    blk r P s j n ≠ blk r P s' j m :=
  fun h => hne (blk_first r P hr hP hs hs' hn hm hj1 hj2 hj1 hj2 h).1

lemma state_update' {st : ℕ → ℕ} (hst : ∀ i, st i ≤ 4) {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ r)
    {s s' : ℕ} (hs : st j = s) (hs' : s' ≤ 4) {a b M : Blk}
    (ha : a ∈ bl r P s j) (hb : b ∈ bl r P s j)
    (hEq : bl r P s' j = insert M (((bl r P s j).erase a).erase b)) :
    state r P (Function.update st j s') = insert M (((state r P st).erase a).erase b) := by
  subst hs
  exact state_update r P hr hP hst hj1 hj2 hs' ha hb hEq

lemma tr01 {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ r) :
    bl r P 1 j = insert (mergeBlocks (blk r P 0 j 0) (blk r P 0 j 1))
      (((bl r P 0 j).erase (blk r P 0 j 0)).erase (blk r P 0 j 1)) := by
  ext x
  rw [mem_bl, Finset.mem_insert, Finset.mem_erase, Finset.mem_erase, mem_bl]
  constructor
  · rintro ⟨n, hn, rfl⟩
    simp only [size] at hn
    interval_cases n
    · exact Or.inl rfl
    · exact Or.inr ⟨blk_ne r P hr hP (by decide) (by decide) (by decide) (by decide) hj1 hj2 (by decide),
        blk_ne r P hr hP (by decide) (by decide) (by decide) (by decide) hj1 hj2 (by decide),
        2, by decide, rfl⟩
    · exact Or.inr ⟨blk_ne r P hr hP (by decide) (by decide) (by decide) (by decide) hj1 hj2 (by decide),
        blk_ne r P hr hP (by decide) (by decide) (by decide) (by decide) hj1 hj2 (by decide),
        3, by decide, rfl⟩
    · exact Or.inr ⟨blk_ne r P hr hP (by decide) (by decide) (by decide) (by decide) hj1 hj2 (by decide),
        blk_ne r P hr hP (by decide) (by decide) (by decide) (by decide) hj1 hj2 (by decide),
        4, by decide, rfl⟩
  · rintro (rfl | ⟨h1, h2, n, hn, rfl⟩)
    · exact ⟨0, by decide, rfl⟩
    · simp only [size] at hn
      interval_cases n
      · exact absurd rfl h2
      · exact absurd rfl h1
      · exact ⟨1, by decide, rfl⟩
      · exact ⟨2, by decide, rfl⟩
      · exact ⟨3, by decide, rfl⟩

lemma tr12 {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ r) :
    bl r P 2 j = insert (mergeBlocks (blk r P 1 j 1) (blk r P 1 j 2))
      (((bl r P 1 j).erase (blk r P 1 j 1)).erase (blk r P 1 j 2)) := by
  ext x
  rw [mem_bl, Finset.mem_insert, Finset.mem_erase, Finset.mem_erase, mem_bl]
  constructor
  · rintro ⟨n, hn, rfl⟩
    simp only [size] at hn
    interval_cases n
    · exact Or.inr ⟨blk_ne r P hr hP (by decide) (by decide) (by decide) (by decide) hj1 hj2 (by decide),
        blk_ne r P hr hP (by decide) (by decide) (by decide) (by decide) hj1 hj2 (by decide),
        0, by decide, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨blk_ne r P hr hP (by decide) (by decide) (by decide) (by decide) hj1 hj2 (by decide),
        blk_ne r P hr hP (by decide) (by decide) (by decide) (by decide) hj1 hj2 (by decide),
        3, by decide, rfl⟩
  · rintro (rfl | ⟨h1, h2, n, hn, rfl⟩)
    · exact ⟨1, by decide, rfl⟩
    · simp only [size] at hn
      interval_cases n
      · exact ⟨0, by decide, rfl⟩
      · exact absurd rfl h2
      · exact absurd rfl h1
      · exact ⟨2, by decide, rfl⟩

lemma tr23 {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ r) :
    bl r P 3 j = insert (mergeBlocks (blk r P 2 j 1) (blk r P 2 j 2))
      (((bl r P 2 j).erase (blk r P 2 j 1)).erase (blk r P 2 j 2)) := by
  ext x
  rw [mem_bl, Finset.mem_insert, Finset.mem_erase, Finset.mem_erase, mem_bl]
  constructor
  · rintro ⟨n, hn, rfl⟩
    simp only [size] at hn
    interval_cases n
    · exact Or.inr ⟨blk_ne r P hr hP (by decide) (by decide) (by decide) (by decide) hj1 hj2 (by decide),
        blk_ne r P hr hP (by decide) (by decide) (by decide) (by decide) hj1 hj2 (by decide),
        0, by decide, rfl⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨h1, h2, n, hn, rfl⟩)
    · exact ⟨1, by decide, rfl⟩
    · simp only [size] at hn
      interval_cases n
      · exact ⟨0, by decide, rfl⟩
      · exact absurd rfl h2
      · exact absurd rfl h1

lemma tr34 {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ r) :
    bl r P 4 j = insert (mergeBlocks (blk r P 3 j 0) (blk r P 3 j 1))
      (((bl r P 3 j).erase (blk r P 3 j 0)).erase (blk r P 3 j 1)) := by
  ext x
  rw [mem_bl, Finset.mem_insert, Finset.mem_erase, Finset.mem_erase, mem_bl]
  constructor
  · rintro ⟨n, hn, rfl⟩
    simp only [size] at hn
    interval_cases n
    exact Or.inl rfl
  · rintro (rfl | ⟨h1, h2, n, hn, rfl⟩)
    · exact ⟨0, by decide, rfl⟩
    · simp only [size] at hn
      interval_cases n
      · exact absurd rfl h2
      · exact absurd rfl h1

end Trans

/-! ### Bounds on all pairs of current blocks -/
section Bounds
variable (r P : ℕ) (hr : 1 ≤ r) (hP : r ≤ P + 1)

instance (k l : ℕ) : Decidable (Listed k l) := by unfold Listed; infer_instance

lemma fl_ne01 : ∀ s < 2, ∀ n < size s, ∀ m < size s, n ≠ m → (fl s n).2 ≠ (fl s m).1 := by decide

lemma fl_nl23 : ∀ s < 4, ∀ n < size s, ∀ m < size s, n ≠ m → 2 ≤ s →
    (fl s n).2 ≠ (fl s m).1 ∧ ¬ Listed (fl s n).2 (fl s m).1 := by
  intro s hs; interval_cases s <;> decide

lemma fl_gamma3 : ∀ n < size 3, ∀ m < size 3, n ≠ m →
    ((fl 3 n).2 = 1 ∧ (fl 3 m).1 = 2) ∨ ((fl 3 n).2 = 4 ∧ (fl 3 m).1 = 0) := by decide

lemma fl_gamma {s : ℕ} (h3 : 3 ≤ s) (h4 : s ≤ 4) {n m : ℕ} (hn : n < size s) (hm : m < size s)
    (hnm : n ≠ m) :
    ((fl s n).2 = 1 ∧ (fl s m).1 = 2) ∨ ((fl s n).2 = 4 ∧ (fl s m).1 = 0) := by
  interval_cases s
  · exact fl_gamma3 n hn m hm hnm
  · simp only [size] at hn hm
    omega

def LowB (st : ℕ → ℕ) (l : ℕ) : Prop :=
  (∀ j, 1 ≤ j → j ≤ r → ∀ n < size (st j), ∀ m < size (st j), n ≠ m →
    overlapLength (wd r P (fl (st j) n).2 j) (wd r P (fl (st j) m).1 j) ≤ l) ∧
  (∀ i j, 1 ≤ i → i ≤ r → 1 ≤ j → j ≤ r → i ≠ j → ∀ n < size (st i), ∀ m < size (st j),
    overlapLength (wd r P (fl (st i) n).2 i) (wd r P (fl (st j) m).1 j) ≤ l)

include hr hP

lemma bnd_state {st : ℕ → ℕ} (hst : ∀ i, st i ≤ 4) {l : ℕ} (h : LowB r P st l) :
    Bnd (state r P st) l := by
  intro c hc d hd hcd x y hx hy
  obtain ⟨i, ⟨hi1, hi2⟩, hc⟩ := (mem_state r P).1 hc
  obtain ⟨j, ⟨hj1, hj2⟩, hd⟩ := (mem_state r P).1 hd
  obtain ⟨n, hn, rfl⟩ := (mem_bl r P).1 hc
  obtain ⟨m, hm, rfl⟩ := (mem_bl r P).1 hd
  rw [(blk_ends r P (hst i) hn i).2] at hx
  rw [(blk_ends r P (hst j) hm j).1] at hy
  cases hx
  cases hy
  by_cases hij : i = j
  · subst hij
    refine h.1 i hi1 hi2 n hn m hm ?_
    rintro rfl
    exact hcd rfl
  · exact h.2 i j hi1 hi2 hj1 hj2 hij n hn m hm

lemma lowB_alpha {st : ℕ → ℕ} {i : ℕ} (hi : 1 ≤ i)
    (hcls : ∀ j, 1 ≤ j → j ≤ r → (st j ≤ 1 ∧ j ≤ i) ∨ st j = 2) :
    LowB r P st (alpha r P i) := by
  refine ⟨?_, ?_⟩
  · intro j hj1 hj2 n hn m hm hnm
    rcases hcls j hj1 hj2 with ⟨hs, hji⟩ | hs
    · have hs2 : st j < 2 := by omega
      have h1 := fl_ne01 _ hs2 n hn m hm hnm
      have := ovl_same r P hr hP (fl_lt (by omega) hn).2 (fl_lt (by omega) hm).1 hj1 hj2 h1
      refine this.trans ?_
      unfold alpha; omega
    · have h1 := fl_nl23 (st j) (by omega) n hn m hm hnm (by omega)
      have hs' : st j ≤ 4 := by omega
      exact (ovl_nl r P hr hP (fl_lt hs' hn).2 (fl_lt hs' hm).1 hj1 hj2 h1.1 h1.2).trans
        (beta_le_alpha r P hr hP hi)
  · intro a b ha1 ha2 hb1 hb2 hab n hn m hm
    have hs : ∀ j, 1 ≤ j → j ≤ r → st j ≤ 4 := by
      intro j hj1 hj2
      rcases hcls j hj1 hj2 with ⟨hs, _⟩ | hs <;> omega
    exact (ovl_cross r P hr hP (fl_lt (hs a ha1 ha2) hn).2 (fl_lt (hs b hb1 hb2) hm).1
      ha1 ha2 hb1 hb2 hab).trans (beta_le_alpha r P hr hP hi)

lemma lowB_beta {st : ℕ → ℕ} (hcls : ∀ j, 1 ≤ j → j ≤ r → st j = 2 ∨ st j = 3) :
    LowB r P st (beta r P) := by
  refine ⟨?_, ?_⟩
  · intro j hj1 hj2 n hn m hm hnm
    have hs := hcls j hj1 hj2
    have h1 := fl_nl23 (st j) (by omega) n hn m hm hnm (by omega)
    have hs' : st j ≤ 4 := by omega
    exact ovl_nl r P hr hP (fl_lt hs' hn).2 (fl_lt hs' hm).1 hj1 hj2 h1.1 h1.2
  · intro a b ha1 ha2 hb1 hb2 hab n hn m hm
    have hs : ∀ j, 1 ≤ j → j ≤ r → st j ≤ 4 := by
      intro j hj1 hj2
      have := hcls j hj1 hj2
      omega
    exact ovl_cross r P hr hP (fl_lt (hs a ha1 ha2) hn).2 (fl_lt (hs b hb1 hb2) hm).1
      ha1 ha2 hb1 hb2 hab

lemma lowB_gamma {st : ℕ → ℕ} (hcls : ∀ j, 1 ≤ j → j ≤ r → st j = 3 ∨ st j = 4) :
    LowB r P st (gamma r P) := by
  refine ⟨?_, ?_⟩
  · intro j hj1 hj2 n hn m hm hnm
    have hs := hcls j hj1 hj2
    have h1 := fl_gamma (by omega) (by omega) hn hm hnm
    rcases h1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]
      exact (ovl_YU r P hr hP hj1 hj2 hj1 hj2).le
    · rw [e1, e2]
      exact ovl_ZX_le r P hr hP hj1 hj2 hj1 hj2
  · intro a b ha1 ha2 hb1 hb2 hab n hn m hm
    have hs := hcls a ha1 ha2
    have hs2 := hcls b hb1 hb2
    have p1 := fl_pairs (s := st a) (by omega) (by omega) hn
    have p2 := fl_pairs (s := st b) (by omega) (by omega) hm
    rcases p1.1 with e1 | e1 <;> rcases p2.2 with e2 | e2
    · rw [e1, e2]
      exact ovl_YX_ne_le r P hr hP ha1 ha2 hb1 hb2 hab
    · rw [e1, e2]
      exact (ovl_YU r P hr hP ha1 ha2 hb1 hb2).le
    · rw [e1, e2]
      exact ovl_ZX_le r P hr hP ha1 ha2 hb1 hb2
    · rw [e1, e2]
      exact ovl_ZU_ne_le r P hr hP ha1 ha2 hb1 hb2 hab

end Bounds

/-! ### One stage of the schedule -/
section Stage
variable (r P : ℕ) (hr : 1 ≤ r) (hP : r ≤ P + 1)

lemma fl_first_inj : ∀ s < 5, ∀ n < size s, ∀ m < size s, n ≠ m → (fl s n).1 ≠ (fl s m).1 := by
  decide

include hr hP

lemma stage {st : ℕ → ℕ} (hst : ∀ i, st i ≤ 4) (hR : Reach (inputFamily r P) (state r P st))
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ r) {s s' : ℕ} (hs : st j = s) (hs' : s' ≤ 4)
    {p q : ℕ} (hp : p < size s) (hq : q < size s) (hpq : p ≠ q) {l : ℕ}
    (hl : overlapLength (wd r P (fl s p).2 j) (wd r P (fl s q).1 j) = l)
    (hLow : LowB r P st l)
    (hEq : bl r P s' j = insert (mergeBlocks (blk r P s j p) (blk r P s j q))
      (((bl r P s j).erase (blk r P s j p)).erase (blk r P s j q))) :
    Reach (inputFamily r P) (state r P (Function.update st j s')) ∧
      overlapLength (blk r P s j p).word (blk r P s j q).word = l := by
  have hs4 : s ≤ 4 := hs ▸ hst j
  have hpa : blk r P s j p ∈ bl r P s j := (mem_bl r P).2 ⟨p, hp, rfl⟩
  have hqa : blk r P s j q ∈ bl r P s j := (mem_bl r P).2 ⟨q, hq, rfl⟩
  have hmem : ∀ x ∈ bl r P s j, x ∈ state r P st := fun x hx =>
    (mem_state r P).2 ⟨j, ⟨hj1, hj2⟩, hs ▸ hx⟩
  have hne : blk r P s j p ≠ blk r P s j q :=
    blk_ne r P hr hP hs4 hs4 hp hq hj1 hj2 (fl_first_inj s (by omega) p hp q hq hpq)
  obtain ⟨g1, g2⟩ := step_gen (inputFamily_ne_nil r P hr hP) (inputFamily_substringFree r P hr hP)
    hR (hmem _ hpa) (hmem _ hqa) hne (blk_ends r P hs4 hp j).2 (blk_ends r P hs4 hq j).1 hl
    (bnd_state r P hr hP hst hLow)
  have := state_update' r P hr hP hst hj1 hj2 hs hs' hpa hqa hEq
  exact ⟨reach_step hR (by rw [this]; exact g1), g2⟩

end Stage

/-! ### Phases (i)-(iii) -/
section Phases
variable (r P : ℕ) (hr : 1 ≤ r) (hP : r ≤ P + 1)

def stI (k : ℕ) : ℕ → ℕ := fun j => if k < j then 2 else 0
def stII (k : ℕ) : ℕ → ℕ := fun j => if j ≤ k then 3 else 2
def stIII (k : ℕ) : ℕ → ℕ := fun j => if j ≤ k then 4 else 3

include hr hP

lemma reach_init : Reach (inputFamily r P) (state r P (fun _ => 0)) := by
  rw [state_zero r P hr hP]
  exact ⟨[], GreedyRun.nil _⟩

lemma phase1 : ∀ d, d ≤ r → Reach (inputFamily r P) (state r P (stI (r - d))) := by
  intro d
  induction d with
  | zero =>
    intro _
    have : state r P (stI (r - 0)) = state r P (fun _ => 0) := by
      refine state_congr r P ?_
      intro j _ hj2
      simp [stI]
      omega
    rw [this]
    exact reach_init r P hr hP
  | succ d ih =>
    intro hd
    have hR := ih (by omega)
    have hi1 : 1 ≤ r - d := by omega
    have hi2 : r - d ≤ r := by omega
    set i := r - d with hi
    have hst1 : ∀ j, stI i j ≤ 4 := by intro j; unfold stI; split_ifs <;> omega
    have step1 := stage r P hr hP hst1 hR hi1 hi2 (s := 0) (s' := 1) (by simp [stI])
      (by omega) (p := 0) (q := 1) (by decide) (by decide) (by decide) (l := alpha r P i)
      (ovl_XY r P hr hP hi1 hi2)
      (lowB_alpha r P hr hP hi1 (by
        intro j _ _
        unfold stI
        by_cases h : i < j
        · right; simp [h]
        · left; simp [h]; omega))
      (tr01 r P hr hP hi1 hi2)
    have hst2 : ∀ j, Function.update (stI i) i 1 j ≤ 4 := by
      intro j
      by_cases h : j = i
      · subst h; simp
      · rw [Function.update_of_ne h]; exact hst1 j
    have step2 := stage r P hr hP hst2 step1.1 hi1 hi2 (s := 1) (s' := 2) (by simp)
      (by omega) (p := 1) (q := 2) (by decide) (by decide) (by decide) (l := alpha r P i)
      (ovl_UV r P hr hP hi1 hi2)
      (lowB_alpha r P hr hP hi1 (by
        intro j _ _
        by_cases h : j = i
        · subst h; left; simp
        · rw [Function.update_of_ne h]
          unfold stI
          by_cases h' : i < j
          · right; simp [h']
          · left; simp [h']; omega))
      (tr12 r P hr hP hi1 hi2)
    have : state r P (Function.update (Function.update (stI i) i 1) i 2) =
        state r P (stI (r - (d + 1))) := by
      refine state_congr r P ?_
      intro j _ hj2
      by_cases h : j = i
      · subst h
        simp [stI]
        omega
      · rw [Function.update_of_ne h, Function.update_of_ne h]
        unfold stI
        by_cases h' : i < j
        · simp [h']; omega
        · simp [h']; omega
    rw [← this]
    exact step2.1

lemma phase2 : ∀ k, k ≤ r → Reach (inputFamily r P) (state r P (stII k)) ∧
    ∀ j, 1 ≤ j → j ≤ k → overlapLength (B r P j) (Z r P j) = beta r P := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, fun j h1 h2 => by omega⟩
    have h1 := phase1 r P hr hP r le_rfl
    have : state r P (stI (r - r)) = state r P (stII 0) := by
      refine state_congr r P ?_
      intro j hj1 hj2
      have h0 : 0 < j := by omega
      have h1 : ¬ j ≤ 0 := by omega
      simp [stI, stII, h0, h1]
    rw [← this]
    exact h1
  | succ k ih =>
    intro hk
    obtain ⟨hR, hf⟩ := ih (by omega)
    have hi1 : 1 ≤ k + 1 := by omega
    have hst : ∀ j, stII k j ≤ 4 := by intro j; unfold stII; split_ifs <;> omega
    have step := stage r P hr hP hst hR hi1 hk (s := 2) (s' := 3) (by simp [stII])
      (by omega) (p := 1) (q := 2) (by decide) (by decide) (by decide) (l := beta r P)
      (ovl_VZ r P hr hP hi1 hk)
      (lowB_beta r P hr hP (by
        intro j _ _
        unfold stII
        by_cases h : j ≤ k
        · right; simp [h]
        · left; simp [h]))
      (tr23 r P hr hP hi1 hk)
    have : state r P (Function.update (stII k) (k + 1) 3) = state r P (stII (k + 1)) := by
      refine state_congr r P ?_
      intro j _ hj2
      by_cases h : j = k + 1
      · subst h; simp [stII]
      · rw [Function.update_of_ne h]
        unfold stII
        by_cases h' : j ≤ k
        · simp [h']; omega
        · simp [h']; omega
    refine ⟨by rw [← this]; exact step.1, ?_⟩
    intro j hj1 hj2
    by_cases h : j = k + 1
    · subst h
      exact step.2
    · exact hf j hj1 (by omega)

lemma phase3 : ∀ k, k ≤ r → Reach (inputFamily r P) (state r P (stIII k)) ∧
    ∀ j, 1 ≤ j → j ≤ k → overlapLength (A r P j) (C r P j) = gamma r P := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, fun j h1 h2 => by omega⟩
    have h1 := (phase2 r P hr hP r le_rfl).1
    have : state r P (stII r) = state r P (stIII 0) := by
      refine state_congr r P ?_
      intro j hj1 hj2
      have h1 : ¬ j ≤ 0 := by omega
      simp [stIII, stII, h1, hj2]
    rw [← this]
    exact h1
  | succ k ih =>
    intro hk
    obtain ⟨hR, hf⟩ := ih (by omega)
    have hi1 : 1 ≤ k + 1 := by omega
    have hst : ∀ j, stIII k j ≤ 4 := by intro j; unfold stIII; split_ifs <;> omega
    have step := stage r P hr hP hst hR hi1 hk (s := 3) (s' := 4) (by simp [stIII])
      (by omega) (p := 0) (q := 1) (by decide) (by decide) (by decide) (l := gamma r P)
      (ovl_YU r P hr hP hi1 hk hi1 hk)
      (lowB_gamma r P hr hP (by
        intro j _ _
        unfold stIII
        by_cases h : j ≤ k
        · right; simp [h]
        · left; simp [h]))
      (tr34 r P hr hP hi1 hk)
    have : state r P (Function.update (stIII k) (k + 1) 4) = state r P (stIII (k + 1)) := by
      refine state_congr r P ?_
      intro j _ hj2
      by_cases h : j = k + 1
      · subst h; simp [stIII]
      · rw [Function.update_of_ne h]
        unfold stIII
        by_cases h' : j ≤ k
        · simp [h']; omega
        · simp [h']; omega
    refine ⟨by rw [← this]; exact step.1, ?_⟩
    intro j hj1 hj2
    by_cases h : j = k + 1
    · subst h
      exact step.2
    · exact hf j hj1 (by omega)

end Phases

/-! ### Phase (iv): concatenation -/
section Concat
variable (r P : ℕ)

def chain : ℕ → Blk
  | 0 => bT r P 1
  | k + 1 => mergeBlocks (chain k) (bT r P (k + 2))

def state4 (k : ℕ) : Finset Blk :=
  insert (chain r P k) (((Finset.Icc 1 r).filter (fun j => k + 1 < j)).image (bT r P))

lemma bT_ends (i : ℕ) : (bT r P i).history.head? = some (wd r P 0 i) ∧
    (bT r P i).history.getLast? = some (wd r P 4 i) := by
  simp [bT, bA, bB, bC, sg, mergeBlocks]

lemma chain_ends (k : ℕ) : (chain r P k).history.head? = some (wd r P 0 1) ∧
    (chain r P k).history.getLast? = some (wd r P 4 (k + 1)) := by
  induction k with
  | zero => exact bT_ends r P 1
  | succ k ih =>
    have h := bT_ends r P (k + 2)
    have hne : (bT r P (k + 2)).history ≠ [] := by
      intro h0
      have := h.1
      rw [h0] at this
      simp at this
    refine ⟨?_, ?_⟩
    · simp only [chain, mergeBlocks]
      rw [List.head?_append, ih.1]
      rfl
    · simp only [chain, mergeBlocks]
      rw [List.getLast?_append, h.2]
      rfl

lemma chain_word (k : ℕ) : (chain r P (k + 1)).word =
    merge (chain r P k).word (T r P (k + 2)) := rfl

variable (hr : 1 ≤ r) (hP : r ≤ P + 1)
include hr hP

lemma state_final : state r P (stIII r) = state4 r P 0 := by
  ext x
  rw [mem_state, state4, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro ⟨i, ⟨hi1, hi2⟩, hx⟩
    rw [mem_bl] at hx
    obtain ⟨n, hn, rfl⟩ := hx
    have h4 : stIII r i = 4 := by simp [stIII, hi2]
    have hn' : n = 0 := by rw [h4] at hn; simp [size] at hn; exact hn
    subst hn'
    by_cases h1 : i = 1
    · subst h1
      left
      simp only [h4]
      rfl
    · right
      refine ⟨i, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨hi1, hi2⟩, by omega⟩
      · simp only [h4]; rfl
  · rintro (rfl | ⟨j, hj, rfl⟩)
    · refine ⟨1, ⟨le_rfl, hr⟩, ?_⟩
      rw [mem_bl]
      have h4 : stIII r 1 = 4 := by simp [stIII, hr]
      exact ⟨0, by rw [h4]; decide, by simp only [h4]; rfl⟩
    · rw [Finset.mem_filter, Finset.mem_Icc] at hj
      refine ⟨j, hj.1, ?_⟩
      rw [mem_bl]
      have h4 : stIII r j = 4 := by simp [stIII, hj.1.2]
      exact ⟨0, by rw [h4]; decide, by simp only [h4]; rfl⟩

lemma phase4 : ∀ k, k + 1 ≤ r → Reach (inputFamily r P) (state4 r P k) ∧
    (chain r P k).word = ((List.range (k + 1)).map (fun j => T r P (j + 1))).flatten := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨?_, by simp [chain, bT, bA, bC, bB, sg, T, A, B, C, mergeBlocks, wd]⟩
    rw [← state_final r P hr hP]
    exact (phase3 r P hr hP r le_rfl).1
  | succ k ih =>
    intro hk
    obtain ⟨hR, hw⟩ := ih (by omega)
    have hk1 : 1 ≤ k + 1 := by omega
    have hk2 : 1 ≤ k + 2 := by omega
    have hmemA : chain r P k ∈ state4 r P k := Finset.mem_insert_self _ _
    have hmemB : bT r P (k + 2) ∈ state4 r P k := by
      refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨k + 2, ?_, rfl⟩)
      rw [Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨hk2, hk⟩, by omega⟩
    have hne : chain r P k ≠ bT r P (k + 2) := by
      intro h
      have e := (chain_ends r P k).1
      rw [h, (bT_ends r P (k + 2)).1] at e
      have := wd_inj r P hr hP (k := 0) (l := 0) (i := k + 2) (j := 1) (by omega) (by omega)
        hk2 hk le_rfl hr (Option.some.inj e)
      omega
    have hbnd : Bnd (state4 r P k) 0 := by
      intro c hc d hd hcd x y hx hy
      have hcases : ∀ e ∈ state4 r P k, e = chain r P k ∨ ∃ j, (1 ≤ j ∧ j ≤ r) ∧ k + 1 < j ∧
          bT r P j = e := by
        intro e he
        rcases Finset.mem_insert.1 he with h | h
        · exact Or.inl h
        · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h
          rw [Finset.mem_filter, Finset.mem_Icc] at hj
          exact Or.inr ⟨j, hj.1, hj.2, rfl⟩
      have hc' := hcases c hc
      have hd' := hcases d hd
      rcases hc' with rfl | ⟨j, hj, hlt, rfl⟩ <;> rcases hd' with rfl | ⟨j', hj', hlt', rfl⟩
      · exact absurd rfl hcd
      · rw [(chain_ends r P k).2] at hx
        rw [(bT_ends r P j').1] at hy
        cases hx; cases hy
        exact (ovl_ZX_ne r P hr hP hk1 (by omega) hj'.1 hj'.2 (by omega)).le
      · rw [(bT_ends r P j).2] at hx
        rw [(chain_ends r P k).1] at hy
        cases hx; cases hy
        exact (ovl_ZX_ne r P hr hP hj.1 hj.2 le_rfl hr (by omega)).le
      · rw [(bT_ends r P j).2] at hx
        rw [(bT_ends r P j').1] at hy
        cases hx; cases hy
        refine (ovl_ZX_ne r P hr hP hj.1 hj.2 hj'.1 hj'.2 ?_).le
        rintro rfl
        exact hcd rfl
    obtain ⟨g1, g2⟩ := step_gen (inputFamily_ne_nil r P hr hP) (inputFamily_substringFree r P hr hP)
      hR hmemA hmemB hne (chain_ends r P k).2 (bT_ends r P (k + 2)).1
      (ovl_ZX_ne r P hr hP hk1 (by omega) hk2 hk (by omega)) hbnd
    have hset : state4 r P (k + 1) = insert (mergeBlocks (chain r P k) (bT r P (k + 2)))
        (((state4 r P k).erase (chain r P k)).erase (bT r P (k + 2))) := by
      ext x
      simp only [state4, Finset.mem_insert, Finset.mem_erase, Finset.mem_image, Finset.mem_filter,
        Finset.mem_Icc]
      constructor
      · rintro (rfl | ⟨j, hj, rfl⟩)
        · exact Or.inl rfl
        · refine Or.inr ⟨?_, ?_, Or.inr ⟨j, ⟨hj.1, by omega⟩, rfl⟩⟩
          · intro h
            have e := (bT_ends r P j).1
            rw [h, (bT_ends r P (k + 2)).1] at e
            have := wd_inj r P hr hP (k := 0) (l := 0) (i := k + 2) (j := j) (by omega) (by omega)
              hk2 hk hj.1.1 hj.1.2 (Option.some.inj e)
            omega
          · intro h
            have e := (bT_ends r P j).1
            rw [h, (chain_ends r P k).1] at e
            have := wd_inj r P hr hP (k := 0) (l := 0) (i := 1) (j := j) (by omega) (by omega)
              le_rfl hr hj.1.1 hj.1.2 (Option.some.inj e)
            omega
      · rintro (rfl | ⟨h1, h2, h3⟩)
        · exact Or.inl rfl
        · rcases h3 with h3 | ⟨j, hj, rfl⟩
          · exact absurd h3 h2
          · refine Or.inr ⟨j, ⟨hj.1, ?_⟩, rfl⟩
            have : j ≠ k + 2 := by
              rintro rfl
              exact h1 rfl
            omega
    have hw' : (chain r P (k + 1)).word =
        ((List.range (k + 1 + 1)).map (fun j => T r P (j + 1))).flatten := by
      have : merge (chain r P k).word (T r P (k + 2)) = (chain r P k).word ++ T r P (k + 2) := by
        have g2' : overlapLength (chain r P k).word (T r P (k + 2)) = 0 := g2
        unfold merge
        rw [g2']
        simp
      rw [chain_word, this, hw]
      simp [List.range_succ]
    refine ⟨reach_step hR (by rw [hset]; exact g1), hw'⟩

end Concat

/-! ### The long word -/
section LongWord
variable (r P : ℕ) (hr : 1 ≤ r) (hP : r ≤ P + 1)
include hr hP

lemma greedy_out : IsGreedyOutput (inputFamily r P) (longWord r P) := by
  obtain ⟨hR, hw⟩ := phase4 r P hr hP (r - 1) (by omega)
  have hset : state4 r P (r - 1) = {chain r P (r - 1)} := by
    unfold state4
    have : ((Finset.Icc 1 r).filter (fun j => r - 1 + 1 < j)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro j hj
      rw [Finset.mem_Icc] at hj
      omega
    rw [this]
    simp
  rw [hset] at hR
  obtain ⟨ls, hrun⟩ := hR
  refine ⟨(chain r P (r - 1)).history, ls, ?_⟩
  have hlw : (chain r P (r - 1)).word = longWord r P := by
    rw [hw, Nat.sub_add_cancel hr]
    rfl
  have : ({chain r P (r - 1)} : Finset Blk) =
      {⟨longWord r P, (chain r P (r - 1)).history⟩} := by
    rw [← hlw]
  rw [this] at hrun
  exact hrun

lemma wd_in {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ r) :
    X r P i ∈ inputFamily r P ∧ Y r P i ∈ inputFamily r P ∧ U r P i ∈ inputFamily r P ∧
    V r P i ∈ inputFamily r P ∧ Z r P i ∈ inputFamily r P := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [mem_inputFamily_iff] <;> exact ⟨i, h1, h2, by simp⟩

lemma binary_merge {s t : Word} (hs : IsBinary s) (ht : IsBinary t) : IsBinary (merge s t) := by
  intro a ha
  rcases mem_merge ha with h | h
  · exact hs a h
  · exact ht a h

lemma binary_T {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ r) : IsBinary (T r P i) := by
  obtain ⟨hx, hy, hu, hv, hz⟩ := wd_in r P hr hP h1 h2
  have b := inputFamily_binary r P hr hP
  exact binary_merge r P hr hP (binary_merge r P hr hP (b _ hx) (b _ hy))
    (binary_merge r P hr hP (binary_merge r P hr hP (b _ hu) (b _ hv)) (b _ hz))

lemma binary_long : IsBinary (longWord r P) := by
  intro a ha
  unfold longWord at ha
  rw [List.mem_flatten] at ha
  obtain ⟨l, hl, hal⟩ := ha
  rw [List.mem_map] at hl
  obtain ⟨j, hj, rfl⟩ := hl
  rw [List.mem_range] at hj
  exact binary_T r P hr hP (by omega) (by omega) a hal

lemma infix_T {i : ℕ} :
    X r P i <:+: T r P i ∧ Y r P i <:+: T r P i ∧ U r P i <:+: T r P i ∧
    V r P i <:+: T r P i ∧ Z r P i <:+: T r P i := by
  have hAT : A r P i <+: T r P i := prefix_merge _ _
  have hCT : C r P i <:+ T r P i := suffix_merge _ _
  have hBC : B r P i <+: C r P i := prefix_merge _ _
  have hZC : Z r P i <:+ C r P i := suffix_merge _ _
  have hXA : X r P i <+: A r P i := prefix_merge _ _
  have hYA : Y r P i <:+ A r P i := suffix_merge _ _
  have hUB : U r P i <+: B r P i := prefix_merge _ _
  have hVB : V r P i <:+ B r P i := suffix_merge _ _
  have hBT : B r P i <:+: T r P i := hBC.isInfix.trans hCT.isInfix
  exact ⟨(hXA.trans hAT).isInfix, hYA.isInfix.trans hAT.isInfix,
    hUB.isInfix.trans hBT, hVB.isInfix.trans hBT, hZC.isInfix.trans hCT.isInfix⟩

lemma super_long : IsCommonSuperstring (inputFamily r P).toList (longWord r P) := by
  intro s hs
  rw [Finset.mem_toList, mem_inputFamily_iff] at hs
  obtain ⟨i, h1, h2, h⟩ := hs
  have hT : T r P i <:+: longWord r P := by
    apply List.infix_of_mem_flatten
    rw [List.mem_map]
    exact ⟨i - 1, List.mem_range.2 (by omega), by rw [Nat.sub_add_cancel h1]⟩
  obtain ⟨a, b, c, d, e⟩ := infix_T r P hr hP (i := i)
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact a.trans hT
  · exact b.trans hT
  · exact c.trans hT
  · exact d.trans hT
  · exact e.trans hT

lemma len_X (i : ℕ) : (X r P i).length = 6 * P + 20 * r + 2 * i + 1 := by
  unfold X
  rw [gapWord_length (by simp [privateGap, commonGap]; omega)]
  simp [privateGap, commonGap]
  omega

lemma len_Y (i : ℕ) : (Y r P i).length = 6 * P + 22 * r + 2 * i + 1 := by
  unfold Y
  rw [gapWord_length (by simp [privateGap, commonGap]; omega)]
  simp [privateGap, commonGap]
  omega

lemma len_U (i : ℕ) : (U r P i).length = 6 * P + 25 * r + i + 1 := by
  unfold U
  rw [gapWord_length (by simp [privateGap, commonGap]; omega)]
  simp [privateGap, commonGap]
  omega

lemma len_V (i : ℕ) : (V r P i).length = 6 * P + 26 * r + i + 1 := by
  unfold V
  rw [gapWord_length (by simp [privateGap, commonGap]; omega)]
  simp [privateGap, commonGap]
  omega

lemma len_Z (i : ℕ) : (Z r P i).length = 4 * P + 18 * r + i + 1 := by
  unfold Z
  rw [gapWord_length (by simp [privateGap, commonGap]; omega)]
  simp [privateGap, commonGap]
  omega

lemma len_T {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ r) :
    (T r P i).length = 12 * P + 55 * r + 5 * i + 1 := by
  have hAC := (phase3 r P hr hP r le_rfl).2 i h1 h2
  have hBZ := (phase2 r P hr hP r le_rfl).2 i h1 h2
  have e1 := merge_length' (X r P i) (Y r P i)
  have e2 := merge_length' (U r P i) (V r P i)
  have e3 := merge_length' (B r P i) (Z r P i)
  have e4 := merge_length' (A r P i) (C r P i)
  rw [ovl_XY r P hr hP h1 h2] at e1
  rw [ovl_UV r P hr hP h1 h2] at e2
  rw [hBZ] at e3
  rw [hAC] at e4
  have a1 := len_X r P hr hP i
  have a2 := len_Y r P hr hP i
  have a3 := len_U r P hr hP i
  have a4 := len_V r P hr hP i
  have a5 := len_Z r P hr hP i
  have e1' : (A r P i).length + alpha r P i = (X r P i).length + (Y r P i).length := e1
  have e2' : (B r P i).length + alpha r P i = (U r P i).length + (V r P i).length := e2
  have e3' : (C r P i).length + beta r P = (B r P i).length + (Z r P i).length := e3
  have e4' : (T r P i).length + gamma r P = (A r P i).length + (C r P i).length := e4
  clear e1 e2 e3 e4
  unfold alpha beta gamma at *
  omega

lemma len_long : (longWord r P).length = 12 * P * r + (115 * r ^ 2 + 7 * r) / 2 := by
  have key : ∀ k, k ≤ r →
      2 * (((List.range k).map (fun j => T r P (j + 1))).flatten.length) =
        k * (24 * P + 110 * r + 2) + 5 * (k * (k + 1)) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have := ih (by omega)
      rw [List.range_succ, List.map_append, List.flatten_append, List.length_append]
      simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        List.append_nil]
      have hl := len_T r P hr hP (i := k + 1) (by omega) (by omega)
      rw [hl]
      nlinarith [this]
  have h1 := key r le_rfl
  unfold longWord
  have h3 : 2 * ((List.map (fun j => T r P (j + 1)) (List.range r)).flatten.length) =
      24 * (P * r) + 115 * r ^ 2 + 7 * r := by
    nlinarith [h1]
  have h4 : 12 * P * r = 12 * (P * r) := by ring
  omega

end LongWord

end GreedySuperstring.Dev.Goal

namespace GreedySuperstring.LowerBound

/-- Theorem 4.1, printed/PDF p.14. Both witnesses have exact lengths.
The source's integer domain is exactly the natural domain below, including (1,0).
The numerator 115*r^2+7*r is even for every natural r. -/
theorem chk_binary_greedy_lower_bound (r P : ℕ) (hr : 1 ≤ r) (hP : r ≤ P + 1) :
    ∃ (S : Finset OAI.Superstring.Word) (H g : OAI.Superstring.Word),
      S.card = 5 * r ∧
      (∀ s ∈ S, IsBinary s ∧ s ≠ []) ∧ SubstringFree S ∧
      IsBinary H ∧ IsBinary g ∧
      OAI.Superstring.IsCommonSuperstring S.toList H ∧
      OAI.Superstring.IsCommonSuperstring S.toList g ∧
      IsGreedyOutput S g ∧
      H.length = 5 * P * r + 27 * r ^ 2 + 4 * P + 19 * r + 1 ∧
      g.length = 12 * P * r + (115 * r ^ 2 + 7 * r) / 2 :=
  ⟨inputFamily r P, shortWord r P, longWord r P, inputFamily_card r P hr hP,
    fun s hs => ⟨inputFamily_binary r P hr hP s hs, inputFamily_ne_nil r P hr hP s hs⟩,
    inputFamily_substringFree r P hr hP, shortWord_binary r P,
    GreedySuperstring.Dev.Goal.binary_long r P hr hP,
    shortWord_superstring r P hr hP, GreedySuperstring.Dev.Goal.super_long r P hr hP,
    GreedySuperstring.Dev.Goal.greedy_out r P hr hP, shortWord_length r P hr,
    GreedySuperstring.Dev.Goal.len_long r P hr hP⟩

end GreedySuperstring.LowerBound
end

theorem solution : type_of% @GreedySuperstring.LowerBound.chk_binary_greedy_lower_bound := @GreedySuperstring.LowerBound.chk_binary_greedy_lower_bound
