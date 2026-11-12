-- Prove2me | solution 1 for GreedySuperstring.LowerBound.large_overlap_pairs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:09:22.328123+00:00
-- url     : https://prove2.me/submissions/3256f44c-2c3b-4291-91f7-1266bee28659

import Mathlib
import Definitions.Def_GreedySuperstring_LowerBound_WordModel
import Definitions.Def_GreedySuperstring_LowerBound_GapModel
import Definitions.Def_GreedySuperstring_LowerBound_Construction
import Theorems.Thm_GreedySuperstring_LowerBound_gap_word_overlap
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

/-! ### the short word -/

end GreedySuperstring.Dev.Family

namespace GreedySuperstring.LowerBound
open GreedySuperstring.Dev.Family OAI.Superstring

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

def listed (k l : Fin 5) : Prop :=
  (k = 0 ∧ l = 1) ∨ (k = 0 ∧ l = 3) ∨ (k = 2 ∧ l = 1) ∨ (k = 2 ∧ l = 3) ∨ (k = 1 ∧ l = 0)

theorem large_core (k l : Fin 5) (r P i j : ℕ) (hr : 1 ≤ r) (hP : r ≤ P + 1)
    (hi1 : 1 ≤ i) (hi2 : i ≤ r) (hj1 : 1 ≤ j) (hj2 : j ≤ r) (hne : k ≠ l ∨ i ≠ j)
    (hnl : ¬ (i = j ∧ listed k l)) :
    overlapLength (W k r P i) (W l r P j) ≤ beta r P := by
  apply W_le k l r P i j hr hi1 hi2 hj1 hj2 hne
  · fin_cases k <;> fin_cases l <;> simp [lpad, rpad, beta] <;> omega
  · intro jj hjj ht
    unfold commonGap privateGap beta at *
    fin_cases k <;> fin_cases l <;> simp [listed] at hnl <;> simp [gp, lpad, rpad] at hjj ht ⊢ <;>
      interval_cases jj <;> simp [gapTests] at ht ⊢ <;> omega

end GreedySuperstring.Dev.Table

namespace GreedySuperstring.LowerBound

open GreedySuperstring.Dev.Family GreedySuperstring.Dev.Table

/- Table of exact overlap lengths (Table 2 and the step (ii)-(iv) bounds), `overlapLength` form. -/
section Table
variable (r P : ℕ) (hr : 1 ≤ r) (hP : r ≤ P + 1)
include hr hP

end Table
end GreedySuperstring.LowerBound
end

section
set_option autoImplicit false

namespace GreedySuperstring.LowerBound

open GreedySuperstring.Dev.Family GreedySuperstring.Dev.Table

theorem chk_large_overlap_pairs (r P : ℕ) (hr : 1 ≤ r) (hP : r ≤ P + 1)
    (s t : OAI.Superstring.Word) (hs : s ∈ inputFamily r P) (ht : t ∈ inputFamily r P)
    (hne : s ≠ t) (hov : beta r P < (overlap s t).length) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ r ∧
      ((s = X r P i ∧ t = Y r P i) ∨
       (s = X r P i ∧ t = V r P i) ∨
       (s = U r P i ∧ t = Y r P i) ∨
       (s = U r P i ∧ t = V r P i) ∨
       (s = Y r P i ∧ t = X r P i)) := by
  obtain ⟨k, i, hi1, hi2, rfl⟩ := (mem_iff_W r P s).mp hs
  obtain ⟨l, j, hj1, hj2, rfl⟩ := (mem_iff_W r P t).mp ht
  have hlen : (overlap (W k r P i) (W l r P j)).length = overlapLength (W k r P i) (W l r P j) := by
    unfold overlap
    rw [List.length_take, Nat.min_eq_left (overlapLength_le_length _ _)]
  rw [hlen] at hov
  have hne' : k ≠ l ∨ i ≠ j := by
    by_contra h
    push Not at h
    obtain ⟨rfl, rfl⟩ := h
    exact hne rfl
  by_cases hnl : ¬ (i = j ∧ listed k l)
  · exact absurd (large_core k l r P i j hr hP hi1 hi2 hj1 hj2 hne' hnl) (by omega)
  · push Not at hnl
    obtain ⟨rfl, hl⟩ := hnl
    refine ⟨i, hi1, hi2, ?_⟩
    unfold listed at hl
    rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))

end GreedySuperstring.LowerBound
end

theorem solution : type_of% @GreedySuperstring.LowerBound.chk_large_overlap_pairs := @GreedySuperstring.LowerBound.chk_large_overlap_pairs
