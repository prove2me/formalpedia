-- Prove2me | solution 1 for GreedySuperstring.LowerBound.gap_word_overlap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:41:56.349829+00:00
-- url     : https://prove2.me/submissions/0ce7d021-8ae9-4713-8dd3-715102dc84c2

import Mathlib
import Definitions.Def_GreedySuperstring_LowerBound_WordModel
import Definitions.Def_GreedySuperstring_LowerBound_GapModel
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

theorem bd_append (u v : List ℕ) : bd (u ++ v) = bd u ++ bd v := by
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

theorem exists_bw {X : List Bool} (h : true ∈ X) :
    ∃ a w b, Pos w ∧ X = bw a w b := by
  -- decompose the tail after the first true
  have tail : ∀ Z : List Bool, ∃ w b, Pos w ∧ Z = bd w ++ List.replicate b false := by
    intro Z
    induction Z with
    | nil => exact ⟨[], 0, by simp [Pos], by simp⟩
    | cons z Z ih =>
      obtain ⟨w, b, hw, rfl⟩ := ih
      cases z with
      | true =>
        refine ⟨1 :: w, b, ?_, by simp⟩
        intro g hg
        simp at hg
        rcases hg with rfl | hg
        · omega
        · exact hw g hg
      | false =>
        cases w with
        | nil => exact ⟨[], b + 1, by simp [Pos], by simp [List.replicate_succ]⟩
        | cons g w' =>
          have hg : 0 < g := hw g (by simp)
          obtain ⟨k, rfl⟩ : ∃ k, g = k + 1 := ⟨g - 1, by omega⟩
          refine ⟨(k + 1 + 1) :: w', b, ?_, ?_⟩
          · intro x hx
            simp at hx
            rcases hx with rfl | hx
            · omega
            · exact hw x (by simp [hx])
          · simp [bd_cons, List.replicate_succ]
  obtain ⟨s1, s2, rfl, hs1⟩ := exists_first_true h
  obtain ⟨w, b, hw, rfl⟩ := tail s2
  exact ⟨s1.length, w, b, hw, by
    rw [allfalse_eq_rep hs1]; simp [bw, List.append_assoc]⟩

theorem suffix_exists {L R a m : ℕ} {u : List ℕ} (hu : Pos u) (hm : m ≤ u.length)
    (h0 : m = 0 → a ≤ L)
    (h1 : ∀ i, m = i + 1 → ∀ g, u[i]? = some g → a < g) :
    bw a (u.drop m) R <:+ bw L u R := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · have := h0 rfl
    refine ⟨List.replicate (L - a) false, ?_⟩
    simp only [List.drop_zero, bw]
    have e : List.replicate L false =
        List.replicate (L - a) false ++ List.replicate a false := by
      rw [← List.replicate_add]; congr 1; omega
    rw [e]; simp only [List.append_assoc, List.cons_append]
  · obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
    have hi : i < u.length := by omega
    have hg := h1 i rfl u[i] (by simp)
    have hupos : 0 < u[i] := hu _ (by simp)
    have hu_eq : u = u.take i ++ u[i] :: u.drop (i + 1) := by
      have := List.take_append_drop i u
      rw [List.drop_eq_getElem_cons hi] at this
      exact this.symm
    refine ⟨List.replicate L false ++ true :: (bd (u.take i) ++ List.replicate (u[i] - 1 - a) false), ?_⟩
    conv_rhs => rw [hu_eq]
    simp only [bw, bd_append, bd_cons, List.append_assoc, List.cons_append]
    have : List.replicate (u[i] - 1) false =
        List.replicate (u[i] - 1 - a) false ++ List.replicate a false := by
      rw [← List.replicate_add]; congr 1; omega
    rw [this]
    simp only [List.append_assoc, List.cons_append]

theorem prefix_exists {L' R' b j : ℕ} {v : List ℕ} (hv : Pos v) (hj : j ≤ v.length)
    (h0 : j = v.length → b ≤ R')
    (h1 : ∀ g, v[j]? = some g → b < g) :
    bw L' (v.take j) b <+: bw L' v R' := by
  rcases Nat.lt_or_ge j v.length with hlt | hge
  · have hg := h1 v[j] (by simp [hlt])
    have hv_eq : v = v.take j ++ v[j] :: v.drop (j + 1) := by
      have := List.take_append_drop j v
      rw [List.drop_eq_getElem_cons hlt] at this
      exact this.symm
    have hvpos : 0 < v[j] := hv _ (by simp)
    refine ⟨List.replicate (v[j] - 1 - b) false ++ true :: (bd (v.drop (j + 1)) ++
      List.replicate R' false), ?_⟩
    conv_rhs => rw [hv_eq]
    simp only [bw, bd_append, bd_cons, List.append_assoc, List.cons_append]
    have : List.replicate (v[j] - 1) false =
        List.replicate b false ++ List.replicate (v[j] - 1 - b) false := by
      rw [← List.replicate_add]; congr 1; omega
    rw [this]
    simp only [List.append_assoc, List.cons_append]
  · have hj' : j = v.length := by omega
    have := h0 hj'
    refine ⟨List.replicate (R' - b) false, ?_⟩
    rw [hj', List.take_length]
    simp only [bw, List.append_assoc]
    have e : List.replicate R' false =
        List.replicate b false ++ List.replicate (R' - b) false := by
      rw [← List.replicate_add]; congr 1; omega
    rw [e]; simp only [List.append_assoc, List.cons_append]

theorem rep_suffix_le {m L R : ℕ} {u : List ℕ} (h : List.replicate m false <:+ bw L u R) :
    m ≤ R := by
  obtain ⟨s, hs⟩ := h
  have hlast : ∃ P, bw L u R = P ++ true :: List.replicate R false := by
    rcases List.eq_nil_or_concat u with rfl | ⟨u', g, rfl⟩
    · exact ⟨List.replicate L false, by simp [bw]⟩
    · exact ⟨List.replicate L false ++ true :: (bd u' ++ List.replicate (g - 1) false), by
        simp [bw, bd_append]⟩
  obtain ⟨P, hP⟩ := hlast
  rw [hP] at hs
  have := congrArg List.reverse hs
  rw [List.reverse_append, List.reverse_append, List.reverse_replicate] at this
  have h2 : List.replicate m false ++ s.reverse = List.replicate R false ++ true :: P.reverse := by
    simpa using this
  exact rep_prefix_le h2

theorem rep_prefix_le' {m L R : ℕ} {u : List ℕ} (h : List.replicate m false <+: bw L u R) :
    m ≤ L := by
  obtain ⟨t, ht⟩ := h
  exact rep_prefix_le (r := bd u ++ List.replicate R false) (t := t) (by simpa [bw] using ht)

def JP (L R : ℕ) (u : List ℕ) (L' R' : ℕ) (v : List ℕ) (j : ℕ) : Prop :=
  j ≤ u.length ∧ j ≤ v.length ∧ u.drop (u.length - j) = v.take j ∧
  (j = u.length → L' ≤ L) ∧
  (j < u.length → ∀ g, u[u.length - j - 1]? = some g → L' < g) ∧
  (j = v.length → R ≤ R') ∧
  (j < v.length → ∀ g, v[j]? = some g → R < g)

theorem mem_J {L R L' R' : ℕ} {u v : List ℕ} {j : ℕ} :
    j ∈ gapMatches L R u L' R' v ↔ JP L R u L' R' v j := by
  have key : ∀ (l : List ℕ) (i c : ℕ), i < l.length →
      ((l[i]?).any (fun g => decide (c < g)) = true ↔ ∀ g, l[i]? = some g → c < g) := by
    intro l i c hi
    rw [List.getElem?_eq_getElem hi]
    simp
  simp only [gapMatches, Finset.mem_filter, Finset.mem_range, gapTests, Bool.and_eq_true,
    decide_eq_true_eq, JP]
  constructor
  · rintro ⟨hj, ⟨h1, h2⟩, h3⟩
    have hju : j ≤ u.length := by omega
    have hjv : j ≤ v.length := by omega
    refine ⟨hju, hjv, h1, ?_, ?_, ?_, ?_⟩
    · intro h; simpa [h] using h2
    · intro h
      have hne : j ≠ u.length := by omega
      rw [if_neg hne] at h2
      exact (key u _ _ (by omega)).mp h2
    · intro h; simpa [h] using h3
    · intro h
      have hne : j ≠ v.length := by omega
      rw [if_neg hne] at h3
      exact (key v _ _ h).mp h3
  · rintro ⟨hju, hjv, h1, h2, h3, h4, h5⟩
    refine ⟨by omega, ⟨h1, ?_⟩, ?_⟩
    · by_cases h : j = u.length
      · simpa [h] using h2 h
      · rw [if_neg h]
        exact (key u _ _ (by omega)).mpr (h3 (by omega))
    · by_cases h : j = v.length
      · simpa [h] using h4 h
      · rw [if_neg h]
        exact (key v _ _ (by omega)).mpr (h5 (by omega))

/-- Extraction of the data of a match containing a one. -/
theorem match_decode {L R L' R' : ℕ} {u v : List ℕ} (hu : Pos u) (hv : Pos v)
    {X : List Bool} (htrue : true ∈ X) (hsuf : X <:+ bw L u R) (hpre : X <+: bw L' v R') :
    ∃ j, JP L R u L' R' v j ∧ X = bw L' (v.take j) R := by
  obtain ⟨a, w, b, hw, rfl⟩ := exists_bw htrue
  obtain ⟨s, hs⟩ := hsuf
  obtain ⟨t, ht⟩ := hpre
  obtain ⟨p, q, e1, e2, e3, e4, e5, -, e7⟩ := lemQ R u hu L s a w b [] hw
    (by simpa [bw, List.append_assoc] using hs)
  obtain ⟨p', q', f1, f2, f3, f4, f5, f6, -⟩ := lemQ R' v hv L' [] a w b t hw
    (by simpa [bw, List.append_assoc] using ht)
  obtain ⟨hp0, haL⟩ := f6 rfl
  obtain ⟨hq0, hbR⟩ := e7 rfl
  have eu : u = p ++ w := by simpa [hq0] using e1
  have ev : v = w ++ q' := by simpa [hp0] using f1
  have hjv : v.take w.length = w := by rw [ev]; exact List.take_left
  refine ⟨w.length, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [eu]
  · simp [ev]
  · rw [eu, hjv]
    have : (p ++ w).length - w.length = p.length := by simp
    rw [this]; exact List.drop_left
  · intro h
    have : p.length = 0 := by
      have hl := h
      rw [eu, List.length_append] at hl
      omega
    have hp : p = [] := List.length_eq_zero_iff.mp this
    rw [← haL]; exact e2 hp
  · intro h g hg
    have hp : p ≠ [] := by
      intro hp; subst hp; rw [eu] at h; simp at h
    rw [← haL]
    apply e3 g
    rw [List.getLast?_eq_getElem?]
    rw [eu] at hg
    have hlt : p.length - 1 < p.length := by
      have := List.length_pos_iff.mpr hp; omega
    have : (p ++ w).length - w.length - 1 = p.length - 1 := by simp
    rw [this, List.getElem?_append_left hlt] at hg
    exact hg
  · intro h
    have : q' = [] := by
      rw [ev] at h; simp at h; exact h
    rw [← hbR]; exact f4 this
  · intro h g hg
    rw [← hbR]
    apply f5 g
    rw [ev] at hg
    rw [List.getElem?_append_right (by omega)] at hg
    simpa [List.head?_eq_getElem?] using hg
  · rw [hjv, haL, hbR]

theorem match_encode {L R L' R' : ℕ} {u v : List ℕ} (hu : Pos u) (hv : Pos v)
    (hst : ¬ bw L u R <:+: bw L' v R') (hts : ¬ bw L' v R' <:+: bw L u R)
    {j : ℕ} (hj : JP L R u L' R' v j) :
    bw L' (v.take j) R <:+ bw L u R ∧ bw L' (v.take j) R <+: bw L' v R' ∧
      (bw L' (v.take j) R).length < (bw L u R).length ∧
      (bw L' (v.take j) R).length < (bw L' v R').length := by
  obtain ⟨hju, hjv, hd, h2, h3, h4, h5⟩ := hj
  have hsuf : bw L' (v.take j) R <:+ bw L u R := by
    have := suffix_exists (L := L) (R := R) (a := L') (m := u.length - j) hu (by omega)
      (fun h => h2 (by omega)) (by
        intro i hi g hg
        have : i = u.length - j - 1 := by omega
        subst this
        exact h3 (by omega) g hg)
    rwa [hd] at this
  have hpre : bw L' (v.take j) R <+: bw L' v R' := by
    apply prefix_exists hv hjv h4
    intro g hg
    have : j < v.length := by
      by_contra hc
      rw [List.getElem?_eq_none (by omega)] at hg; simp at hg
    exact h5 this g hg
  refine ⟨hsuf, hpre, ?_, ?_⟩
  · rcases Nat.lt_or_ge (bw L' (v.take j) R).length (bw L u R).length with h | h
    · exact h
    · exfalso
      have heq := hsuf.eq_of_length (le_antisymm hsuf.length_le h)
      exact hst (heq ▸ hpre.isInfix)
  · rcases Nat.lt_or_ge (bw L' (v.take j) R).length (bw L' v R').length with h | h
    · exact h
    · exfalso
      have heq := hpre.eq_of_length (le_antisymm hpre.length_le h)
      exact hts (heq ▸ hsuf.isInfix)

theorem overlapLength_map {α β : Type} [DecidableEq α] [DecidableEq β] {f : α → β}
    (hf : Function.Injective f) (s t : List α) :
    overlapLength (s.map f) (t.map f) = overlapLength s t := by
  unfold overlapLength
  simp only [List.length_map]
  congr 1
  apply Finset.filter_congr
  intro n _
  rw [← List.map_drop, ← List.map_take]
  exact (List.map_injective_iff.mpr hf).eq_iff

theorem len_mono {L' R : ℕ} {v : List ℕ} (hv : Pos v) {j j' : ℕ} (h : j ≤ j') :
    (bw L' (v.take j) R).length ≤ (bw L' (v.take j') R).length := by
  have hp : ∀ k, Pos (v.take k) := fun k x hx => hv x (List.mem_of_mem_take hx)
  rw [bw_length (hp j), bw_length (hp j')]
  have : v.take j = (v.take j').take j := by rw [List.take_take]; congr 1; omega
  have h2 := List.take_append_drop j (v.take j')
  have h3 : (v.take j).sum ≤ (v.take j').sum := by
    rw [this]
    conv_rhs => rw [← List.take_append_drop j (v.take j')]
    rw [List.sum_append]; omega
  omega

theorem overlap_bits {L R L' R' : ℕ} {u v : List ℕ} (hu : Pos u) (hv : Pos v)
    (hst : ¬ bw L u R <:+: bw L' v R') (hts : ¬ bw L' v R' <:+: bw L u R) :
    overlapLength (bw L u R) (bw L' v R') =
      if (gapMatches L R u L' R' v).Nonempty then
        (bw L' (v.take ((gapMatches L R u L' R' v).sup id)) R).length
      else min R L' := by
  set O := bw L u R with hO
  set T := bw L' v R' with hT
  set J := gapMatches L R u L' R' v with hJ
  have hOl : R + 1 ≤ O.length := by rw [hO, bw_length hu]; omega
  have hTl : L' + 1 ≤ T.length := by rw [hT, bw_length hv]; omega
  have memF : ∀ n, n ∈ (Finset.range (min O.length T.length)).filter
      (fun n => O.drop (O.length - n) = T.take n) ↔
      (n < O.length ∧ n < T.length) ∧ O.drop (O.length - n) = T.take n := by
    intro n; simp [Finset.mem_filter, Finset.mem_range]
  -- the zero run is always a match
  have hzero : min R L' ∈ (Finset.range (min O.length T.length)).filter
      (fun n => O.drop (O.length - n) = T.take n) := by
    rw [memF]
    have hsuf : List.replicate (min R L') false <:+ O := by
      refine ⟨List.replicate L false ++ true :: (bd u ++ List.replicate (R - min R L') false), ?_⟩
      rw [hO]; simp only [bw, List.append_assoc, List.cons_append]
      rw [← List.replicate_add]; congr 4; omega
    have hpre : List.replicate (min R L') false <+: T := by
      refine ⟨List.replicate (L' - min R L') false ++ true :: (bd v ++ List.replicate R' false), ?_⟩
      have e : List.replicate L' false =
          List.replicate (min R L') false ++ List.replicate (L' - min R L') false := by
        rw [← List.replicate_add]; congr 1; omega
      rw [hT]; simp only [bw]
      rw [e]; simp only [List.append_assoc, List.cons_append]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have h1 := List.suffix_iff_eq_drop.mp hsuf
    have h2 := List.prefix_iff_eq_take.mp hpre
    simp only [List.length_replicate] at h1 h2
    rw [← h1, ← h2]
  have hJF : ∀ j, JP L R u L' R' v j →
      (bw L' (v.take j) R).length ∈ (Finset.range (min O.length T.length)).filter
      (fun n => O.drop (O.length - n) = T.take n) := by
    intro j hj
    obtain ⟨h1, h2, h3, h4⟩ := match_encode hu hv hst hts hj
    rw [memF]
    refine ⟨⟨h3, h4⟩, ?_⟩
    have e1 := List.suffix_iff_eq_drop.mp h1
    have e2 := List.prefix_iff_eq_take.mp h2
    rw [← e1, ← e2]
  have hcases : ∀ n, n ∈ (Finset.range (min O.length T.length)).filter
      (fun n => O.drop (O.length - n) = T.take n) →
      (∃ j, JP L R u L' R' v j ∧ n = (bw L' (v.take j) R).length) ∨ n ≤ min R L' := by
    intro n hn
    rw [memF] at hn
    obtain ⟨⟨hn1, hn2⟩, hn3⟩ := hn
    have hsuf : T.take n <:+ O := by rw [← hn3]; exact List.drop_suffix _ _
    have hpre : T.take n <+: T := List.take_prefix _ _
    have hlen : (T.take n).length = n := by simp; omega
    by_cases ht : true ∈ T.take n
    · obtain ⟨j, hj, hX⟩ := match_decode hu hv ht hsuf hpre
      left
      refine ⟨j, hj, ?_⟩
      rw [← hX, hlen]
    · right
      have hall : ∀ x ∈ T.take n, x = false := by
        intro x hx; cases x with
        | true => exact absurd hx ht
        | false => rfl
      have hrep := allfalse_eq_rep hall
      rw [hlen] at hrep
      rw [hrep] at hsuf hpre
      have a1 := rep_suffix_le hsuf
      have a2 := rep_prefix_le' hpre
      omega
  unfold overlapLength
  split_ifs with hne
  · obtain ⟨j0, hj0, hjsup⟩ := Finset.exists_mem_eq_sup J hne id
    have hjP : JP L R u L' R' v j0 := mem_J.mp hj0
    rw [hjsup]
    apply le_antisymm
    · apply Finset.sup_le
      intro n hn
      rcases hcases n hn with ⟨j, hj, rfl⟩ | h
      · have hjJ : j ∈ J := mem_J.mpr hj
        have : j ≤ J.sup id := Finset.le_sup (f := id) hjJ
        rw [hjsup] at this
        exact len_mono hv this
      · have : (bw L' (v.take j0) R).length ≥ L' + 1 + R := by
          have hp : Pos (v.take j0) := fun x hx => hv x (List.mem_of_mem_take hx)
          rw [bw_length hp]; omega
        simp only [id]
        omega
    · exact Finset.le_sup (f := id) (hJF j0 hjP)
  · apply le_antisymm
    · apply Finset.sup_le
      intro n hn
      rcases hcases n hn with ⟨j, hj, rfl⟩ | h
      · exact absurd ⟨j, mem_J.mpr hj⟩ hne
      · exact h
    · exact Finset.le_sup (f := id) hzero

end GreedySuperstring.Dev.GapOverlap

namespace GreedySuperstring.LowerBound

open GreedySuperstring.Dev.GapOverlap

theorem chk_gap_word_overlap (L R L' R' : ℕ) (u v : List ℕ)
    (hu : ∀ g ∈ u, 0 < g) (hv : ∀ g ∈ v, 0 < g)
    (hst : ¬ gapWord L u R <:+: gapWord L' v R')
    (hts : ¬ gapWord L' v R' <:+: gapWord L u R) :
    overlap (gapWord L u R) (gapWord L' v R') =
      if (gapMatches L R u L' R' v).Nonempty then
        gapWord L' (v.take ((gapMatches L R u L' R' v).sup id)) R
      else List.replicate (min R L') zeroSymbol := by
  have hst' : ¬ bw L u R <:+: bw L' v R' := by
    intro h; apply hst; rw [gapWord_eq_map, gapWord_eq_map]; exact h.map _
  have hts' : ¬ bw L' v R' <:+: bw L u R := by
    intro h; apply hts; rw [gapWord_eq_map, gapWord_eq_map]; exact h.map _
  simp only [gapWord_eq_map]
  rw [overlap, overlapLength_map sym_inj, overlap_bits hu hv hst' hts', ← List.map_take]
  split_ifs with hne
  · obtain ⟨j0, hj0, hjsup⟩ := Finset.exists_mem_eq_sup _ hne id
    have hjP := mem_J.mp hj0
    rw [hjsup]
    have := (match_encode hu hv hst' hts' hjP).2.1
    simp only [id]
    rw [← List.prefix_iff_eq_take.mp this]
  · have : (bw L' v R').take (min R L') = List.replicate (min R L') false := by
      rw [bw, List.take_append_of_le_length (by simp)]
      simp [List.take_replicate, min_comm]
    rw [this]
    simp [zeroSymbol, sym, List.map_replicate]

end GreedySuperstring.LowerBound
end

theorem solution : type_of% @GreedySuperstring.LowerBound.chk_gap_word_overlap := @GreedySuperstring.LowerBound.chk_gap_word_overlap
