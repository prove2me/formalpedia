-- Prove2me | solution 1 for HammingSumset729.Approximation.lemma_A_5
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:16:29.438609+00:00
-- url     : https://prove2.me/submissions/6e73bcb4-1aa3-4bbf-b325-fd9a905cf52e

import Definitions.Def_HammingSumset729_Approximation_Strings

set_option autoImplicit false
open scoped ENNReal NNReal
open HammingSumset729.Approximation

/-- Column with an index offset `k`. -/
private def F {α : Type*} (ell i : ℕ) (l : List α) (k : ℕ) : List α :=
  ((l.zipIdx k).filter fun ai => ai.2 % ell = i).map Prod.fst

private lemma F_nil {α : Type*} (ell i k : ℕ) : F ell i ([] : List α) k = [] := by
  simp [F]

private lemma F_cons {α : Type*} (ell i : ℕ) (a : α) (l : List α) (k : ℕ) :
    F ell i (a :: l) k = (if k % ell = i then [a] else []) ++ F ell i l (k + 1) := by
  by_cases h : k % ell = i <;> simp [F, List.zipIdx_cons, h]

private lemma F_append {α : Type*} (ell i : ℕ) (l₁ l₂ : List α) (k : ℕ) :
    F ell i (l₁ ++ l₂) k = F ell i l₁ k ++ F ell i l₂ (k + l₁.length) := by
  simp [F, List.zipIdx_append, List.filter_append]

private lemma F_shift {α : Type*} (ell i : ℕ) (l : List α) (k : ℕ) :
    F ell i l (k + ell) = F ell i l k := by
  induction l generalizing k with
  | nil => simp [F_nil]
  | cons a l ih =>
    rw [F_cons, F_cons, Nat.add_mod_right, show k + ell + 1 = (k + 1) + ell by omega, ih]

private lemma F_blk {α : Type*} (ell i : ℕ) (hi : i < ell) (a : List α) (k : ℕ)
    (hk : k + a.length ≤ ell) :
    F ell i a k = if k ≤ i then (a[i - k]?).toList else [] := by
  induction a generalizing k with
  | nil => simp [F_nil]
  | cons x l ih =>
    simp only [List.length_cons] at hk
    rw [F_cons, ih (k + 1) (by omega), Nat.mod_eq_of_lt (by omega : k < ell)]
    rcases lt_trichotomy k i with h | h | h
    · have e : i - k = (i - (k + 1)) + 1 := by omega
      rw [if_neg h.ne, if_pos (by omega), if_pos h.le, e, List.getElem?_cons_succ]
      simp
    · subst h
      simp
    · rw [if_neg h.ne', if_neg (by omega), if_neg (by omega)]
      simp

private lemma column_eq_F {α : Type*} (s : List α) (ell i : ℕ) :
    column s ell i = F ell i s 0 := rfl

private lemma column_split {α : Type*} (b : List α) (ell i : ℕ) (hi : i < ell) :
    column b ell i = (b[i]?).toList ++ column (b.drop ell) ell i := by
  rw [column_eq_F, column_eq_F]
  conv_lhs => rw [← List.take_append_drop ell b]
  rw [F_append, F_blk ell i hi _ 0 (by simp), if_pos (Nat.zero_le _), Nat.sub_zero,
    List.getElem?_take_of_lt hi]
  congr 1
  by_cases h : ell ≤ b.length
  · rw [List.length_take, min_eq_left h]
    simpa using F_shift ell i (b.drop ell) 0
  · have : b.drop ell = [] := List.drop_eq_nil_of_le (by omega)
    rw [this, F_nil, F_nil]

private lemma dist_eq {α : Type*} [DecidableEq α] : ∀ (s t : List α), s.length = t.length →
    distance s t = ∑ j ∈ Finset.range s.length, if s[j]? ≠ t[j]? then 1 else 0
  | [], [], _ => by simp [distance]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: s, y :: t, h => by
    rw [List.length_cons, Finset.sum_range_succ']
    have IH := dist_eq s t (by simpa using h)
    simp only [distance] at IH ⊢
    rw [List.zip_cons_cons, List.filter_cons]
    by_cases hxy : x = y
    · simp [hxy] at IH ⊢; omega
    · simp [hxy] at IH ⊢; omega

private lemma column_get {α : Type*} (ell : ℕ) (hell : 0 < ell) (r : ℕ) (hr : r < ell) :
    ∀ M (s : List α), s.length = M * ell → ∀ q, q < M →
      (column s ell r)[q]? = s[q * ell + r]? := by
  intro M
  induction M with
  | zero => intro s _ q hq; omega
  | succ M ih =>
    intro s hs q hq
    rw [column_split s ell r hr]
    have hr' : r < s.length := by rw [hs]; nlinarith
    rw [List.getElem?_eq_getElem hr']
    cases q with
    | zero => simp
    | succ q =>
      simp only [Option.toList_some, List.singleton_append, List.getElem?_cons_succ]
      rw [ih (s.drop ell) (by simp [hs]; rw [Nat.succ_mul]; omega) q (by omega),
        List.getElem?_drop]
      congr 1; rw [Nat.succ_mul]; ring

private lemma column_length {α : Type*} (ell : ℕ) (hell : 0 < ell) (r : ℕ) (hr : r < ell) :
    ∀ M (s : List α), s.length = M * ell → (column s ell r).length = M := by
  intro M
  induction M with
  | zero =>
    intro s hs
    have : s = [] := List.eq_nil_of_length_eq_zero (by simpa using hs)
    subst this; simp [column_eq_F, F_nil]
  | succ M ih =>
    intro s hs
    rw [column_split s ell r hr]
    have hr' : r < s.length := by rw [hs]; nlinarith
    rw [List.getElem?_eq_getElem hr']
    simp only [Option.toList_some, List.singleton_append, List.length_cons]
    rw [ih (s.drop ell) (by simp [hs]; rw [Nat.succ_mul]; omega)]

private lemma flatMap_get {β : Type*} (M : ℕ) (f : ℕ → List β) :
    ∀ n, (∀ i, i < n → (f i).length = M) →
      ((List.range n).flatMap f).length = n * M ∧
      ∀ r q, r < n → q < M → ((List.range n).flatMap f)[r * M + q]? = (f r)[q]? := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hf
    obtain ⟨hl, hg⟩ := ih (fun i hi => hf i (by omega))
    rw [List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append, hl,
      hf n (by omega)]
    refine ⟨by ring, ?_⟩
    intro r q hr hq
    by_cases hrn : r < n
    · rw [List.getElem?_append_left (by rw [hl]; nlinarith), hg r q hrn hq]
    · have : r = n := by omega
      subst this
      rw [List.getElem?_append_right (by rw [hl]; exact Nat.le_add_right _ _), hl]
      congr 1; omega

private lemma columns_get {α : Type*} (ell : ℕ) (hell : 0 < ell) (M : ℕ) (s : List α)
    (hs : s.length = M * ell) :
    (columns s ell).length = ell * M ∧
      ∀ r q, r < ell → q < M → (columns s ell)[r * M + q]? = s[q * ell + r]? := by
  obtain ⟨h1, h2⟩ := flatMap_get M (column s ell) ell
    (fun i hi => column_length ell hell i hi M s hs)
  refine ⟨h1, fun r q hr hq => ?_⟩
  unfold columns
  rw [h2 r q hr hq, column_get ell hell r hr M s hs q hq]

private lemma column_mem {α : Type*} (s : List α) (ell r : ℕ) (c : α)
    (h : c ∈ column s ell r) : c ∈ s := by
  unfold column at h
  simp only [List.mem_map, List.mem_filter] at h
  obtain ⟨⟨a, i⟩, ⟨hmem, _⟩, rfl⟩ := h
  rw [List.mk_mem_zipIdx_iff_getElem?] at hmem
  exact List.mem_of_getElem? hmem

private lemma columns_mem {α : Type*} (s : List α) (ell : ℕ) (c : α)
    (h : c ∈ columns s ell) : c ∈ s := by
  unfold columns at h
  simp only [List.mem_flatMap] at h
  obtain ⟨r, _, hr⟩ := h
  exact column_mem s ell r c hr

private lemma encodedText_ne {α : Type*} (t : List α) (ell j : ℕ) :
    (encodedText t ell)[j]? ≠ some (Sum.inr true) := by
  intro h
  have hm : (Sum.inr true : α ⊕ Bool) ∈ encodedText t ell := List.mem_of_getElem? h
  unfold encodedText at hm
  rcases List.mem_append.mp hm with h1 | h1
  · have := columns_mem _ _ _ h1
    simp at this
  · have := columns_mem _ _ _ h1
    rcases List.mem_append.mp this with h2 | h2
    · have := List.mem_of_mem_drop h2
      simp at this
    · simp at h2

private lemma sum_mul_split (f : ℕ → ℕ) (b : ℕ) : ∀ a,
    ∑ j ∈ Finset.range (a * b), f j = ∑ i ∈ Finset.range a, ∑ k ∈ Finset.range b, f (i * b + k)
  | 0 => by simp
  | a + 1 => by
    rw [Nat.succ_mul, Finset.sum_range_add, sum_mul_split f b a, Finset.sum_range_succ]

theorem solution {α : Type*} [DecidableEq α] (t p : List α)
    (m₁ m₂ ell : ℕ) (hell : 0 < ell) (hm₂ : 0 < m₂) (hm : m₂ ≤ m₁)
    (ht : t.length = m₁ * ell) (hp : p.length = m₂ * ell)
    (alpha : ℕ) (halpha : alpha ≤ (m₁ - m₂) * ell) :
    (shiftDistance t p alpha : ℤ) =
      (shiftDistance (encodedText t ell) (encodedPattern p t.length ell)
        (alpha / ell + alpha % ell * m₁) : ℤ) - ((m₁ : ℤ) - m₂) * ell := by
  set x := alpha / ell with hx
  set y := alpha % ell with hy
  have hy' : y < ell := Nat.mod_lt _ hell
  have hxy : alpha = x * ell + y := by rw [hx, hy, Nat.mul_comm]; exact (Nat.div_add_mod _ _).symm
  have hxle : x ≤ m₁ - m₂ := by
    rw [hx]; exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm]; exact halpha)
  set s := t.map (Sum.inl : α → α ⊕ Bool) with hs
  have hsl : s.length = m₁ * ell := by simp [hs, ht]
  set s' := s.drop ell ++ List.replicate ell (Sum.inr false) with hs'
  have hs'l : s'.length = m₁ * ell := by
    simp [hs', hsl]
    have : ell ≤ m₁ * ell := Nat.le_mul_of_pos_left _ (by omega)
    omega
  obtain ⟨hc1l, hc1⟩ := columns_get ell hell m₁ s hsl
  obtain ⟨hc2l, hc2⟩ := columns_get ell hell m₁ s' hs'l
  set u := p.map (Sum.inl : α → α ⊕ Bool) ++
    List.replicate (t.length - p.length) (Sum.inr true) with hu
  have hul : u.length = m₁ * ell := by
    simp [hu, hp, ht]
    have : m₂ * ell ≤ m₁ * ell := Nat.mul_le_mul_right _ hm
    omega
  obtain ⟨hpl, hpg⟩ := columns_get ell hell m₁ u hul
  have hT : encodedText t ell = columns s ell ++ columns s' ell := rfl
  have hP : encodedPattern p t.length ell = columns u ell := rfl
  have hPl : (encodedPattern p t.length ell).length = m₁ * ell := by
    rw [hP, hpl, Nat.mul_comm]
  have hTl : (encodedText t ell).length = 2 * (m₁ * ell) := by
    rw [hT, List.length_append, hc1l, hc2l]; ring
  -- Text value at a general position
  have hTval : ∀ r q, r < ell → q < m₂ →
      (encodedText t ell)[x + y * m₁ + (r * m₁ + q)]? = s[alpha + (q * ell + r)]? := by
    intro r q hr hq
    have hq1 : x + q < m₁ := by omega
    have hidx : alpha + (q * ell + r) = (x + q) * ell + (y + r) := by rw [hxy]; ring
    have hlt : alpha + (q * ell + r) < m₁ * ell := by
      have : alpha + q * ell + ell ≤ m₁ * ell := by
        have h1 : (q + 1) * ell ≤ m₂ * ell := Nat.mul_le_mul_right _ (by omega)
        have h2 : (m₁ - m₂) * ell + m₂ * ell = m₁ * ell := by
          rw [← Nat.add_mul, Nat.sub_add_cancel hm]
        nlinarith
      omega
    rw [hT]
    by_cases hyr : y + r < ell
    · have e : x + y * m₁ + (r * m₁ + q) = (y + r) * m₁ + (x + q) := by ring
      rw [e, List.getElem?_append_left (by rw [hc1l]; nlinarith), hc1 _ _ hyr hq1, hidx]
    · have e : x + y * m₁ + (r * m₁ + q) = ell * m₁ + ((y + r - ell) * m₁ + (x + q)) := by
        have : y + r = ell + (y + r - ell) := by omega
        conv_lhs => rw [show x + y * m₁ + (r * m₁ + q) = (y + r) * m₁ + (x + q) by ring, this]
        ring
      have hk : ell + ((x + q) * ell + (y + r - ell)) = alpha + (q * ell + r) := by
        rw [hidx]
        have : y + r = ell + (y + r - ell) := by omega
        conv_rhs => rw [this]
        ring
      have hdl : (s.drop ell).length = m₁ * ell - ell := by simp [hsl]
      rw [e, List.getElem?_append_right (by rw [hc1l]; exact Nat.le_add_right _ _), hc1l,
        Nat.add_sub_cancel_left, hc2 _ _ (by omega) hq1, hs',
        List.getElem?_append_left (by rw [hdl]; omega), List.getElem?_drop, hk]
  have hPval_lo : ∀ r q, r < ell → q < m₂ →
      (encodedPattern p t.length ell)[r * m₁ + q]? = (p.map Sum.inl)[q * ell + r]? := by
    intro r q hr hq
    have key : q * ell + ell ≤ m₂ * ell := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hq
    have hml : (p.map (Sum.inl : α → α ⊕ Bool)).length = m₂ * ell := by simp [hp]
    rw [hP, hpg r q hr (by omega), hu, List.getElem?_append_left (by rw [hml]; omega)]
  have hPval_hi : ∀ r q, r < ell → m₂ ≤ q → q < m₁ →
      (encodedPattern p t.length ell)[r * m₁ + q]? = some (Sum.inr true) := by
    intro r q hr hq1 hq2
    have h1 : q * ell + ell ≤ m₁ * ell := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hq2
    have h2 : m₂ * ell ≤ q * ell := Nat.mul_le_mul_right _ hq1
    have hml : (p.map (Sum.inl : α → α ⊕ Bool)).length = m₂ * ell := by simp [hp]
    rw [hP, hpg r q hr hq2, hu, List.getElem?_append_right (by rw [hml]; omega), hml,
      List.getElem?_replicate, if_pos (by rw [hp, ht]; omega)]
  -- Express both distances as sums
  have hlhs_valid : alpha + p.length ≤ t.length := by
    rw [hp, ht]
    have h2 : (m₁ - m₂) * ell + m₂ * ell = m₁ * ell := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hm]
    omega
  have hL : shiftDistance t p alpha =
      ∑ j ∈ Finset.range (m₂ * ell), if t[alpha + j]? ≠ p[j]? then 1 else 0 := by
    rw [shiftDistance, dist_eq _ _ (by simp [substring]; omega)]
    have hsl2 : (substring t alpha p.length).length = m₂ * ell := by
      simp [substring]; omega
    rw [hsl2]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have e : (substring t alpha p.length)[j]? = t[alpha + j]? := by
      simp only [substring]
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop]
    simp only [e]
  have hβ : x + y * m₁ + (encodedPattern p t.length ell).length ≤
      (encodedText t ell).length := by
    rw [hPl, hTl]
    have : y * m₁ ≤ (ell - 1) * m₁ := Nat.mul_le_mul_right _ (by omega)
    have h2 : (ell - 1) * m₁ + m₁ = ell * m₁ := by
      rw [← Nat.succ_mul]; congr 1; omega
    have h3 : ell * m₁ = m₁ * ell := Nat.mul_comm _ _
    omega
  have hR : shiftDistance (encodedText t ell) (encodedPattern p t.length ell) (x + y * m₁) =
      ∑ j ∈ Finset.range (ell * m₁),
        if (encodedText t ell)[x + y * m₁ + j]? ≠ (encodedPattern p t.length ell)[j]?
        then 1 else 0 := by
    have hsl3 : (substring (encodedText t ell) (x + y * m₁)
        (encodedPattern p t.length ell).length).length =
        (encodedPattern p t.length ell).length := by
      simp only [substring, List.length_take, List.length_drop]; omega
    have hsl2 : (substring (encodedText t ell) (x + y * m₁)
        (encodedPattern p t.length ell).length).length = ell * m₁ := by
      rw [hsl3, hPl, Nat.mul_comm]
    rw [shiftDistance, dist_eq _ _ hsl3]
    rw [hsl2]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have e : (substring (encodedText t ell) (x + y * m₁)
        (encodedPattern p t.length ell).length)[j]? = (encodedText t ell)[x + y * m₁ + j]? := by
      simp only [substring]
      rw [List.getElem?_take_of_lt (by rw [hPl]; rw [Nat.mul_comm]; exact hj'),
        List.getElem?_drop]
    simp only [e]
  have hRsplit : ∑ j ∈ Finset.range (ell * m₁),
        (if (encodedText t ell)[x + y * m₁ + j]? ≠ (encodedPattern p t.length ell)[j]?
        then 1 else 0) =
      ∑ j ∈ Finset.range (m₂ * ell), (if t[alpha + j]? ≠ p[j]? then 1 else 0) +
        (m₁ - m₂) * ell := by
    rw [sum_mul_split]
    have inner : ∀ r ∈ Finset.range ell,
        ∑ q ∈ Finset.range m₁,
          (if (encodedText t ell)[x + y * m₁ + (r * m₁ + q)]? ≠
            (encodedPattern p t.length ell)[r * m₁ + q]? then 1 else 0) =
        ∑ q ∈ Finset.range m₂, (if t[alpha + (q * ell + r)]? ≠ p[q * ell + r]? then 1 else 0)
          + (m₁ - m₂) := by
      intro r hr
      have hr' := Finset.mem_range.mp hr
      conv_lhs => enter [1]; rw [show m₁ = m₂ + (m₁ - m₂) by omega]
      rw [Finset.sum_range_add]
      congr 1
      · apply Finset.sum_congr rfl
        intro q hq
        have hq' := Finset.mem_range.mp hq
        rw [hTval r q hr' hq', hPval_lo r q hr' hq', hs, List.getElem?_map, List.getElem?_map]
        by_cases hc : t[alpha + (q * ell + r)]? = p[q * ell + r]?
        · rw [hc]; simp
        · rw [if_pos hc, if_pos]
          intro h
          exact hc (Option.map_injective Sum.inl_injective h)
      · rw [Finset.sum_congr rfl (g := fun _ => 1)]
        · simp
        · intro q hq
          have hq' := Finset.mem_range.mp hq
          rw [hPval_hi r (m₂ + q) hr' (by omega) (by omega), if_pos (encodedText_ne _ _ _)]
    have hsm := sum_mul_split (fun j => if t[alpha + j]? ≠ p[j]? then 1 else 0) ell m₂
    rw [Finset.sum_congr rfl inner, Finset.sum_add_distrib, Finset.sum_comm, hsm]
    simp [Nat.mul_comm]
  rw [hL, hR, hRsplit]
  push_cast [Nat.cast_sub hm]
  ring
