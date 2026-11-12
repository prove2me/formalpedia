-- Prove2me | solution 1 for GreedySuperstring.LowerBound.greedy_invariants
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:41:56.162814+00:00
-- url     : https://prove2.me/submissions/7202069e-60a3-459f-9697-42827da5f71d

import Mathlib
import Definitions.Def_GreedySuperstring_LowerBound_GreedyModel
universe invariant_u

section
set_option autoImplicit false


namespace GreedySuperstring.Dev.Inv

open GreedySuperstring.LowerBound

section
variable {α : Type*} [DecidableEq α]

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

lemma ol_ge {s t : List α} {n : ℕ} (h1 : n < s.length) (h2 : n < t.length)
    (h3 : s.drop (s.length - n) = t.take n) : n ≤ overlapLength s t := by
  unfold overlapLength
  exact Finset.le_sup (f := id)
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_min h1 h2), h3⟩)

lemma ol_le_left (s t : List α) : overlapLength s t ≤ s.length := by
  rcases ol_cases s t with h | h <;> omega

lemma ol_le_right (s t : List α) : overlapLength s t ≤ t.length := by
  rcases ol_cases s t with h | h <;> omega

lemma ol_spec (s t : List α) :
    s.drop (s.length - overlapLength s t) = t.take (overlapLength s t) := by
  rcases ol_cases s t with h | h
  · rw [h]; simp
  · exact h.2.2

lemma length_overlap (s t : List α) : (overlap s t).length = overlapLength s t := by
  unfold overlap
  rw [List.length_take]
  have := ol_le_right s t
  omega

lemma ol_eq_of_overlap_eq {s t s' t' : List α} (h : overlap s t = overlap s' t') :
    overlapLength s t = overlapLength s' t' := by
  rw [← length_overlap s t, ← length_overlap s' t', h]

lemma drop_suffix_eq {Q M : List α} (h : Q <:+ M) {n : ℕ} (hn : n ≤ Q.length) :
    M.drop (M.length - n) = Q.drop (Q.length - n) := by
  obtain ⟨X, rfl⟩ := h
  have : (X ++ Q).length - n = X.length + (Q.length - n) := by
    simp only [List.length_append]; omega
  rw [this, List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
    Nat.add_sub_cancel_left]

lemma take_of_prefix {P M : List α} (h : P <+: M) {n : ℕ} (hn : n ≤ P.length) :
    M.take n = P.take n := by
  obtain ⟨Y, rfl⟩ := h
  rw [List.take_append, Nat.sub_eq_zero_of_le hn, List.take_zero, List.append_nil]

lemma suffix_drop_of_le {a P : List α} (ha : a <:+ P) {k : ℕ} (hk : a.length ≤ k) :
    a <:+ P.drop (P.length - k) := by
  obtain ⟨X, rfl⟩ := ha
  have hk' : (X ++ a).length - k ≤ X.length := by
    simp only [List.length_append]; omega
  rw [List.drop_append_of_le_length hk']
  exact List.suffix_append _ _

lemma ol_suffix_eq {Q M c : List α} (h : Q <:+ M) (hc : ¬ Q <:+: c) :
    overlapLength M c = overlapLength Q c := by
  unfold overlapLength
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
  have hlen := h.length_le
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hQ : n < Q.length := by
      by_contra hn
      push Not at hn
      apply hc
      have : Q <:+ M.drop (M.length - n) := suffix_drop_of_le h hn
      rw [h3] at this
      exact (this.isInfix).trans ((List.take_prefix n c).isInfix)
    refine ⟨⟨hQ, h2⟩, ?_⟩
    rw [← drop_suffix_eq h hQ.le]; exact h3
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨by omega, h2⟩, ?_⟩
    rw [drop_suffix_eq h h1.le]; exact h3

lemma ol_prefix_eq {P M c : List α} (h : P <+: M) (hc : ¬ P <:+: c) :
    overlapLength c M = overlapLength c P := by
  unfold overlapLength
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
  have hlen := h.length_le
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hP : n < P.length := by
      by_contra hn
      push Not at hn
      apply hc
      have : P <+: M.take n := by
        obtain ⟨Y, rfl⟩ := h
        rw [List.take_append, List.take_of_length_le hn]
        exact List.prefix_append _ _
      rw [← h3] at this
      exact (this.isInfix).trans ((List.drop_suffix _ _).isInfix)
    refine ⟨⟨h1, hP⟩, ?_⟩
    rw [← take_of_prefix h hP.le]; exact h3
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, by omega⟩, ?_⟩
    rw [take_of_prefix h h2.le]; exact h3

lemma infix_append_split {c X Y : List α} (h : c <:+: X ++ Y) :
    c <:+: X ∨ c <:+: Y ∨ ∃ a' c', c = a' ++ c' ∧ a' <:+ X ∧ c' <+: Y := by
  obtain ⟨s, t, h⟩ := h
  have h' : s ++ (c ++ t) = X ++ Y := by simpa [List.append_assoc] using h
  rcases List.append_eq_append_iff.mp h' with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
  · rcases List.append_eq_append_iff.mp h2 with ⟨e, h3, h4⟩ | ⟨c', h3, h4⟩
    · left
      exact ⟨s, e, by rw [h1, h3]; simp⟩
    · right; right
      exact ⟨a', c', h3, ⟨s, h1.symm⟩, ⟨t, h4.symm⟩⟩
  · right; left
    exact ⟨c', t, by rw [h2]; simp⟩

lemma chain_prefix (ts : List (List α)) : ∀ y : List α, y <+: chainMerge (y :: ts) := by
  induction ts with
  | nil => intro y; simp [chainMerge]
  | cons v ts ih =>
    intro y
    have h1 := ol_spec y v
    have h2 : y = pref y v ++ v.take (overlapLength y v) := by
      unfold pref; rw [← h1]; exact (List.take_append_drop _ _).symm
    have h3 : chainMerge (y :: v :: ts) = pref y v ++ chainMerge (v :: ts) := by
      simp [chainMerge]
    rw [h3]
    conv_lhs => rw [h2]
    exact (List.prefix_append_right_inj _).mpr ((List.take_prefix _ _).trans (ih v))

lemma prefix_append_drop {u C : List α} (h : u <+: C) : u ++ C.drop u.length = C := by
  rw [List.prefix_iff_eq_take] at h
  calc u ++ C.drop u.length = C.take u.length ++ C.drop u.length := by rw [← h]
    _ = C := List.take_append_drop _ _

lemma chain_append (L : List (List α)) (x y : List α) (ts : List (List α)) :
    chainMerge (L ++ [x] ++ y :: ts)
      = chainMerge (L ++ [x]) ++ (chainMerge (y :: ts)).drop (overlapLength x y) := by
  induction L with
  | nil =>
    have h1 := ol_spec x y
    have h2 : x = pref x y ++ y.take (overlapLength x y) := by
      unfold pref; rw [← h1]; exact (List.take_append_drop _ _).symm
    have h3 : y.take (overlapLength x y) <+: chainMerge (y :: ts) :=
      (List.take_prefix _ _).trans (chain_prefix ts y)
    have h4 := prefix_append_drop h3
    have hl : (y.take (overlapLength x y)).length = overlapLength x y := by
      rw [List.length_take]; have := ol_le_right x y; omega
    rw [hl] at h4
    have h5 : chainMerge (x :: y :: ts) = pref x y ++ chainMerge (y :: ts) := by
      simp [chainMerge]
    have h6 : x ++ (chainMerge (y :: ts)).drop (overlapLength x y)
        = pref x y ++ chainMerge (y :: ts) := by
      calc x ++ (chainMerge (y :: ts)).drop (overlapLength x y)
          = (pref x y ++ y.take (overlapLength x y)) ++
              (chainMerge (y :: ts)).drop (overlapLength x y) := by rw [← h2]
        _ = pref x y ++ (y.take (overlapLength x y) ++
              (chainMerge (y :: ts)).drop (overlapLength x y)) := by simp
        _ = pref x y ++ chainMerge (y :: ts) := by rw [h4]
    simp only [List.nil_append, List.singleton_append, chainMerge]
    simpa [chainMerge] using h5.trans h6.symm
  | cons u L ih =>
    cases L with
    | nil =>
      simp only [List.cons_append, List.nil_append, chainMerge] at ih ⊢
      rw [ih]
      simp [chainMerge]
    | cons v L' =>
      simp only [List.cons_append, chainMerge] at ih ⊢
      rw [ih]
      simp

lemma chain_merge_append (L : List (List α)) (x y : List α) (ts : List (List α))
    (h : overlapLength (chainMerge (L ++ [x])) (chainMerge (y :: ts)) = overlapLength x y) :
    chainMerge (L ++ [x] ++ y :: ts)
      = merge (chainMerge (L ++ [x])) (chainMerge (y :: ts)) := by
  rw [chain_append]; unfold merge; rw [h]

def Inv (F : Finset (Block α)) : Prop :=
  (∀ a ∈ F, ∀ b ∈ F, a ≠ b → ¬ a.word <:+: b.word) ∧
  (∀ a ∈ F, a.history ≠ [] ∧ a.word = chainMerge a.history) ∧
  (∀ a ∈ F, ∀ b ∈ F, a ≠ b → ∀ x y : List α,
      a.history.getLast? = some x → b.history.head? = some y →
      overlap a.word b.word = overlap x y)

lemma suffix_merge (P Q : List α) : Q <:+ merge P Q := by
  refine ⟨P.take (P.length - overlapLength P Q), ?_⟩
  have h1 := ol_spec P Q
  unfold merge
  calc P.take (P.length - overlapLength P Q) ++ Q
      = P.take (P.length - overlapLength P Q) ++
          (Q.take (overlapLength P Q) ++ Q.drop (overlapLength P Q)) := by
        rw [List.take_append_drop]
    _ = (P.take (P.length - overlapLength P Q) ++ P.drop (P.length - overlapLength P Q)) ++
          Q.drop (overlapLength P Q) := by rw [← h1, List.append_assoc]
    _ = P ++ Q.drop (overlapLength P Q) := by rw [List.take_append_drop]

lemma prefix_merge (P Q : List α) : P <+: merge P Q := List.prefix_append _ _

lemma key1 {B : Finset (Block α)}
    (hA : ∀ a ∈ B, ∀ b ∈ B, a ≠ b → ¬ a.word <:+: b.word) {p q c : Block α}
    (hp : p ∈ B) (hq : q ∈ B) (hc : c ∈ B) (hcp : c ≠ p) (hcq : c ≠ q)
    (hmax : ∀ c ∈ B, ∀ d ∈ B, c.word ≠ d.word →
      overlapLength c.word d.word ≤ overlapLength p.word q.word) :
    ¬ c.word <:+: merge p.word q.word := by
  intro hin
  have hcP : ¬ c.word <:+: p.word := hA c hc p hp hcp
  have hcQ : ¬ c.word <:+: q.word := hA c hc q hq hcq
  have hPc : ¬ p.word <:+: c.word := hA p hp c hc (Ne.symm hcp)
  have hne : p.word ≠ c.word := fun h => hPc (h ▸ List.infix_refl _)
  have hle := hmax p hp c hc hne
  have hdrop : q.word.drop (overlapLength p.word q.word) <:+ q.word := List.drop_suffix _ _
  unfold merge at hin
  rcases infix_append_split hin with h | h | ⟨a', c', hceq, ha, hc'⟩
  · exact hcP h
  · exact hcQ (h.trans hdrop.isInfix)
  · by_cases ha0 : a' = []
    · apply hcQ
      rw [hceq, ha0, List.nil_append]
      exact hc'.isInfix.trans hdrop.isInfix
    by_cases hc0 : c' = []
    · apply hcP
      rw [hceq, hc0, List.append_nil]
      exact ha.isInfix
    by_cases hn : a'.length ≤ overlapLength p.word q.word
    · have hs := ol_spec p.word q.word
      have hsuf : a' <:+ q.word.take (overlapLength p.word q.word) := by
        rw [← hs]; exact suffix_drop_of_le ha hn
      obtain ⟨e, he⟩ := hsuf
      obtain ⟨f, hf⟩ := hc'
      apply hcQ
      rw [hceq]
      refine ⟨e, f, ?_⟩
      calc e ++ (a' ++ c') ++ f = (e ++ a') ++ (c' ++ f) := by simp
        _ = q.word.take (overlapLength p.word q.word) ++
              q.word.drop (overlapLength p.word q.word) := by rw [he, hf]
        _ = q.word := List.take_append_drop _ _
    · push Not at hn
      obtain ⟨X, hX⟩ := ha
      have hlt : a'.length < p.word.length := by
        by_contra hge
        push Not at hge
        have hX0 : X.length = 0 := by
          have := congrArg List.length hX
          simp only [List.length_append] at this
          omega
        have hX1 : X = [] := List.length_eq_zero_iff.mp hX0
        rw [hX1, List.nil_append] at hX
        apply hPc
        rw [hceq, hX]
        exact (List.prefix_append _ _).isInfix
      have hltc : a'.length < c.word.length := by
        rw [hceq, List.length_append]
        have := List.length_pos_iff.mpr hc0
        omega
      have hd : p.word.drop (p.word.length - a'.length) = c.word.take a'.length := by
        have := drop_suffix_eq (M := p.word) (Q := a') ⟨X, hX⟩ le_rfl
        rw [this, hceq, List.take_left]
        simp
      have := ol_ge hlt hltc hd
      omega

lemma step_inv {B B' : Finset (Block α)} {l : ℕ} (hB : Inv B) (hs : GreedyStep B l B') :
    Inv B' ∧ ∀ c ∈ B', ∀ d ∈ B', c.word ≠ d.word → overlapLength c.word d.word ≤ l := by
  obtain ⟨hA, hBB, hC⟩ := hB
  obtain ⟨a, ha, b, hb, hne, hmax, hl, hB'⟩ := hs
  have memB' : ∀ c, c ∈ B' ↔ c = mergeBlocks a b ∨ (c ∈ B ∧ c ≠ a ∧ c ≠ b) := by
    intro c
    subst hB'
    simp only [Finset.mem_insert, Finset.mem_erase]
    tauto
  have hab : a ≠ b := fun h => hne (h ▸ rfl)
  have hm : (mergeBlocks a b).word = merge a.word b.word := rfl
  have nw : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → x.word ≠ y.word :=
    fun x hx y hy h e => hA x hx y hy h (e ▸ List.infix_refl _)
  have hbne := (hBB b hb).1
  have hane := (hBB a ha).1
  -- facts about a third block
  have k1 : ∀ c ∈ B, c ≠ a → c ≠ b → ¬ c.word <:+: (mergeBlocks a b).word := by
    intro c hc hca hcb
    rw [hm]
    exact key1 hA ha hb hc hca hcb hmax
  have k2 : ∀ c ∈ B, c ≠ a → c ≠ b → ¬ (mergeBlocks a b).word <:+: c.word := by
    intro c hc hca hcb h
    exact hA a ha c hc (Ne.symm hca) ((prefix_merge _ _).isInfix.trans h)
  have k3 : ∀ c ∈ B, c ≠ a → c ≠ b →
      overlapLength (mergeBlocks a b).word c.word = overlapLength b.word c.word := by
    intro c hc hca hcb
    rw [hm]
    exact ol_suffix_eq (suffix_merge _ _) (hA b hb c hc (Ne.symm hcb))
  have k4 : ∀ c ∈ B, c ≠ a → c ≠ b →
      overlapLength c.word (mergeBlocks a b).word = overlapLength c.word a.word := by
    intro c hc hca hcb
    rw [hm]
    exact ol_prefix_eq (prefix_merge _ _) (hA a ha c hc (Ne.symm hca))
  have hhist : (mergeBlocks a b).history = a.history ++ b.history := rfl
  have hmerge : (mergeBlocks a b).word = chainMerge (mergeBlocks a b).history := by
    obtain ⟨hne1, hw1⟩ := hBB a ha
    obtain ⟨hne2, hw2⟩ := hBB b hb
    rcases List.eq_nil_or_concat a.history with h | ⟨L, x, hL⟩
    · exact absurd h hne1
    rw [List.concat_eq_append] at hL
    cases hy : b.history with
    | nil => exact absurd hy hne2
    | cons y ts =>
      have hov := ol_eq_of_overlap_eq
        (hC a ha b hb hab x y (by simp [hL]) (by simp [hy]))
      rw [hL] at hw1
      rw [hy] at hw2
      rw [hm, hhist, hL, hy,
        chain_merge_append L x y ts (by rw [← hw1, ← hw2]; exact hov), ← hw1, ← hw2]
  have hlast : ∀ x, (mergeBlocks a b).history.getLast? = some x → b.history.getLast? = some x := by
    intro x hx
    rw [hhist, List.getLast?_append_of_ne_nil _ hbne] at hx
    exact hx
  have hhead : ∀ y, (mergeBlocks a b).history.head? = some y → a.history.head? = some y := by
    intro y hy
    rw [hhist, List.head?_append_of_ne_nil _ hane] at hy
    exact hy
  have hbound : ∀ c ∈ B', ∀ d ∈ B', c.word ≠ d.word → overlapLength c.word d.word ≤ l := by
    intro c hc d hd hcd
    rw [hl]
    rcases (memB' c).mp hc with rfl | ⟨hcB, hca, hcb⟩ <;>
      rcases (memB' d).mp hd with rfl | ⟨hdB, hda, hdb⟩
    · exact absurd rfl hcd
    · rw [k3 d hdB hda hdb]
      exact hmax b hb d hdB (nw b hb d hdB (Ne.symm hdb))
    · rw [k4 c hcB hca hcb]
      exact hmax c hcB a ha (nw c hcB a ha hca)
    · exact hmax c hcB d hdB hcd
  refine ⟨⟨?_, ?_, ?_⟩, hbound⟩
  · intro c hc d hd hcd
    rcases (memB' c).mp hc with rfl | ⟨hcB, hca, hcb⟩ <;>
      rcases (memB' d).mp hd with rfl | ⟨hdB, hda, hdb⟩
    · exact absurd rfl hcd
    · exact k2 d hdB hda hdb
    · exact k1 c hcB hca hcb
    · exact hA c hcB d hdB hcd
  · intro c hc
    rcases (memB' c).mp hc with rfl | ⟨hcB, hca, hcb⟩
    · refine ⟨?_, hmerge⟩
      rw [hhist]
      intro h
      exact hane (List.append_eq_nil_iff.mp h).1
    · exact hBB c hcB
  · intro c hc d hd hcd x y hx hy
    rcases (memB' c).mp hc with rfl | ⟨hcB, hca, hcb⟩ <;>
      rcases (memB' d).mp hd with rfl | ⟨hdB, hda, hdb⟩
    · exact absurd rfl hcd
    · have := hC b hb d hdB (Ne.symm hdb) x y (hlast x hx) hy
      unfold overlap at this ⊢
      rw [k3 d hdB hda hdb]
      exact this
    · have := hC c hcB a ha hca x y hx (hhead y hy)
      unfold overlap at this ⊢
      rw [k4 c hcB hca hcb, hm]
      rw [hm] at *
      have hp : a.word <+: merge a.word b.word := prefix_merge _ _
      rw [take_of_prefix hp (ol_le_right _ _ |>.trans' le_rfl)]
      exact this
    · exact hC c hcB d hdB hcd x y hx hy

end

lemma init_inv {α : Type*} [DecidableEq α] (S : Finset (List α)) (hsf : SubstringFree S) :
    Inv (initialBlocks S) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [initialBlocks, Finset.mem_image] at ha hb
    obtain ⟨s, hs, rfl⟩ := ha
    obtain ⟨t, ht, rfl⟩ := hb
    exact hsf s hs t ht (fun h => hab (by rw [h]))
  · intro a ha
    simp only [initialBlocks, Finset.mem_image] at ha
    obtain ⟨s, hs, rfl⟩ := ha
    simp [chainMerge]
  · intro a ha b hb hab x y hx hy
    simp only [initialBlocks, Finset.mem_image] at ha hb
    obtain ⟨s, hs, rfl⟩ := ha
    obtain ⟨t, ht, rfl⟩ := hb
    simp at hx hy
    subst hx; subst hy
    rfl

lemma run_main {α : Type*} [DecidableEq α] {B F : Finset (Block α)} {ls : List ℕ}
    (hrun : GreedyRun B ls F) (hB : Inv B) (K : ℕ)
    (hK : ∀ c ∈ B, ∀ d ∈ B, c.word ≠ d.word → overlapLength c.word d.word ≤ K) :
    Inv F ∧ ls.Pairwise (fun x y => y ≤ x) ∧ ∀ l ∈ ls, l ≤ K := by
  induction hrun generalizing K with
  | nil B => exact ⟨hB, List.Pairwise.nil, by simp⟩
  | @cons B B' B'' l ls hs hr ih =>
    obtain ⟨hB', hbd⟩ := step_inv hB hs
    have hlK : l ≤ K := by
      obtain ⟨a, ha, b, hb, hne, hmax, hl, _⟩ := hs
      rw [hl]; exact hK a ha b hb hne
    obtain ⟨h1, h2, h3⟩ := ih hB' l hbd
    refine ⟨h1, ?_, ?_⟩
    · exact List.pairwise_cons.mpr ⟨h3, h2⟩
    · intro l' hl'
      rcases List.mem_cons.mp hl' with rfl | h
      · exact hlK
      · exact (h3 l' h).trans hlK

end GreedySuperstring.Dev.Inv

namespace GreedySuperstring.LowerBound

/-- Lemma 2.1, printed/PDF p.7. Runs may be any finite prefix, including
zero steps. Histories only record the original words in concatenation order. -/
theorem chk_greedy_invariants {α : Type invariant_u} [DecidableEq α]
    (S : Finset (List α)) (hne : ∀ s ∈ S, s ≠ []) (hsf : SubstringFree S)
    (ls : List ℕ) (F : Finset (Block α)) (hrun : GreedyRun (initialBlocks S) ls F) :
    (∀ a ∈ F, ∀ b ∈ F, a ≠ b → ¬ a.word <:+: b.word) ∧
    (∀ a ∈ F, a.history ≠ [] ∧ a.word = chainMerge a.history) ∧
    (∀ a ∈ F, ∀ b ∈ F, a ≠ b → ∀ x y : List α,
      a.history.getLast? = some x → b.history.head? = some y →
      overlap a.word b.word = overlap x y) ∧
    ls.Pairwise (fun x y => y ≤ x) := by
  have := GreedySuperstring.Dev.Inv.run_main hrun (GreedySuperstring.Dev.Inv.init_inv S hsf)
    ((initialBlocks S).sup (fun c => c.word.length))
    (fun c hc d hd _ => (GreedySuperstring.Dev.Inv.ol_le_left _ _).trans
      (Finset.le_sup (f := fun c : Block α => c.word.length) hc))
  obtain ⟨⟨h1, h2, h3⟩, h4, _⟩ := this
  exact ⟨h1, h2, h3, h4⟩

end GreedySuperstring.LowerBound
end

theorem solution : type_of% @GreedySuperstring.LowerBound.chk_greedy_invariants := @GreedySuperstring.LowerBound.chk_greedy_invariants
