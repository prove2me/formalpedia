-- Prove2me | solution 1 for LodhaMoore.exists_advances_append_replicate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T11:34:29.22979+00:00
-- url     : https://prove2.me/submissions/c1ba5fa7-db44-4dee-9f74-edfffdee8d56

import Mathlib
import Definitions.Def_LodhaMooreWords
import Definitions.Def_LodhaMoore
import Theorems.Thm_LodhaMoore_noPotentialCancellation_of_advanceAt
section
namespace LodhaMoore

end LodhaMoore
end

section
namespace LodhaMoore

end LodhaMoore
end

section
/-!
# Lodha–Moore §5, Lemmas 5.6, 5.9, 5.10 and 5.11 (group S5)

Y. Lodha and J. T. Moore, arXiv:1308.4250v3, pp. 11–14. Helpers live in `LodhaMoore.Dev.S5`;
the targets are `LodhaMoore.chk_<name>` at the end.

* Lemma 5.6: expanding a non-exposed `y_s^n` (`step56`) keeps the prefix closure of the indices
  from growing and lowers the profile of `|exponents|` by depth lexicographically (`main56`).
* Lemma 5.9: potential cancellations are computed by `pcf`; advancing one occurrence cannot create
  one at the preceding occurrence (`key59`).
* Lemma 5.10: induction on the word, advancing the first occurrence as far as possible (`maxadv`)
  and padding with `0^{2^N}` (`rep_adv`).
* Lemma 5.11: `B`-words act on sequences (`Sem`, invariant under advancing); the path of the
  proof gives a `B`-word without potential cancellations (`claim511`); Lemma 5.10 turns it into
  `v yᴺ`, and `yᴺ` maps `(0^{2^N}1)^∞` to `(01^{2^N})^∞`, which is not tail equivalent, while every
  `X`-word preserves tail equivalence.
-/

namespace LodhaMoore.Dev.S5
open LodhaMoore

/-! ### Orders on `Y`-letters -/

/-- The `y`-part of a profile: the sum of `|exponent|` over the letters `y_t` with `|t| = d`. -/
def rawProf (W : Word) (d : ℕ) : ℕ :=
  (W.map fun p => match p.1 with | .y t => if t.length = d then p.2.natAbs else 0 | .x _ => 0).sum

@[simp] theorem rawProf_nil (d : ℕ) : rawProf [] d = 0 := rfl

/-! ### Moving letters -/


/-! ### Standard forms as `X`-word plus strictly ordered `Y`-word -/

/-! ### Prefix closures -/

/-! ### The action of `x_s^{±1}` on indices -/

/-! ### The inverse of the tail action, for the prefix closures -/

/-! ### The new letters -/


/-! ### Potential cancellations, computed -/

/-- The occurrence `y` (`true`) or `y⁻¹` (`false`). -/
def occ : Bool → BLetter
  | true => .y
  | false => .yinv

/-- Whether an occurrence `occ σ` followed by `w` is a potential cancellation: advance it as long as
possible and test whether its inverse follows. -/
def pcf : Bool → BWord → Bool
  | true, .zero :: .zero :: w => pcf true w
  | true, .zero :: .one :: w => pcf false w
  | true, .one :: w => pcf true w
  | true, .yinv :: _ => true
  | false, .zero :: w => pcf false w
  | false, .one :: .zero :: w => pcf true w
  | false, .one :: .one :: w => pcf false w
  | false, .y :: _ => true
  | _, _ => false

@[simp] theorem pcf_t00 (w : BWord) : pcf true (.zero :: .zero :: w) = pcf true w := rfl
@[simp] theorem pcf_t01 (w : BWord) : pcf true (.zero :: .one :: w) = pcf false w := rfl
@[simp] theorem pcf_t1 (w : BWord) : pcf true (.one :: w) = pcf true w := rfl
@[simp] theorem pcf_tyinv (w : BWord) : pcf true (.yinv :: w) = true := rfl
@[simp] theorem pcf_ty (w : BWord) : pcf true (.y :: w) = false := rfl
@[simp] theorem pcf_t0y (w : BWord) : pcf true (.zero :: .y :: w) = false := rfl
@[simp] theorem pcf_t0yinv (w : BWord) : pcf true (.zero :: .yinv :: w) = false := rfl
@[simp] theorem pcf_tnil : pcf true [] = false := rfl
@[simp] theorem pcf_t0nil : pcf true [.zero] = false := rfl
@[simp] theorem pcf_f0 (w : BWord) : pcf false (.zero :: w) = pcf false w := rfl
@[simp] theorem pcf_f10 (w : BWord) : pcf false (.one :: .zero :: w) = pcf true w := rfl
@[simp] theorem pcf_f11 (w : BWord) : pcf false (.one :: .one :: w) = pcf false w := rfl
@[simp] theorem pcf_fy (w : BWord) : pcf false (.y :: w) = true := rfl
@[simp] theorem pcf_fyinv (w : BWord) : pcf false (.yinv :: w) = false := rfl
@[simp] theorem pcf_f1y (w : BWord) : pcf false (.one :: .y :: w) = false := rfl
@[simp] theorem pcf_f1yinv (w : BWord) : pcf false (.one :: .yinv :: w) = false := rfl
@[simp] theorem pcf_fnil : pcf false [] = false := rfl
@[simp] theorem pcf_f1nil : pcf false [.one] = false := rfl

@[simp] theorem occ_true : occ true = .y := rfl
@[simp] theorem occ_false : occ false = .yinv := rfl

/-- A digit letter. -/
def IsDig (b : BLetter) : Prop := b = .zero ∨ b = .one

theorem occ_not_dig (σ : Bool) : ¬ IsDig (occ σ) := by cases σ <;> simp [occ, IsDig]

/-- `pcf` of an all-digit word is `false`. -/
theorem pcf_digits : ∀ (σ : Bool) (w : BWord), (∀ b ∈ w, IsDig b) → pcf σ w = false
  | true, .zero :: .zero :: w, h => pcf_digits true w (fun b hb => h b (by simp [hb]))
  | true, .zero :: .one :: w, h => pcf_digits false w (fun b hb => h b (by simp [hb]))
  | true, .one :: w, h => pcf_digits true w (fun b hb => h b (by simp [hb]))
  | false, .zero :: w, h => pcf_digits false w (fun b hb => h b (by simp [hb]))
  | false, .one :: .zero :: w, h => pcf_digits true w (fun b hb => h b (by simp [hb]))
  | false, .one :: .one :: w, h => pcf_digits false w (fun b hb => h b (by simp [hb]))
  | true, [], _ => rfl
  | false, [], _ => rfl
  | true, [.zero], _ => rfl
  | false, [.one], _ => rfl
  | true, .zero :: .y :: _, h => rfl
  | true, .zero :: .yinv :: _, h => rfl
  | false, .one :: .y :: _, h => rfl
  | false, .one :: .yinv :: _, h => rfl
  | true, .y :: _, h => rfl
  | false, .yinv :: _, h => rfl
  | true, .yinv :: _, h => absurd (h .yinv List.mem_cons_self) (by simp [IsDig])
  | false, .y :: _, h => absurd (h .y List.mem_cons_self) (by simp [IsDig])

theorem occ_inj {a b : Bool} (h : occ a = occ b) : a = b := by
  cases a <;> cases b <;> simp_all [occ]

/-- The six advancing substitutions: `occ σ` followed by `c` becomes `o` followed by `occ σ'`. -/
inductive Rule : Bool → BWord → BWord → Bool → Prop
  | y00 : Rule true [.zero, .zero] [.zero] true
  | y01 : Rule true [.zero, .one] [.one, .zero] false
  | y1 : Rule true [.one] [.one, .one] true
  | yinv0 : Rule false [.zero] [.zero, .zero] false
  | yinv10 : Rule false [.one, .zero] [.zero, .one] true
  | yinv11 : Rule false [.one, .one] [.one] false

theorem Rule.pcf_eq {σ σ' : Bool} {c o : BWord} (h : Rule σ c o σ') (X : BWord) :
    pcf σ (c ++ X) = pcf σ' X := by
  cases h <;> rfl

theorem Rule.c_ne {σ σ' : Bool} {c o : BWord} (h : Rule σ c o σ') : c ≠ [] := by
  cases h <;> simp

theorem advanceAt_cases {L M : BWord} {i j : ℕ} (h : AdvanceAt (L, i) (M, j)) :
    ∃ pre σ c o σ' post, Rule σ c o σ' ∧ L = pre ++ occ σ :: (c ++ post) ∧
      M = pre ++ o ++ occ σ' :: post ∧ i = pre.length ∧ j = pre.length + o.length := by
  cases h with
  | y00 pre post => exact ⟨pre, true, _, _, true, post, Rule.y00, by simp [occ], by simp [occ], rfl, rfl⟩
  | y01 pre post => exact ⟨pre, true, _, _, false, post, Rule.y01, by simp [occ], by simp [occ], rfl, rfl⟩
  | y1 pre post => exact ⟨pre, true, _, _, true, post, Rule.y1, by simp [occ], by simp [occ], rfl, rfl⟩
  | yinv0 pre post =>
    exact ⟨pre, false, _, _, false, post, Rule.yinv0, by simp [occ], by simp [occ], rfl, rfl⟩
  | yinv10 pre post =>
    exact ⟨pre, false, _, _, true, post, Rule.yinv10, by simp [occ], by simp [occ], rfl, rfl⟩
  | yinv11 pre post =>
    exact ⟨pre, false, _, _, false, post, Rule.yinv11, by simp [occ], by simp [occ], rfl, rfl⟩

theorem Rule.advanceAt {σ σ' : Bool} {c o : BWord} (h : Rule σ c o σ') (pre post : BWord) :
    AdvanceAt (pre ++ occ σ :: (c ++ post), pre.length) (pre ++ o ++ occ σ' :: post, pre.length + o.length) := by
  cases h
  · simpa [occ] using AdvanceAt.y00 pre post
  · simpa [occ] using AdvanceAt.y01 pre post
  · simpa [occ] using AdvanceAt.y1 pre post
  · simpa [occ] using AdvanceAt.yinv0 pre post
  · simpa [occ] using AdvanceAt.yinv10 pre post
  · simpa [occ] using AdvanceAt.yinv11 pre post

theorem pcf_true_cases {σ : Bool} {w : BWord} (h : pcf σ w = true) :
    (∃ c o σ' w₀, Rule σ c o σ' ∧ w = c ++ w₀ ∧ pcf σ' w₀ = true) ∨ ∃ w₀, w = occ (!σ) :: w₀ := by
  match σ, w, h with
  | true, .zero :: .zero :: w, h => exact Or.inl ⟨_, _, _, w, Rule.y00, rfl, h⟩
  | true, .zero :: .one :: w, h => exact Or.inl ⟨_, _, _, w, Rule.y01, rfl, h⟩
  | true, .one :: w, h => exact Or.inl ⟨_, _, _, w, Rule.y1, rfl, h⟩
  | true, .yinv :: w, _ => exact Or.inr ⟨w, rfl⟩
  | false, .zero :: w, h => exact Or.inl ⟨_, _, _, w, Rule.yinv0, rfl, h⟩
  | false, .one :: .zero :: w, h => exact Or.inl ⟨_, _, _, w, Rule.yinv10, rfl, h⟩
  | false, .one :: .one :: w, h => exact Or.inl ⟨_, _, _, w, Rule.yinv11, rfl, h⟩
  | false, .y :: w, _ => exact Or.inr ⟨w, rfl⟩
  | true, [], h => simp [pcf] at h
  | false, [], h => simp [pcf] at h
  | true, [.zero], h => simp [pcf] at h
  | false, [.one], h => simp [pcf] at h
  | true, .zero :: .y :: _, h => simp [pcf] at h
  | true, .zero :: .yinv :: _, h => simp [pcf] at h
  | false, .one :: .y :: _, h => simp [pcf] at h
  | false, .one :: .yinv :: _, h => simp [pcf] at h
  | true, .y :: _, h => simp [pcf] at h
  | false, .yinv :: _, h => simp [pcf] at h

theorem drop_eq_cons_cons {L : BWord} {j : ℕ} {a b : BLetter} (ha : L[j]? = some a)
    (hb : L[j + 1]? = some b) : ∃ w, L.drop j = a :: b :: w := by
  refine ⟨L.drop (j + 2), ?_⟩
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 ha
  obtain ⟨hj1, rfl⟩ := List.getElem?_eq_some_iff.1 hb
  rw [List.drop_eq_getElem_cons hj, List.drop_eq_getElem_cons hj1]

theorem drop_len_add {α : Type*} (pre R : List α) (k : ℕ) : (pre ++ R).drop (pre.length + k) = R.drop k := by
  simp

theorem pc_of_pcf : ∀ (n : ℕ) (L : BWord) (i : ℕ) (σ : Bool) (w : BWord), w.length ≤ n →
    L.drop i = occ σ :: w → pcf σ w = true → PotentialCancellation L i := by
  intro n
  induction n with
  | zero =>
    intro L i σ w hn hw hp
    have : w = [] := List.length_eq_zero_iff.1 (by omega)
    subst this
    cases σ <;> simp [pcf] at hp
  | succ n ih =>
    intro L i σ w hn hw hp
    have hi : i < L.length := by
      by_contra h
      push Not at h
      rw [List.drop_eq_nil_of_le h] at hw
      simp at hw
    rcases pcf_true_cases hp with ⟨c, o, σ', w₀, hr, rfl, hp₀⟩ | ⟨w₀, rfl⟩
    · have hL : L = L.take i ++ occ σ :: (c ++ w₀) := by rw [← hw, List.take_append_drop]
      have hlen : (L.take i).length = i := by simp; omega
      have hadv := hr.advanceAt (L.take i) w₀
      rw [← hL, hlen] at hadv
      have hc : 0 < c.length := List.length_pos_iff.2 hr.c_ne
      have hlen0 : w₀.length ≤ n := by simp at hn; omega
      obtain ⟨L', j, hrt, hcond⟩ := ih (L.take i ++ o ++ occ σ' :: w₀) (i + o.length) σ' w₀ hlen0
        (by
          have h := drop_len_add (L.take i) (o ++ occ σ' :: w₀) o.length
          rw [hlen, List.drop_left] at h
          simpa [List.append_assoc] using h) hp₀
      exact ⟨L', j, Relation.ReflTransGen.head hadv hrt, hcond⟩
    · refine ⟨L, i, Relation.ReflTransGen.refl, ?_⟩
      have h0 : L[i]? = some (occ σ) := by
        have := congrArg (fun l => l[0]?) hw
        simpa [List.getElem?_drop] using this
      have h1 : L[i + 1]? = some (occ (!σ)) := by
        have := congrArg (fun l => l[1]?) hw
        simpa [List.getElem?_drop] using this
      cases σ
      · exact Or.inr ⟨h0, h1⟩
      · exact Or.inl ⟨h0, h1⟩

theorem pc_iff (L : BWord) (i : ℕ) :
    PotentialCancellation L i ↔ ∃ σ w, L.drop i = occ σ :: w ∧ pcf σ w = true := by
  constructor
  · rintro ⟨L', j, hr, hc⟩
    refine Relation.ReflTransGen.head_induction_on
      (motive := fun a _ => ∃ σ w, a.1.drop a.2 = occ σ :: w ∧ pcf σ w = true) hr ?_ ?_
    · rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨w, hw⟩ := drop_eq_cons_cons h1 h2
        exact ⟨true, _, hw, rfl⟩
      · obtain ⟨w, hw⟩ := drop_eq_cons_cons h1 h2
        exact ⟨false, _, hw, rfl⟩
    · rintro ⟨L₁, i₁⟩ ⟨L₂, i₂⟩ hadv - ⟨σ', w', hw', hp'⟩
      obtain ⟨pre, σ, c, o, σ'', post, hrule, rfl, rfl, rfl, rfl⟩ := advanceAt_cases hadv
      simp only [List.append_assoc] at hw'
      rw [drop_len_add, List.drop_left] at hw'
      simp only [List.cons.injEq] at hw'
      obtain ⟨h1, rfl⟩ := hw'
      have := occ_inj h1; subst this
      refine ⟨σ, c ++ post, ?_, by rw [hrule.pcf_eq]; exact hp'⟩
      show (pre ++ occ σ :: (c ++ post)).drop pre.length = _
      rw [List.drop_left]
  · rintro ⟨σ, w, hw, hp⟩
    exact pc_of_pcf w.length L i σ w le_rfl hw hp

theorem noPC_iff (L : BWord) :
    NoPotentialCancellation L ↔ ∀ σ v, (occ σ :: v) <:+ L → pcf σ v = false := by
  constructor
  · intro h σ v hs
    rw [List.suffix_iff_eq_drop] at hs
    set i := L.length - (occ σ :: v).length
    have hi : L[i]? = some (occ σ) := by
      have := congrArg (fun l => l[0]?) hs
      simp only [List.getElem?_drop, List.getElem?_cons_zero, Nat.add_zero] at this
      exact this.symm
    by_contra hp
    refine h i (by cases σ <;> simp [hi, occ]) ((pc_iff L i).2 ⟨σ, v, hs.symm, ?_⟩)
    simpa using hp
  · intro h i _ hpc
    obtain ⟨σ, w, hw, hp⟩ := (pc_iff L i).1 hpc
    have := h σ w (hw ▸ List.drop_suffix i L)
    rw [hp] at this
    exact absurd this (by decide)

theorem suffix_cases {τ : Bool} {v : BWord} : ∀ {pre R : BWord}, (occ τ :: v) <:+ pre ++ R →
    (occ τ :: v) <:+ R ∨ ∃ p, (occ τ :: p) <:+ pre ∧ v = p ++ R
  | [], R, h => Or.inl (by simpa using h)
  | a :: pre, R, h => by
    rw [List.cons_append, List.suffix_cons_iff] at h
    rcases h with h | h
    · simp only [List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨pre, List.suffix_refl _, rfl⟩
    · rcases suffix_cases h with h | ⟨p, hp, rfl⟩
      · exact Or.inl h
      · exact Or.inr ⟨p, hp.trans (List.suffix_cons a pre), rfl⟩

theorem not_suffix_dig {τ : Bool} {p o : BWord} (ho : ∀ b ∈ o, IsDig b) (h : (occ τ :: p) <:+ o) :
    False :=
  occ_not_dig τ (ho _ (h.subset List.mem_cons_self))

/-! ### Lemma 5.10 -/

theorem _root_.LodhaMoore.Advances.tr {a b c : BWord} (h1 : Advances a b) (h2 : Advances b c) :
    Advances a c := Relation.ReflTransGen.trans h1 h2

theorem _root_.LodhaMoore.Advances.rfl' {a : BWord} : Advances a a := Relation.ReflTransGen.refl

theorem pcf_single_dig (τ : Bool) (a : BLetter) (D : BWord) (hD : ∀ b ∈ D, IsDig b)
    (h : pcf τ [a] = false) : pcf τ (a :: D) = false := by
  have two : ∀ σ, (∀ d D', D = d :: D' → pcf σ D' = false ∧ pcf (!σ) D' = false) := by
    intro σ d D' hDD
    subst hDD
    exact ⟨pcf_digits _ _ (fun b hb => hD b (List.mem_cons_of_mem _ hb)),
      pcf_digits _ _ (fun b hb => hD b (List.mem_cons_of_mem _ hb))⟩
  cases τ <;> cases a
  · simp only [pcf_f0]; exact pcf_digits _ _ hD
  · rcases D with _ | ⟨d, D'⟩
    · rfl
    · rcases hD d List.mem_cons_self with rfl | rfl
      · simp only [pcf_f10]; exact (two true _ _ rfl).1
      · simp only [pcf_f11]; exact (two false _ _ rfl).1
  · simp at h
  · simp
  · rcases D with _ | ⟨d, D'⟩
    · rfl
    · rcases hD d List.mem_cons_self with rfl | rfl
      · simp only [pcf_t00]; exact (two true _ _ rfl).1
      · simp only [pcf_t01]; exact (two false _ _ rfl).1
  · simp only [pcf_t1]; exact pcf_digits _ _ hD
  · simp
  · simp at h

/-- A finite binary sequence as a `B`-word. -/
def dg (u : Seq) : BWord := u.map fun d => if d then BLetter.one else .zero

theorem dg_dig (u : Seq) : ∀ b ∈ dg u, IsDig b := by
  intro b hb
  simp only [dg, List.mem_map] at hb
  obtain ⟨d, -, rfl⟩ := hb
  cases d <;> simp [IsDig]

@[simp] theorem dg_nil : dg [] = [] := rfl
@[simp] theorem dg_cons (d : Bool) (u : Seq) :
    dg (d :: u) = (if d then BLetter.one else .zero) :: dg u := rfl
@[simp] theorem dg_append (u v : Seq) : dg (u ++ v) = dg u ++ dg v := by simp [dg]
theorem dg_replicate_false (k : ℕ) : dg (List.replicate k false) = List.replicate k .zero := by
  simp [dg, List.map_replicate]

theorem advanceAt_context {L M : BWord} {i j : ℕ} (h : AdvanceAt (L, i) (M, j)) (P Q : BWord) :
    AdvanceAt (P ++ L ++ Q, P.length + i) (P ++ M ++ Q, P.length + j) := by
  obtain ⟨pre, σ, c, o, σ', post, hr, rfl, rfl, rfl, rfl⟩ := advanceAt_cases h
  have := hr.advanceAt (P ++ pre) (post ++ Q)
  simpa [List.append_assoc, Nat.add_assoc] using this

theorem advances_context {A B : BWord} (h : Advances A B) (P Q : BWord) :
    Advances (P ++ A ++ Q) (P ++ B ++ Q) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    obtain ⟨i, j, hij⟩ := hs
    exact ih.tail ⟨_, _, advanceAt_context hij P Q⟩

theorem Rule.advances {σ σ' : Bool} {c o : BWord} (h : Rule σ c o σ') (pre post : BWord) :
    Advances (pre ++ occ σ :: (c ++ post)) (pre ++ o ++ occ σ' :: post) :=
  Relation.ReflTransGen.single ⟨_, _, h.advanceAt pre post⟩

theorem noPC_suffix {L R : BWord} (h : NoPotentialCancellation L) (hs : R <:+ L) :
    NoPotentialCancellation R := by
  rw [noPC_iff] at h ⊢
  exact fun σ v hv => h σ v (hv.trans hs)

theorem pcf_append_dig : ∀ (n : ℕ) (p : BWord) (τ : Bool) (D : BWord), p.length ≤ n →
    (∀ b ∈ D, IsDig b) → pcf τ p = false → pcf τ (p ++ D) = false := by
  intro n
  induction n with
  | zero =>
    intro p τ D hp hD _
    have : p = [] := List.length_eq_zero_iff.1 (by omega)
    subst this
    exact pcf_digits τ D hD
  | succ n ih =>
    intro p τ D hp hD h
    rcases p with _ | ⟨a, _ | ⟨b, p⟩⟩
    · exact pcf_digits τ D hD
    · exact pcf_single_dig τ a D hD h
    · simp only [List.length_cons] at hp
      cases τ <;> cases a <;> cases b <;>
        simp only [List.cons_append, pcf_t00, pcf_t01, pcf_t1, pcf_tyinv, pcf_ty, pcf_t0y,
          pcf_t0yinv, pcf_f0, pcf_f10, pcf_f11, pcf_fy, pcf_fyinv, pcf_f1y, pcf_f1yinv] at h ⊢
      all_goals first
        | rfl
        | exact absurd h (by decide)
        | exact ih p _ D (by omega) hD h
        | exact ih (_ :: p) _ D (by simp; omega) hD h

theorem noPC_append_dg {Λ : BWord} (h : NoPotentialCancellation Λ) (u : Seq) :
    NoPotentialCancellation (Λ ++ dg u) := by
  rw [noPC_iff] at h ⊢
  intro τ v hs
  rcases suffix_cases hs with hs | ⟨p, hp, rfl⟩
  · exact (not_suffix_dig (dg_dig u) hs).elim
  · exact pcf_append_dig _ p τ _ le_rfl (dg_dig u) (h τ p hp)

theorem maxadv : ∀ (n : ℕ) (s : Seq) (σ : Bool) (X : BWord), s.length ≤ n →
    ∃ t σ' r, Advances (occ σ :: (dg s ++ X)) (dg t ++ occ σ' :: (r ++ X)) ∧
      pcf σ (dg s ++ X) = pcf σ' (r ++ X) ∧
      ((σ' = true ∧ (r = [] ∨ r = [.zero])) ∨ (σ' = false ∧ (r = [] ∨ r = [.one]))) := by
  intro n
  induction n with
  | zero =>
    intro s σ X hs
    have : s = [] := List.length_eq_zero_iff.1 (by omega)
    subst this
    refine ⟨[], σ, [], Advances.rfl', rfl, ?_⟩
    cases σ <;> simp
  | succ n ih =>
    intro s σ X hs
    -- one advance by the rule, then the induction hypothesis
    have step : ∀ {c o : BWord} {σ' : Bool} (s' t₀ : Seq), Rule σ c o σ' → dg s = c ++ dg s' →
        o = dg t₀ → s'.length ≤ n →
        ∃ t σ'' r, Advances (occ σ :: (dg s ++ X)) (dg t ++ occ σ'' :: (r ++ X)) ∧
          pcf σ (dg s ++ X) = pcf σ'' (r ++ X) ∧
          ((σ'' = true ∧ (r = [] ∨ r = [.zero])) ∨ (σ'' = false ∧ (r = [] ∨ r = [.one]))) := by
      intro c o σ' s' t₀ hr hs' ho hlen
      obtain ⟨t, σ'', r, had, hpcf, hcase⟩ := ih s' σ' X hlen
      refine ⟨t₀ ++ t, σ'', r, ?_, ?_, hcase⟩
      · have h1 := hr.advances [] (dg s' ++ X)
        have h2 := advances_context had (dg t₀) []
        rw [hs', List.append_assoc]
        refine h1.tr ?_
        simpa [ho] using h2
      · rw [hs', List.append_assoc, hr.pcf_eq, hpcf]
    cases σ
    · rcases s with _ | ⟨_ | _, s'⟩
      · exact ⟨[], false, [], Advances.rfl', rfl, by simp⟩
      · exact step s' [false, false] Rule.yinv0 (by simp) (by simp) (by simp at hs; omega)
      · rcases s' with _ | ⟨_ | _, s''⟩
        · exact ⟨[], false, [.one], Advances.rfl', rfl, by simp⟩
        · exact step s'' [false, true] Rule.yinv10 (by simp) (by simp) (by simp at hs; omega)
        · exact step s'' [true] Rule.yinv11 (by simp) (by simp) (by simp at hs; omega)
    · rcases s with _ | ⟨_ | _, s'⟩
      · exact ⟨[], true, [], Advances.rfl', rfl, by simp⟩
      · rcases s' with _ | ⟨_ | _, s''⟩
        · exact ⟨[], true, [.zero], Advances.rfl', rfl, by simp⟩
        · exact step s'' [false] Rule.y00 (by simp) (by simp) (by simp at hs; omega)
        · exact step s'' [true, false] Rule.y01 (by simp) (by simp) (by simp at hs; omega)
      · exact step s' [true, true] Rule.y1 (by simp) (by simp) (by simp at hs; omega)

theorem rep_adv : ∀ N : ℕ, Advances (List.replicate N BLetter.y ++ List.replicate (2 ^ N) BLetter.zero)
    (BLetter.zero :: List.replicate N BLetter.y)
  | 0 => by simpa using (Advances.rfl' : Advances [BLetter.zero] _)
  | N + 1 => by
    have ih := rep_adv N
    have h1 := advances_context ih [BLetter.y] (List.replicate (2 ^ N) BLetter.zero)
    have h2 := advances_context ih [BLetter.y, BLetter.zero] []
    have h3 := Rule.y00.advances [] (List.replicate N BLetter.y)
    rw [List.replicate_succ, pow_succ, mul_two, List.replicate_add]
    refine (by simpa using h1 : Advances _ _).tr ((by simpa using h2 : Advances _ _).tr ?_)
    simpa using h3

theorem noPC_advances {A B : BWord} (h : Advances A B) (hA : NoPotentialCancellation A) :
    NoPotentialCancellation B := by
  induction h with
  | refl => exact hA
  | tail _ hs ih =>
    obtain ⟨i, j, hij⟩ := hs
    exact noPotentialCancellation_of_advanceAt _ _ i j ih hij

theorem lemma510 : ∀ Λ : BWord, NoPotentialCancellation Λ →
    ∃ u s : Seq, Advances (Λ ++ u.map fun d => if d then BLetter.one else .zero)
      (s.map (fun d => if d then BLetter.one else .zero) ++
        List.replicate (Λ.countP fun l => l = .y ∨ l = .yinv) BLetter.y)
  | [], _ => ⟨[], [], by simpa using (Advances.rfl' : Advances [] [])⟩
  | a :: Λ, h => by
    have hΛ : NoPotentialCancellation Λ := noPC_suffix h (List.suffix_cons a Λ)
    obtain ⟨u₁, s₁, adv₁⟩ := lemma510 Λ hΛ
    change Advances (Λ ++ dg u₁) (dg s₁ ++ _) at adv₁
    change ∃ u s : Seq, Advances (a :: Λ ++ dg u) (dg s ++ _)
    set N := Λ.countP fun l => l = .y ∨ l = .yinv with hN
    have hdig : ∀ d : Bool, (if d then BLetter.one else .zero) = a → 
        ∃ u s : Seq, Advances (a :: Λ ++ dg u) (dg s ++ List.replicate ((a :: Λ).countP fun l => l = .y ∨ l = .yinv) BLetter.y) := by
      intro d hd
      refine ⟨u₁, d :: s₁, ?_⟩
      have := advances_context adv₁ [a] []
      rw [List.countP_cons, ← hN]
      subst hd
      cases d <;> simpa using this
    have hocc : ∀ σ : Bool, occ σ = a →
        ∃ u s : Seq, Advances (a :: Λ ++ dg u) (dg s ++ List.replicate ((a :: Λ).countP fun l => l = .y ∨ l = .yinv) BLetter.y) := by
      intro σ hσ
      subst hσ
      have hcnt : ((occ σ :: Λ).countP fun l => l = .y ∨ l = .yinv) = N + 1 := by
        rw [List.countP_cons, ← hN]; cases σ <;> simp
      rw [hcnt]
      have adv₂ := advances_context adv₁ [occ σ] []
      simp only [List.singleton_append, List.append_nil] at adv₂
      have hnpc := noPC_advances adv₂ (by simpa using noPC_append_dg h u₁)
      have hp := (noPC_iff _).1 hnpc σ _ (List.suffix_refl _)
      obtain ⟨t, σ', r, adv₃, hpcf, hcase⟩ := maxadv _ s₁ σ (List.replicate N BLetter.y) le_rfl
      have adv := adv₂.tr adv₃
      rcases hcase with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩
      · refine ⟨u₁, t, ?_⟩
        simpa [List.replicate_succ] using adv
      · refine ⟨u₁ ++ List.replicate (2 ^ N) false, t ++ [false], ?_⟩
        have a1 := advances_context adv [] (dg (List.replicate (2 ^ N) false))
        have a2 := advances_context (rep_adv N) (dg t ++ [BLetter.y, BLetter.zero]) []
        have a3 := Rule.y00.advances (dg t) (List.replicate N BLetter.y)
        rw [dg_replicate_false] at a1
        simp only [List.nil_append, List.append_nil] at a1 a2
        rw [dg_append, ← List.append_assoc, dg_replicate_false]
        refine (by simpa using a1 : Advances _ _).tr ((by simpa using a2 : Advances _ _).tr ?_)
        simpa [List.replicate_succ] using a3
      · rcases Nat.eq_zero_or_pos N with hN0 | hN0
        · refine ⟨u₁ ++ [true, false], t ++ [false, true], ?_⟩
          have a1 := advances_context adv [] (dg [true, false])
          have a3 := Rule.yinv10.advances (dg t) []
          rw [hN0] at a1
          rw [dg_append, ← List.append_assoc, hN0]
          refine (by simpa using a1 : Advances _ _).tr ?_
          simpa using a3
        · exfalso
          rw [hpcf] at hp
          obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
          rw [hM] at hp
          simp [List.replicate_succ] at hp
      · refine ⟨u₁ ++ List.replicate (2 ^ N) false, t ++ [false, true], ?_⟩
        have a1 := advances_context adv [] (dg (List.replicate (2 ^ N) false))
        have a2 := advances_context (rep_adv N) (dg t ++ [BLetter.yinv, BLetter.one]) []
        have a3 := Rule.yinv10.advances (dg t) (List.replicate N BLetter.y)
        rw [dg_replicate_false] at a1
        simp only [List.nil_append, List.append_nil] at a1 a2
        rw [dg_append, ← List.append_assoc, dg_replicate_false]
        refine (by simpa using a1 : Advances _ _).tr ((by simpa using a2 : Advances _ _).tr ?_)
        simpa [List.replicate_succ] using a3
    cases a
    · exact hdig false rfl
    · exact hdig true rfl
    · exact hocc true rfl
    · exact hocc false rfl


/-! ### The recursion for `y` and `y⁻¹` on infinite sequences -/

/-! ### Localizations and the group `SeqGroup` -/

/-! ### `B`-word semantics -/

/-! ### Letters as functions -/

/-! ### Tail equivalence -/

/-! ### A sequence that `y^N` moves to a sequence that is not tail equivalent to it -/

/-! ### Lemma 5.11 -/

end LodhaMoore.Dev.S5

namespace LodhaMoore

end LodhaMoore
end

section
open LodhaMoore
theorem solution (Λ : BWord) (h : NoPotentialCancellation Λ) :
    ∃ u s : Seq, Advances (Λ ++ u.map fun d => if d then BLetter.one else .zero)
      (s.map (fun d => if d then BLetter.one else .zero) ++
        List.replicate (Λ.countP fun l => l = .y ∨ l = .yinv) BLetter.y) :=
  Dev.S5.lemma510 Λ h
end
