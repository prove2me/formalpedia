-- Prove2me | solution 1 for LodhaMoore.isXWord_or_eval_ne_of_sufficientlyExpanded
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T11:34:28.898069+00:00
-- url     : https://prove2.me/submissions/d010beae-ba0f-4ff1-befd-bb8841d1556d

import Mathlib
import Definitions.Def_LodhaMooreWords
import Definitions.Def_LodhaMoore
import Theorems.Thm_LodhaMoore_exists_advances_append_replicate

section
namespace LodhaMoore

theorem incompat_app {s a b : Seq} {x y : Bool} (hxy : x ≠ y) :
    Incompatible (s ++ x :: a) (s ++ y :: b) := by
  constructor
  · intro h
    rw [List.prefix_append_right_inj] at h
    exact hxy (List.cons_prefix_cons.1 h).1
  · intro h
    rw [List.prefix_append_right_inj] at h
    exact hxy (List.cons_prefix_cons.1 h).1.symm

end LodhaMoore
end

section
namespace LodhaMoore

/-- The order condition of Definition 5.1. -/
def OC (W : Word) : Prop :=
  ∀ (i j : ℕ) (hi : i < W.length) (hj : j < W.length) (s t : Seq) (m n : ℤ),
    W[i] = (.y s, m) → W[j] = (.y t, n) → s <+: t → j ≤ i

theorem oc_append {Ξ Υ : Word} (hΞ : ∀ p ∈ Ξ, ∀ t, p.1 ≠ .y t) : OC (Ξ ++ Υ) ↔ OC Υ := by
  constructor
  · intro h i j hi hj s t m n hiv hjv hst
    have := h (Ξ.length + i) (Ξ.length + j) (by simp; omega) (by simp; omega) s t m n
      (by rw [List.getElem_append_right (by omega)]; simpa using hiv)
      (by rw [List.getElem_append_right (by omega)]; simpa using hjv) hst
    omega
  · intro h i j hi hj s t m n hiv hjv hst
    have big : ∀ k (hk : k < (Ξ ++ Υ).length) (u : Seq) (r : ℤ), (Ξ ++ Υ)[k] = (Gen.y u, r) →
        Ξ.length ≤ k := by
      intro k hk u r hk'
      by_contra hc
      push Not at hc
      rw [List.getElem_append_left hc] at hk'
      exact hΞ _ (List.getElem_mem hc) u (by rw [hk'])
    have hi' := big i hi s m hiv
    have hj' := big j hj t n hjv
    rw [List.getElem_append_right hi'] at hiv
    rw [List.getElem_append_right hj'] at hjv
    have := h (i - Ξ.length) (j - Ξ.length) (by simp at hi; omega) (by simp at hj; omega) s t m n hiv hjv hst
    omega

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

/-- Strict standard order between two letters: the first index is not an initial part of the
second. -/
def SO (p q : Gen × ℤ) : Prop := ∀ a b, p.1 = .y a → q.1 = .y b → ¬ a <+: b

theorem oc_iff_pairwise (W : Word) : OC W ↔ W.Pairwise SO := by
  rw [List.pairwise_iff_getElem]
  constructor
  · intro h i j hi hj hij a b ha hb hab
    have := h i j hi hj a b (W[i]).2 (W[j]).2 (by ext <;> simp [ha]) (by ext <;> simp [hb]) hab
    omega
  · intro h i j hi hj s t m n hiv hjv hst
    by_contra hc
    push Not at hc
    exact h i j hi hj hc s t (by rw [hiv]) (by rw [hjv]) hst

/-- The `y`-part of a profile: the sum of `|exponent|` over the letters `y_t` with `|t| = d`. -/
def rawProf (W : Word) (d : ℕ) : ℕ :=
  (W.map fun p => match p.1 with | .y t => if t.length = d then p.2.natAbs else 0 | .x _ => 0).sum

@[simp] theorem rawProf_nil (d : ℕ) : rawProf [] d = 0 := rfl

/-! ### Moving letters -/


/-! ### Standard forms as `X`-word plus strictly ordered `Y`-word -/

theorem xword_noy {Ξ : Word} (h : IsXWord Ξ) : ∀ p ∈ Ξ, ∀ t, p.1 ≠ .y t := by
  intro p hp t ht; obtain ⟨u, hu⟩ := h.2 p hp; rw [hu] at ht; cases ht

theorem sf_decomp {Ω : Word} (h : IsStandardForm Ω) :
    ∃ Ξ Υ, Ω = Ξ ++ Υ ∧ IsXWord Ξ ∧ IsYWord Υ ∧ Υ.Pairwise SO := by
  obtain ⟨-, ⟨Ξ, Υ, rfl, hΞ, hΥ⟩, hoc⟩ := h
  exact ⟨Ξ, Υ, rfl, hΞ, hΥ, (oc_iff_pairwise Υ).1 ((oc_append (xword_noy hΞ)).1 hoc)⟩

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


/-! ### The recursion for `y` and `y⁻¹` on infinite sequences -/

theorem yStep_len (σ : Bool) (ξ : Stream' Bool) : 1 ≤ (yStep σ ξ).1.length := by
  unfold yStep
  cases σ <;> simp only <;> split <;> simp

theorem yOut_prefix_succ : ∀ (k : ℕ) (σ : Bool) (ξ : Stream' Bool), yOut k σ ξ <+: yOut (k + 1) σ ξ
  | 0, _, _ => List.nil_prefix
  | k + 1, σ, ξ => by
    show (yStep σ ξ).1 ++ yOut k _ _ <+: (yStep σ ξ).1 ++ yOut (k + 1) _ _
    exact (List.prefix_append_right_inj _).2 (yOut_prefix_succ k _ _)

theorem yOut_length : ∀ (k : ℕ) (σ : Bool) (ξ : Stream' Bool), k ≤ (yOut k σ ξ).length
  | 0, _, _ => Nat.zero_le _
  | k + 1, σ, ξ => by
    show k + 1 ≤ ((yStep σ ξ).1 ++ yOut k _ _).length
    have := yOut_length k (yStep σ ξ).2.1 (yStep σ ξ).2.2
    have := yStep_len σ ξ
    simp only [List.length_append]; omega

theorem yOut_prefix_le {k k' : ℕ} (h : k ≤ k') (σ : Bool) (ξ : Stream' Bool) :
    yOut k σ ξ <+: yOut k' σ ξ := by
  induction k', h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ k' _ ih => exact ih.trans (yOut_prefix_succ k' σ ξ)

theorem getD_of_prefix {l₁ l₂ : List Bool} (h : l₁ <+: l₂) {n : ℕ} (hn : n < l₁.length) :
    l₁.getD n false = l₂.getD n false := by
  rw [List.getD_eq_getElem _ _ hn, List.getD_eq_getElem _ _ (by have := h.length_le; omega)]
  exact h.getElem hn

theorem yFun_get (σ : Bool) (ξ : Stream' Bool) {m k : ℕ} (h : m < k) :
    yFun σ ξ m = (yOut k σ ξ).getD m false := by
  show (yOut (m + 1) σ ξ).getD m false = _
  exact getD_of_prefix (yOut_prefix_le (by omega) σ ξ) (by have := yOut_length (m + 1) σ ξ; omega)

theorem yFun_step (σ : Bool) (ξ : Stream' Bool) :
    yFun σ ξ = (yStep σ ξ).1 ++ₛ yFun (yStep σ ξ).2.1 (yStep σ ξ).2.2 := by
  apply Stream'.ext
  intro n
  show yFun σ ξ n = _
  rw [yFun_get σ ξ (show n < n + 2 by omega)]
  show ((yStep σ ξ).1 ++ yOut (n + 1) _ _).getD n false = _
  by_cases hn : n < (yStep σ ξ).1.length
  · rw [Stream'.get_append_left (h := hn), List.getD_append _ _ _ _ hn, List.getD_eq_getElem _ _ hn]
  · push Not at hn
    obtain ⟨m, hm⟩ : ∃ m, n = (yStep σ ξ).1.length + m := ⟨n - (yStep σ ξ).1.length, by omega⟩
    rw [hm, Stream'.get_append_right, List.getD_append_right _ _ _ _ (by omega)]
    simp only [Nat.add_sub_cancel_left]
    show _ = yFun _ _ m
    have := yStep_len σ ξ
    rw [yFun_get _ _ (show m < n + 1 from by omega)]
    rw [hm]

theorem y_00 (X : Stream' Bool) :
    yFun true (Stream'.cons false (Stream'.cons false X)) = Stream'.cons false (yFun true X) := by
  rw [yFun_step]; rfl

theorem y_01 (X : Stream' Bool) : yFun true (Stream'.cons false (Stream'.cons true X)) =
    Stream'.cons true (Stream'.cons false (yFun false X)) := by
  rw [yFun_step]; rfl

theorem y_1 (X : Stream' Bool) :
    yFun true (Stream'.cons true X) = Stream'.cons true (Stream'.cons true (yFun true X)) := by
  rw [yFun_step]; rfl

theorem yi_0 (X : Stream' Bool) :
    yFun false (Stream'.cons false X) = Stream'.cons false (Stream'.cons false (yFun false X)) := by
  rw [yFun_step]; rfl

theorem yi_10 (X : Stream' Bool) : yFun false (Stream'.cons true (Stream'.cons false X)) =
    Stream'.cons false (Stream'.cons true (yFun true X)) := by
  rw [yFun_step]; rfl

theorem yi_11 (X : Stream' Bool) :
    yFun false (Stream'.cons true (Stream'.cons true X)) = Stream'.cons true (yFun false X) := by
  rw [yFun_step]; rfl

theorem eta2 (ξ : Stream' Bool) :
    ξ = Stream'.cons (ξ 0) (Stream'.cons (ξ 1) (Stream'.drop 2 ξ)) := by
  apply Stream'.ext
  intro n
  rcases n with _ | _ | n
  · rfl
  · rfl
  · show ξ (n + 2) = ξ (n + 2); rfl

theorem y_inv_aux (n : ℕ) : ∀ ξ : Stream' Bool,
    yFun false (yFun true ξ) n = ξ n ∧ yFun true (yFun false ξ) n = ξ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ξ
  obtain ⟨a, b, X, rfl⟩ : ∃ a b X, ξ = Stream'.cons a (Stream'.cons b X) := ⟨_, _, _, eta2 ξ⟩
  cases a <;> cases b
  · constructor
    · rw [y_00, yi_0]
      rcases n with _ | _ | m
      · rfl
      · rfl
      · exact (ih m (by omega) X).1
    · rw [yi_0, y_00]
      rcases n with _ | m
      · rfl
      · exact (ih m (by omega) _).2
  · constructor
    · rw [y_01, yi_10]
      rcases n with _ | _ | m
      · rfl
      · rfl
      · exact (ih m (by omega) X).2
    · rw [yi_0, y_00]
      rcases n with _ | m
      · rfl
      · exact (ih m (by omega) _).2
  · constructor
    · rw [y_1, yi_11]
      rcases n with _ | m
      · rfl
      · exact (ih m (by omega) _).1
    · rw [yi_10, y_01]
      rcases n with _ | _ | m
      · rfl
      · rfl
      · exact (ih m (by omega) X).1
  · constructor
    · rw [y_1, yi_11]
      rcases n with _ | m
      · rfl
      · exact (ih m (by omega) _).1
    · rw [yi_11, y_1]
      rcases n with _ | _ | m
      · rfl
      · rfl
      · exact (ih m (by omega) X).2

theorem yi_y (ξ : Stream' Bool) : yFun false (yFun true ξ) = ξ :=
  Stream'.ext fun n => (y_inv_aux n ξ).1

theorem y_yi (ξ : Stream' Bool) : yFun true (yFun false ξ) = ξ :=
  Stream'.ext fun n => (y_inv_aux n ξ).2

/-! ### Localizations and the group `SeqGroup` -/

/-- `s` is an initial part of the infinite sequence `ξ`. -/
def SPre (s : Seq) (ξ : Stream' Bool) : Prop := Stream'.take s.length ξ = s

theorem spre_append (s : Seq) (η : Stream' Bool) : SPre s (s ++ₛ η) := by
  unfold SPre
  induction s with
  | nil => rfl
  | cons a s ih =>
    rw [Stream'.cons_append_stream, List.length_cons, Stream'.take_succ_cons, ih]

theorem spre_iff {s : Seq} {ξ : Stream' Bool} : SPre s ξ ↔ ∃ η, ξ = s ++ₛ η := by
  constructor
  · intro h
    refine ⟨Stream'.drop s.length ξ, ?_⟩
    conv_lhs => rw [← Stream'.append_take_drop s.length ξ]
    rw [h]
  · rintro ⟨η, rfl⟩; exact spre_append s η

theorem localize_on (s : Seq) (f : Stream' Bool → Stream' Bool) (η : Stream' Bool) :
    localize s f (s ++ₛ η) = s ++ₛ f η := by
  have h := spre_append s η
  unfold SPre at h
  unfold localize
  rw [if_pos h, Stream'.drop_append_stream]

theorem localize_off {s : Seq} (f : Stream' Bool → Stream' Bool) {ξ : Stream' Bool} (h : ¬ SPre s ξ) :
    localize s f ξ = ξ := by
  unfold SPre at h
  unfold localize; rw [if_neg h]

theorem localize_comp {s : Seq} {f g : Stream' Bool → Stream' Bool} (hfg : ∀ η, f (g η) = η)
    (ξ : Stream' Bool) : localize s f (localize s g ξ) = ξ := by
  by_cases h : SPre s ξ
  · obtain ⟨η, rfl⟩ := spre_iff.1 h
    rw [localize_on, localize_on, hfg]
  · rw [localize_off g h, localize_off f h]

theorem ySeq_bij (s : Seq) : Function.Bijective (ySeq s) := by
  refine Function.bijective_iff_has_inverse.2 ⟨localize s (yFun false), ?_, ?_⟩
  · intro ξ; exact localize_comp yi_y ξ
  · intro ξ; exact localize_comp y_yi ξ

/-- The function of an element of `SeqGroup`. -/
def appG (g : SeqGroup) (ξ : Stream' Bool) : Stream' Bool := (MulOpposite.unop g) ξ

theorem appG_mul (g h : SeqGroup) (ξ : Stream' Bool) : appG (g * h) ξ = appG h (appG g ξ) := by
  simp [appG, MulOpposite.unop_mul, Equiv.Perm.mul_apply]

theorem appG_one (ξ : Stream' Bool) : appG 1 ξ = ξ := rfl

theorem appG_inv_cancel (g : SeqGroup) (ξ : Stream' Bool) : appG g (appG g⁻¹ ξ) = ξ := by
  rw [← appG_mul, inv_mul_cancel, appG_one]

/-- Powers of a permutation, through a function and an inverse function. -/
theorem perm_zpow_apply (E : Equiv.Perm (Stream' Bool)) (f g : Stream' Bool → Stream' Bool)
    (hf : ∀ ξ, E ξ = f ξ) (hg : ∀ ξ, E⁻¹ ξ = g ξ) (k : ℤ) (ξ : Stream' Bool) :
    (E ^ k) ξ = if 0 < k then f^[k.natAbs] ξ else g^[k.natAbs] ξ := by
  have hfE : ⇑E = f := funext hf
  have hgE : ⇑E⁻¹ = g := funext hg
  rcases k with n | n
  · rcases n with _ | n
    · simp
    · simp only [Int.ofNat_eq_natCast, zpow_natCast, Equiv.Perm.coe_pow, hfE]
      rw [if_pos (by omega)]; rfl
  · rw [zpow_negSucc, ← inv_pow, Equiv.Perm.coe_pow, hgE, if_neg (by omega)]
    rfl

/-! ### `B`-word semantics -/

/-- The function of one letter of a `B`-word. -/
def bsem : BLetter → Stream' Bool → Stream' Bool
  | .zero, η => Stream'.cons false η
  | .one, η => Stream'.cons true η
  | .y, η => yFun true η
  | .yinv, η => yFun false η

/-- The function of a `B`-word: digits are written, `y^{±1}` applies `y^{±1}` to what follows. -/
def Sem (L : BWord) (η : Stream' Bool) : Stream' Bool := L.foldr bsem η

theorem Sem_append (A B : BWord) (η : Stream' Bool) : Sem (A ++ B) η = Sem A (Sem B η) := by
  simp [Sem, List.foldr_append]

theorem Sem_dg (u : Seq) (η : Stream' Bool) : Sem (dg u) η = u ++ₛ η := by
  induction u with
  | nil => rfl
  | cons d u ih =>
    show bsem _ (Sem (dg u) η) = _
    rw [ih, Stream'.cons_append_stream]
    cases d <;> rfl

theorem Sem_rep (σ : Bool) (n : ℕ) (η : Stream' Bool) :
    Sem (List.replicate n (occ σ)) η = (yFun σ)^[n] η := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, Function.iterate_succ_apply']
    show bsem _ (Sem _ η) = _
    rw [ih]; cases σ <;> rfl

/-- `y^k` as a `B`-word. -/
def ypow (k : ℤ) : BWord := List.replicate k.natAbs (occ (decide (0 < k)))

theorem Sem_ypow (k : ℤ) (η : Stream' Bool) :
    Sem (ypow k) η = if 0 < k then (yFun true)^[k.natAbs] η else (yFun false)^[k.natAbs] η := by
  unfold ypow; rw [Sem_rep]; split_ifs with h <;> simp [h]

theorem Rule.sem {σ σ' : Bool} {c o : BWord} (h : Rule σ c o σ') (X : Stream' Bool) :
    bsem (occ σ) (Sem c X) = Sem o (bsem (occ σ') X) := by
  cases h
  · exact y_00 X
  · exact y_01 X
  · exact y_1 X
  · exact yi_0 X
  · exact yi_10 X
  · exact yi_11 X

theorem Sem_advanceAt {L M : BWord} {i j : ℕ} (h : AdvanceAt (L, i) (M, j)) (η : Stream' Bool) :
    Sem L η = Sem M η := by
  obtain ⟨pre, σ, c, o, σ', post, hr, rfl, rfl, -, -⟩ := advanceAt_cases h
  rw [Sem_append, Sem_append, Sem_append]
  show Sem pre (bsem (occ σ) (Sem (c ++ post) η)) = Sem pre (Sem o (bsem (occ σ') (Sem post η)))
  rw [Sem_append, hr.sem]

theorem Sem_advances {L M : BWord} (h : Advances L M) (η : Stream' Bool) : Sem L η = Sem M η := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    obtain ⟨i, j, hij⟩ := hs
    rw [ih, Sem_advanceAt hij]

/-! ### Letters as functions -/

theorem appG_ys_zpow (s : Seq) (k : ℤ) (ξ : Stream' Bool) :
    appG (ys s ^ k) ξ = if 0 < k then (ySeq s)^[k.natAbs] ξ
      else (localize s (yFun false))^[k.natAbs] ξ := by
  have hE : ys s = MulOpposite.op (Equiv.ofBijective (ySeq s) (ySeq_bij s)) := by
    simp [ys, toSeqGroup, dif_pos (ySeq_bij s)]
  rw [hE, appG, MulOpposite.unop_zpow, MulOpposite.unop_op]
  apply perm_zpow_apply
  · intro ξ; rfl
  · intro ξ
    rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq]
    exact (localize_comp y_yi ξ).symm

theorem iterate_localize_on (s : Seq) (f : Stream' Bool → Stream' Bool) (n : ℕ) (η : Stream' Bool) :
    (localize s f)^[n] (s ++ₛ η) = s ++ₛ f^[n] η := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, localize_on, Function.iterate_succ_apply']

theorem iterate_localize_off {s : Seq} (f : Stream' Bool → Stream' Bool) (n : ℕ) {ξ : Stream' Bool}
    (h : ¬ SPre s ξ) : (localize s f)^[n] ξ = ξ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, localize_off f h]

/-- A letter `y_s^k` on the sequences below `s`. -/
theorem appG_letter_on (s : Seq) (k : ℤ) (η : Stream' Bool) :
    appG ((Gen.y s).val ^ k) (s ++ₛ η) = s ++ₛ Sem (ypow k) η := by
  show appG (ys s ^ k) _ = _
  rw [appG_ys_zpow, Sem_ypow]
  split_ifs
  · exact iterate_localize_on s _ _ η
  · exact iterate_localize_on s _ _ η

/-- A letter `y_s^k` fixes the sequences not below `s`. -/
theorem appG_letter_off {s : Seq} (k : ℤ) {ξ : Stream' Bool} (h : ¬ SPre s ξ) :
    appG ((Gen.y s).val ^ k) ξ = ξ := by
  show appG (ys s ^ k) _ = _
  rw [appG_ys_zpow]
  split_ifs
  · exact iterate_localize_off _ _ h
  · exact iterate_localize_off _ _ h

/-! ### Tail equivalence -/

/-- `ξ` and `ζ` are tail equivalent. -/
def TailEq (ξ ζ : Stream' Bool) : Prop := ∃ a b, Stream'.drop a ξ = Stream'.drop b ζ

theorem TailEq.rfl' (ξ : Stream' Bool) : TailEq ξ ξ := ⟨0, 0, rfl⟩

theorem TailEq.symm' {ξ ζ : Stream' Bool} (h : TailEq ξ ζ) : TailEq ζ ξ := by
  obtain ⟨a, b, h⟩ := h; exact ⟨b, a, h.symm⟩

theorem TailEq.trans' {ξ ζ θ : Stream' Bool} (h1 : TailEq ξ ζ) (h2 : TailEq ζ θ) : TailEq ξ θ := by
  obtain ⟨a, b, h1⟩ := h1
  obtain ⟨c, d, h2⟩ := h2
  refine ⟨a + c, d + b, ?_⟩
  rw [← Stream'.drop_drop, h1, Stream'.drop_drop, add_comm b c, ← Stream'.drop_drop, h2,
    Stream'.drop_drop]

theorem tailEq_append (w : List Bool) (X : Stream' Bool) : TailEq (w ++ₛ X) X :=
  ⟨w.length, 0, Stream'.drop_append_stream w X⟩

theorem tailEq_of_append {w v : List Bool} {X Y : Stream' Bool} (h : TailEq (w ++ₛ X) (v ++ₛ Y)) :
    TailEq X Y :=
  ((tailEq_append w X).symm'.trans' h).trans' (tailEq_append v Y)

/-- The elements of `SeqGroup` that move every sequence to a tail-equivalent one. -/
def TPsub : Subgroup SeqGroup where
  carrier := {g | ∀ ξ, TailEq (appG g ξ) ξ}
  one_mem' := fun ξ => TailEq.rfl' ξ
  mul_mem' := by
    intro a b ha hb ξ
    rw [appG_mul]
    exact (hb _).trans' (ha ξ)
  inv_mem' := by
    intro a ha ξ
    have := ha (appG a⁻¹ ξ)
    rw [appG_inv_cancel] at this
    exact this.symm'

theorem tailEq_xFun (η : Stream' Bool) : TailEq (xFun η) η := by
  obtain ⟨a, b, X, rfl⟩ : ∃ a b X, η = Stream'.cons a (Stream'.cons b X) := ⟨_, _, _, eta2 η⟩
  cases a <;> cases b
  · exact ⟨1, 2, rfl⟩
  · exact ⟨2, 2, rfl⟩
  · exact ⟨1, 0, rfl⟩
  · exact ⟨1, 0, rfl⟩

theorem xs_mem (s : Seq) : xs s ∈ TPsub := by
  intro ξ
  have hx : TailEq (xSeq s ξ) ξ := by
    by_cases h : SPre s ξ
    · obtain ⟨η, rfl⟩ := spre_iff.1 h
      rw [xSeq, localize_on]
      exact ((tailEq_append s _).trans' (tailEq_xFun η)).trans' (tailEq_append s η).symm'
    · rw [xSeq, localize_off _ h]; exact TailEq.rfl' ξ
  unfold xs toSeqGroup
  split_ifs with hb
  · exact hx
  · exact TailEq.rfl' ξ

theorem xword_mem {Ξ : Word} (h : IsXWord Ξ) : Ξ.eval ∈ TPsub := by
  unfold Word.eval
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg
  obtain ⟨s, hs⟩ := h.2 p hp
  rw [hs]
  exact Subgroup.zpow_mem _ (xs_mem s) _

/-! ### A sequence that `y^N` moves to a sequence that is not tail equivalent to it -/

/-- `(0^{2^k} 1^m)^∞`. -/
def Qs (k m : ℕ) : Stream' Bool := fun n => decide (2 ^ k ≤ n % (2 ^ k + m))

/-- `0^{2^k} 1^m`. -/
def Qw (k m : ℕ) : List Bool := List.replicate (2 ^ k) false ++ List.replicate m true

theorem Qw_length (k m : ℕ) : (Qw k m).length = 2 ^ k + m := by simp [Qw]

theorem Qs_eq (k m : ℕ) : Qs k m = Qw k m ++ₛ Qs k m := by
  apply Stream'.ext
  intro n
  by_cases hn : n < (Qw k m).length
  · rw [Stream'.get_append_left (h := hn)]
    have h2 : (Qw k m)[n]? = some (decide (2 ^ k ≤ n)) := by
      have hn' : n < 2 ^ k + m := by rw [Qw_length] at hn; exact hn
      unfold Qw
      rw [List.getElem?_append]
      simp only [List.length_replicate]
      split_ifs with h
      · rw [List.getElem?_replicate, if_pos h]
        simp only [Option.some.injEq]
        exact (decide_eq_false (by omega)).symm
      · rw [List.getElem?_replicate, if_pos (by omega)]
        simp only [Option.some.injEq]
        exact (decide_eq_true (by omega)).symm
    rw [List.getElem?_eq_getElem hn] at h2
    rw [Option.some.inj h2]
    rw [Qw_length] at hn
    show decide (2 ^ k ≤ n % (2 ^ k + m)) = _
    rw [Nat.mod_eq_of_lt hn]
  · push Not at hn
    obtain ⟨j, rfl⟩ : ∃ j, n = (Qw k m).length + j := ⟨n - (Qw k m).length, by omega⟩
    rw [Stream'.get_append_right]
    show decide (2 ^ k ≤ ((Qw k m).length + j) % (2 ^ k + m)) = decide (2 ^ k ≤ j % (2 ^ k + m))
    rw [Qw_length, Nat.add_mod_left]

theorem stream_fix_unique {w : List Bool} (hw : w ≠ []) {X Z : Stream' Bool} (hX : X = w ++ₛ X)
    (hZ : Z = w ++ₛ Z) : X = Z := by
  apply Stream'.ext
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [hX, hZ]
  by_cases h : n < w.length
  · rw [Stream'.get_append_left (h := h), Stream'.get_append_left (h := h)]
  · push Not at h
    obtain ⟨j, rfl⟩ : ∃ j, n = w.length + j := ⟨n - w.length, by omega⟩
    rw [Stream'.get_append_right, Stream'.get_append_right]
    have : 0 < w.length := List.length_pos_iff.2 hw
    exact ih j (by omega)

theorem y_rep_false (j : ℕ) (Z : Stream' Bool) :
    yFun true (List.replicate (2 * j) false ++ₛ Z) = List.replicate j false ++ₛ yFun true Z := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, List.replicate_succ, List.replicate_succ,
      Stream'.cons_append_stream, Stream'.cons_append_stream, y_00, ih, List.replicate_succ,
      Stream'.cons_append_stream]

theorem y_rep_true (m : ℕ) (Z : Stream' Bool) :
    yFun true (List.replicate m true ++ₛ Z) = List.replicate (2 * m) true ++ₛ yFun true Z := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, Stream'.cons_append_stream, y_1, ih,
      show 2 * (m + 1) = 2 * m + 1 + 1 by ring, List.replicate_succ, List.replicate_succ,
      Stream'.cons_append_stream, Stream'.cons_append_stream]

theorem y_Qs (k m : ℕ) : yFun true (Qs (k + 1) m) = Qs k (2 * m) := by
  apply stream_fix_unique (w := Qw k (2 * m)) (by simp [Qw])
  · conv_lhs => rw [Qs_eq]
    rw [Qw, Stream'.append_append_stream, pow_succ, mul_comm, y_rep_false, y_rep_true,
      ← Stream'.append_append_stream]
    rfl
  · exact Qs_eq k (2 * m)

theorem y_iter_Qs (N m : ℕ) : (yFun true)^[N] (Qs N m) = Qs 0 (2 ^ N * m) := by
  induction N generalizing m with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply, y_Qs, ih, pow_succ]
    ring_nf

theorem not_tailEq_Qs {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) : ¬ TailEq (Qs 0 M) (Qs N 1) := by
  rintro ⟨a, b, h⟩
  set P := 2 ^ N + 1 with hP
  have hN2 : 2 ≤ 2 ^ N := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ N := Nat.pow_le_pow_right (by norm_num) hN
  set n₀ := (b + 1) * P with hn₀
  have hb : b ≤ n₀ := by rw [hn₀]; nlinarith
  have e1 := congrArg (fun s => Stream'.get s (n₀ - b)) h
  have e2 := congrArg (fun s => Stream'.get s (n₀ - b + 1)) h
  simp only [Stream'.get_drop] at e1 e2
  have q1 : Qs N 1 (b + (n₀ - b)) = false := by
    rw [show b + (n₀ - b) = n₀ by omega]
    show decide (2 ^ N ≤ n₀ % (2 ^ N + 1)) = false
    rw [hn₀, ← hP, Nat.mul_mod_left]
    simp
  have q2 : Qs N 1 (b + (n₀ - b + 1)) = false := by
    rw [show b + (n₀ - b + 1) = 1 + n₀ by omega]
    show decide (2 ^ N ≤ (1 + n₀) % (2 ^ N + 1)) = false
    rw [hn₀, ← hP, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    simp; omega
  have r1 : Qs 0 M (a + (n₀ - b)) = false := by rw [← q1]; exact e1
  have r2 : Qs 0 M (a + (n₀ - b + 1)) = false := by rw [← q2]; exact e2
  simp only [Qs, pow_zero, decide_eq_false_iff_not, not_le, Nat.lt_one_iff] at r1 r2
  rw [show a + (n₀ - b + 1) = a + (n₀ - b) + 1 by omega] at r2
  have d1 := Nat.dvd_of_mod_eq_zero r1
  have d2 := Nat.dvd_of_mod_eq_zero r2
  have := (Nat.dvd_add_right d1).1 d2
  have := Nat.le_of_dvd (by norm_num) this
  omega

/-! ### Lemma 5.11 -/

/-- The letter `p` is a `y`-letter whose index extends `c`. -/
def isExt (c : Seq) (p : Gen × ℤ) : Bool :=
  match p.1 with
  | .y t => c.isPrefixOf t
  | .x _ => false

theorem isExt_y (c t : Seq) (k : ℤ) : isExt c (.y t, k) = decide (c <+: t) := by
  rw [Bool.eq_iff_iff]; simp [isExt, List.isPrefixOf_iff_prefix]

theorem eval_cons (p : Gen × ℤ) (V : Word) : Word.eval (p :: V) = p.1.val ^ p.2 * Word.eval V := by
  simp [Word.eval]

theorem eval_append (A B : Word) : Word.eval (A ++ B) = A.eval * B.eval := by
  simp [Word.eval, List.prod_append]

theorem spre_comp {s t : Seq} {ξ : Stream' Bool} (hs : SPre s ξ) (ht : SPre t ξ) :
    s <+: t ∨ t <+: s := by
  unfold SPre at hs ht
  rcases le_total s.length t.length with h | h
  · left
    have := Stream'.take_prefix_take_left (a := ξ) (h := h)
    rwa [hs, ht] at this
  · right
    have := Stream'.take_prefix_take_left (a := ξ) (h := h)
    rwa [hs, ht] at this

theorem not_spre_incomp {c t : Seq} (h : Incompatible c t) (η : Stream' Bool) :
    ¬ SPre t (c ++ₛ η) := by
  intro ht
  rcases spre_comp (spre_append c η) ht with h' | h'
  · exact h.1 h'
  · exact h.2 h'

theorem letter_cone {c t : Seq} (hct : c <+: t) (k : ℤ) (η : Stream' Bool) :
    ∃ η', appG ((Gen.y t).val ^ k) (c ++ₛ η) = c ++ₛ η' := by
  by_cases h : SPre t (c ++ₛ η)
  · obtain ⟨ζ, hζ⟩ := spre_iff.1 h
    obtain ⟨r, rfl⟩ := hct
    rw [hζ, appG_letter_on, Stream'.append_append_stream]
    exact ⟨_, rfl⟩
  · exact ⟨η, appG_letter_off k h⟩

theorem restrict (c : Seq) : ∀ V : Word, (∀ p ∈ V, ∃ t, p.1 = .y t ∧ (c <+: t ∨ Incompatible c t)) →
    ∀ η, ∃ η', appG V.eval (c ++ₛ η) = c ++ₛ η' ∧
      appG V.eval (c ++ₛ η) = appG (Word.eval (V.filter (isExt c))) (c ++ₛ η)
  | [], _, η => ⟨η, rfl, rfl⟩
  | (g, k) :: V, h, η => by
    obtain ⟨t, ht, hct⟩ := h (g, k) List.mem_cons_self
    simp only at ht
    subst ht
    have ih := restrict c V (fun q hq => h q (List.mem_cons_of_mem _ hq))
    rw [List.filter_cons, isExt_y]
    rcases hct with hct | hct
    · obtain ⟨η₁, h₁⟩ := letter_cone hct k η
      obtain ⟨η₂, h₂, h₃⟩ := ih η₁
      rw [if_pos (by simpa using hct)]
      refine ⟨η₂, ?_, ?_⟩
      · rw [eval_cons, appG_mul]; simp only; rw [h₁, h₂]
      · rw [eval_cons, eval_cons, appG_mul, appG_mul]; simp only; rw [h₁, h₃]
    · rw [if_neg (by simpa using hct.1)]
      have h₁ : appG ((Gen.y t).val ^ k) (c ++ₛ η) = c ++ₛ η :=
        appG_letter_off k (not_spre_incomp hct η)
      obtain ⟨η₂, h₂, h₃⟩ := ih η
      refine ⟨η₂, ?_, ?_⟩
      · rw [eval_cons, appG_mul]; simp only; rw [h₁, h₂]
      · rw [eval_cons, appG_mul]; simp only; rw [h₁, h₃]

theorem fixed (u : Seq) (η : Stream' Bool) : ∀ V : Word,
    (∀ p ∈ V, ∃ t, p.1 = .y t ∧ Incompatible u t) → appG V.eval (u ++ₛ η) = u ++ₛ η
  | [], _ => rfl
  | (g, k) :: V, h => by
    obtain ⟨t, ht, hut⟩ := h (g, k) List.mem_cons_self
    simp only at ht
    subst ht
    rw [eval_cons, appG_mul]
    simp only
    rw [appG_letter_off k (not_spre_incomp hut η)]
    exact fixed u η V (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem suffix_replicate {x : BLetter} {q : BWord} {m : ℕ} {a : BLetter}
    (h : (x :: q) <:+ List.replicate m a) : x = a ∧ q = List.replicate q.length a := by
  have hs := h.subset
  have hx : x = a := List.eq_of_mem_replicate (hs List.mem_cons_self)
  refine ⟨hx, List.eq_replicate_iff.2 ⟨rfl, fun b hb => List.eq_of_mem_replicate (hs (List.mem_cons_of_mem _ hb))⟩⟩

theorem pcf_occ_rep (σ : Bool) (j : ℕ) (X : BWord) (hj : 0 < j) :
    pcf σ (List.replicate j (occ σ) ++ X) = false := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  cases σ <;> simp [List.replicate_succ]

theorem noPC_ypow_dg (n : ℤ) (p : Seq) : NoPotentialCancellation (ypow n ++ dg p) := by
  rw [noPC_iff]
  intro τ v hs
  rcases suffix_cases hs with hs | ⟨q, hq, rfl⟩
  · exact (not_suffix_dig (dg_dig p) hs).elim
  · obtain ⟨hτ, hq2⟩ := suffix_replicate hq
    have hτ := occ_inj hτ
    subst hτ
    rcases Nat.eq_zero_or_pos q.length with h0 | h0
    · rw [List.length_eq_zero_iff.1 h0]; exact pcf_digits _ _ (dg_dig p)
    · rw [hq2]; exact pcf_occ_rep _ _ _ h0

theorem noPC_step {n nc : ℤ} (hn : n ≠ 0) (hnc : nc ≠ 0) {Λ' Λ'' : BWord}
    (h : NoPotentialCancellation Λ') (hΛ : Λ' = ypow nc ++ Λ'') :
    NoPotentialCancellation (ypow n ++ (dg [decide (n < 0)] ++ Λ')) := by
  have h' := h
  rw [noPC_iff] at h ⊢
  intro τ v hs
  rcases suffix_cases hs with hs | ⟨q, hq, rfl⟩
  · rcases suffix_cases hs with hs | ⟨q, hq, -⟩
    · exact h τ v hs
    · exact (not_suffix_dig (dg_dig _) hq).elim
  · obtain ⟨hτ, hq2⟩ := suffix_replicate hq
    have hτ := occ_inj hτ
    subst hτ
    rcases Nat.eq_zero_or_pos q.length with h0 | h0
    · rw [List.length_eq_zero_iff.1 h0, hΛ]
      obtain ⟨i, hi⟩ : ∃ i, nc.natAbs = i + 1 := ⟨nc.natAbs - 1, by omega⟩
      unfold ypow
      rw [hi, List.replicate_succ]
      rcases lt_or_gt_of_ne hn with hn' | hn'
      · simp [hn', show ¬ (0 < n) by omega]
        cases decide (0 < nc) <;> simp
      · simp [hn', show ¬ (n < 0) by omega]
        cases decide (0 < nc) <;> simp
    · rw [hq2]; exact pcf_occ_rep _ _ _ h0

theorem eval_single (p : Gen × ℤ) : Word.eval [p] = p.1.val ^ p.2 := by simp [Word.eval]

theorem isExt_mono {t c : Seq} (htc : t <+: c) {q : Gen × ℤ} (h : isExt c q = true) :
    isExt t q = true := by
  obtain ⟨g, k⟩ := q
  cases g with
  | x u => simp [isExt] at h
  | y a =>
    rw [isExt_y] at h ⊢
    simp only [decide_eq_true_eq] at h ⊢
    exact htc.trans h

/-- The path below a letter of a sufficiently expanded standard form (the recursive procedure in
the proof of Lemma 5.11), with the `B`-word that computes its evaluation. -/
theorem claim511 {Ω Ξ₀ Υ : Word} (hΩe : Ω = Ξ₀ ++ Υ) (hΞ₀ : IsXWord Ξ₀) (hΥ : IsYWord Υ)
    (hS : Υ.Pairwise SO) (hse : SufficientlyExpanded Ω) (B : ℕ)
    (hB : ∀ t k, (Gen.y t, k) ∈ Υ → t.length < B) :
    ∀ m t n, B - t.length ≤ m → (Gen.y t, n) ∈ Υ → ∃ p Λ, NoPotentialCancellation Λ ∧
      (∃ Λ', Λ = ypow n ++ Λ') ∧
      ∀ η, appG (Word.eval (Υ.filter (isExt t))) ((t ++ p) ++ₛ η) = t ++ₛ Sem Λ η := by
  have memΩ : ∀ q, q ∈ Υ → q ∈ Ω := by
    intro q h; rw [hΩe]; exact List.mem_append_right _ h
  have occΥ : ∀ t, YOccurs Ω t → ∃ k, (Gen.y t, k) ∈ Υ := by
    rintro t ⟨k, hk⟩
    rw [hΩe] at hk
    rcases List.mem_append.1 hk with h | h
    · exact absurd rfl (xword_noy hΞ₀ _ h t)
    · exact ⟨k, h⟩
  intro m
  induction m with
  | zero =>
    intro t n hm hmem
    have := hB t n hmem; omega
  | succ m ih =>
    intro t n hm hmem
    have hn : n ≠ 0 := hΥ.1 _ hmem
    obtain ⟨Υa, Υb, hsplit⟩ := List.append_of_mem hmem
    have hS' := hS
    rw [hsplit, List.pairwise_append, List.pairwise_cons] at hS'
    obtain ⟨-, ⟨hSb, -⟩, hSab⟩ := hS'
    have hYa : ∀ q ∈ Υa, ∃ a, q.1 = .y a := fun q hq => hΥ.2 q (by rw [hsplit]; simp [hq])
    have hYb : ∀ q ∈ Υb, ∃ b, q.1 = .y b := fun q hq => hΥ.2 q (by rw [hsplit]; simp [hq])
    have hfiltb : ∀ c, t <+: c → Υb.filter (isExt c) = [] := by
      intro c htc
      rw [List.filter_eq_nil_iff]
      intro q hq
      obtain ⟨b, hb⟩ := hYb q hq
      have hq' : q = (.y b, q.2) := Prod.ext hb rfl
      rw [hq', isExt_y]
      simp only [decide_eq_true_eq]
      intro hcb
      exact hSb q hq t b rfl hb (htc.trans hcb)
    have hfilt : Υ.filter (isExt t) = Υa.filter (isExt t) ++ [(.y t, n)] := by
      rw [hsplit, List.filter_append, List.filter_cons, isExt_y,
        if_pos (by simp), hfiltb t (List.prefix_refl t)]
    have hA : ∀ q ∈ Υa.filter (isExt t), ∃ a, q.1 = .y a ∧ t <+: a ∧ a ≠ t ∧ YOccurs Ω a := by
      intro q hq
      rw [List.mem_filter] at hq
      obtain ⟨a, ha⟩ := hYa q hq.1
      have hq' : q = (.y a, q.2) := Prod.ext ha rfl
      have hta : t <+: a := by have := hq.2; rw [hq', isExt_y] at this; simpa using this
      refine ⟨a, ha, hta, ?_, ⟨q.2, ?_⟩⟩
      · intro hat
        subst hat
        exact hSab q hq.1 (.y a, n) List.mem_cons_self a a ha rfl (List.prefix_refl a)
      · have : q ∈ Ω := memΩ q (by rw [hsplit]; simp [hq.1])
        rwa [hq'] at this
    have hevalt : ∀ ξ, appG (Word.eval (Υ.filter (isExt t))) ξ =
        appG ((Gen.y t).val ^ n) (appG (Word.eval (Υa.filter (isExt t))) ξ) := by
      intro ξ; rw [hfilt, eval_append, appG_mul, eval_single]
    by_cases hexp : Exposed Ω t
    · obtain ⟨u, htu, hu⟩ := hexp
      obtain ⟨p, rfl⟩ := htu
      refine ⟨p, ypow n ++ dg p, noPC_ypow_dg n p, ⟨_, rfl⟩, fun η => ?_⟩
      rw [hevalt, fixed (t ++ p) η]
      · rw [Stream'.append_append_stream, appG_letter_on, Sem_append, Sem_dg]
      · intro q hq
        obtain ⟨a, ha, hta, hat, hocc⟩ := hA q hq
        refine ⟨a, ha, ?_⟩
        by_contra hinc
        have hat' : a <+: t := hu a (fun h => hinc ⟨h.2, h.1⟩) hocc
        exact hat (hat'.eq_of_length (le_antisymm hat'.length_le hta.length_le))
    · set d := decide (n < 0) with hd
      have hchild : YOccurs Ω (t ++ [d]) := by
        have hse' := hse t ⟨n, memΩ _ hmem⟩ hexp
        rcases lt_or_gt_of_ne hn with h | h
        · have := hse'.2 ⟨n, h, memΩ _ hmem⟩
          simpa [hd, h] using this
        · have := hse'.1 ⟨n, h, memΩ _ hmem⟩
          simpa [hd, show ¬ n < 0 by omega] using this
      obtain ⟨nc, hnc⟩ := occΥ _ hchild
      have hlenc := hB _ _ hnc
      obtain ⟨p', Λ', hnpc, ⟨Λ'', hΛ'⟩, hev⟩ := ih (t ++ [d]) nc (by simp; omega) hnc
      have hnc0 : nc ≠ 0 := hΥ.1 _ hnc
      refine ⟨d :: p', ypow n ++ (dg [d] ++ Λ'), noPC_step hn hnc0 hnpc hΛ', ⟨_, rfl⟩, fun η => ?_⟩
      have hcone : ∀ q ∈ Υa.filter (isExt t),
          ∃ a, q.1 = .y a ∧ (t ++ [d] <+: a ∨ Incompatible (t ++ [d]) a) := by
        intro q hq
        obtain ⟨a, ha, hta, hat, -⟩ := hA q hq
        refine ⟨a, ha, ?_⟩
        obtain ⟨r, rfl⟩ := hta
        rcases r with _ | ⟨e, r⟩
        · simp at hat
        · by_cases he : e = d
          · subst he; left; simp
          · right; exact incompat_app (fun h => he h.symm)
      obtain ⟨η', -, hres⟩ := restrict (t ++ [d]) _ hcone (p' ++ₛ η)
      have hfc : (Υa.filter (isExt t)).filter (isExt (t ++ [d])) = Υ.filter (isExt (t ++ [d])) := by
        have hnot : ¬ (t ++ [d] <+: t) := by
          intro h; have := h.length_le; simp at this
        rw [hsplit, List.filter_append, List.filter_cons, isExt_y, if_neg (by simpa using hnot),
          hfiltb _ (List.prefix_append _ _), List.append_nil, List.filter_filter]
        apply List.filter_congr
        intro q _
        cases h : isExt (t ++ [d]) q
        · rfl
        · simp [isExt_mono (List.prefix_append t [d]) h]
      have e1 : (t ++ d :: p') ++ₛ η = (t ++ [d]) ++ₛ (p' ++ₛ η) := by
        rw [← Stream'.append_append_stream]; simp
      rw [e1, hevalt, hres, hfc, ← Stream'.append_append_stream, hev, Stream'.append_append_stream,
        appG_letter_on, Sem_append, Sem_append, Sem_dg]

theorem lemma511 (Ω : Word) (hΩ : IsStandardForm Ω) (hse : SufficientlyExpanded Ω) :
    IsXWord Ω ∨ ∀ Ξ, IsXWord Ξ → Ω.eval ≠ Ξ.eval := by
  obtain ⟨Ξ₀, Υ, hΩe, hΞ₀, hΥ, hS⟩ := sf_decomp hΩ
  rcases List.eq_nil_or_concat Υ with hnil | ⟨Υ', last, hlast⟩
  · left; subst hnil; rw [hΩe, List.append_nil]; exact hΞ₀
  right
  intro Ξ hΞ heq
  rw [List.concat_eq_append] at hlast
  obtain ⟨t₁, hg⟩ := hΥ.2 last (by rw [hlast]; simp)
  set n₁ := last.2 with hn₁
  have hlast' : last = (.y t₁, n₁) := Prod.ext hg rfl
  have hmem : (Gen.y t₁, n₁) ∈ Υ := by rw [hlast, ← hlast']; simp
  have hn₁0 : n₁ ≠ 0 := hΥ.1 (Gen.y t₁, n₁) hmem
  set B := (Υ.map fun p => match p.1 with | .y t => t.length + 1 | .x _ => 0).sum with hBdef
  have hB : ∀ t k, (Gen.y t, k) ∈ Υ → t.length < B := by
    intro t k h
    have := List.single_le_sum (l := Υ.map fun p => match p.1 with | .y t => t.length + 1 | .x _ => 0)
      (fun _ _ => Nat.zero_le _) _ (List.mem_map.2 ⟨_, h, rfl⟩)
    simp only at this
    omega
  obtain ⟨p, Λ, hnpc, ⟨Λ', hΛ⟩, hev⟩ := claim511 hΩe hΞ₀ hΥ hS hse B hB _ t₁ n₁ le_rfl hmem
  have htop : ∀ q ∈ Υ, ∃ a, q.1 = .y a ∧ (t₁ <+: a ∨ Incompatible t₁ a) := by
    intro q hq
    obtain ⟨a, ha⟩ := hΥ.2 q hq
    refine ⟨a, ha, ?_⟩
    rw [hlast] at hq hS
    rcases List.mem_append.1 hq with hq | hq
    · have hSO := (List.pairwise_append.1 hS).2.2 q hq last (by simp) a t₁ ha hg
      by_cases h : t₁ <+: a
      · exact Or.inl h
      · exact Or.inr ⟨h, hSO⟩
    · simp at hq; subst hq; rw [hg] at ha; simp only [Gen.y.injEq] at ha; subst ha
      exact Or.inl (List.prefix_refl _)
  obtain ⟨u, s, hadv⟩ := exists_advances_append_replicate Λ hnpc
  change Advances (Λ ++ dg u) (dg s ++ _) at hadv
  set N := Λ.countP fun l => l = .y ∨ l = .yinv with hN
  have hN1 : 1 ≤ N := by
    rw [hN, hΛ, List.countP_append]
    have : (ypow n₁).countP (fun l => l = .y ∨ l = .yinv) = n₁.natAbs := by
      unfold ypow
      rw [List.countP_replicate]
      cases decide (0 < n₁) <;> simp
    rw [this]; omega
  have hmemTP : Υ.eval ∈ TPsub := by
    have : Υ.eval = Ξ₀.eval⁻¹ * Ξ.eval := by rw [← heq, hΩe, eval_append]; group
    rw [this]
    exact TPsub.mul_mem (TPsub.inv_mem (xword_mem hΞ₀)) (xword_mem hΞ)
  set ξ := t₁ ++ₛ (p ++ₛ (u ++ₛ Qs N 1)) with hξ
  have key := hmemTP ξ
  obtain ⟨-, -, hres⟩ := restrict t₁ Υ htop (p ++ₛ (u ++ₛ Qs N 1))
  have hval : appG Υ.eval ξ = t₁ ++ₛ (s ++ₛ Qs 0 (2 ^ N * 1)) := by
    rw [hξ, hres, ← Stream'.append_append_stream, hev, ← Sem_dg u, ← Sem_append,
      Sem_advances hadv, Sem_append, Sem_dg]
    congr 2
    rw [← y_iter_Qs]
    exact Sem_rep true N _
  rw [hval] at key
  have k1 := tailEq_of_append key
  have k2 := tailEq_of_append k1
  have k3 := k2.trans' (tailEq_append u (Qs N 1))
  exact not_tailEq_Qs hN1 (by have := Nat.one_le_two_pow (n := N); omega) k3

end LodhaMoore.Dev.S5

namespace LodhaMoore

end LodhaMoore
end

section
open LodhaMoore
theorem solution (Ω : Word) (hΩ : IsStandardForm Ω)
    (hse : SufficientlyExpanded Ω) : IsXWord Ω ∨ ∀ Ξ, IsXWord Ξ → Ω.eval ≠ Ξ.eval :=
  Dev.S5.lemma511 Ω hΩ hse
end
