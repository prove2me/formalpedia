-- Prove2me | solution 1 for LodhaMoore.exists_derives_sufficientlyExpanded
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T11:34:28.771616+00:00
-- url     : https://prove2.me/submissions/c91c273d-c664-40d8-afa7-cd5f301aa6ee

import Mathlib
import Definitions.Def_LodhaMooreWords
import Definitions.Def_LodhaMoore
section
namespace LodhaMoore

theorem Step.context {W W' : Word} (h : Step W W') (p q : Word) :
    Step (p ++ W ++ q) (p ++ W' ++ q) := by
  cases h with
  | moveX pre post s t t' i h =>
    simpa [List.append_assoc] using Step.moveX (p ++ pre) (post ++ q) s t t' i h
  | moveXInv pre post s t t' i h =>
    simpa [List.append_assoc] using Step.moveXInv (p ++ pre) (post ++ q) s t t' i h
  | expand pre post s => simpa [List.append_assoc] using Step.expand (p ++ pre) (post ++ q) s
  | expandInv pre post s => simpa [List.append_assoc] using Step.expandInv (p ++ pre) (post ++ q) s
  | commute pre post u v i j h =>
    simpa [List.append_assoc] using Step.commute (p ++ pre) (post ++ q) u v i j h
  | split pre post g i j hi hj hij =>
    simpa [List.append_assoc] using Step.split (p ++ pre) (post ++ q) g i j hi hj hij
  | merge pre post g i j hi hj hij =>
    simpa [List.append_assoc] using Step.merge (p ++ pre) (post ++ q) g i j hi hj hij
  | cancel pre post s i hi => simpa [List.append_assoc] using Step.cancel (p ++ pre) (post ++ q) s i hi

theorem Derives.context {W W' : Word} (h : Derives W W') (p q : Word) :
    Derives (p ++ W ++ q) (p ++ W' ++ q) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (hs.context p q)

theorem xFin_of_incompatible {s t : Seq} (h : Incompatible s t) : xFin s t = some t := by
  unfold xFin; rw [if_neg h.1, if_neg h.2]

theorem xFinInv_of_incompatible {s t : Seq} (h : Incompatible s t) : xFinInv s t = some t := by
  unfold xFinInv; rw [if_neg h.1, if_neg h.2]

end LodhaMoore
end

section
namespace LodhaMoore

/-- The tail action of `x` on finite sequences: `00r ↦ 0r`, `01r ↦ 10r`, `1r ↦ 11r`. -/
def xr : List Bool → Option (List Bool)
  | false :: false :: r => some (false :: r)
  | false :: true :: r => some (true :: false :: r)
  | true :: r => some (true :: true :: r)
  | _ => none

/-- The tail action of `x⁻¹`: `0r ↦ 00r`, `10r ↦ 01r`, `11r ↦ 1r`. -/
def xrInv : List Bool → Option (List Bool)
  | false :: r => some (false :: false :: r)
  | true :: false :: r => some (false :: true :: r)
  | true :: true :: r => some (true :: r)
  | _ => none

theorem xFin_append (s r : Seq) : xFin s (s ++ r) = (xr r).map (s ++ ·) := by
  unfold xFin
  rw [if_pos (List.prefix_append _ _)]
  simp only [List.drop_left]
  rcases r with _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩ <;> rfl

theorem xFinInv_append (s r : Seq) : xFinInv s (s ++ r) = (xrInv r).map (s ++ ·) := by
  unfold xFinInv
  rw [if_pos (List.prefix_append _ _)]
  simp only [List.drop_left]
  rcases r with _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩ <;> rfl

theorem xr_prefix {r q r' q' : List Bool} (hr : xr r = some r') (hq : xr q = some q')
    (h : r' <+: q') : r <+: q := by
  rcases r with _ | ⟨_ | _, _ | ⟨_ | _, r⟩⟩ <;> rcases q with _ | ⟨_ | _, _ | ⟨_ | _, q⟩⟩ <;>
    simp only [xr, reduceCtorEq, Option.some.injEq] at hr hq <;> (try subst hr) <;> (try subst hq) <;>
    simp_all [List.cons_prefix_cons]

theorem xrInv_prefix {r q r' q' : List Bool} (hr : xrInv r = some r') (hq : xrInv q = some q')
    (h : r' <+: q') : r <+: q := by
  rcases r with _ | ⟨_ | _, _ | ⟨_ | _, r⟩⟩ <;> rcases q with _ | ⟨_ | _, _ | ⟨_ | _, q⟩⟩ <;>
    simp only [xrInv, reduceCtorEq, Option.some.injEq] at hr hq <;> (try subst hr) <;> (try subst hq) <;>
    simp_all [List.cons_prefix_cons]

/-- `t.x_s^e` for `e = ±1`. -/
def xAct (e : ℤ) (s t : Seq) : Option Seq := if e = 1 then xFin s t else xFinInv s t

theorem step_moveX_e {e : ℤ} (he : e = 1 ∨ e = -1) (pre post : Word) (s t t' : Seq) (i : ℤ)
    (h : xAct e s t = some t') :
    Step (pre ++ [(.y t, i), (.x s, e)] ++ post) (pre ++ [(.x s, e), (.y t', i)] ++ post) := by
  rcases he with rfl | rfl
  · exact Step.moveX pre post s t t' i (by simpa [xAct] using h)
  · exact Step.moveXInv pre post s t t' i (by simpa [xAct] using h)

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

/-- Weak order: the first index is an initial part of the second only if they are equal. -/
def WOr (p q : Gen × ℤ) : Prop := ∀ a b, p.1 = .y a → q.1 = .y b → a <+: b → a = b

theorem SO.wor {p q : Gen × ℤ} (h : SO p q) : WOr p q := fun a b ha hb hab => absurd hab (h a b ha hb)

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

theorem rawProf_append (A B : Word) (d : ℕ) : rawProf (A ++ B) d = rawProf A d + rawProf B d := by
  simp [rawProf]

theorem rawProf_cons (p : Gen × ℤ) (W : Word) (d : ℕ) :
    rawProf (p :: W) d = rawProf [p] d + rawProf W d := by
  simp [rawProf]

theorem rawProf_perm {A B : Word} (h : A.Perm B) (d : ℕ) : rawProf A d = rawProf B d := by
  unfold rawProf; exact (h.map _).sum_eq

/-! ### Moving letters -/

theorem _root_.LodhaMoore.Derives.tr {a b c : Word} (h1 : Derives a b) (h2 : Derives b c) : Derives a c :=
  Relation.ReflTransGen.trans h1 h2

theorem _root_.LodhaMoore.Derives.rfl' {a : Word} : Derives a a := Relation.ReflTransGen.refl

theorem derives_single {W W' : Word} (h : Step W W') : Derives W W' := Relation.ReflTransGen.single h

theorem derives_cons {W W' : Word} (p : Gen × ℤ) (h : Derives W W') : Derives (p :: W) (p :: W') := by
  simpa using h.context [p] []

theorem derives_append_left {W W' : Word} (A : Word) (h : Derives W W') : Derives (A ++ W) (A ++ W') := by
  simpa using h.context A []

theorem derives_append_right {W W' : Word} (B : Word) (h : Derives W W') : Derives (W ++ B) (W' ++ B) := by
  simpa using h.context [] B

/-- Moving a `y`-letter right past letters with incompatible indices. -/
theorem derives_pass_right {a : Seq} {k : ℤ} :
    ∀ L : Word, (∀ q ∈ L, ∃ b, q.1 = .y b ∧ Incompatible a b) →
      Derives ((.y a, k) :: L) (L ++ [(.y a, k)])
  | [], _ => Relation.ReflTransGen.refl
  | q :: L, h => by
    obtain ⟨b, hb, hab⟩ := h q (by simp)
    obtain ⟨g, j⟩ := q
    simp only at hb
    subst hb
    have h1 : Derives ((.y a, k) :: (.y b, j) :: L) ((.y b, j) :: (.y a, k) :: L) := by
      have := Step.commute [] L a b k j hab
      simpa using derives_single this
    have h2 := derives_cons (.y b, j) (derives_pass_right (k := k) L (fun q hq => h q (by simp [hq])))
    exact h1.tr (by simpa using h2)

/-- Partition a `Y`-word into its `y_t`-letters and the rest. -/
theorem derives_partition (t : Seq) :
    ∀ R : Word, (∀ p ∈ R, ∃ a, p.1 = .y a) →
      R.Pairwise (fun p q => p.1 ≠ .y t → q.1 = .y t → ∃ a, p.1 = .y a ∧ Incompatible a t) →
      Derives R (R.filter (fun p => decide (p.1 = .y t)) ++ R.filter (fun p => !decide (p.1 = .y t)))
  | [], _, _ => Relation.ReflTransGen.refl
  | p :: R, hY, hP => by
    rw [List.pairwise_cons] at hP
    have ih := derives_partition t R (fun q hq => hY q (by simp [hq])) hP.2
    by_cases hp : p.1 = .y t
    · simp only [List.filter_cons, hp, decide_true, if_true, Bool.not_true]
      simpa using derives_cons p ih
    · simp only [List.filter_cons, hp, decide_false, Bool.not_false, if_true]
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine (derives_cons p ih).trans ?_
      obtain ⟨a, ha⟩ := hY p (by simp)
      obtain ⟨g, k⟩ := p
      simp only at ha hp
      subst ha
      have := derives_pass_right (a := a) (k := k) (R.filter (fun p => decide (p.1 = .y t))) (by
        intro q hq
        rw [List.mem_filter] at hq
        have hq2 : q.1 = .y t := by simpa using hq.2
        obtain ⟨a', ha', hinc⟩ := hP.1 q hq.1 hp hq2
        simp only [Gen.y.injEq] at ha'
        subst ha'
        exact ⟨t, hq2, hinc⟩)
      have := derives_append_right (R.filter (fun p => !decide (p.1 = .y t))) this
      simp only [List.cons_append, List.append_assoc] at this ⊢
      exact this

/-- The letter `y_t^c`, or nothing when `c = 0`. -/
def lc (t : Seq) (c : ℤ) : Word := if c = 0 then [] else [(.y t, c)]

theorem derives_merge2 (t : Seq) (c b : ℤ) (hb : b ≠ 0) (W : Word) :
    Derives (lc t c ++ (.y t, b) :: W) (lc t (c + b) ++ W) := by
  by_cases hc : c = 0
  · subst hc; simp [lc, hb]; exact Relation.ReflTransGen.refl
  simp only [lc, hc, if_false]
  by_cases hcb : c + b = 0
  · have hb' : b = -c := by omega
    subst hb'
    simp only [hcb, if_true, List.nil_append]
    simpa using derives_single (Step.cancel [] W t c hc)
  simp only [hcb, if_false]
  rcases lt_or_gt_of_ne hc with hc' | hc' <;> rcases lt_or_gt_of_ne hb with hb' | hb'
  · simpa using derives_single (Step.merge [] W (.y t) c b hc hb (by nlinarith))
  · -- c < 0 < b
    rcases lt_or_gt_of_ne hcb with h | h
    · -- |c| > |b|: split c = (c + b) + (-b)
      have s1 := Step.split [] ((.y t, b) :: W) (.y t) (c + b) (-b) hcb (by omega) (by nlinarith)
      rw [show c + b + -b = c by ring] at s1
      have s2 := Step.cancel [(.y t, c + b)] W t (-b) (by omega)
      rw [neg_neg] at s2
      exact (derives_single (by simpa using s1)).tr (derives_single (by simpa using s2))
    · have s1 := Step.split [(.y t, c)] W (.y t) (-c) (c + b) (by omega) hcb (by nlinarith)
      rw [show -c + (c + b) = b by ring] at s1
      have s2 := Step.cancel [] ((.y t, c + b) :: W) t c hc
      exact (derives_single (by simpa using s1)).tr (derives_single (by simpa using s2))
  · -- b < 0 < c
    rcases lt_or_gt_of_ne hcb with h | h
    · have s1 := Step.split [(.y t, c)] W (.y t) (-c) (c + b) (by omega) hcb (by nlinarith)
      rw [show -c + (c + b) = b by ring] at s1
      have s2 := Step.cancel [] ((.y t, c + b) :: W) t c hc
      exact (derives_single (by simpa using s1)).tr (derives_single (by simpa using s2))
    · have s1 := Step.split [] ((.y t, b) :: W) (.y t) (c + b) (-b) hcb (by omega) (by nlinarith)
      rw [show c + b + -b = c by ring] at s1
      have s2 := Step.cancel [(.y t, c + b)] W t (-b) (by omega)
      rw [neg_neg] at s2
      exact (derives_single (by simpa using s1)).tr (derives_single (by simpa using s2))
  · simpa using derives_single (Step.merge [] W (.y t) c b hc hb (by nlinarith))

theorem derives_merge (t : Seq) (W : Word) :
    ∀ (R : Word) (c : ℤ), (∀ p ∈ R, p.1 = .y t ∧ p.2 ≠ 0) →
      Derives (lc t c ++ R ++ W) (lc t (c + (R.map Prod.snd).sum) ++ W)
  | [], c, _ => by simpa using (Derives.rfl' : Derives (lc t c ++ W) _)
  | p :: R, c, h => by
    obtain ⟨hp1, hp2⟩ := h p (by simp)
    obtain ⟨g, b⟩ := p
    simp only at hp1 hp2
    subst hp1
    have h1 := derives_merge2 t c b hp2 (R ++ W)
    have h2 := derives_merge t W R (c + b) (fun q hq => h q (by simp [hq]))
    simp only [List.map_cons, List.sum_cons]
    rw [show c + (b + (R.map Prod.snd).sum) = c + b + (R.map Prod.snd).sum by ring]
    exact (by simpa using h1 : Derives (lc t c ++ (Gen.y t, b) :: R ++ W) (lc t (c + b) ++ R ++ W)).trans h2

theorem rawProf_lc (t : Seq) (c : ℤ) (d : ℕ) :
    rawProf (lc t c) d = if t.length = d then c.natAbs else 0 := by
  unfold lc rawProf
  by_cases hc : c = 0
  · subst hc; simp
  · simp [hc]

theorem rawProf_lc_le (t : Seq) (c : ℤ) (R : Word) (hR : ∀ p ∈ R, p.1 = .y t) (d : ℕ) :
    rawProf (lc t (c + (R.map Prod.snd).sum)) d ≤ rawProf (lc t c) d + rawProf R d := by
  induction R generalizing c with
  | nil => simp
  | cons p R ih =>
    obtain ⟨g, b⟩ := p
    have hg : g = .y t := hR (g, b) (by simp)
    subst hg
    have := ih (c + b) (fun q hq => hR q (by simp [hq]))
    simp only [List.map_cons, List.sum_cons]
    rw [show c + (b + (R.map Prod.snd).sum) = c + b + (R.map Prod.snd).sum by ring]
    refine this.trans ?_
    rw [rawProf_cons (.y t, b) R d]
    have key : rawProf (lc t (c + b)) d ≤ rawProf (lc t c) d + rawProf [(.y t, b)] d := by
      rw [rawProf_lc, rawProf_lc]
      simp only [rawProf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      split_ifs
      · exact Int.natAbs_add_le c b
      · omega
    omega

/-- Canonicalization: a weakly ordered `Y`-word derives a standard `Y`-word. -/
theorem canon : ∀ (n : ℕ) (V : Word), V.length ≤ n → IsYWord V → V.Pairwise WOr →
    ∃ V', Derives V V' ∧ IsYWord V' ∧ V'.Pairwise SO ∧
      (∀ t k, (Gen.y t, k) ∈ V' → ∃ k', (Gen.y t, k') ∈ V) ∧ ∀ d, rawProf V' d ≤ rawProf V d := by
  intro n
  induction n with
  | zero =>
    intro V hV _ _
    have : V = [] := List.length_eq_zero_iff.1 (by omega)
    subst this
    exact ⟨[], Relation.ReflTransGen.refl, ⟨by simp [IsWord], by simp⟩, by simp, by simp, by simp⟩
  | succ n ih =>
    intro V hV hY hW
    match V, hV, hY, hW with
    | [], _, _, _ =>
      exact ⟨[], Relation.ReflTransGen.refl, ⟨by simp [IsWord], by simp⟩, by simp, by simp, by simp⟩
    | (g, k) :: R, hV, hY, hW =>
      obtain ⟨t, hg⟩ := hY.2 (g, k) List.mem_cons_self
      simp only at hg
      subst hg
      have hk : k ≠ 0 := hY.1 (Gen.y t, k) List.mem_cons_self
      rw [List.pairwise_cons] at hW
      set Rt := R.filter (fun p => decide (p.1 = .y t)) with hRt
      set Ro := R.filter (fun p => !decide (p.1 = .y t)) with hRo
      have hRY : ∀ p ∈ R, ∃ a, p.1 = .y a := fun p hp => hY.2 p (by simp [hp])
      -- step 1: partition
      have d1 : Derives R (Rt ++ Ro) := by
        apply derives_partition t R hRY
        refine hW.2.imp_of_mem ?_
        intro p q hp hq hpq hpt hqt
        obtain ⟨a, ha⟩ := hRY p hp
        refine ⟨a, ha, ?_, ?_⟩
        · intro hat
          have := hpq a t ha hqt hat
          subst this; exact hpt ha
        · intro hta
          have := hW.1 p hp t a rfl ha hta
          subst this; exact hpt ha
      -- step 2: merge
      have hRt : ∀ p ∈ Rt, p.1 = .y t ∧ p.2 ≠ 0 := by
        intro p hp
        rw [hRt, List.mem_filter] at hp
        exact ⟨by simpa using hp.2, hY.1 p (by simp [hp.1])⟩
      set K := k + (Rt.map Prod.snd).sum with hK
      have d2 : Derives ((.y t, k) :: Rt ++ Ro) (lc t K ++ Ro) := by
        have := derives_merge t Ro Rt k hRt
        simpa [lc, hk] using this
      -- step 3: recurse on Ro
      have hRoY : IsYWord Ro := ⟨fun p hp => hY.1 p (by simp [(List.mem_filter.1 hp).1]),
        fun p hp => hY.2 p (by simp [(List.mem_filter.1 hp).1])⟩
      have hRoW : Ro.Pairwise WOr := hW.2.filter _
      have hRolen : Ro.length ≤ n := by
        have := List.length_filter_le (fun p => !decide (p.1 = Gen.y t)) R
        rw [← hRo] at this
        simp at hV; omega
      obtain ⟨Vo, d3, hVoY, hVoS, hVoI, hVoP⟩ := ih Ro hRolen hRoY hRoW
      have hVo_ne : ∀ b j, (Gen.y b, j) ∈ Vo → b ≠ t ∧ ¬ t <+: b := by
        intro b j hb
        obtain ⟨j', hj'⟩ := hVoI b j hb
        have hmem := List.mem_filter.1 hj'
        have hbt : b ≠ t := by intro h; subst h; simp at hmem
        exact ⟨hbt, fun htb => hbt (hW.1 _ hmem.1 t b rfl rfl htb).symm⟩
      refine ⟨lc t K ++ Vo, ?_, ?_, ?_, ?_, ?_⟩
      · refine (derives_cons _ d1).trans ?_
        refine (by simpa using d2 : Derives ((Gen.y t, k) :: (Rt ++ Ro)) (lc t K ++ Ro)).trans ?_
        exact derives_append_left _ d3
      · constructor
        · intro p hp
          rcases List.mem_append.1 hp with hp | hp
          · unfold lc at hp; split_ifs at hp with hK0
            · simp at hp
            · simp at hp; subst hp; exact hK0
          · exact hVoY.1 p hp
        · intro p hp
          rcases List.mem_append.1 hp with hp | hp
          · unfold lc at hp; split_ifs at hp
            · simp at hp
            · simp at hp; subst hp; exact ⟨t, rfl⟩
          · exact hVoY.2 p hp
      · rw [List.pairwise_append]
        refine ⟨?_, hVoS, ?_⟩
        · unfold lc; split_ifs <;> simp
        · intro p hp q hq a b ha hb hab
          unfold lc at hp; split_ifs at hp
          · simp at hp
          simp at hp; subst hp
          simp only [Gen.y.injEq] at ha; subst ha
          obtain ⟨b', hb'⟩ := hVoY.2 q hq
          rw [hb] at hb'; simp only [Gen.y.injEq] at hb'; subst hb'
          exact (hVo_ne b q.2 (by rw [← hb]; exact hq)).2 hab
      · intro u j hu
        rcases List.mem_append.1 hu with hu | hu
        · unfold lc at hu; split_ifs at hu
          · simp at hu
          simp at hu; obtain ⟨rfl, -⟩ := hu; exact ⟨k, by simp⟩
        · obtain ⟨j', hj'⟩ := hVoI u j hu
          exact ⟨j', by simp [(List.mem_filter.1 hj').1]⟩
      · intro d
        have hperm : (Rt ++ Ro).Perm R := List.filter_append_perm _ R
        have e1 : rawProf ((Gen.y t, k) :: R) d = rawProf (lc t k) d + rawProf Rt d + rawProf Ro d := by
          rw [rawProf_cons, ← rawProf_perm hperm, rawProf_append]
          simp [lc, hk]; omega
        rw [e1, rawProf_append]
        have := rawProf_lc_le t k Rt (fun p hp => (hRt p hp).1) d
        rw [← hK] at this
        have := hVoP d
        omega


/-! ### Standard forms as `X`-word plus strictly ordered `Y`-word -/

theorem xword_noy {Ξ : Word} (h : IsXWord Ξ) : ∀ p ∈ Ξ, ∀ t, p.1 ≠ .y t := by
  intro p hp t ht; obtain ⟨u, hu⟩ := h.2 p hp; rw [hu] at ht; cases ht

theorem sf_decomp {Ω : Word} (h : IsStandardForm Ω) :
    ∃ Ξ Υ, Ω = Ξ ++ Υ ∧ IsXWord Ξ ∧ IsYWord Υ ∧ Υ.Pairwise SO := by
  obtain ⟨-, ⟨Ξ, Υ, rfl, hΞ, hΥ⟩, hoc⟩ := h
  exact ⟨Ξ, Υ, rfl, hΞ, hΥ, (oc_iff_pairwise Υ).1 ((oc_append (xword_noy hΞ)).1 hoc)⟩

theorem sf_of {Ξ Υ : Word} (hΞ : IsXWord Ξ) (hΥ : IsYWord Υ) (hS : Υ.Pairwise SO) :
    IsStandardForm (Ξ ++ Υ) := by
  refine ⟨?_, ⟨Ξ, Υ, rfl, hΞ, hΥ⟩, ?_⟩
  · intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hΞ.1 p hp
    · exact hΥ.1 p hp
  · show OC _
    rw [oc_append (xword_noy hΞ), oc_iff_pairwise]
    exact hS

theorem rawProf_xword {Ξ : Word} (h : IsXWord Ξ) (d : ℕ) : rawProf Ξ d = 0 := by
  induction Ξ with
  | nil => rfl
  | cons p Ξ ih =>
    rw [rawProf_cons, ih ⟨fun q hq => h.1 q (by simp [hq]), fun q hq => h.2 q (by simp [hq])⟩]
    obtain ⟨u, hu⟩ := h.2 p (by simp)
    simp [rawProf, hu]

/-! ### Prefix closures -/

/-- The finite set of initial parts of the indices of the `y`-letters of `W`. -/
def PCset (W : Word) : Finset Seq :=
  (W.flatMap fun p => match p.1 with | .y t => t.inits | .x _ => []).toFinset

theorem mem_PCset {W : Word} {t : Seq} : t ∈ PCset W ↔ ∃ o k, (Gen.y o, k) ∈ W ∧ t <+: o := by
  simp only [PCset, List.mem_toFinset, List.mem_flatMap]
  constructor
  · rintro ⟨⟨g, k⟩, hp, ht⟩
    cases g with
    | x u => simp at ht
    | y o => exact ⟨o, k, hp, (List.mem_inits _ _).1 ht⟩
  · rintro ⟨o, k, hp, ht⟩
    exact ⟨(.y o, k), hp, (List.mem_inits _ _).2 ht⟩

theorem length_lt_card_PCset {W : Word} {t : Seq} {k : ℤ} (h : (Gen.y t, k) ∈ W) :
    t.length < (PCset W).card := by
  have hsub : (Finset.range (t.length + 1)).image (fun i => t.take i) ⊆ PCset W := by
    intro u hu
    simp only [Finset.mem_image, Finset.mem_range] at hu
    obtain ⟨i, -, rfl⟩ := hu
    exact mem_PCset.2 ⟨t, k, h, List.take_prefix _ _⟩
  have hinj : Set.InjOn (fun i => t.take i) (Finset.range (t.length + 1) : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have := congrArg List.length hij
    simp at this; omega
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at this
  omega

/-! ### The action of `x_s^{±1}` on indices -/

/-- The child of `s` whose `y`-letter is absent when `y_s` is expanded with `x_s^e`. -/
def cb (e : ℤ) : Bool := if e = 1 then false else true

/-- The tail action of `x^e`. -/
def xrE (e : ℤ) : List Bool → Option (List Bool) := if e = 1 then xr else xrInv

theorem xAct_append {e : ℤ} (he : e = 1 ∨ e = -1) (s r : Seq) :
    xAct e s (s ++ r) = (xrE e r).map (s ++ ·) := by
  rcases he with rfl | rfl
  · simp [xAct, xrE, xFin_append]
  · simp [xAct, xrE, xFinInv_append]

theorem xAct_incomp {e : ℤ} (he : e = 1 ∨ e = -1) {s t : Seq} (h : Incompatible s t) :
    xAct e s t = some t := by
  rcases he with rfl | rfl
  · simp [xAct, xFin_of_incompatible h]
  · simp [xAct, xFinInv_of_incompatible h]

theorem xrE_some {e : ℤ} (he : e = 1 ∨ e = -1) {r : List Bool} (h0 : r ≠ []) (h1 : r ≠ [cb e]) :
    ∃ r', xrE e r = some r' := by
  rcases he with rfl | rfl <;> rcases r with _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩ <;> simp_all [xrE, xr, xrInv, cb]

theorem xrE_img {e : ℤ} (he : e = 1 ∨ e = -1) {r r' : List Bool} (h : xrE e r = some r') :
    r' ≠ [] ∧ r' ≠ [!cb e] := by
  rcases he with rfl | rfl <;> rcases r with _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩ <;>
    simp [xrE, xr, xrInv, cb] at h ⊢ <;> subst h <;> simp

theorem xrE_prefix {e : ℤ} (he : e = 1 ∨ e = -1) {r q r' q' : List Bool} (hr : xrE e r = some r')
    (hq : xrE e q = some q') (h : r' <+: q') : r <+: q := by
  rcases he with rfl | rfl
  · exact xr_prefix (by simpa [xrE] using hr) (by simpa [xrE] using hq) h
  · exact xrInv_prefix (by simpa [xrE] using hr) (by simpa [xrE] using hq) h

theorem dom_fact {e : ℤ} (he : e = 1 ∨ e = -1) {s a : Seq} (h1 : ¬ a <+: s) (h2 : a ≠ s ++ [cb e]) :
    ∃ a', xAct e s a = some a' ∧
      ((Incompatible s a ∧ a' = a) ∨ ∃ r r', a = s ++ r ∧ a' = s ++ r' ∧ xrE e r = some r') := by
  by_cases hsa : s <+: a
  · obtain ⟨r, rfl⟩ := hsa
    have hr0 : r ≠ [] := by rintro rfl; simp at h1
    have hr1 : r ≠ [cb e] := by rintro rfl; exact h2 rfl
    obtain ⟨r', hr'⟩ := xrE_some he hr0 hr1
    exact ⟨s ++ r', by rw [xAct_append he, hr']; rfl, Or.inr ⟨r, r', rfl, rfl, hr'⟩⟩
  · exact ⟨a, xAct_incomp he ⟨hsa, h1⟩, Or.inl ⟨⟨hsa, h1⟩, rfl⟩⟩

/-- The moved index: `t.x_s^e` when defined. -/
def act (e : ℤ) (s t : Seq) : Seq := (xAct e s t).getD t

/-- A letter after `x_s^e` has moved left past it. -/
def mv (e : ℤ) (s : Seq) (p : Gen × ℤ) : Gen × ℤ :=
  match p.1 with
  | .y t => (.y (act e s t), p.2)
  | .x u => (.x u, p.2)

theorem derives_moveX_mv {s : Seq} {e : ℤ} (he : e = 1 ∨ e = -1) :
    ∀ Υ : Word, (∀ p ∈ Υ, ∃ t t', p.1 = .y t ∧ xAct e s t = some t') →
      Derives (Υ ++ [(.x s, e)]) ((.x s, e) :: Υ.map (mv e s))
  | [], _ => Derives.rfl'
  | (g, i) :: Υ, h => by
    obtain ⟨t, t', hg, ht'⟩ := h (g, i) List.mem_cons_self
    simp only at hg
    subst hg
    have ih := derives_moveX_mv he Υ (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have h1 := derives_cons (.y t, i) ih
    have h2 := derives_single (step_moveX_e he [] (Υ.map (mv e s)) s t t' i ht')
    have hmv : mv e s (.y t, i) = (.y t', i) := by simp [mv, act, ht']
    simp only [List.map_cons, hmv]
    exact (by simpa using h1 : Derives ((Gen.y t, i) :: Υ ++ [(.x s, e)])
      ((.y t, i) :: (.x s, e) :: Υ.map (mv e s))).tr (by simpa using h2)

/-! ### The inverse of the tail action, for the prefix closures -/

/-- The inverse of `x^e` on tails, extended by `[] ↦ []` and `[!cb e] ↦ [cb e]`. -/
def psi (e : ℤ) (r : List Bool) : List Bool :=
  if e = 1 then
    match r with
    | [] => []
    | [true] => [false]
    | false :: r => false :: false :: r
    | true :: false :: r => false :: true :: r
    | true :: true :: r => true :: r
  else
    match r with
    | [] => []
    | [false] => [true]
    | false :: false :: r => false :: r
    | false :: true :: r => true :: false :: r
    | true :: r => true :: true :: r

theorem psi_xrE {e : ℤ} (he : e = 1 ∨ e = -1) {r r' : List Bool} (h : xrE e r = some r') :
    psi e r' = r := by
  rcases he with rfl | rfl <;> rcases r with _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩ <;>
    simp [xrE, xr, xrInv] at h ⊢ <;> subst h <;> simp [psi]

theorem psi_inj {e : ℤ} (he : e = 1 ∨ e = -1) {a b : List Bool} (h : psi e a = psi e b) : a = b := by
  rcases he with rfl | rfl <;> rcases a with _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩ <;>
    rcases b with _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩ <;> simp_all [psi]

theorem psi_mono {e : ℤ} (he : e = 1 ∨ e = -1) {q r : List Bool} (h : q <+: r) (hq : q ≠ [!cb e]) :
    psi e q <+: psi e r := by
  obtain ⟨x, rfl⟩ := h
  rcases he with rfl | rfl <;> rcases q with _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩ <;>
    simp_all [psi, cb]

theorem psi_special {e : ℤ} (he : e = 1 ∨ e = -1) : psi e [!cb e] = [cb e] := by
  rcases he with rfl | rfl <;> simp [psi, cb]

/-- The inverse of `x_s^e` on indices, extended. -/
def phi (e : ℤ) (s t : Seq) : Seq := if s <+: t then s ++ psi e (t.drop s.length) else t

theorem phi_append (e : ℤ) (s r : Seq) : phi e s (s ++ r) = s ++ psi e r := by
  simp [phi]

theorem phi_not {e : ℤ} {s t : Seq} (h : ¬ s <+: t) : phi e s t = t := by simp [phi, h]

theorem phi_inj {e : ℤ} (he : e = 1 ∨ e = -1) (s : Seq) : Function.Injective (phi e s) := by
  intro a b h
  by_cases ha : s <+: a <;> by_cases hb : s <+: b
  · obtain ⟨r, rfl⟩ := ha
    obtain ⟨q, rfl⟩ := hb
    rw [phi_append, phi_append] at h
    rw [psi_inj he (List.append_cancel_left h)]
  · obtain ⟨r, rfl⟩ := ha
    rw [phi_append, phi_not hb] at h
    exact absurd (h ▸ List.prefix_append s _) hb
  · obtain ⟨q, rfl⟩ := hb
    rw [phi_append, phi_not ha] at h
    exact absurd (h ▸ List.prefix_append s _) ha
  · rwa [phi_not ha, phi_not hb] at h

/-- `phi` of an initial part of a moved index or of a new index. -/
theorem phi_prefix {e : ℤ} (he : e = 1 ∨ e = -1) {s t r : Seq} (h : t <+: s ++ r) :
    phi e s t <+: s ∨ phi e s t = s ++ [cb e] ∨ phi e s t <+: s ++ psi e r := by
  by_cases hst : s <+: t
  · obtain ⟨q, rfl⟩ := hst
    rw [phi_append]
    rw [List.prefix_append_right_inj] at h
    by_cases hq : q = [!cb e]
    · subst hq; right; left; rw [psi_special he]
    · right; right; rw [List.prefix_append_right_inj]; exact psi_mono he h hq
  · left
    rw [phi_not hst]
    rcases List.prefix_or_prefix_of_prefix h (List.prefix_append s r) with h' | h'
    · exact h'
    · exact absurd h' hst

/-! ### The new letters -/

/-- The tails of the three new indices of the expansion with `x_s^e`. -/
def ct (e : ℤ) : List (List Bool) :=
  if e = 1 then [[false], [true, false], [true, true]] else [[false, false], [false, true], [true]]

/-- The letters the expansion of `y_s^e` introduces after `x_s^e`. -/
def newL (e : ℤ) (s : Seq) : Word :=
  if e = 1 then [(.y (s ++ [false]), 1), (.y (s ++ [true, false]), -1), (.y (s ++ [true, true]), 1)]
  else [(.y (s ++ [false, false]), -1), (.y (s ++ [false, true]), 1), (.y (s ++ [true]), -1)]

theorem derives_expand {e : ℤ} (he : e = 1 ∨ e = -1) (s : Seq) (W : Word) :
    Derives ((.y s, e) :: W) ((.x s, e) :: (newL e s ++ W)) := by
  rcases he with rfl | rfl
  · simpa [newL] using derives_single (Step.expand [] W s)
  · simpa [newL] using derives_single (Step.expandInv [] W s)

theorem mem_newL {e : ℤ} (he : e = 1 ∨ e = -1) {s : Seq} {p : Gen × ℤ} (hp : p ∈ newL e s) :
    ∃ c ∈ ct e, p.1 = .y (s ++ c) ∧ p.2 ≠ 0 := by
  rcases he with rfl | rfl <;> simp [newL, ct] at hp ⊢ <;> rcases hp with rfl | rfl | rfl <;> simp

theorem ct_ne_nil {e : ℤ} (he : e = 1 ∨ e = -1) {c : List Bool} (hc : c ∈ ct e) : c ≠ [] := by
  rcases he with rfl | rfl <;> simp [ct] at hc <;> rcases hc with rfl | rfl | rfl <;> simp

/-- An image tail that is an initial part of a new tail equals it. -/
theorem ct_prefix {e : ℤ} (he : e = 1 ∨ e = -1) {c r' : List Bool} (hc : c ∈ ct e) (h0 : r' ≠ [])
    (h1 : r' ≠ [!cb e]) (h : r' <+: c) : r' = c := by
  obtain ⟨x, rfl⟩ := h
  rcases he with rfl | rfl <;> simp [ct, cb] at hc h1 <;>
    rcases r' with _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩ <;> simp_all

theorem newL_pairwise {e : ℤ} (he : e = 1 ∨ e = -1) (s : Seq) : (newL e s).Pairwise SO := by
  rcases he with rfl | rfl <;> simp [newL, SO]

theorem isYWord_newL {e : ℤ} (he : e = 1 ∨ e = -1) (s : Seq) : IsYWord (newL e s) := by
  constructor
  · intro p hp; obtain ⟨c, -, -, h⟩ := mem_newL he hp; exact h
  · intro p hp; obtain ⟨c, -, h, -⟩ := mem_newL he hp; exact ⟨_, h⟩

theorem rawProf_newL {e : ℤ} (he : e = 1 ∨ e = -1) (s : Seq) {d : ℕ} (hd : d ≤ s.length) :
    rawProf (newL e s) d = 0 := by
  rcases he with rfl | rfl <;> simp [newL, rawProf] <;> omega

/-- The covering consequence of `s` not being exposed. -/
theorem cover {Ω : Word} {s : Seq} {e : ℤ} (he : e = 1 ∨ e = -1) (hexp : ¬ Exposed Ω s)
    (hnot : ¬ YOccurs Ω (s ++ [cb e])) {c : List Bool} (hc : c ∈ ct e) :
    ∃ o k, (Gen.y o, k) ∈ Ω ∧ s ++ psi e c <+: o := by
  have hcne : psi e c ≠ [] := by
    rcases he with rfl | rfl <;> simp [ct] at hc <;> rcases hc with rfl | rfl | rfl <;> simp [psi]
  unfold Exposed at hexp
  push Not at hexp
  obtain ⟨t, hinc, ⟨k, hk⟩, hts⟩ := hexp (s ++ psi e c) (List.prefix_append _ _)
  have hcomp : t <+: s ++ psi e c ∨ s ++ psi e c <+: t := by
    by_contra hh; push Not at hh; exact hinc ⟨hh.1, hh.2⟩
  rcases hcomp with h | h
  · -- `t` is `s` followed by a nonempty initial part of `psi e c`
    have hst : s <+: t := by
      rcases List.prefix_or_prefix_of_prefix h (List.prefix_append s _) with h' | h'
      · exact absurd h' hts
      · exact h'
    obtain ⟨q, rfl⟩ := hst
    rw [List.prefix_append_right_inj] at h
    have hq0 : q ≠ [] := by rintro rfl; simp at hts
    obtain ⟨x, hx⟩ := h
    by_cases hqc : q = psi e c
    · subst hqc; exact ⟨s ++ psi e c, k, hk, List.prefix_refl _⟩
    · exfalso
      apply hnot
      refine ⟨k, ?_⟩
      convert hk using 3
      rcases he with rfl | rfl <;> simp [ct] at hc <;> rcases hc with rfl | rfl | rfl <;>
        rcases q with _ | ⟨_ | _, _ | ⟨_ | _, _⟩⟩ <;> simp_all [psi, cb]
  · exact ⟨t, k, hk, h⟩

theorem mem_lc {t : Seq} {c : ℤ} {q : Gen × ℤ} (h : q ∈ lc t c) : q = (.y t, c) ∧ c ≠ 0 := by
  unfold lc at h; split_ifs at h with hc
  · simp at h
  · simp at h; exact ⟨h, hc⟩

theorem xrE_ne_nil {e : ℤ} (he : e = 1 ∨ e = -1) {r r' : List Bool} (h : xrE e r = some r') :
    r ≠ [] := by
  rintro rfl; rcases he with rfl | rfl <;> simp [xrE, xr, xrInv] at h

theorem cb_le_psi {e : ℤ} (he : e = 1 ∨ e = -1) : ∃ c ∈ ct e, [cb e] <+: psi e c := by
  rcases he with rfl | rfl
  · exact ⟨[false], by simp [ct], by simp [psi, cb]⟩
  · exact ⟨[false, true], by simp [ct], by simp [psi, cb]⟩

/-- How an index changes when `x_s^e` moves left past it. -/
def MovedIdx (e : ℤ) (s a a' : Seq) : Prop :=
  (Incompatible s a ∧ a' = a) ∨ ∃ r r', a = s ++ r ∧ a' = s ++ r' ∧ xrE e r = some r'

theorem MovedIdx.reflect {e : ℤ} (he : e = 1 ∨ e = -1) {s a b a' b' : Seq} (h4 : MovedIdx e s a a')
    (h5 : MovedIdx e s b b') (h : a' <+: b') : a <+: b := by
  rcases h4 with ⟨hia, rfl⟩ | ⟨r, r', rfl, rfl, hr⟩ <;>
    rcases h5 with ⟨hib, rfl⟩ | ⟨q, q', rfl, rfl, hq⟩
  · exact h
  · exfalso
    rcases List.prefix_or_prefix_of_prefix h (List.prefix_append s q') with h' | h'
    · exact hia.2 h'
    · exact hia.1 h'
  · exact absurd ((List.prefix_append s r').trans h) hib.1
  · rw [List.prefix_append_right_inj] at h ⊢
    exact xrE_prefix he hr hq h

theorem MovedIdx.not_le {e : ℤ} (he : e = 1 ∨ e = -1) {s a a' : Seq} (h4 : MovedIdx e s a a') :
    ¬ a' <+: s := by
  rcases h4 with ⟨hia, rfl⟩ | ⟨r, r', rfl, rfl, hr⟩
  · exact hia.2
  · intro hle
    have h1 := hle.length_le
    rw [List.length_append] at h1
    exact (xrE_img he hr).1 (List.length_eq_zero_iff.1 (by omega))

theorem MovedIdx.newL {e : ℤ} (he : e = 1 ∨ e = -1) {s a a' : Seq} (h4 : MovedIdx e s a a')
    {c : List Bool} (hc : c ∈ ct e) (h : a' <+: s ++ c) : a' = s ++ c := by
  rcases h4 with ⟨hia, rfl⟩ | ⟨r, r', rfl, rfl, hr⟩
  · exfalso
    rcases List.prefix_or_prefix_of_prefix h (List.prefix_append s c) with h' | h'
    · exact hia.2 h'
    · exact hia.1 h'
  · rw [List.prefix_append_right_inj] at h
    rw [ct_prefix he hc (xrE_img he hr).1 (xrE_img he hr).2 h]

theorem rawProf_single (t : Seq) (k : ℤ) (d : ℕ) :
    rawProf [(.y t, k)] d = if t.length = d then k.natAbs else 0 := by
  simp [rawProf]

theorem rawProf_map_mv {e : ℤ} (he : e = 1 ∨ e = -1) {s : Seq} {d : ℕ} (hd : d ≤ s.length) :
    ∀ L : Word, (∀ p ∈ L, ∃ a a', p.1 = .y a ∧ mv e s p = (.y a', p.2) ∧ MovedIdx e s a a') →
      rawProf (L.map (mv e s)) d = rawProf L d
  | [], _ => rfl
  | p :: L, h => by
    rw [List.map_cons, rawProf_cons, rawProf_cons p,
      rawProf_map_mv he hd L (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    obtain ⟨a, a', ha, hm, h4⟩ := h p List.mem_cons_self
    have hp : p = (.y a, p.2) := Prod.ext ha rfl
    rw [hm, hp, rawProf_single, rawProf_single]
    rcases h4 with ⟨-, rfl⟩ | ⟨r, r', rfl, rfl, hr⟩
    · rfl
    · have h1 := xrE_ne_nil he hr
      have h2 := (xrE_img he hr).1
      have h1' : r.length ≠ 0 := fun h => h1 (List.length_eq_zero_iff.1 h)
      have h2' : r'.length ≠ 0 := fun h => h2 (List.length_eq_zero_iff.1 h)
      simp only [List.length_append]
      rw [if_neg (by omega), if_neg (by omega)]

/-- One expansion (the proof of Lemma 5.6): expand `y_s^n` by one letter `y_s^e`, move `x_s^e` to
the `X`-part and sort the new letters in. -/
theorem step56 {Ω : Word} (hΩ : IsStandardForm Ω) {s : Seq} {n e : ℤ} (he : e = 1 ∨ e = -1)
    (hmem : (Gen.y s, n) ∈ Ω) (hsign : 0 < n * e) (hnot : ¬ YOccurs Ω (s ++ [cb e]))
    (hexp : ¬ Exposed Ω s) :
    ∃ Ω', Derives Ω Ω' ∧ IsStandardForm Ω' ∧ (PCset Ω').card ≤ (PCset Ω).card ∧
      (∀ d ≤ s.length, rawProf Ω' d ≤ rawProf Ω d) ∧ rawProf Ω' s.length < rawProf Ω s.length := by
  have hcov : ∀ c ∈ ct e, ∃ o k, (Gen.y o, k) ∈ Ω ∧ s ++ psi e c <+: o :=
    fun c hc => cover he hexp hnot hc
  have hsΩ := hmem
  obtain ⟨Ξ, Υ, rfl, hΞ, hΥ, hS⟩ := sf_decomp hΩ
  have hmemΥ : (Gen.y s, n) ∈ Υ := by
    rcases List.mem_append.1 hmem with h | h
    · exact absurd rfl (xword_noy hΞ _ h s)
    · exact h
  obtain ⟨Υ₁, Υ₂, rfl⟩ := List.append_of_mem hmemΥ
  have hS' := hS
  rw [List.pairwise_append, List.pairwise_cons] at hS'
  obtain ⟨hS₁, ⟨hSs, hS₂⟩, hS12⟩ := hS'
  have he0 : e ≠ 0 := by rcases he with rfl | rfl <;> decide
  have hn0 : n ≠ 0 := by rintro rfl; simp at hsign
  -- the letters before `y_s`
  have hmv : ∀ p ∈ Υ₁, ∃ a a', p.1 = .y a ∧ mv e s p = (.y a', p.2) ∧ MovedIdx e s a a' ∧
      xAct e s a = some a' := by
    intro p hp
    obtain ⟨a, ha⟩ := hΥ.2 p (by simp [hp])
    have h1 : ¬ a <+: s := hS12 p hp (.y s, n) (by simp) a s ha rfl
    have h2 : a ≠ s ++ [cb e] := by
      rintro rfl
      have : (p.1, p.2) ∈ Ξ ++ (Υ₁ ++ (Gen.y s, n) :: Υ₂) := by simp [hp]
      rw [ha] at this
      exact hnot ⟨p.2, this⟩
    obtain ⟨a', h3, h4⟩ := dom_fact he h1 h2
    exact ⟨a, a', ha, by simp [mv, ha, act, h3], h4, h3⟩
  -- the letters after `y_s`
  have hΥ₂ : ∀ q ∈ Υ₂, ∃ b, q.1 = .y b ∧ ¬ s <+: b := by
    intro q hq
    obtain ⟨b, hb⟩ := hΥ.2 q (by simp [hq])
    exact ⟨b, hb, hSs q hq s b rfl hb⟩
  set Υ₁' := Υ₁.map (mv e s) with hΥ₁'
  set int := Υ₁' ++ (newL e s ++ (lc s (n - e) ++ Υ₂)) with hint
  -- the derivation up to sorting
  have hd1 : Derives (Ξ ++ (Υ₁ ++ (Gen.y s, n) :: Υ₂))
      (Ξ ++ (Υ₁ ++ (Gen.y s, e) :: (lc s (n - e) ++ Υ₂))) := by
    by_cases hne : n = e
    · subst hne; simp [lc]; exact Derives.rfl'
    · apply derives_append_left; apply derives_append_left
      have hsplit := Step.split [] Υ₂ (.y s) e (n - e) he0 (sub_ne_zero.2 hne)
        (by rcases he with rfl | rfl <;> omega)
      rw [show e + (n - e) = n by ring] at hsplit
      simpa [lc, sub_ne_zero.2 hne] using derives_single hsplit
  have hd2 : Derives (Ξ ++ (Υ₁ ++ (Gen.y s, e) :: (lc s (n - e) ++ Υ₂)))
      (Ξ ++ (Υ₁ ++ (Gen.x s, e) :: (newL e s ++ (lc s (n - e) ++ Υ₂)))) :=
    derives_append_left _ (derives_append_left _ (derives_expand he s _))
  have hd3 : Derives (Ξ ++ (Υ₁ ++ (Gen.x s, e) :: (newL e s ++ (lc s (n - e) ++ Υ₂))))
      ((Ξ ++ [(Gen.x s, e)]) ++ int) := by
    have h := derives_moveX_mv he Υ₁ (fun p hp => by
      obtain ⟨a, a', ha, -, -, h3⟩ := hmv p hp; exact ⟨a, a', ha, h3⟩)
    have h' := h.context Ξ (newL e s ++ (lc s (n - e) ++ Υ₂))
    simpa [hint, hΥ₁'] using h'
  -- the intermediate word is weakly ordered
  have hWO : int.Pairwise WOr := by
    refine List.pairwise_append.2 ⟨?_, List.pairwise_append.2 ⟨(newL_pairwise he s).imp SO.wor,
      List.pairwise_append.2 ⟨by unfold lc; split_ifs <;> simp, hS₂.imp SO.wor, ?_⟩, ?_⟩, ?_⟩
    · rw [hΥ₁', List.pairwise_map]
      refine hS₁.imp_of_mem ?_
      intro p q hp hq hpq a' b' ha' hb' hab
      exfalso
      obtain ⟨a, a'', ha, hma, h4, -⟩ := hmv p hp
      obtain ⟨b, b'', hb, hmb, h5, -⟩ := hmv q hq
      rw [hma] at ha'; rw [hmb] at hb'
      simp only [Gen.y.injEq] at ha' hb'
      subst ha' hb'
      exact hpq a b ha hb (h4.reflect he h5 hab)
    · intro p hp q hq a b ha hb hab
      obtain ⟨rfl, -⟩ := mem_lc hp
      simp only [Gen.y.injEq] at ha; subst ha
      obtain ⟨b', hb', hsb⟩ := hΥ₂ q hq
      rw [hb] at hb'; simp only [Gen.y.injEq] at hb'; subst hb'
      exact absurd hab hsb
    · intro p hp q hq a b ha hb hab
      obtain ⟨c, hc, hpc, -⟩ := mem_newL he hp
      rw [hpc] at ha; simp only [Gen.y.injEq] at ha; subst ha
      exfalso
      rcases List.mem_append.1 hq with hq | hq
      · obtain ⟨rfl, -⟩ := mem_lc hq
        simp only [Gen.y.injEq] at hb; subst hb
        have := hab.length_le
        simp only [List.length_append] at this
        have := ct_ne_nil he hc
        exact this (List.length_eq_zero_iff.1 (by omega))
      · obtain ⟨b', hb', hsb⟩ := hΥ₂ q hq
        rw [hb] at hb'; simp only [Gen.y.injEq] at hb'; subst hb'
        exact hsb ((List.prefix_append s c).trans hab)
    · intro p' hp' q hq a' b ha' hb hab
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hp'
      obtain ⟨a, a'', ha, hma, h4, -⟩ := hmv p hp
      rw [hma] at ha'; simp only [Gen.y.injEq] at ha'; subst ha'
      rcases List.mem_append.1 hq with hq | hq
      · obtain ⟨c, hc, hqc, -⟩ := mem_newL he hq
        rw [hqc] at hb; simp only [Gen.y.injEq] at hb; subst hb
        exact h4.newL he hc hab
      · exfalso
        rcases List.mem_append.1 hq with hq | hq
        · obtain ⟨rfl, -⟩ := mem_lc hq
          simp only [Gen.y.injEq] at hb; subst hb
          exact h4.not_le he hab
        · obtain ⟨b', hb', hsb⟩ := hΥ₂ q hq
          rw [hb] at hb'; simp only [Gen.y.injEq] at hb'; subst hb'
          rcases h4 with ⟨-, h4⟩ | ⟨r, r', h4, rfl, -⟩
          · rw [h4] at hab; exact hS12 p hp q (by simp [hq]) _ b ha hb hab
          · exact hsb ((List.prefix_append s r').trans hab)
  -- the intermediate word is a `Y`-word
  have hintY : IsYWord int := by
    constructor
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        obtain ⟨a, a', -, hma, -, -⟩ := hmv q hq
        rw [hma]; exact hΥ.1 q (by simp [hq])
      rcases List.mem_append.1 hp with hp | hp
      · exact (isYWord_newL he s).1 p hp
      rcases List.mem_append.1 hp with hp | hp
      · obtain ⟨rfl, h⟩ := mem_lc hp; exact h
      · exact hΥ.1 p (by simp [hp])
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
        obtain ⟨a, a', -, hma, -, -⟩ := hmv q hq
        rw [hma]; exact ⟨a', rfl⟩
      rcases List.mem_append.1 hp with hp | hp
      · exact (isYWord_newL he s).2 p hp
      rcases List.mem_append.1 hp with hp | hp
      · obtain ⟨rfl, -⟩ := mem_lc hp; exact ⟨s, rfl⟩
      · exact hΥ.2 p (by simp [hp])
  obtain ⟨V, hd4, hVY, hVS, hVI, hVP⟩ := canon int.length int le_rfl hintY hWO
  have hX : IsXWord (Ξ ++ [(Gen.x s, e)]) := by
    constructor
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact hΞ.1 p hp
      · simp at hp; subst hp; exact he0
    · intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact hΞ.2 p hp
      · simp at hp; subst hp; exact ⟨s, rfl⟩
  -- the profile up to depth `|s|`
  have key : ∀ d ≤ s.length, rawProf int d + (if s.length = d then 1 else 0) =
      rawProf (Ξ ++ (Υ₁ ++ (Gen.y s, n) :: Υ₂)) d := by
    intro d hd
    have hmv' : ∀ p ∈ Υ₁, ∃ a a', p.1 = .y a ∧ mv e s p = (.y a', p.2) ∧ MovedIdx e s a a' := by
      intro p hp; obtain ⟨a, a', h1, h2, h3, -⟩ := hmv p hp; exact ⟨a, a', h1, h2, h3⟩
    rw [hint, rawProf_append, rawProf_append, rawProf_append, rawProf_append, rawProf_append,
      rawProf_cons, rawProf_xword hΞ, hΥ₁', rawProf_map_mv he hd Υ₁ hmv', rawProf_newL he s hd,
      rawProf_lc, rawProf_single]
    split_ifs with h
    · rcases he with rfl | rfl <;> omega
    · omega
  refine ⟨(Ξ ++ [(Gen.x s, e)]) ++ V, ((hd1.tr hd2).tr hd3).tr (derives_append_left _ hd4),
    sf_of hX hVY hVS, ?_, ?_, ?_⟩
  · -- the prefix closure does not grow
    have hsub : PCset ((Ξ ++ [(Gen.x s, e)]) ++ V) ⊆ PCset int := by
      intro t ht
      obtain ⟨o, k, ho, hto⟩ := mem_PCset.1 ht
      have ho' : (Gen.y o, k) ∈ V := by
        rcases List.mem_append.1 ho with h | h
        · exact absurd rfl (xword_noy hX _ h o)
        · exact h
      obtain ⟨k', hk'⟩ := hVI o k ho'
      exact mem_PCset.2 ⟨o, k', hk', hto⟩
    refine (Finset.card_le_card hsub).trans ?_
    have inPC : ∀ u, (u <+: s ∨ u = s ++ [cb e] ∨ ∃ c ∈ ct e, u <+: s ++ psi e c) →
        u ∈ PCset (Ξ ++ (Υ₁ ++ (Gen.y s, n) :: Υ₂)) := by
      rintro u (h | rfl | ⟨c, hc, h⟩)
      · exact mem_PCset.2 ⟨s, n, hsΩ, h⟩
      · obtain ⟨c, hc, hcc⟩ := cb_le_psi he
        obtain ⟨o, k, ho, hso⟩ := hcov c hc
        exact mem_PCset.2 ⟨o, k, ho, ((List.prefix_append_right_inj s).2 hcc).trans hso⟩
      · obtain ⟨o, k, ho, hso⟩ := hcov c hc
        exact mem_PCset.2 ⟨o, k, ho, h.trans hso⟩
    refine Finset.card_le_card_of_injOn (phi e s) ?_ (phi_inj he s).injOn
    intro t ht
    obtain ⟨o, k, ho, hto⟩ := mem_PCset.1 ht
    rcases List.mem_append.1 ho with ho | ho
    · obtain ⟨p, hp, hpo⟩ := List.mem_map.1 ho
      obtain ⟨a, a', ha, hma, h4, -⟩ := hmv p hp
      rw [hma] at hpo; simp only [Prod.mk.injEq, Gen.y.injEq] at hpo; obtain ⟨rfl, -⟩ := hpo
      have hpΩ : (Gen.y a, p.2) ∈ Ξ ++ (Υ₁ ++ (Gen.y s, n) :: Υ₂) := by
        rw [← ha]; simp [hp]
      rcases h4 with ⟨hia, rfl⟩ | ⟨r, r', rfl, rfl, hr⟩
      · have hst : ¬ s <+: t := fun h => hia.1 (h.trans hto)
        rw [phi_not hst]
        exact mem_PCset.2 ⟨_, _, hpΩ, hto⟩
      · rcases phi_prefix he hto with h | h | h
        · exact inPC _ (Or.inl h)
        · exact inPC _ (Or.inr (Or.inl h))
        · rw [psi_xrE he hr] at h
          exact mem_PCset.2 ⟨_, _, hpΩ, h⟩
    rcases List.mem_append.1 ho with ho | ho
    · obtain ⟨c, hc, hoc, -⟩ := mem_newL he ho
      simp only [Gen.y.injEq] at hoc; subst hoc
      rcases phi_prefix he hto with h | h | h
      · exact inPC _ (Or.inl h)
      · exact inPC _ (Or.inr (Or.inl h))
      · exact inPC _ (Or.inr (Or.inr ⟨c, hc, h⟩))
    rcases List.mem_append.1 ho with ho | ho
    · obtain ⟨h, -⟩ := mem_lc ho
      simp only [Prod.mk.injEq, Gen.y.injEq] at h; obtain ⟨ho', -⟩ := h
      rw [ho'] at hto
      have hto' : t <+: s ++ [] := by simpa using hto
      rcases phi_prefix he hto' with h | h | h
      · exact inPC _ (Or.inl h)
      · exact inPC _ (Or.inr (Or.inl h))
      · exact inPC _ (Or.inl (by simpa [psi] using h))
    · obtain ⟨b, hb, hsb⟩ := hΥ₂ _ ho
      simp only [Gen.y.injEq] at hb; subst hb
      have hst : ¬ s <+: t := fun h => hsb (h.trans hto)
      rw [phi_not hst]
      exact mem_PCset.2 ⟨_, k, by simp [ho], hto⟩
  · intro d hd
    have := key d hd
    have := hVP d
    rw [rawProf_append, rawProf_xword hX]
    omega
  · have := key s.length le_rfl
    have := hVP s.length
    rw [rawProf_append, rawProf_xword hX]
    simp at *
    omega


theorem lex_of_le {m : ℕ} {f g : Fin m → ℕ} (i : Fin m) (hle : ∀ j ≤ i, f j ≤ g j)
    (hlt : f i < g i) : Pi.Lex (· < ·) (fun {_} (a b : ℕ) => a < b) f g := by
  classical
  set S := Finset.univ.filter fun j => f j ≠ g j with hS
  have hiS : i ∈ S := by simp [hS, hlt.ne]
  have hne : S.Nonempty := ⟨i, hiS⟩
  have hjS := Finset.min'_mem S hne
  have hji : S.min' hne ≤ i := Finset.min'_le S i hiS
  refine ⟨S.min' hne, fun k hk => ?_, ?_⟩
  · by_contra hc
    have : S.min' hne ≤ k := Finset.min'_le S k (by simp [hS, hc])
    exact absurd hk (not_lt.2 this)
  · have h1 := hle _ hji
    have h2 : f (S.min' hne) ≠ g (S.min' hne) := by simpa [hS] using hjS
    omega

theorem main56 (m : ℕ) : ∀ Ω, IsStandardForm Ω → (PCset Ω).card ≤ m →
    ∃ Ω', Derives Ω Ω' ∧ IsStandardForm Ω' ∧ SufficientlyExpanded Ω' := by
  have wf : WellFounded (Pi.Lex (· < ·) (fun {_} (a b : ℕ) => a < b) : (Fin m → ℕ) → (Fin m → ℕ) → Prop) :=
    Pi.Lex.wellFounded (· < ·) (fun _ => wellFounded_lt)
  intro Ω
  induction Ω using (InvImage.wf (fun Ω : Word => fun d : Fin m => rawProf Ω d) wf).induction with
  | _ Ω ih =>
  intro hΩ hcard
  by_cases hse : SufficientlyExpanded Ω
  · exact ⟨Ω, Derives.rfl', hΩ, hse⟩
  unfold SufficientlyExpanded at hse
  push Not at hse
  obtain ⟨s, -, hexp, h⟩ := hse
  have key : ∀ (n e : ℤ), (e = 1 ∨ e = -1) → (Gen.y s, n) ∈ Ω → 0 < n * e →
      ¬ YOccurs Ω (s ++ [cb e]) → ∃ Ω', Derives Ω Ω' ∧ IsStandardForm Ω' ∧ SufficientlyExpanded Ω' := by
    intro n e he hmem hsign hnot
    obtain ⟨Ω₁, d₁, hΩ₁, hc₁, hle, hlt⟩ := step56 hΩ he hmem hsign hnot hexp
    have hsm : s.length < m := (length_lt_card_PCset hmem).trans_le hcard
    have hlex : Pi.Lex (· < ·) (fun {_} (a b : ℕ) => a < b) (fun d : Fin m => rawProf Ω₁ d)
        (fun d : Fin m => rawProf Ω d) :=
      lex_of_le ⟨s.length, hsm⟩ (fun j hj => hle j (by exact_mod_cast hj)) hlt
    obtain ⟨Ω₂, d₂, hΩ₂, hse₂⟩ := ih Ω₁ hlex hΩ₁ (hc₁.trans hcard)
    exact ⟨Ω₂, d₁.tr d₂, hΩ₂, hse₂⟩
  by_cases hpos : YOccursPos Ω s → YOccurs Ω (s ++ [false])
  · obtain ⟨hneg, hnot⟩ := h hpos
    obtain ⟨n, hn, hmem⟩ := hneg
    exact key n (-1) (Or.inr rfl) hmem (by nlinarith) (by simpa [cb] using hnot)
  · push Not at hpos
    obtain ⟨⟨n, hn, hmem⟩, hnot⟩ := hpos
    exact key n 1 (Or.inl rfl) hmem (by nlinarith) (by simpa [cb] using hnot)

theorem lemma56 (Ω : Word) (hΩ : IsStandardForm Ω) :
    ∃ Ω', Derives Ω Ω' ∧ IsStandardForm Ω' ∧ SufficientlyExpanded Ω' :=
  main56 _ Ω hΩ le_rfl


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

/-! ### Lemma 5.10 -/

/-- A finite binary sequence as a `B`-word. -/
def dg (u : Seq) : BWord := u.map fun d => if d then BLetter.one else .zero

@[simp] theorem dg_nil : dg [] = [] := rfl
@[simp] theorem dg_cons (d : Bool) (u : Seq) :
    dg (d :: u) = (if d then BLetter.one else .zero) :: dg u := rfl
@[simp] theorem dg_append (u v : Seq) : dg (u ++ v) = dg u ++ dg v := by simp [dg]


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
theorem solution (Ω : Word) (hΩ : IsStandardForm Ω) :
    ∃ Ω', Derives Ω Ω' ∧ IsStandardForm Ω' ∧ SufficientlyExpanded Ω' :=
  Dev.S5.lemma56 Ω hΩ
end
