-- Prove2me | solution 1 for MathieuM23.m23_four_transitive
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-05T11:14:43.532121+00:00
-- url     : https://prove2.me/submissions/5ecf6965-30b6-4581-ab1c-d246585df5bb

import Definitions.Def_MathieuM23_Group

/-!
# Tabulated permutations of `Fin 23`

Permutations of `Fin 23` are represented by their value tables (`List ℕ`), on which composition is a
cheap structural computation.  This is the computational backbone of the verified stabilizer-chain
certificate for `M₂₃`.
-/

namespace M23Cert

open MathieuM23

/-- A permutation table: the list of images of `0, …, 22`. -/
abbrev Tab := List ℕ

/-- The table of a permutation of `Fin 23`. -/
def tab (p : Equiv.Perm (Fin 23)) : Tab := List.ofFn fun i => (p i : ℕ)

/-- Table lookup. -/
def tget (l : Tab) (i : ℕ) : ℕ := l.getD i 0

/-- Composition of tables: `(p * q) i = p (q i)`. -/
def tmul (p q : Tab) : Tab := q.map (tget p)

/-- The identity table. -/
def tid : Tab := List.range 23

theorem tget_tab (p : Equiv.Perm (Fin 23)) (i : Fin 23) : tget (tab p) i = p i := by
  unfold tget tab
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp only [List.getElem_ofFn]

theorem tab_one : tab 1 = tid := by
  simp only [tab, tid]
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.getElem_ofFn, List.getElem_range]
    rfl

theorem tab_mul (p q : Equiv.Perm (Fin 23)) : tab (p * q) = tmul (tab p) (tab q) := by
  unfold tmul tab
  rw [List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp, Equiv.Perm.coe_mul]
  have := tget_tab p (q i)
  simpa [tget, tab] using this.symm

theorem tab_inj {p q : Equiv.Perm (Fin 23)} (h : tab p = tab q) : p = q := by
  ext i
  have := congrArg (fun l => tget l i) h
  simp only [tget_tab] at this
  exact this

theorem tab_eq_iff {p q : Equiv.Perm (Fin 23)} : tab p = tab q ↔ p = q :=
  ⟨tab_inj, fun h => h ▸ rfl⟩

theorem tab_inv_of_mul {p q : Equiv.Perm (Fin 23)} (h : tmul (tab p) (tab q) = tid) :
    q = p⁻¹ := by
  rw [← tab_mul, ← tab_one, tab_eq_iff] at h
  exact eq_inv_of_mul_eq_one_right h

end M23Cert

/-!
# Straight-line programs for elements of `M₂₃`

An entry list `1, g₁, g₂, g₂⁻¹, …` where every further entry is the product of two earlier ones.
All entries lie in `M₂₃`; their value tables are certified by `slpChk`.
-/

namespace M23Cert

open MathieuM23

/-- List lookup written by direct recursion (cheap in the kernel). -/
def nthD {α : Type} (d : α) : List α → ℕ → α
  | [], _ => d
  | a :: _, 0 => a
  | _ :: l, n + 1 => nthD d l n

/-- Chunked table access (chunks of 24 tables), to keep lookups cheap in the kernel. -/
def Tget (tc : List (List Tab)) (k : ℕ) : Tab := nthD tid (nthD [] tc (k / 24)) (k % 24)

/-- The initial entries of a straight-line program. -/
def basePerms : List (Equiv.Perm (Fin 23)) := [1, g₁, g₂, g₂⁻¹]

def slpStepP (acc : List (Equiv.Perm (Fin 23))) (nij : ℕ × ℕ × ℕ) :
    List (Equiv.Perm (Fin 23)) :=
  acc ++ [acc.getD nij.2.1 1 * acc.getD nij.2.2 1]

/-- The permutations denoted by a straight-line program. -/
def slpPerms (prog : List (ℕ × ℕ × ℕ)) : List (Equiv.Perm (Fin 23)) :=
  prog.foldl slpStepP basePerms

/-- The `k`-th entry of a straight-line program (junk value `1` out of range). -/
def P (prog : List (ℕ × ℕ × ℕ)) (k : ℕ) : Equiv.Perm (Fin 23) := (slpPerms prog).getD k 1

/-- Check that `get` is the table function of the straight-line program `prog`: the `n`-th entry
(the entries of `prog` are `(n, i, j)` with consecutive `n`, the first one after `p`) is the product
of the two earlier entries `i` and `j`. -/
def slpChk (get : ℕ → Tab) : ℕ → List (ℕ × ℕ × ℕ) → Bool
  | _, [] => true
  | p, (n, i, j) :: rest =>
    decide (n = p + 1) && decide (i < n) && decide (j < n) &&
      (get n == tmul (get i) (get j)) && slpChk get n rest

theorem getD_mem_of_forall {α : Type} {S : Set α} (d : α) (hd : d ∈ S) (l : List α)
    (h : ∀ p ∈ l, p ∈ S) (i : ℕ) : l.getD i d ∈ S := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]; exact hd

theorem basePerms_mem : ∀ p ∈ basePerms, p ∈ M23 := by
  intro p hp
  simp only [basePerms, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · exact inv_mem (Subgroup.subset_closure (by simp))

theorem foldl_mem (prog : List (ℕ × ℕ × ℕ)) :
    ∀ acc : List (Equiv.Perm (Fin 23)), (∀ p ∈ acc, p ∈ M23) →
      ∀ p ∈ prog.foldl slpStepP acc, p ∈ M23 := by
  induction prog with
  | nil => intro acc h; simpa using h
  | cons e rest ih =>
    intro acc h
    apply ih
    intro p hp
    simp only [slpStepP, List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact h p hp
    · exact mul_mem (getD_mem_of_forall (S := (M23 : Set _)) 1 (one_mem _) acc h _)
        (getD_mem_of_forall (S := (M23 : Set _)) 1 (one_mem _) acc h _)

theorem P_mem (prog : List (ℕ × ℕ × ℕ)) (k : ℕ) : P prog k ∈ M23 :=
  getD_mem_of_forall (S := (M23 : Set (Equiv.Perm (Fin 23)))) 1 (one_mem _) (slpPerms prog)
    (fun p hp => foldl_mem prog basePerms basePerms_mem p hp) k

theorem tab_getD (l : List (Equiv.Perm (Fin 23))) (i : ℕ) :
    tab (l.getD i 1) = (l.map tab).getD i tid := by
  rw [← tab_one]
  by_cases hi : i < l.length
  · simp
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]

theorem slp_tab_aux (get : ℕ → Tab) (prog : List (ℕ × ℕ × ℕ)) :
    ∀ (acc : List (Equiv.Perm (Fin 23))) (p : ℕ), acc.length = p + 1 →
      (∀ k < acc.length, tab (acc.getD k 1) = get k) → slpChk get p prog = true →
      ∀ k < acc.length + prog.length, tab ((prog.foldl slpStepP acc).getD k 1) = get k := by
  induction prog with
  | nil => intro acc p _ h _ k hk; simpa using h k (by simpa using hk)
  | cons e rest ih =>
    obtain ⟨n, i, j⟩ := e
    intro acc p hlen h hchk k hk
    simp only [slpChk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hchk
    obtain ⟨⟨⟨⟨hn, hi⟩, hj⟩, hget⟩, hrest⟩ := hchk
    simp only [List.foldl_cons]
    apply ih (acc ++ [acc.getD i 1 * acc.getD j 1]) n _ _ hrest k
    · simpa [slpStepP, Nat.add_assoc, Nat.add_comm 1] using hk
    · simp [hlen, hn]
    · intro k hk
      simp only [List.length_append, List.length_singleton] at hk
      by_cases hk' : k < acc.length
      · rw [List.getD_append _ _ _ _ hk']; exact h k hk'
      · have : k = acc.length := by omega
        subst this
        rw [List.getD_append_right _ _ _ _ (by omega)]
        simp only [Nat.sub_self, List.getD_cons_zero, tab_mul]
        have hn' : acc.length = n := by omega
        rw [hn', hget, h i (by omega), h j (by omega)]

/-- If `get` is the table function of `prog`, then `get k` is the table of the `k`-th entry. -/
theorem slp_tab (get : ℕ → Tab) (prog : List (ℕ × ℕ × ℕ))
    (hbase : ∀ k < 4, tab (basePerms.getD k 1) = get k) (hchk : slpChk get 3 prog = true) :
    ∀ k < 4 + prog.length, tab (P prog k) = get k := by
  intro k hk
  refine slp_tab_aux get prog basePerms 3 (by simp [basePerms]) ?_ hchk k ?_
  · intro k hk; exact hbase k (by simpa [basePerms] using hk)
  · simpa [basePerms] using hk

end M23Cert

/-!
# Levels of a stabilizer chain

A level consists of a base point `b`, a list `gens` of generators (indices into a straight-line
program) and a Schreier tree `tr` of the orbit of `b`.  This file contains the cheap per-level
checks (`entOk`, `cover`) and the facts they give about transversal elements.
-/

namespace M23Cert

open MathieuM23

/-- A transversal entry: the point `x`, the index `k` of an element `u` with `u b = x`, the index
`ki` of its inverse, and the tree edge `u = s * u_p` (`s` a generator, `p` the parent point). -/
structure Ent where
  x : ℕ
  k : ℕ
  ki : ℕ
  s : ℕ
  p : ℕ

/-- One level of a stabilizer chain. -/
structure Lvl where
  b : ℕ
  gens : List ℕ
  tr : List Ent

/-- All entries of a level: the root `b` (with the identity) and the tree entries. -/
def Lvl.all (L : Lvl) : List Ent := ⟨L.b, 0, 0, 0, L.b⟩ :: L.tr

/-- Look up the entry for the point `x`. -/
def lk (es : List Ent) (x : ℕ) : Option Ent := es.find? (fun e => e.x == x)

theorem lk_some {es : List Ent} {x : ℕ} {e : Ent} (h : lk es x = some e) : e ∈ es ∧ e.x = x := by
  unfold lk at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem lk_isSome {es : List Ent} {x : ℕ} (h : (lk es x).isSome = true) :
    ∃ e ∈ es, e.x = x := by
  cases hl : lk es x with
  | none => simp [hl] at h
  | some e => exact ⟨e, (lk_some hl).1, (lk_some hl).2⟩

theorem lk_none {es : List Ent} {x : ℕ} (h : lk es x = none) : ∀ e ∈ es, e.x ≠ x := by
  intro e he hx
  unfold lk at h
  have := List.find?_eq_none.mp h e he
  simp [hx] at this

theorem lk_of_mem {es : List Ent} {e : Ent} (he : e ∈ es) (hnd : (es.map (·.x)).Nodup) :
    lk es e.x = some e := by
  cases hl : lk es e.x with
  | none => exact absurd rfl (lk_none hl e he)
  | some f =>
    obtain ⟨hf, hfx⟩ := lk_some hl
    have : f = e := by
      have := List.inj_on_of_nodup_map hnd hf he hfx
      exact this
    rw [this]

/-- Cheap per-level check. -/
def entOk (get : ℕ → Tab) (N : ℕ) (prev : List ℕ) (L : Lvl) : Bool :=
  decide (L.b < 23) && !prev.contains L.b && decide ((L.all.map (·.x)).Nodup) &&
  L.all.all (fun e => decide (e.x < 23) && decide (e.k < N) && (tget (get e.k) L.b == e.x) &&
    prev.all (fun p => tget (get e.k) p == p))

/-- The orbit list covers every point not among the earlier base points. -/
def cover (prev : List ℕ) (L : Lvl) : Bool :=
  (List.range 23).all (fun x => prev.contains x || (lk L.all x).isSome)

/-- The point of `Fin 23` with the given number (junk if `≥ 23`). -/
abbrev fo (n : ℕ) : Fin 23 := Fin.ofNat 23 n

theorem fo_val {n : ℕ} (h : n < 23) : (fo n : ℕ) = n := by
  simp [fo, Nat.mod_eq_of_lt h]

theorem fo_val' (x : Fin 23) : fo x = x := by
  ext; rw [fo_val x.2]

/-- Facts about the transversal elements of a level, as used for multiple transitivity. -/
theorem level_trans (prog : List (ℕ × ℕ × ℕ)) (get : ℕ → Tab)
    (hget : ∀ k < 4 + prog.length, tab (P prog k) = get k)
    (prev : List ℕ) (hprev : ∀ p ∈ prev, p < 23) (L : Lvl)
    (hent : entOk get (4 + prog.length) prev L = true) (hcov : cover prev L = true) :
    L.b < 23 ∧ L.b ∉ prev ∧
      ∀ x : Fin 23, (∀ p ∈ prev, (x : ℕ) ≠ p) →
        ∃ u ∈ M23, u (fo L.b) = x ∧ ∀ p ∈ prev, u (fo p) = fo p := by
  simp only [entOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.all_eq_true,
    beq_iff_eq] at hent
  obtain ⟨⟨⟨hb, hnp⟩, hnd⟩, hall⟩ := hent
  refine ⟨hb, by simpa using hnp, ?_⟩
  intro x hx
  have hc := List.all_eq_true.mp hcov x.val (List.mem_range.mpr x.2)
  simp only [Bool.or_eq_true, List.contains_iff_mem] at hc
  rcases hc with hc | hc
  · exact absurd rfl (hx _ hc)
  obtain ⟨e, he, hex⟩ := lk_isSome hc
  obtain ⟨⟨⟨hxe, hk⟩, hb'⟩, hfix⟩ := by simpa using hall e he
  refine ⟨P prog e.k, P_mem _ _, ?_, ?_⟩
  · have := tget_tab (P prog e.k) (fo L.b)
    rw [hget _ (by omega), fo_val hb, hb'] at this
    apply Fin.ext
    rw [← this, hex]
  · intro p hp
    have hp23 := hprev p hp
    have := tget_tab (P prog e.k) (fo p)
    rw [hget _ (by omega), fo_val hp23, hfix p hp] at this
    exact Fin.ext (by rw [← this, fo_val hp23])

end M23Cert

/-!
# 4-transitivity from transversal data

If a subgroup `M` of `Sym(Fin 23)` contains, for four distinct points `b₀, …, b₃`, elements mapping
`b_i` to any prescribed point outside `{b₀,…,b_{i-1}}` while fixing `b₀,…,b_{i-1}`, then `M` is
4-transitive.
-/

namespace M23Cert

open MathieuM23

theorem four_chain (M : Subgroup (Equiv.Perm (Fin 23))) (b0 b1 b2 b3 : Fin 23)
    (hb : Function.Injective ![b0, b1, b2, b3])
    (h0 : ∀ x, ∃ u ∈ M, u b0 = x)
    (h1 : ∀ x, x ≠ b0 → ∃ u ∈ M, u b1 = x ∧ u b0 = b0)
    (h2 : ∀ x, x ≠ b0 → x ≠ b1 → ∃ u ∈ M, u b2 = x ∧ u b0 = b0 ∧ u b1 = b1)
    (h3 : ∀ x, x ≠ b0 → x ≠ b1 → x ≠ b2 →
      ∃ u ∈ M, u b3 = x ∧ u b0 = b0 ∧ u b1 = b1 ∧ u b2 = b2) :
    MulAction.IsMultiplyPretransitive M (Fin 23) 4 := by
  rw [MulAction.isMultiplyPretransitive_iff]
  let e : Fin 4 ↪ Fin 23 := ⟨![b0, b1, b2, b3], hb⟩
  have key : ∀ f : Fin 4 ↪ Fin 23, ∃ g : M, g • e = f := by
    intro f
    have f01 : f 0 ≠ f 1 := fun h => by simpa using f.injective h
    have f02 : f 0 ≠ f 2 := fun h => by simpa using f.injective h
    have f03 : f 0 ≠ f 3 := fun h => by simpa using f.injective h
    have f12 : f 1 ≠ f 2 := fun h => by simpa using f.injective h
    have f13 : f 1 ≠ f 3 := fun h => by simpa using f.injective h
    have f23 : f 2 ≠ f 3 := fun h => by simpa using f.injective h
    obtain ⟨g1, hg1M, hg1⟩ := h0 (f 0)
    obtain ⟨u1, hu1M, hu1, hu1'⟩ := h1 (g1⁻¹ (f 1)) (by
      intro h
      apply f01
      rw [← hg1, ← h]; simp)
    set g2 := g1 * u1 with hg2
    have g2M : g2 ∈ M := mul_mem hg1M hu1M
    have g2b1 : g2 b1 = f 1 := by simp [hg2, hu1]
    have g2b0 : g2 b0 = f 0 := by simp [hg2, hu1', hg1]
    obtain ⟨u2, hu2M, hu2, hu2', hu2''⟩ := h2 (g2⁻¹ (f 2))
      (by intro h; apply f02; rw [← g2b0, ← h]; simp)
      (by intro h; apply f12; rw [← g2b1, ← h]; simp)
    set g3 := g2 * u2 with hg3
    have g3M : g3 ∈ M := mul_mem g2M hu2M
    have g3b2 : g3 b2 = f 2 := by simp [hg3, hu2]
    have g3b1 : g3 b1 = f 1 := by simp [hg3, hu2'', g2b1]
    have g3b0 : g3 b0 = f 0 := by simp [hg3, hu2', g2b0]
    obtain ⟨u3, hu3M, hu3, hu3', hu3'', hu3'''⟩ := h3 (g3⁻¹ (f 3))
      (by intro h; apply f03; rw [← g3b0, ← h]; simp)
      (by intro h; apply f13; rw [← g3b1, ← h]; simp)
      (by intro h; apply f23; rw [← g3b2, ← h]; simp)
    set g4 := g3 * u3 with hg4
    have g4M : g4 ∈ M := mul_mem g3M hu3M
    refine ⟨⟨g4, g4M⟩, ?_⟩
    ext i
    fin_cases i
    · simp [e, hg4, hu3', g3b0]
    · simp [e, hg4, hu3'', g3b1]
    · simp [e, hg4, hu3''', g3b2]
    · simp [e, hg4, hu3]
  intro x y
  obtain ⟨gx, hx⟩ := key x
  obtain ⟨gy, hy⟩ := key y
  refine ⟨gy * gx⁻¹, ?_⟩
  rw [← hx, ← hy]
  ext i
  simp [Subgroup.smul_def]

theorem inj4 {α : Type} {a b c d : α} (h01 : a ≠ b) (h02 : a ≠ c) (h03 : a ≠ d) (h12 : b ≠ c)
    (h13 : b ≠ d) (h23 : c ≠ d) : Function.Injective ![a, b, c, d] := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp at h ⊢ <;>
    first
    | exact absurd h h01 | exact absurd h h02 | exact absurd h h03 | exact absurd h h12
    | exact absurd h h13 | exact absurd h h23 | exact absurd h.symm h01 | exact absurd h.symm h02
    | exact absurd h.symm h03 | exact absurd h.symm h12 | exact absurd h.symm h13
    | exact absurd h.symm h23

/-- Check for multiple transitivity: per level the cheap checks `entOk` and `cover`. -/
def fourChk (get : ℕ → Tab) (N : ℕ) : List ℕ → List Lvl → Bool
  | _, [] => true
  | prev, L :: Ls => entOk get N prev L && cover prev L && fourChk get N (prev ++ [L.b]) Ls

theorem four_of_check (prog : List (ℕ × ℕ × ℕ)) (get : ℕ → Tab)
    (hget : ∀ k < 4 + prog.length, tab (P prog k) = get k) (L0 L1 L2 L3 : Lvl)
    (hchk : fourChk get (4 + prog.length) [] [L0, L1, L2, L3] = true) :
    MulAction.IsMultiplyPretransitive M23 (Fin 23) 4 := by
  simp only [fourChk, Bool.and_eq_true, List.nil_append, List.cons_append] at hchk
  obtain ⟨⟨e0, c0⟩, ⟨e1, c1⟩, ⟨e2, c2⟩, ⟨e3, c3⟩, -⟩ := hchk
  obtain ⟨hb0, -, t0⟩ := level_trans prog get hget [] (by simp) L0 e0 c0
  obtain ⟨hb1, nb1, t1⟩ := level_trans prog get hget [L0.b] (by simp [hb0]) L1 e1 c1
  obtain ⟨hb2, nb2, t2⟩ := level_trans prog get hget [L0.b, L1.b] (by simp [hb0, hb1]) L2 e2 c2
  obtain ⟨hb3, nb3, t3⟩ :=
    level_trans prog get hget [L0.b, L1.b, L2.b] (by simp [hb0, hb1, hb2]) L3 e3 c3
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at nb1 nb2 nb3
  have ne : ∀ {a b : ℕ}, a < 23 → b < 23 → a ≠ b → fo a ≠ fo b := by
    intro a b ha hb hab h
    apply hab
    have := congrArg Fin.val h
    rwa [fo_val ha, fo_val hb] at this
  have ne' : ∀ {x : Fin 23} {a : ℕ}, a < 23 → x ≠ fo a → (x : ℕ) ≠ a := by
    intro x a ha hx h
    apply hx
    ext
    rw [fo_val ha]; exact h
  have n01 := ne hb0 hb1 (Ne.symm nb1)
  have n02 := ne hb0 hb2 (Ne.symm nb2.1)
  have n12 := ne hb1 hb2 (Ne.symm nb2.2)
  have n03 := ne hb0 hb3 (Ne.symm nb3.1)
  have n13 := ne hb1 hb3 (Ne.symm nb3.2.1)
  have n23 := ne hb2 hb3 (Ne.symm nb3.2.2)
  refine four_chain M23 (fo L0.b) (fo L1.b) (fo L2.b) (fo L3.b) ?_ ?_ ?_ ?_ ?_
  · exact inj4 n01 n02 n03 n12 n13 n23
  · intro x
    obtain ⟨u, hu, hub, -⟩ := t0 x (by simp)
    exact ⟨u, hu, hub⟩
  · intro x hx
    obtain ⟨u, hu, hub, hf⟩ := t1 x (by simpa using ne' hb0 hx)
    exact ⟨u, hu, hub, by simpa using hf L0.b (by simp)⟩
  · intro x hx0 hx1
    obtain ⟨u, hu, hub, hf⟩ := t2 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨ne' hb0 hx0, ne' hb1 hx1⟩)
    exact ⟨u, hu, hub, by simpa using hf L0.b (by simp), by simpa using hf L1.b (by simp)⟩
  · intro x hx0 hx1 hx2
    obtain ⟨u, hu, hub, hf⟩ := t3 x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨ne' hb0 hx0, ne' hb1 hx1, ne' hb2 hx2⟩)
    exact ⟨u, hu, hub, by simpa using hf L0.b (by simp), by simpa using hf L1.b (by simp),
      by simpa using hf L2.b (by simp)⟩

end M23Cert

set_option maxRecDepth 100000

namespace M23Cert

/-- Straight-line program `four`: entries `(n, i, j)` say that entry `n` is the product of the
earlier entries `i` and `j`; entries `0..3` are `1, g₁, g₂, g₂⁻¹`. -/
def fourProg : List (ℕ × ℕ × ℕ) :=
  [(4, 2, 3), (5, 2, 2), (6, 1, 2), (7, 6, 4), (8, 3, 3), (9, 7, 8), (10, 2, 5), (11, 4, 10), (12, 10, 8), (13, 8, 8), (14, 11, 12), (15, 9, 1), (16, 13, 1), (17, 16, 1), (18, 5, 1), (19, 14, 12), (20, 15, 12), (21, 5, 5), (22, 1, 21), (23, 1, 22), (24, 12, 23), (25, 18, 17), (26, 24, 19), (27, 19, 25), (28, 25, 1), (29, 1, 8), (30, 23, 29), (31, 8, 3), (32, 5, 31), (33, 31, 4), (34, 32, 33), (35, 32, 34), (36, 30, 35), (37, 1, 36), (38, 17, 32), (39, 35, 38), (40, 20, 39), (41, 37, 39), (42, 40, 23), (43, 17, 28), (44, 3, 1), (45, 4, 44), (46, 5, 45), (47, 1, 46), (48, 32, 47), (49, 26, 48), (50, 17, 49), (51, 26, 50), (52, 43, 51), (53, 42, 39), (54, 52, 53), (55, 27, 1), (56, 26, 55), (57, 28, 56), (58, 1, 30), (59, 58, 23), (60, 53, 59), (61, 51, 60), (62, 42, 61), (63, 57, 54), (64, 41, 27), (65, 62, 54), (66, 27, 61), (67, 54, 64), (68, 41, 58), (69, 61, 68), (70, 66, 69), (71, 65, 51), (72, 36, 56), (73, 70, 72), (74, 73, 64), (75, 63, 64), (76, 71, 64), (77, 75, 74), (78, 74, 77), (79, 78, 77), (80, 54, 36), (81, 63, 80), (82, 64, 81), (83, 72, 82), (84, 72, 69), (85, 83, 84), (86, 51, 85), (87, 77, 79), (88, 85, 83), (89, 85, 88), (90, 67, 89), (91, 89, 85), (92, 79, 91), (93, 92, 90), (94, 54, 50), (95, 61, 94), (96, 53, 95), (97, 72, 96), (98, 64, 97), (99, 87, 76), (100, 76, 99), (101, 93, 90), (102, 72, 61), (103, 79, 102), (104, 99, 103), (105, 87, 89), (106, 103, 105), (107, 103, 106), (108, 98, 107), (109, 77, 53), (110, 90, 109), (111, 97, 91), (112, 111, 97), (113, 104, 112), (114, 110, 101), (115, 86, 103), (116, 107, 115), (117, 101, 116), (118, 114, 107), (119, 100, 118), (120, 113, 108), (121, 120, 118), (122, 117, 86), (123, 114, 119), (124, 122, 108), (125, 124, 109), (126, 76, 72), (127, 101, 126), (128, 123, 127), (129, 108, 121), (130, 119, 129), (131, 117, 112), (132, 131, 116), (133, 108, 132), (134, 129, 133), (135, 130, 128), (136, 134, 135), (137, 128, 135), (138, 121, 86), (139, 137, 138), (140, 138, 86), (141, 90, 111), (142, 100, 141), (143, 127, 142), (144, 117, 143), (145, 109, 144), (146, 144, 127), (147, 146, 131), (148, 133, 147), (149, 148, 133), (150, 145, 149), (151, 136, 150), (152, 140, 109), (153, 152, 148), (154, 86, 150), (155, 153, 154), (156, 151, 125), (157, 125, 154), (158, 139, 109), (159, 139, 158), (160, 135, 157), (161, 160, 156), (162, 154, 156), (163, 161, 156), (164, 2, 1), (165, 2, 6), (166, 1, 165), (167, 109, 118), (168, 127, 167), (169, 86, 168), (170, 158, 169), (171, 159, 170), (172, 128, 146), (173, 148, 172), (174, 139, 173), (175, 169, 174), (176, 170, 148), (177, 175, 176), (178, 175, 177), (179, 162, 178), (180, 154, 150), (181, 157, 180), (182, 156, 181), (183, 44, 3), (184, 183, 1), (185, 184, 155), (186, 185, 1), (187, 185, 164), (188, 2, 186), (189, 185, 186), (190, 185, 185), (191, 185, 190), (192, 182, 181), (193, 109, 145), (194, 86, 193), (195, 135, 194), (196, 158, 195), (197, 192, 196), (198, 155, 179), (199, 1, 3), (200, 196, 166), (201, 199, 200), (202, 201, 197), (203, 200, 200), (204, 203, 202), (205, 204, 1), (206, 204, 164), (207, 185, 205), (208, 204, 205), (209, 204, 185), (210, 204, 190), (211, 185, 209), (212, 204, 209), (213, 204, 210), (214, 204, 204), (215, 204, 214), (216, 171, 179), (217, 163, 197), (218, 197, 157), (219, 199, 216), (220, 171, 175), (221, 171, 220), (222, 155, 221), (223, 222, 187), (224, 223, 190), (225, 200, 224), (226, 225, 224), (227, 226, 219), (228, 224, 224), (229, 228, 227), (230, 229, 1), (231, 229, 186), (232, 1, 230), (233, 2, 230), (234, 229, 185), (235, 229, 190), (236, 185, 235), (237, 204, 235), (238, 229, 237), (239, 229, 204), (240, 229, 214), (241, 204, 239), (242, 229, 239), (243, 204, 240), (244, 204, 241), (245, 229, 243), (246, 229, 229), (247, 229, 246), (248, 229, 247), (249, 170, 222), (250, 157, 249), (251, 175, 158), (252, 163, 251), (253, 252, 196), (254, 217, 253), (255, 252, 181), (256, 255, 164), (257, 256, 212), (258, 257, 214), (259, 1, 258), (260, 259, 3), (261, 260, 250), (262, 203, 258), (263, 262, 224), (264, 263, 258), (265, 264, 261), (266, 228, 258), (267, 266, 224), (268, 267, 258), (269, 268, 265), (270, 258, 258), (271, 270, 258), (272, 271, 258), (273, 272, 269), (274, 273, 164), (275, 273, 186), (276, 273, 187), (277, 273, 185), (278, 273, 190), (279, 273, 204), (280, 273, 240), (281, 273, 229), (282, 273, 246), (283, 229, 281), (284, 273, 247), (285, 222, 178), (286, 198, 285), (287, 1, 200), (288, 218, 170), (289, 288, 233), (290, 289, 238), (291, 290, 245), (292, 291, 248), (293, 287, 292), (294, 293, 254), (295, 203, 224), (296, 295, 224), (297, 296, 294), (298, 267, 297), (299, 258, 292), (300, 299, 258), (301, 300, 298), (302, 301, 1), (303, 301, 164), (304, 301, 190), (305, 301, 209), (306, 301, 304), (307, 301, 214), (308, 301, 239), (309, 301, 279), (310, 301, 215), (311, 301, 240), (312, 229, 308), (313, 301, 229), (314, 301, 246), (315, 273, 313), (316, 301, 313), (317, 301, 283), (318, 254, 249), (319, 198, 318), (320, 259, 1), (321, 320, 319), (322, 200, 258), (323, 322, 258), (324, 323, 321), (325, 286, 275), (326, 325, 213), (327, 326, 243), (328, 327, 283), (329, 228, 328), (330, 329, 292), (331, 330, 324), (332, 271, 331), (333, 332, 1), (334, 332, 164), (335, 332, 185), (336, 332, 190), (337, 332, 209), (338, 185, 335), (339, 301, 335), (340, 332, 214), (341, 332, 239), (342, 332, 279), (343, 204, 340), (344, 332, 229), (345, 332, 246), (346, 229, 344), (347, 273, 344), (348, 332, 283), (349, 273, 346)]

/-- The value tables of all entries of `fourProg`, in chunks of 24. -/
def fourTabs : List (List Tab) :=
  [[[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22], [10, 22, 7, 15, 20, 5, 19, 2, 8, 9, 0, 11, 12, 13, 18, 3, 16, 21, 14, 6, 4, 17, 1], [1, 10, 22, 7, 17, 2, 11, 21, 5, 15, 9, 0, 6, 20, 12, 8, 3, 14, 19, 13, 16, 4, 18], [11, 0, 5, 16, 21, 8, 12, 3, 15, 10, 1, 6, 14, 19, 17, 9, 20, 4, 22, 18, 13, 7, 2], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22], [10, 9, 18, 21, 14, 22, 0, 4, 2, 8, 15, 1, 11, 16, 6, 5, 7, 12, 13, 20, 3, 17, 19], [22, 0, 1, 2, 21, 7, 11, 17, 5, 3, 9, 10, 19, 4, 12, 8, 15, 18, 6, 13, 16, 20, 14], [22, 0, 1, 2, 21, 7, 11, 17, 5, 3, 9, 10, 19, 4, 12, 8, 15, 18, 6, 13, 16, 20, 14], [6, 11, 8, 20, 7, 15, 14, 16, 9, 1, 0, 12, 17, 18, 4, 10, 13, 21, 2, 22, 19, 3, 5], [11, 10, 5, 16, 17, 8, 12, 15, 3, 0, 22, 19, 18, 6, 21, 9, 4, 20, 1, 14, 13, 2, 7], [9, 15, 19, 4, 12, 18, 1, 17, 22, 5, 8, 10, 0, 3, 11, 2, 21, 6, 20, 16, 7, 14, 13], [9, 15, 19, 4, 12, 18, 1, 17, 22, 5, 8, 10, 0, 3, 11, 2, 21, 6, 20, 16, 7, 14, 13], [1, 10, 22, 7, 17, 2, 11, 21, 5, 15, 9, 0, 6, 20, 12, 8, 3, 14, 19, 13, 16, 4, 18], [14, 12, 9, 19, 16, 10, 4, 13, 1, 11, 6, 17, 21, 2, 7, 0, 18, 3, 8, 5, 22, 20, 15], [15, 8, 13, 17, 6, 19, 10, 14, 18, 2, 5, 9, 1, 7, 0, 22, 4, 11, 16, 3, 21, 12, 20], [22, 7, 15, 9, 13, 8, 14, 5, 3, 0, 11, 19, 18, 6, 1, 16, 4, 2, 21, 12, 17, 20, 10], [6, 15, 13, 0, 22, 10, 5, 9, 1, 11, 14, 17, 21, 2, 8, 19, 18, 20, 7, 4, 16, 3, 12], [14, 12, 9, 19, 16, 10, 4, 13, 1, 11, 6, 17, 21, 2, 7, 0, 18, 3, 8, 5, 22, 20, 15], [15, 19, 4, 5, 3, 22, 20, 18, 2, 8, 10, 1, 11, 16, 13, 21, 7, 17, 6, 0, 14, 12, 9], [8, 5, 20, 14, 11, 13, 9, 12, 19, 22, 2, 15, 10, 21, 1, 18, 17, 0, 3, 7, 4, 6, 16], [7, 11, 10, 5, 2, 15, 19, 20, 8, 16, 0, 22, 14, 17, 18, 3, 9, 1, 12, 6, 4, 13, 21], [15, 8, 13, 17, 6, 19, 10, 14, 18, 2, 5, 9, 1, 7, 0, 22, 4, 11, 16, 3, 21, 12, 20], [3, 8, 13, 21, 19, 6, 0, 18, 14, 7, 5, 9, 22, 2, 10, 1, 20, 11, 16, 15, 17, 12, 4], [15, 8, 13, 17, 6, 19, 10, 14, 18, 2, 5, 9, 1, 7, 0, 22, 4, 11, 16, 3, 21, 12, 20]],
   [[8, 5, 20, 14, 11, 13, 9, 12, 19, 22, 2, 15, 10, 21, 1, 18, 17, 0, 3, 7, 4, 6, 16], [13, 11, 8, 0, 7, 10, 3, 16, 19, 1, 20, 17, 12, 4, 18, 15, 6, 5, 2, 22, 9, 14, 21], [19, 13, 4, 1, 15, 21, 22, 10, 7, 16, 20, 18, 2, 6, 5, 3, 0, 8, 14, 12, 11, 9, 17], [21, 15, 19, 8, 12, 2, 14, 17, 7, 5, 4, 0, 10, 11, 3, 18, 9, 13, 20, 16, 22, 1, 6], [20, 21, 16, 15, 9, 10, 22, 8, 19, 1, 13, 17, 12, 4, 2, 0, 6, 14, 18, 3, 7, 5, 11], [19, 11, 8, 4, 2, 3, 18, 16, 9, 22, 10, 12, 21, 14, 20, 0, 13, 17, 7, 1, 6, 15, 5], [3, 9, 18, 6, 13, 17, 16, 4, 2, 20, 5, 1, 12, 0, 21, 15, 7, 11, 14, 8, 10, 22, 19], [12, 6, 15, 13, 3, 9, 17, 20, 10, 0, 11, 14, 4, 22, 21, 1, 19, 7, 5, 2, 18, 16, 8], [11, 0, 5, 16, 21, 8, 12, 3, 15, 10, 1, 6, 14, 19, 17, 9, 20, 4, 22, 18, 13, 7, 2], [12, 6, 15, 13, 3, 9, 17, 20, 10, 0, 11, 14, 4, 22, 21, 1, 19, 7, 5, 2, 18, 16, 8], [14, 12, 9, 19, 16, 10, 4, 13, 1, 11, 6, 17, 21, 2, 7, 0, 18, 3, 8, 5, 22, 20, 15], [17, 14, 10, 18, 20, 1, 21, 19, 0, 6, 12, 4, 7, 5, 3, 11, 22, 16, 15, 8, 2, 13, 9], [11, 21, 5, 14, 10, 9, 22, 8, 3, 16, 12, 13, 4, 17, 6, 1, 19, 7, 15, 2, 18, 0, 20], [11, 17, 5, 18, 0, 9, 1, 8, 15, 16, 12, 13, 20, 21, 19, 22, 6, 2, 3, 7, 14, 10, 4], [17, 14, 10, 18, 20, 1, 21, 19, 0, 6, 12, 4, 7, 5, 3, 11, 22, 16, 15, 8, 2, 13, 9], [16, 3, 12, 15, 2, 14, 13, 8, 17, 21, 7, 20, 19, 1, 18, 4, 9, 22, 11, 0, 10, 5, 6], [9, 5, 14, 3, 10, 18, 17, 8, 1, 13, 20, 4, 6, 11, 12, 2, 16, 21, 22, 7, 0, 15, 19], [6, 18, 20, 22, 5, 19, 21, 15, 2, 10, 8, 14, 7, 17, 3, 0, 16, 4, 13, 11, 12, 9, 1], [2, 1, 11, 21, 17, 7, 20, 12, 22, 14, 18, 13, 5, 8, 9, 19, 10, 4, 16, 3, 15, 6, 0], [22, 20, 18, 0, 11, 6, 15, 1, 5, 12, 2, 3, 21, 16, 9, 14, 4, 7, 8, 19, 13, 10, 17], [1, 2, 3, 9, 13, 8, 18, 5, 15, 10, 11, 6, 14, 19, 22, 16, 20, 7, 17, 12, 21, 4, 0], [1, 2, 3, 9, 13, 8, 18, 5, 15, 10, 11, 6, 14, 19, 22, 16, 20, 7, 17, 12, 21, 4, 0], [9, 18, 21, 8, 16, 2, 13, 22, 5, 15, 1, 0, 6, 20, 19, 7, 3, 4, 12, 11, 17, 14, 10], [9, 14, 17, 8, 16, 7, 13, 1, 5, 3, 22, 10, 19, 4, 6, 2, 15, 20, 12, 11, 21, 18, 0]],
   [[10, 17, 4, 15, 20, 3, 19, 0, 8, 16, 2, 1, 18, 21, 12, 5, 9, 13, 14, 6, 7, 22, 11], [20, 8, 15, 3, 11, 1, 12, 19, 7, 0, 4, 13, 14, 9, 2, 21, 16, 6, 5, 22, 10, 17, 18], [22, 1, 0, 19, 17, 12, 21, 5, 13, 14, 16, 2, 7, 11, 9, 20, 18, 4, 10, 15, 6, 3, 8], [17, 13, 19, 12, 8, 2, 9, 21, 6, 5, 0, 4, 10, 18, 16, 11, 14, 15, 20, 3, 22, 1, 7], [7, 16, 19, 21, 5, 18, 12, 10, 15, 6, 22, 11, 2, 8, 4, 3, 9, 14, 13, 0, 17, 20, 1], [10, 21, 5, 19, 11, 9, 8, 22, 4, 6, 12, 15, 3, 1, 16, 17, 14, 0, 13, 2, 18, 7, 20], [22, 20, 18, 0, 11, 6, 15, 1, 5, 12, 2, 3, 21, 16, 9, 14, 4, 7, 8, 19, 13, 10, 17], [4, 6, 17, 18, 22, 2, 16, 19, 7, 5, 21, 0, 10, 11, 20, 8, 9, 1, 3, 14, 12, 13, 15], [15, 22, 8, 14, 17, 4, 0, 12, 10, 21, 9, 19, 20, 18, 11, 7, 16, 13, 1, 5, 2, 6, 3], [0, 11, 19, 2, 14, 9, 20, 12, 13, 5, 1, 3, 7, 18, 17, 8, 6, 4, 21, 10, 16, 22, 15], [15, 9, 14, 19, 13, 21, 16, 20, 7, 4, 5, 22, 12, 10, 17, 3, 2, 11, 18, 8, 0, 1, 6], [3, 7, 10, 11, 16, 8, 5, 17, 18, 14, 21, 4, 9, 20, 15, 6, 13, 22, 2, 19, 1, 12, 0], [19, 22, 12, 15, 14, 4, 9, 0, 13, 16, 7, 11, 6, 18, 17, 8, 1, 20, 5, 2, 21, 3, 10], [3, 7, 10, 11, 16, 8, 5, 17, 18, 14, 21, 4, 9, 20, 15, 6, 13, 22, 2, 19, 1, 12, 0], [21, 12, 18, 13, 10, 22, 7, 4, 16, 9, 6, 17, 14, 15, 19, 20, 8, 0, 11, 3, 1, 5, 2], [15, 16, 21, 0, 3, 20, 8, 11, 9, 7, 19, 2, 22, 6, 5, 17, 14, 12, 13, 10, 18, 1, 4], [9, 0, 11, 2, 7, 20, 3, 4, 15, 19, 5, 6, 8, 14, 22, 13, 10, 17, 12, 16, 1, 18, 21], [2, 1, 11, 21, 17, 7, 20, 12, 22, 14, 18, 13, 5, 8, 9, 19, 10, 4, 16, 3, 15, 6, 0], [8, 17, 4, 0, 9, 7, 2, 13, 20, 3, 1, 12, 5, 22, 18, 14, 11, 6, 19, 16, 15, 10, 21], [12, 22, 3, 18, 1, 13, 0, 11, 14, 19, 6, 15, 5, 9, 17, 16, 2, 7, 21, 4, 20, 8, 10], [0, 10, 3, 11, 17, 9, 16, 12, 15, 5, 19, 1, 7, 8, 4, 22, 20, 14, 13, 2, 6, 18, 21], [3, 21, 11, 4, 22, 14, 13, 9, 6, 8, 19, 7, 17, 18, 16, 0, 1, 15, 20, 10, 5, 2, 12], [0, 10, 12, 9, 21, 18, 22, 3, 2, 20, 16, 13, 6, 19, 11, 8, 17, 14, 15, 1, 7, 4, 5], [4, 8, 3, 5, 22, 11, 14, 6, 20, 7, 2, 17, 18, 16, 10, 13, 9, 19, 15, 21, 0, 1, 12]],
   [[1, 20, 3, 6, 7, 10, 11, 4, 12, 0, 16, 2, 18, 15, 13, 8, 19, 17, 21, 9, 5, 22, 14], [10, 7, 9, 22, 3, 16, 13, 21, 6, 0, 17, 12, 15, 8, 19, 2, 1, 14, 4, 20, 18, 5, 11], [0, 10, 12, 9, 21, 18, 22, 3, 2, 20, 16, 13, 6, 19, 11, 8, 17, 14, 15, 1, 7, 4, 5], [7, 15, 2, 21, 11, 18, 0, 3, 17, 10, 20, 8, 9, 5, 4, 6, 19, 12, 22, 14, 16, 13, 1], [7, 4, 17, 3, 6, 0, 5, 22, 13, 21, 11, 14, 20, 10, 12, 16, 2, 19, 18, 9, 8, 15, 1], [7, 20, 9, 10, 13, 22, 1, 21, 2, 16, 19, 5, 0, 14, 8, 17, 12, 4, 6, 15, 3, 11, 18], [3, 7, 20, 16, 19, 5, 10, 4, 12, 17, 1, 18, 0, 11, 2, 14, 6, 21, 22, 8, 9, 13, 15], [4, 9, 17, 1, 11, 15, 7, 13, 20, 6, 8, 5, 3, 2, 12, 21, 0, 19, 10, 14, 16, 18, 22], [3, 10, 6, 9, 2, 12, 17, 5, 0, 4, 21, 16, 11, 7, 15, 20, 19, 1, 14, 18, 8, 22, 13], [0, 19, 8, 7, 21, 22, 12, 20, 15, 3, 1, 14, 2, 11, 17, 18, 10, 16, 5, 13, 9, 4, 6], [9, 16, 15, 4, 18, 21, 8, 1, 13, 2, 0, 22, 11, 6, 17, 12, 5, 10, 20, 14, 19, 7, 3], [0, 19, 8, 7, 21, 22, 12, 20, 15, 3, 1, 14, 2, 11, 17, 18, 10, 16, 5, 13, 9, 4, 6], [6, 22, 2, 7, 14, 13, 15, 0, 11, 12, 9, 4, 17, 21, 19, 1, 20, 8, 5, 16, 10, 3, 18], [12, 6, 8, 20, 17, 11, 18, 0, 14, 2, 3, 21, 16, 4, 13, 19, 9, 15, 22, 10, 1, 7, 5], [10, 9, 6, 22, 15, 4, 20, 17, 16, 19, 12, 1, 14, 8, 18, 3, 5, 11, 7, 0, 13, 21, 2], [13, 16, 4, 20, 5, 17, 21, 14, 3, 1, 2, 22, 10, 9, 0, 11, 7, 15, 19, 8, 12, 6, 18], [12, 10, 14, 0, 7, 5, 16, 1, 19, 20, 6, 13, 8, 21, 15, 22, 3, 9, 11, 4, 2, 17, 18], [16, 3, 13, 12, 0, 11, 9, 6, 10, 1, 18, 4, 14, 7, 19, 5, 20, 2, 21, 17, 8, 15, 22], [2, 18, 9, 5, 12, 15, 19, 0, 6, 22, 21, 1, 17, 11, 4, 13, 20, 3, 8, 7, 14, 16, 10], [14, 9, 10, 8, 2, 4, 21, 16, 19, 13, 12, 15, 20, 0, 7, 17, 1, 5, 22, 18, 3, 6, 11], [12, 6, 8, 20, 17, 11, 18, 0, 14, 2, 3, 21, 16, 4, 13, 19, 9, 15, 22, 10, 1, 7, 5], [8, 22, 2, 11, 16, 19, 10, 12, 18, 5, 7, 6, 15, 21, 17, 4, 1, 20, 14, 0, 13, 9, 3], [17, 20, 22, 19, 7, 21, 10, 6, 16, 9, 4, 18, 1, 3, 12, 13, 8, 11, 2, 14, 15, 0, 5], [22, 1, 0, 19, 17, 12, 21, 5, 13, 14, 16, 2, 7, 11, 9, 20, 18, 4, 10, 15, 6, 3, 8]],
   [[20, 21, 10, 2, 0, 3, 7, 9, 1, 16, 14, 5, 22, 15, 6, 18, 13, 11, 12, 17, 8, 19, 4], [5, 22, 16, 3, 1, 6, 4, 0, 20, 19, 13, 10, 14, 8, 11, 21, 15, 2, 18, 17, 12, 9, 7], [20, 21, 10, 2, 0, 3, 7, 9, 1, 16, 14, 5, 22, 15, 6, 18, 13, 11, 12, 17, 8, 19, 4], [14, 5, 15, 20, 21, 13, 17, 18, 9, 6, 22, 0, 12, 2, 10, 7, 4, 8, 19, 1, 3, 11, 16], [12, 0, 16, 8, 15, 10, 19, 18, 21, 5, 1, 7, 20, 17, 11, 22, 6, 13, 9, 4, 3, 14, 2], [2, 14, 5, 19, 15, 4, 0, 8, 10, 3, 9, 22, 20, 6, 16, 21, 13, 11, 18, 12, 17, 1, 7], [6, 4, 16, 2, 19, 12, 10, 17, 21, 13, 22, 7, 0, 5, 8, 11, 15, 14, 3, 9, 20, 18, 1], [7, 11, 0, 17, 14, 3, 8, 19, 18, 2, 22, 13, 4, 15, 20, 5, 21, 12, 1, 6, 16, 10, 9], [18, 0, 14, 8, 10, 20, 9, 1, 19, 15, 16, 2, 21, 7, 3, 13, 11, 12, 5, 17, 4, 22, 6], [7, 20, 9, 10, 13, 22, 1, 21, 2, 16, 19, 5, 0, 14, 8, 17, 12, 4, 6, 15, 3, 11, 18], [19, 16, 2, 22, 15, 9, 11, 10, 0, 21, 6, 3, 7, 20, 18, 12, 4, 14, 8, 5, 17, 13, 1], [6, 21, 0, 9, 5, 2, 13, 22, 7, 10, 8, 17, 19, 16, 1, 4, 14, 20, 18, 3, 12, 15, 11], [7, 19, 20, 16, 3, 10, 15, 4, 9, 14, 1, 11, 17, 13, 21, 0, 6, 8, 12, 2, 22, 18, 5], [19, 11, 22, 15, 5, 16, 2, 18, 13, 1, 0, 17, 10, 20, 12, 4, 8, 7, 14, 9, 6, 21, 3], [7, 1, 10, 13, 15, 20, 9, 8, 11, 18, 2, 3, 21, 14, 17, 12, 6, 0, 4, 22, 19, 16, 5], [11, 19, 13, 20, 16, 1, 9, 15, 17, 8, 14, 21, 12, 5, 0, 2, 22, 6, 7, 18, 3, 4, 10], [1, 10, 22, 20, 19, 9, 16, 11, 3, 18, 5, 14, 0, 17, 21, 4, 2, 13, 7, 6, 12, 8, 15], [0, 16, 6, 4, 17, 15, 11, 2, 8, 5, 20, 3, 18, 12, 22, 10, 14, 7, 1, 9, 21, 19, 13], [10, 17, 20, 22, 12, 15, 7, 11, 2, 13, 18, 5, 19, 9, 6, 16, 14, 3, 4, 21, 0, 1, 8], [17, 1, 10, 11, 18, 22, 16, 0, 7, 6, 2, 8, 15, 3, 13, 4, 21, 14, 9, 20, 5, 12, 19], [20, 21, 8, 17, 18, 11, 14, 6, 22, 13, 0, 7, 4, 9, 16, 5, 15, 1, 10, 12, 2, 19, 3], [17, 1, 10, 11, 18, 22, 16, 0, 7, 6, 2, 8, 15, 3, 13, 4, 21, 14, 9, 20, 5, 12, 19], [7, 1, 10, 13, 15, 20, 9, 8, 11, 18, 2, 3, 21, 14, 17, 12, 6, 0, 4, 22, 19, 16, 5], [18, 0, 1, 17, 22, 3, 5, 21, 7, 9, 16, 8, 14, 11, 13, 20, 19, 12, 15, 2, 4, 6, 10]],
   [[2, 9, 21, 14, 4, 20, 10, 17, 5, 22, 16, 3, 7, 12, 19, 0, 11, 8, 18, 6, 13, 1, 15], [17, 9, 16, 12, 0, 13, 22, 5, 3, 18, 21, 14, 1, 19, 8, 7, 10, 2, 4, 15, 6, 11, 20], [2, 6, 16, 19, 4, 18, 5, 14, 21, 20, 15, 1, 13, 7, 9, 11, 22, 8, 0, 17, 3, 12, 10], [4, 10, 17, 3, 8, 22, 15, 1, 11, 13, 14, 2, 6, 5, 9, 0, 21, 19, 16, 20, 12, 7, 18], [14, 17, 3, 22, 19, 15, 11, 4, 20, 9, 6, 1, 8, 7, 12, 2, 5, 21, 13, 16, 10, 0, 18], [16, 1, 18, 2, 15, 5, 3, 13, 7, 17, 14, 21, 6, 10, 8, 19, 20, 4, 12, 9, 11, 0, 22], [4, 8, 3, 5, 22, 11, 14, 6, 20, 7, 2, 17, 18, 16, 10, 13, 9, 19, 15, 21, 0, 1, 12], [15, 10, 19, 4, 7, 22, 16, 0, 17, 8, 5, 11, 18, 13, 9, 6, 3, 12, 21, 1, 2, 14, 20], [0, 14, 20, 8, 1, 18, 21, 4, 19, 11, 22, 2, 16, 5, 13, 15, 3, 6, 7, 10, 17, 9, 12], [8, 14, 6, 17, 7, 13, 5, 10, 16, 12, 18, 21, 19, 2, 9, 4, 1, 20, 3, 0, 15, 11, 22], [7, 13, 5, 12, 21, 11, 3, 16, 19, 14, 15, 6, 2, 1, 9, 22, 0, 4, 17, 18, 20, 8, 10], [1, 2, 19, 5, 20, 6, 21, 8, 11, 9, 22, 13, 17, 14, 12, 18, 10, 3, 0, 16, 15, 7, 4], [15, 7, 11, 3, 0, 13, 12, 21, 4, 14, 1, 8, 20, 9, 10, 6, 18, 2, 22, 17, 19, 16, 5], [0, 4, 11, 16, 7, 13, 17, 18, 3, 21, 19, 9, 22, 14, 1, 15, 12, 20, 5, 8, 2, 6, 10], [8, 7, 21, 1, 10, 2, 20, 3, 17, 11, 0, 12, 22, 9, 14, 4, 19, 15, 13, 16, 6, 5, 18], [7, 9, 20, 19, 13, 17, 8, 21, 18, 6, 10, 5, 0, 11, 1, 22, 12, 3, 16, 15, 4, 14, 2], [3, 11, 6, 16, 9, 15, 17, 5, 13, 20, 0, 2, 8, 12, 7, 18, 22, 1, 19, 4, 10, 14, 21], [4, 11, 17, 10, 5, 6, 19, 9, 7, 21, 22, 18, 0, 2, 14, 12, 16, 8, 3, 15, 1, 13, 20], [21, 18, 22, 20, 7, 0, 6, 2, 10, 15, 1, 9, 8, 3, 4, 12, 13, 14, 5, 17, 19, 11, 16], [13, 3, 20, 1, 9, 4, 19, 17, 22, 12, 11, 21, 7, 10, 5, 0, 2, 14, 6, 8, 15, 18, 16], [1, 15, 6, 16, 12, 7, 19, 14, 13, 17, 8, 18, 4, 10, 5, 20, 0, 9, 2, 21, 3, 11, 22], [1, 7, 11, 14, 20, 18, 22, 13, 3, 6, 4, 16, 17, 15, 2, 9, 10, 19, 0, 8, 5, 12, 21], [0, 18, 7, 11, 3, 9, 2, 17, 8, 19, 15, 6, 13, 22, 16, 5, 1, 4, 12, 21, 10, 20, 14], [15, 21, 0, 11, 4, 8, 19, 12, 17, 1, 6, 16, 13, 20, 3, 22, 10, 7, 18, 14, 5, 2, 9]],
   [[4, 12, 17, 8, 18, 7, 20, 15, 14, 1, 16, 21, 3, 5, 11, 19, 2, 0, 9, 13, 22, 10, 6], [5, 10, 7, 13, 14, 18, 6, 4, 12, 11, 8, 21, 15, 16, 17, 9, 22, 19, 1, 20, 3, 0, 2], [19, 16, 13, 18, 15, 6, 2, 4, 0, 14, 7, 21, 9, 5, 1, 20, 8, 3, 10, 12, 17, 11, 22], [16, 13, 12, 6, 17, 2, 11, 0, 21, 14, 22, 5, 3, 1, 9, 10, 7, 18, 19, 8, 20, 4, 15], [12, 14, 22, 17, 20, 11, 9, 0, 6, 1, 10, 13, 16, 4, 21, 19, 18, 5, 8, 3, 2, 7, 15], [12, 20, 13, 18, 0, 4, 5, 8, 17, 7, 3, 1, 15, 21, 14, 19, 16, 2, 11, 6, 22, 9, 10], [15, 3, 16, 1, 5, 14, 18, 12, 19, 4, 13, 10, 9, 0, 17, 20, 22, 7, 21, 6, 2, 11, 8], [18, 16, 22, 11, 15, 7, 19, 8, 4, 9, 12, 0, 20, 3, 1, 10, 21, 5, 14, 17, 6, 2, 13], [21, 18, 22, 20, 7, 0, 6, 2, 10, 15, 1, 9, 8, 3, 4, 12, 13, 14, 5, 17, 19, 11, 16], [8, 4, 16, 14, 19, 9, 15, 21, 6, 18, 1, 3, 13, 7, 11, 17, 5, 0, 10, 20, 22, 2, 12], [3, 22, 5, 9, 4, 18, 7, 14, 0, 15, 8, 12, 19, 10, 11, 13, 2, 17, 21, 20, 6, 1, 16], [14, 12, 9, 18, 19, 10, 21, 11, 8, 17, 6, 13, 20, 1, 3, 7, 16, 0, 2, 22, 15, 4, 5], [21, 16, 14, 22, 10, 7, 11, 3, 8, 5, 1, 2, 19, 12, 4, 17, 6, 15, 20, 9, 0, 18, 13], [2, 22, 5, 17, 15, 12, 13, 8, 16, 19, 7, 6, 9, 14, 21, 10, 18, 4, 0, 11, 3, 1, 20], [8, 21, 16, 0, 4, 2, 20, 6, 10, 3, 13, 14, 11, 15, 7, 9, 22, 17, 5, 12, 19, 18, 1], [22, 18, 2, 13, 9, 20, 15, 19, 11, 1, 10, 5, 21, 0, 17, 12, 16, 14, 4, 7, 8, 6, 3], [20, 2, 17, 3, 22, 0, 11, 18, 12, 15, 21, 8, 6, 1, 14, 10, 16, 13, 7, 5, 19, 9, 4], [9, 16, 14, 4, 21, 18, 8, 3, 12, 0, 2, 17, 5, 6, 22, 13, 11, 10, 19, 15, 20, 7, 1], [1, 2, 11, 16, 8, 14, 12, 9, 0, 18, 22, 5, 20, 19, 4, 17, 7, 13, 6, 15, 3, 21, 10], [7, 11, 22, 1, 2, 3, 17, 4, 12, 18, 16, 14, 15, 5, 21, 10, 8, 13, 20, 0, 9, 19, 6], [9, 18, 21, 8, 16, 2, 13, 22, 5, 15, 1, 0, 6, 20, 19, 7, 3, 4, 12, 11, 17, 14, 10], [18, 1, 10, 22, 4, 21, 0, 14, 2, 7, 15, 9, 13, 17, 6, 5, 8, 19, 11, 20, 3, 16, 12], [14, 22, 0, 1, 20, 17, 10, 18, 7, 2, 3, 9, 13, 21, 19, 5, 8, 6, 11, 4, 15, 16, 12], [18, 11, 0, 20, 4, 6, 1, 13, 17, 14, 22, 15, 21, 12, 7, 10, 2, 19, 5, 3, 9, 8, 16]],
   [[21, 11, 15, 2, 7, 16, 10, 13, 12, 9, 20, 6, 14, 18, 0, 5, 19, 1, 22, 4, 8, 17, 3], [21, 1, 3, 6, 17, 5, 12, 8, 14, 19, 13, 20, 18, 7, 10, 4, 0, 9, 2, 15, 16, 11, 22], [18, 21, 0, 20, 17, 2, 11, 10, 7, 12, 15, 19, 5, 6, 13, 4, 8, 3, 16, 9, 22, 14, 1], [4, 6, 22, 8, 14, 2, 5, 10, 19, 21, 12, 7, 20, 15, 0, 9, 11, 13, 16, 1, 3, 17, 18], [10, 3, 5, 7, 15, 21, 20, 1, 0, 13, 4, 9, 11, 18, 14, 17, 19, 8, 22, 16, 6, 2, 12], [10, 17, 11, 0, 19, 7, 2, 14, 12, 4, 20, 1, 13, 8, 21, 5, 3, 6, 15, 18, 9, 22, 16], [11, 14, 21, 13, 8, 17, 20, 5, 7, 9, 15, 3, 10, 22, 18, 4, 1, 19, 0, 6, 12, 16, 2], [20, 10, 11, 7, 14, 9, 16, 5, 8, 19, 4, 6, 13, 22, 2, 17, 1, 15, 21, 12, 18, 0, 3], [5, 13, 1, 3, 22, 19, 12, 18, 11, 21, 15, 6, 8, 17, 14, 9, 16, 2, 7, 20, 0, 10, 4], [9, 22, 10, 7, 3, 12, 13, 21, 6, 0, 17, 16, 8, 15, 2, 19, 1, 11, 5, 18, 20, 4, 14], [19, 3, 4, 5, 7, 13, 22, 0, 16, 20, 15, 1, 8, 17, 11, 12, 10, 6, 9, 21, 18, 14, 2], [15, 16, 8, 14, 9, 19, 10, 1, 7, 3, 17, 2, 0, 13, 5, 20, 22, 12, 18, 21, 6, 4, 11], [13, 9, 2, 22, 18, 11, 21, 19, 20, 4, 10, 8, 15, 3, 17, 6, 16, 14, 1, 7, 5, 12, 0], [14, 19, 5, 20, 0, 6, 1, 11, 3, 15, 7, 16, 10, 17, 4, 13, 18, 21, 22, 8, 12, 9, 2], [4, 9, 7, 0, 21, 11, 16, 2, 22, 17, 3, 6, 1, 15, 10, 12, 20, 18, 13, 8, 19, 5, 14], [6, 1, 8, 20, 4, 15, 14, 9, 16, 11, 2, 18, 22, 12, 7, 10, 21, 13, 0, 17, 19, 5, 3], [2, 3, 9, 10, 19, 15, 17, 8, 16, 11, 6, 18, 22, 12, 0, 20, 21, 5, 7, 14, 4, 13, 1], [0, 22, 11, 7, 14, 6, 13, 18, 16, 5, 17, 12, 4, 3, 10, 8, 21, 2, 9, 1, 20, 19, 15], [17, 15, 18, 8, 20, 6, 1, 11, 16, 5, 0, 12, 4, 3, 9, 7, 21, 19, 10, 13, 14, 2, 22], [5, 9, 19, 16, 21, 11, 3, 15, 6, 8, 22, 0, 13, 20, 1, 18, 7, 14, 4, 12, 2, 10, 17], [14, 8, 19, 5, 16, 11, 10, 0, 3, 2, 1, 6, 17, 7, 15, 21, 4, 13, 9, 20, 12, 22, 18], [2, 8, 9, 16, 20, 13, 22, 12, 21, 6, 0, 4, 14, 7, 5, 18, 19, 1, 17, 3, 10, 11, 15], [0, 15, 12, 18, 10, 13, 3, 9, 21, 6, 2, 4, 14, 7, 17, 16, 19, 11, 5, 22, 20, 1, 8], [0, 8, 4, 9, 17, 3, 7, 5, 19, 13, 11, 14, 10, 18, 2, 21, 1, 12, 6, 15, 20, 22, 16]],
   [[10, 8, 11, 19, 4, 16, 9, 6, 0, 12, 2, 20, 3, 18, 21, 15, 13, 5, 14, 22, 1, 17, 7], [16, 0, 18, 20, 12, 14, 2, 5, 10, 17, 13, 21, 4, 8, 7, 1, 3, 9, 11, 6, 15, 19, 22], [5, 10, 7, 13, 14, 18, 6, 4, 12, 11, 8, 21, 15, 16, 17, 9, 22, 19, 1, 20, 3, 0, 2], [17, 10, 21, 11, 1, 16, 8, 13, 0, 5, 18, 14, 22, 12, 3, 6, 2, 15, 9, 4, 19, 7, 20], [17, 13, 18, 14, 21, 22, 10, 15, 8, 2, 5, 7, 1, 11, 0, 20, 16, 9, 3, 4, 12, 6, 19], [5, 18, 14, 21, 17, 7, 2, 15, 0, 11, 16, 6, 8, 20, 10, 1, 13, 12, 19, 4, 3, 9, 22], [7, 16, 8, 3, 17, 22, 6, 12, 11, 18, 0, 9, 14, 1, 10, 15, 5, 20, 2, 4, 21, 19, 13], [11, 10, 5, 16, 17, 8, 12, 15, 3, 0, 22, 19, 18, 6, 21, 9, 4, 20, 1, 14, 13, 2, 7], [0, 19, 17, 13, 12, 9, 5, 3, 15, 18, 14, 2, 11, 6, 4, 22, 8, 10, 7, 21, 20, 16, 1], [11, 14, 20, 6, 18, 0, 8, 16, 9, 1, 21, 5, 19, 12, 17, 7, 3, 22, 15, 2, 13, 4, 10], [0, 15, 17, 4, 22, 16, 20, 7, 11, 5, 3, 8, 9, 13, 21, 14, 12, 19, 2, 18, 6, 1, 10], [0, 21, 10, 6, 11, 18, 9, 13, 22, 7, 4, 17, 2, 5, 12, 1, 15, 14, 3, 16, 20, 8, 19], [0, 1, 14, 11, 19, 15, 20, 13, 17, 18, 6, 22, 7, 5, 8, 12, 2, 16, 10, 3, 9, 21, 4], [6, 4, 13, 12, 9, 15, 3, 14, 17, 18, 0, 22, 7, 5, 10, 11, 2, 21, 8, 20, 19, 16, 1], [18, 10, 21, 17, 2, 14, 5, 4, 15, 12, 1, 0, 20, 9, 3, 13, 11, 19, 7, 22, 16, 8, 6], [13, 14, 3, 4, 5, 8, 7, 10, 2, 9, 0, 15, 18, 6, 17, 12, 11, 19, 16, 20, 1, 21, 22], [20, 19, 5, 7, 18, 12, 11, 8, 16, 10, 0, 4, 13, 15, 6, 22, 14, 21, 17, 9, 3, 2, 1], [0, 4, 22, 13, 8, 20, 5, 10, 2, 15, 16, 7, 19, 11, 6, 17, 21, 14, 18, 1, 9, 3, 12], [0, 12, 7, 10, 6, 5, 11, 18, 21, 20, 14, 19, 8, 13, 16, 2, 3, 22, 15, 4, 9, 1, 17], [0, 14, 15, 3, 16, 20, 6, 17, 11, 8, 21, 18, 1, 12, 13, 2, 19, 10, 9, 22, 5, 7, 4], [0, 19, 4, 5, 17, 9, 15, 6, 14, 12, 2, 13, 3, 22, 20, 16, 21, 8, 10, 1, 18, 11, 7], [0, 7, 13, 6, 20, 15, 22, 10, 21, 9, 8, 3, 17, 5, 2, 14, 11, 4, 12, 19, 18, 1, 16], [0, 1, 8, 22, 3, 12, 9, 5, 16, 10, 20, 4, 13, 15, 17, 7, 14, 2, 6, 11, 18, 21, 19], [0, 1, 17, 4, 11, 7, 18, 15, 2, 6, 9, 19, 5, 12, 16, 13, 8, 14, 20, 22, 10, 21, 3]],
   [[9, 11, 19, 0, 21, 1, 12, 6, 10, 8, 13, 22, 4, 15, 2, 3, 18, 20, 16, 17, 5, 14, 7], [3, 20, 21, 19, 13, 4, 22, 10, 7, 14, 8, 17, 12, 9, 16, 11, 5, 15, 0, 2, 1, 18, 6], [14, 22, 7, 12, 1, 8, 20, 0, 13, 4, 15, 2, 11, 10, 9, 16, 19, 17, 5, 6, 21, 18, 3], [0, 19, 14, 11, 2, 10, 18, 12, 22, 3, 6, 7, 17, 9, 5, 16, 1, 13, 4, 20, 8, 21, 15], [3, 12, 7, 10, 0, 21, 11, 2, 19, 1, 14, 5, 15, 18, 22, 13, 6, 9, 17, 20, 16, 4, 8], [8, 20, 10, 12, 4, 17, 7, 22, 1, 6, 0, 2, 9, 16, 18, 15, 5, 21, 13, 3, 11, 14, 19], [8, 15, 6, 20, 19, 0, 11, 5, 12, 21, 14, 9, 17, 16, 2, 7, 10, 4, 1, 18, 13, 3, 22], [0, 21, 18, 10, 3, 9, 20, 7, 11, 12, 22, 8, 16, 13, 15, 1, 5, 2, 19, 17, 6, 14, 4], [0, 1, 16, 19, 22, 13, 10, 12, 14, 20, 18, 3, 15, 7, 2, 5, 17, 8, 9, 4, 6, 21, 11], [0, 19, 8, 21, 1, 6, 14, 11, 4, 20, 7, 13, 22, 3, 17, 9, 10, 15, 18, 12, 5, 16, 2], [0, 19, 10, 12, 2, 3, 7, 22, 17, 5, 18, 21, 9, 11, 8, 6, 15, 4, 20, 1, 14, 16, 13], [0, 1, 8, 21, 10, 18, 20, 9, 13, 12, 7, 22, 4, 5, 3, 15, 19, 11, 2, 14, 17, 16, 6], [0, 1, 17, 4, 11, 7, 18, 15, 2, 6, 9, 19, 5, 12, 16, 13, 8, 14, 20, 22, 10, 21, 3], [0, 1, 2, 21, 9, 20, 10, 6, 12, 5, 15, 3, 11, 7, 4, 13, 22, 19, 17, 16, 14, 8, 18], [15, 18, 6, 13, 14, 20, 16, 2, 12, 5, 0, 3, 11, 7, 17, 21, 22, 8, 4, 10, 9, 19, 1], [19, 13, 17, 12, 14, 10, 1, 3, 22, 20, 0, 11, 9, 21, 5, 6, 8, 16, 15, 7, 4, 2, 18], [3, 14, 19, 13, 18, 4, 16, 7, 12, 5, 10, 15, 11, 2, 21, 17, 1, 8, 20, 0, 9, 6, 22], [8, 19, 11, 20, 12, 16, 3, 22, 6, 2, 1, 7, 0, 21, 14, 4, 18, 5, 17, 9, 15, 13, 10], [0, 18, 3, 6, 4, 10, 7, 17, 22, 20, 19, 11, 9, 21, 15, 12, 8, 2, 5, 1, 14, 16, 13], [0, 13, 11, 17, 15, 7, 21, 5, 8, 10, 2, 9, 4, 6, 19, 22, 16, 3, 20, 18, 14, 1, 12], [0, 3, 12, 2, 8, 18, 19, 6, 16, 17, 11, 5, 14, 13, 1, 15, 21, 7, 20, 9, 10, 22, 4], [0, 5, 22, 16, 12, 13, 21, 15, 17, 6, 14, 18, 19, 20, 3, 4, 2, 11, 9, 10, 8, 1, 7], [0, 20, 18, 22, 11, 7, 8, 13, 19, 10, 4, 17, 16, 14, 21, 9, 2, 3, 5, 15, 12, 1, 6], [0, 1, 4, 3, 16, 13, 14, 7, 19, 17, 10, 18, 6, 20, 12, 11, 2, 22, 15, 21, 5, 8, 9]],
   [[0, 1, 12, 18, 21, 11, 5, 20, 22, 15, 14, 9, 7, 13, 19, 6, 4, 2, 10, 3, 17, 8, 16], [0, 1, 19, 11, 2, 5, 8, 13, 3, 16, 6, 10, 20, 9, 7, 22, 14, 4, 12, 21, 15, 17, 18], [0, 1, 9, 21, 22, 7, 4, 6, 16, 19, 15, 17, 10, 14, 11, 3, 2, 18, 13, 8, 20, 12, 5], [0, 1, 7, 10, 21, 22, 15, 9, 4, 12, 8, 18, 13, 5, 3, 20, 19, 14, 6, 11, 16, 17, 2], [0, 1, 3, 22, 14, 15, 17, 5, 11, 2, 20, 6, 9, 18, 13, 4, 8, 19, 7, 21, 12, 16, 10], [0, 1, 6, 15, 8, 18, 13, 5, 9, 11, 12, 17, 7, 20, 21, 14, 16, 4, 10, 3, 22, 19, 2], [0, 1, 2, 8, 5, 14, 15, 10, 11, 20, 13, 21, 3, 6, 9, 7, 18, 16, 19, 22, 4, 12, 17], [0, 1, 2, 12, 20, 4, 13, 15, 3, 14, 7, 8, 21, 10, 5, 6, 17, 22, 16, 18, 9, 11, 19], [0, 1, 2, 11, 14, 9, 7, 13, 21, 4, 6, 12, 8, 15, 20, 10, 19, 18, 22, 17, 5, 3, 16], [7, 4, 11, 22, 9, 18, 19, 2, 5, 14, 13, 12, 3, 8, 0, 10, 15, 17, 21, 16, 6, 20, 1], [8, 15, 6, 20, 19, 0, 11, 5, 12, 21, 14, 9, 17, 16, 2, 7, 10, 4, 1, 18, 13, 3, 22], [8, 0, 1, 20, 14, 11, 18, 16, 4, 7, 22, 2, 6, 17, 5, 19, 3, 15, 9, 13, 12, 21, 10], [12, 7, 11, 9, 21, 14, 20, 8, 2, 4, 6, 22, 17, 13, 3, 0, 1, 10, 18, 5, 15, 19, 16], [10, 13, 18, 3, 19, 16, 6, 0, 2, 11, 14, 8, 7, 22, 12, 15, 1, 4, 9, 21, 17, 20, 5], [8, 9, 0, 19, 2, 5, 22, 3, 21, 17, 16, 7, 10, 6, 12, 11, 20, 13, 14, 18, 15, 1, 4], [3, 5, 14, 15, 12, 20, 7, 22, 9, 0, 8, 1, 6, 10, 21, 13, 18, 19, 16, 2, 17, 4, 11], [0, 16, 4, 9, 18, 14, 10, 11, 20, 13, 5, 3, 7, 17, 2, 22, 15, 12, 6, 1, 19, 21, 8], [0, 1, 18, 14, 12, 13, 22, 10, 2, 7, 4, 17, 9, 8, 19, 15, 21, 20, 5, 16, 6, 3, 11], [0, 1, 2, 11, 14, 9, 7, 13, 21, 4, 6, 12, 8, 15, 20, 10, 19, 18, 22, 17, 5, 3, 16], [10, 22, 7, 11, 18, 9, 2, 13, 17, 20, 19, 12, 8, 3, 4, 0, 6, 14, 1, 21, 5, 15, 16], [12, 10, 9, 6, 15, 17, 8, 11, 0, 19, 22, 2, 4, 21, 14, 20, 5, 18, 16, 1, 3, 13, 7], [0, 20, 8, 3, 1, 12, 2, 17, 4, 13, 14, 19, 18, 5, 9, 11, 22, 15, 10, 16, 21, 6, 7], [0, 21, 10, 17, 12, 7, 13, 5, 8, 11, 9, 2, 22, 1, 20, 4, 16, 3, 19, 14, 18, 6, 15], [0, 21, 16, 14, 15, 1, 9, 22, 20, 18, 19, 17, 4, 5, 10, 7, 3, 8, 11, 12, 13, 6, 2]],
   [[0, 21, 16, 17, 10, 18, 22, 5, 6, 15, 9, 4, 20, 7, 13, 19, 12, 11, 2, 8, 1, 14, 3], [0, 1, 6, 17, 21, 20, 16, 11, 10, 7, 13, 8, 2, 18, 15, 4, 3, 19, 9, 12, 14, 22, 5], [0, 1, 17, 19, 16, 6, 15, 12, 21, 11, 18, 5, 2, 13, 10, 9, 22, 20, 3, 14, 7, 4, 8], [0, 1, 22, 14, 8, 13, 18, 2, 10, 7, 3, 19, 9, 12, 17, 6, 20, 21, 11, 16, 15, 4, 5], [0, 1, 22, 19, 17, 7, 2, 12, 4, 8, 18, 9, 10, 6, 15, 3, 16, 11, 5, 21, 13, 14, 20], [0, 1, 2, 11, 14, 13, 16, 9, 18, 12, 6, 4, 22, 5, 3, 17, 19, 21, 8, 10, 15, 20, 7], [0, 1, 2, 12, 20, 4, 13, 15, 3, 14, 7, 8, 21, 10, 5, 6, 17, 22, 16, 18, 9, 11, 19], [0, 1, 2, 8, 5, 14, 15, 10, 11, 20, 13, 21, 3, 6, 9, 7, 18, 16, 19, 22, 4, 12, 17], [0, 1, 2, 21, 9, 20, 10, 6, 12, 5, 15, 3, 11, 7, 4, 13, 22, 19, 17, 16, 14, 8, 18], [0, 1, 2, 3, 4, 7, 22, 5, 17, 11, 10, 9, 18, 20, 21, 19, 16, 8, 12, 15, 13, 14, 6], [11, 12, 14, 17, 16, 2, 20, 6, 7, 19, 1, 0, 22, 13, 15, 5, 3, 4, 18, 9, 8, 21, 10], [8, 19, 12, 17, 13, 22, 1, 9, 16, 7, 0, 18, 4, 3, 11, 5, 14, 15, 10, 20, 21, 2, 6], [7, 11, 15, 16, 14, 9, 3, 19, 22, 17, 6, 0, 20, 13, 1, 12, 5, 21, 4, 18, 2, 10, 8], [0, 6, 9, 5, 21, 22, 20, 12, 16, 7, 8, 18, 4, 3, 10, 17, 14, 2, 11, 1, 13, 15, 19], [0, 19, 18, 12, 10, 20, 3, 11, 14, 22, 2, 4, 21, 5, 8, 16, 15, 9, 7, 6, 13, 1, 17], [0, 1, 21, 9, 15, 19, 13, 20, 8, 12, 22, 6, 5, 7, 17, 18, 2, 16, 10, 3, 11, 14, 4], [0, 1, 18, 12, 14, 9, 7, 13, 6, 19, 21, 11, 5, 20, 15, 22, 4, 2, 10, 3, 8, 17, 16], [0, 1, 2, 14, 11, 13, 10, 22, 18, 7, 19, 3, 9, 5, 4, 20, 6, 15, 8, 16, 21, 17, 12], [0, 1, 2, 17, 7, 21, 19, 10, 9, 13, 20, 14, 3, 22, 11, 5, 12, 16, 15, 6, 4, 18, 8], [0, 1, 2, 4, 3, 7, 15, 18, 17, 6, 16, 21, 5, 20, 9, 14, 10, 13, 12, 22, 8, 19, 11], [0, 1, 2, 18, 13, 4, 20, 19, 3, 21, 5, 17, 14, 10, 7, 22, 8, 6, 16, 12, 11, 9, 15], [18, 20, 19, 0, 5, 16, 22, 8, 10, 13, 7, 15, 12, 4, 9, 17, 14, 11, 21, 3, 1, 2, 6], [2, 21, 4, 7, 22, 5, 13, 11, 0, 1, 12, 15, 14, 17, 18, 20, 10, 9, 19, 3, 16, 8, 6], [10, 6, 21, 13, 12, 9, 5, 15, 3, 14, 18, 7, 11, 19, 20, 1, 8, 0, 2, 17, 4, 16, 22]],
   [[5, 18, 14, 21, 17, 7, 2, 15, 0, 11, 16, 6, 8, 20, 10, 1, 13, 12, 19, 4, 3, 9, 22], [0, 4, 6, 3, 8, 13, 21, 22, 2, 14, 18, 15, 5, 9, 10, 17, 19, 7, 12, 11, 1, 20, 16], [0, 1, 12, 16, 15, 22, 2, 9, 11, 18, 8, 7, 19, 10, 20, 14, 6, 3, 13, 17, 5, 4, 21], [0, 1, 2, 14, 11, 13, 10, 22, 18, 7, 19, 3, 9, 5, 4, 20, 6, 15, 8, 16, 21, 17, 12], [0, 1, 2, 3, 4, 7, 22, 5, 17, 11, 10, 9, 18, 20, 21, 19, 16, 8, 12, 15, 13, 14, 6], [10, 6, 21, 13, 12, 15, 22, 9, 0, 7, 18, 14, 2, 4, 16, 17, 8, 3, 11, 1, 19, 20, 5], [0, 7, 10, 1, 21, 15, 5, 13, 20, 3, 8, 9, 18, 22, 2, 14, 19, 4, 16, 11, 17, 6, 12], [0, 21, 15, 16, 19, 5, 4, 2, 12, 20, 3, 6, 1, 13, 10, 18, 14, 22, 7, 11, 9, 8, 17], [0, 21, 14, 11, 17, 13, 3, 1, 10, 9, 7, 16, 18, 2, 15, 5, 22, 12, 20, 19, 4, 8, 6], [0, 1, 7, 21, 8, 5, 13, 2, 4, 11, 10, 9, 20, 6, 14, 15, 19, 17, 22, 16, 12, 3, 18], [0, 1, 2, 4, 10, 13, 12, 22, 8, 19, 3, 7, 15, 18, 17, 6, 16, 21, 5, 20, 9, 14, 11], [0, 1, 2, 11, 14, 13, 16, 9, 18, 12, 6, 4, 22, 5, 3, 17, 19, 21, 8, 10, 15, 20, 7], [0, 1, 2, 4, 3, 12, 9, 5, 20, 14, 16, 22, 18, 17, 15, 6, 10, 8, 7, 21, 13, 11, 19], [0, 1, 2, 3, 16, 17, 18, 19, 20, 21, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 22], [4, 22, 19, 9, 14, 17, 13, 2, 20, 21, 0, 5, 6, 7, 12, 3, 10, 15, 8, 18, 16, 11, 1], [21, 12, 15, 20, 10, 2, 7, 22, 17, 9, 1, 0, 18, 14, 13, 19, 3, 16, 6, 5, 11, 8, 4], [0, 9, 6, 12, 4, 7, 3, 21, 15, 18, 2, 16, 8, 19, 11, 10, 13, 5, 17, 22, 14, 1, 20], [0, 16, 22, 7, 20, 14, 17, 4, 2, 9, 10, 19, 13, 5, 18, 11, 15, 8, 12, 1, 21, 3, 6], [0, 21, 18, 6, 16, 19, 3, 15, 9, 12, 2, 10, 20, 13, 5, 4, 7, 17, 11, 22, 8, 1, 14], [0, 1, 20, 22, 3, 6, 21, 17, 10, 4, 14, 16, 7, 9, 11, 19, 8, 2, 18, 5, 12, 15, 13], [0, 1, 16, 3, 10, 7, 8, 19, 13, 11, 4, 12, 18, 14, 6, 5, 2, 22, 9, 15, 17, 20, 21], [0, 1, 15, 21, 9, 13, 7, 14, 20, 6, 22, 18, 17, 19, 11, 12, 2, 10, 4, 3, 5, 8, 16], [0, 1, 11, 16, 5, 19, 12, 9, 2, 18, 21, 13, 17, 6, 10, 7, 20, 8, 14, 22, 4, 15, 3], [0, 1, 6, 12, 15, 5, 17, 14, 22, 9, 8, 21, 19, 7, 13, 18, 16, 2, 4, 3, 11, 20, 10]],
   [[0, 1, 22, 21, 15, 6, 12, 16, 7, 3, 9, 11, 17, 4, 10, 20, 2, 18, 5, 13, 19, 14, 8], [0, 1, 2, 15, 21, 14, 4, 18, 6, 17, 9, 3, 5, 19, 16, 7, 22, 13, 11, 10, 8, 20, 12], [0, 1, 2, 20, 17, 8, 9, 4, 5, 14, 7, 15, 3, 18, 21, 19, 12, 10, 13, 22, 16, 6, 11], [0, 1, 2, 19, 14, 21, 4, 12, 22, 8, 11, 3, 7, 15, 16, 5, 6, 20, 9, 10, 17, 13, 18], [0, 1, 2, 9, 15, 8, 16, 12, 18, 11, 21, 3, 17, 13, 10, 19, 22, 7, 5, 4, 20, 14, 6], [0, 1, 2, 16, 3, 19, 9, 12, 11, 18, 10, 15, 17, 14, 21, 8, 4, 7, 6, 22, 20, 13, 5], [3, 2, 7, 4, 17, 14, 18, 0, 5, 12, 6, 10, 19, 21, 8, 16, 11, 13, 1, 20, 22, 15, 9], [3, 8, 12, 17, 20, 10, 2, 7, 22, 14, 6, 0, 4, 19, 11, 5, 9, 1, 16, 21, 13, 15, 18], [19, 16, 13, 0, 5, 9, 21, 7, 17, 20, 10, 12, 8, 3, 1, 11, 6, 15, 4, 2, 18, 14, 22], [0, 17, 8, 15, 18, 10, 13, 7, 22, 1, 21, 19, 5, 2, 12, 9, 20, 16, 6, 14, 3, 11, 4], [0, 19, 17, 2, 4, 18, 3, 6, 16, 12, 5, 11, 15, 22, 20, 14, 21, 7, 1, 10, 9, 13, 8], [0, 19, 17, 11, 20, 12, 6, 22, 13, 4, 3, 15, 16, 14, 9, 5, 10, 1, 8, 7, 18, 2, 21], [0, 1, 13, 5, 8, 3, 14, 22, 21, 19, 2, 7, 12, 17, 16, 4, 18, 10, 6, 9, 11, 15, 20], [0, 3, 14, 9, 17, 6, 21, 1, 10, 11, 2, 19, 22, 7, 15, 5, 18, 20, 12, 16, 8, 4, 13], [0, 1, 7, 21, 8, 5, 13, 2, 4, 11, 10, 9, 20, 6, 14, 15, 19, 17, 22, 16, 12, 3, 18], [0, 1, 2, 10, 3, 18, 15, 11, 8, 20, 4, 22, 6, 5, 21, 12, 16, 14, 13, 9, 19, 17, 7], [0, 1, 2, 3, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 4, 5, 6, 7, 8, 9, 22], [0, 1, 17, 4, 9, 19, 5, 12, 16, 13, 8, 14, 20, 22, 10, 21, 11, 7, 18, 15, 2, 6, 3], [0, 1, 17, 4, 9, 12, 3, 19, 7, 14, 8, 13, 18, 2, 6, 15, 11, 16, 20, 21, 22, 10, 5], [0, 1, 2, 12, 7, 4, 6, 5, 10, 21, 17, 19, 18, 16, 11, 9, 20, 8, 3, 14, 13, 15, 22], [0, 1, 2, 3, 10, 5, 15, 14, 13, 12, 16, 22, 19, 18, 21, 20, 4, 11, 8, 9, 6, 7, 17], [16, 17, 14, 20, 6, 5, 9, 2, 13, 12, 0, 22, 19, 18, 8, 3, 4, 7, 21, 15, 10, 11, 1], [12, 8, 7, 13, 4, 2, 18, 17, 5, 20, 1, 0, 15, 6, 9, 14, 3, 10, 19, 22, 11, 21, 16], [0, 17, 22, 14, 21, 15, 18, 8, 4, 5, 11, 19, 10, 3, 16, 13, 7, 2, 12, 1, 6, 9, 20]],
   [[0, 20, 19, 8, 16, 18, 3, 12, 7, 15, 2, 10, 21, 14, 11, 4, 9, 22, 5, 17, 6, 1, 13], [0, 10, 17, 18, 13, 6, 5, 16, 2, 20, 4, 14, 9, 22, 15, 11, 7, 21, 8, 1, 12, 3, 19], [0, 2, 15, 10, 19, 8, 9, 16, 14, 6, 12, 1, 17, 7, 21, 3, 18, 11, 4, 22, 13, 5, 20], [0, 11, 22, 8, 15, 9, 12, 20, 16, 17, 5, 13, 4, 3, 10, 7, 19, 2, 6, 1, 18, 21, 14], [0, 1, 13, 17, 3, 19, 12, 5, 4, 16, 6, 10, 18, 20, 11, 14, 21, 2, 15, 22, 8, 7, 9], [0, 1, 10, 3, 4, 18, 21, 14, 9, 11, 16, 8, 15, 6, 19, 22, 2, 17, 20, 7, 5, 13, 12], [0, 1, 7, 12, 20, 9, 18, 6, 13, 19, 17, 15, 5, 14, 11, 8, 2, 4, 16, 3, 22, 21, 10], [0, 1, 5, 16, 11, 3, 7, 15, 19, 2, 20, 6, 10, 9, 22, 8, 21, 14, 12, 4, 17, 13, 18], [0, 1, 2, 7, 12, 6, 16, 15, 19, 5, 20, 3, 22, 14, 10, 18, 17, 9, 11, 4, 21, 13, 8], [0, 1, 2, 13, 5, 21, 20, 16, 22, 6, 18, 7, 3, 15, 12, 14, 8, 4, 9, 17, 10, 19, 11], [0, 1, 2, 6, 11, 10, 22, 13, 16, 20, 14, 21, 18, 4, 15, 17, 19, 5, 3, 9, 8, 7, 12], [0, 1, 2, 5, 18, 22, 16, 19, 15, 7, 13, 3, 6, 21, 10, 12, 8, 11, 9, 4, 14, 20, 17], [0, 1, 2, 10, 3, 14, 20, 8, 11, 15, 4, 7, 5, 6, 12, 21, 16, 18, 19, 17, 13, 9, 22], [0, 1, 2, 22, 9, 10, 6, 20, 16, 13, 21, 14, 12, 4, 19, 8, 15, 7, 3, 11, 17, 5, 18]]]

/-- Stabilizer chain data. -/
def fourLvls : List Lvl :=
  [⟨0, [],
    [⟨10, 1, 0, 1, 0⟩, ⟨1, 2, 0, 2, 0⟩, ⟨9, 164, 0, 2, 10⟩, ⟨17, 186, 0, 185, 10⟩, ⟨6, 205, 0, 204, 10⟩, ⟨15, 230, 0, 229, 10⟩, ⟨4, 302, 0, 301, 10⟩, ⟨16, 333, 0, 332, 10⟩, ⟨22, 6, 0, 1, 1⟩, ⟨5, 187, 0, 185, 9⟩, ⟨18, 206, 0, 204, 9⟩, ⟨11, 274, 0, 273, 9⟩, ⟨21, 303, 0, 301, 9⟩, ⟨12, 334, 0, 332, 9⟩, ⟨14, 188, 0, 2, 17⟩, ⟨2, 189, 0, 185, 17⟩, ⟨19, 231, 0, 229, 17⟩, ⟨8, 275, 0, 273, 17⟩, ⟨13, 207, 0, 185, 6⟩, ⟨20, 208, 0, 204, 6⟩, ⟨3, 232, 0, 1, 15⟩, ⟨7, 276, 0, 273, 5⟩]⟩,
   ⟨1, [],
    [⟨22, 185, 0, 185, 1⟩, ⟨15, 190, 0, 185, 22⟩, ⟨4, 209, 0, 204, 22⟩, ⟨18, 234, 0, 229, 22⟩, ⟨6, 277, 0, 273, 22⟩, ⟨17, 335, 0, 332, 22⟩, ⟨8, 191, 0, 185, 15⟩, ⟨12, 210, 0, 204, 15⟩, ⟨13, 235, 0, 229, 15⟩, ⟨19, 278, 0, 273, 15⟩, ⟨9, 304, 0, 301, 15⟩, ⟨20, 336, 0, 332, 15⟩, ⟨14, 211, 0, 185, 4⟩, ⟨16, 305, 0, 301, 4⟩, ⟨10, 337, 0, 332, 4⟩, ⟨2, 338, 0, 185, 17⟩, ⟨11, 339, 0, 301, 17⟩, ⟨7, 213, 0, 204, 12⟩, ⟨3, 236, 0, 185, 13⟩, ⟨5, 237, 0, 204, 13⟩, ⟨21, 306, 0, 301, 9⟩]⟩,
   ⟨2, [],
    [⟨14, 204, 0, 204, 2⟩, ⟨8, 214, 0, 204, 14⟩, ⟨4, 239, 0, 229, 14⟩, ⟨21, 279, 0, 273, 14⟩, ⟨17, 215, 0, 204, 8⟩, ⟨12, 240, 0, 229, 8⟩, ⟨20, 307, 0, 301, 8⟩, ⟨13, 340, 0, 332, 8⟩, ⟨19, 241, 0, 204, 4⟩, ⟨9, 242, 0, 229, 4⟩, ⟨16, 308, 0, 301, 4⟩, ⟨10, 341, 0, 332, 4⟩, ⟨15, 309, 0, 301, 21⟩, ⟨7, 342, 0, 332, 21⟩, ⟨11, 310, 0, 301, 17⟩, ⟨18, 280, 0, 273, 12⟩, ⟨6, 311, 0, 301, 12⟩, ⟨5, 343, 0, 204, 13⟩, ⟨3, 244, 0, 204, 19⟩, ⟨22, 312, 0, 229, 16⟩]⟩,
   ⟨3, [],
    [⟨21, 229, 0, 229, 3⟩, ⟨8, 246, 0, 229, 21⟩, ⟨14, 281, 0, 273, 21⟩, ⟨15, 313, 0, 301, 21⟩, ⟨7, 344, 0, 332, 21⟩, ⟨12, 247, 0, 229, 8⟩, ⟨17, 282, 0, 273, 8⟩, ⟨20, 314, 0, 301, 8⟩, ⟨13, 345, 0, 332, 8⟩, ⟨4, 283, 0, 229, 14⟩, ⟨19, 315, 0, 273, 15⟩, ⟨9, 316, 0, 301, 15⟩, ⟨6, 346, 0, 229, 7⟩, ⟨5, 347, 0, 273, 7⟩, ⟨11, 248, 0, 229, 12⟩, ⟨18, 284, 0, 273, 12⟩, ⟨16, 317, 0, 301, 4⟩, ⟨10, 348, 0, 332, 4⟩, ⟨22, 349, 0, 273, 6⟩]⟩]

end M23Cert

open MathieuM23 M23Cert

set_option maxRecDepth 100000 in
theorem fourBase : (List.range 4).all (fun k => Tget fourTabs k == tab (basePerms.getD k 1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem fourSlp : slpChk (Tget fourTabs) 3 fourProg = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem fourLvlsOk : fourChk (Tget fourTabs) (4 + fourProg.length) [] fourLvls = true := by
  decide +kernel

theorem solution : MulAction.IsMultiplyPretransitive M23 (Fin 23) 4 := by
  have hget : ∀ k < 4 + fourProg.length, tab (P fourProg k) = Tget fourTabs k := by
    apply slp_tab _ _ _ fourSlp
    intro k hk
    have := List.all_eq_true.mp fourBase k (List.mem_range.mpr hk)
    simp only [beq_iff_eq] at this
    exact this.symm
  obtain ⟨L0, L1, L2, L3, hL⟩ : ∃ L0 L1 L2 L3, fourLvls = [L0, L1, L2, L3] := ⟨_, _, _, _, rfl⟩
  refine four_of_check fourProg (Tget fourTabs) hget L0 L1 L2 L3 ?_
  rw [← hL]
  exact fourLvlsOk
