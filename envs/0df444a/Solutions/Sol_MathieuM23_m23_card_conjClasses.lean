-- Prove2me | solution 1 for MathieuM23.m23_card_conjClasses
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-05T12:34:01.558144+00:00
-- url     : https://prove2.me/submissions/1b55be66-4b2f-4862-9e24-edcaf1b67dff

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
# One step of a stabilizer chain (Schreier's lemma, orbit–stabilizer)

Let `K = ⟨S⟩` be a subgroup of `Sym(Fin 23)`, `b` a point, `Orb` a finite set of points containing
`b`, and `t : Fin 23 → Perm` a candidate transversal (`t y b = y`, `t y ∈ K`, `t b = 1`).  If `S`
preserves `Orb` and all Schreier generators `t(s y)⁻¹ s t(y)` lie in a subgroup `K'` of `K` fixing
`b`, then `|K| = |Orb| · |K'|`.
-/

namespace M23Cert

open Equiv

/-- Factorization through the transversal: every element of `⟨S⟩` maps `b` into `Orb`, and
`t(g b)⁻¹ g` lies in `K'`. -/
theorem level_factor (S : Set (Perm (Fin 23))) (K' : Subgroup (Perm (Fin 23))) (b : Fin 23)
    (Orb : Finset (Fin 23)) (t : Fin 23 → Perm (Fin 23))
    (hb : b ∈ Orb) (htb : t b = 1)
    (hS : ∀ s ∈ S, ∀ y ∈ Orb, s y ∈ Orb ∧ (t (s y))⁻¹ * s * t y ∈ K') :
    (∀ g ∈ Subgroup.closure S, ∀ y ∈ Orb, g y ∈ Orb) ∧
      ∀ g ∈ Subgroup.closure S, (t (g b))⁻¹ * g ∈ K' := by
  classical
  -- `closure S` preserves `Orb`
  have hcl : ∀ g ∈ Subgroup.closure S, ∀ y ∈ Orb, g y ∈ Orb := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact fun y hy => (hS x hx y hy).1
    | one => exact fun y hy => by simpa using hy
    | mul x y _ _ hx hy => exact fun z hz => by simpa using hx _ (hy z hz)
    | inv x _ hx =>
      intro y hy
      have himg : Orb.image x = Orb := by
        apply Finset.eq_of_subset_of_card_le
        · intro a ha
          obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
          exact hx c hc
        · rw [Finset.card_image_of_injective _ x.injective]
      have : y ∈ Orb.image x := by rw [himg]; exact hy
      obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp this
      have : x⁻¹ y = z := by rw [← hzy]; simp
      rw [this]; exact hz
  -- every element of `closure S` factors through the transversal
  have hP : ∀ g ∈ Subgroup.closure S, (t (g b))⁻¹ * g ∈ K' := by
    intro g hg
    induction hg using Subgroup.closure_induction_left with
    | one => simp [htb]
    | mul_left s hs g hg ih =>
      have hgb : g b ∈ Orb := hcl g hg b hb
      have h1 := (hS s hs (g b) hgb).2
      have := K'.mul_mem h1 ih
      convert this using 1
      simp [mul_assoc]
    | inv_mul_cancel s hs g hg ih =>
      have hgb : g b ∈ Orb := hcl g hg b hb
      have hsinv : s⁻¹ ∈ Subgroup.closure S := inv_mem (Subgroup.subset_closure hs)
      have hz : s⁻¹ (g b) ∈ Orb := hcl _ hsinv _ hgb
      have h1 := (hS s hs (s⁻¹ (g b)) hz).2
      have h1' : (t (s (s⁻¹ (g b))))⁻¹ * s * t (s⁻¹ (g b)) = (t (g b))⁻¹ * s * t (s⁻¹ (g b)) := by
        simp
      rw [h1'] at h1
      have := K'.mul_mem (K'.inv_mem h1) ih
      convert this using 1
      simp [mul_assoc]
  exact ⟨hcl, hP⟩

theorem level_step (S : Set (Perm (Fin 23))) (K' : Subgroup (Perm (Fin 23))) (b : Fin 23)
    (Orb : Finset (Fin 23)) (t : Fin 23 → Perm (Fin 23))
    (hb : b ∈ Orb) (htb : t b = 1)
    (ht : ∀ y ∈ Orb, t y ∈ Subgroup.closure S ∧ t y b = y)
    (hS : ∀ s ∈ S, ∀ y ∈ Orb, s y ∈ Orb ∧ (t (s y))⁻¹ * s * t y ∈ K')
    (hK' : K' ≤ Subgroup.closure S) (hfix : ∀ g ∈ K', g b = b) :
    Nat.card (Subgroup.closure S) = Orb.card * Nat.card K' := by
  classical
  obtain ⟨hcl, hP⟩ := level_factor S K' b Orb t hb htb hS
  -- orbit–stabilizer
  let K := Subgroup.closure S
  have horb : MulAction.orbit K b = (Orb : Set (Fin 23)) := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      exact hcl g.1 g.2 b hb
    · intro hy
      obtain ⟨h1, h2⟩ := ht y hy
      exact ⟨⟨t y, h1⟩, h2⟩
  have hstab : Nat.card (MulAction.stabilizer K b) = Nat.card K' := by
    have hmap : (MulAction.stabilizer K b).map K.subtype = K' := by
      ext g
      constructor
      · rintro ⟨k, hk, rfl⟩
        have hkb : (k : Perm (Fin 23)) b = b := hk
        have := hP k.1 k.2
        rwa [hkb, htb, inv_one, one_mul] at this
      · intro hg
        refine ⟨⟨g, hK' hg⟩, ?_, rfl⟩
        simpa using hfix g hg
    rw [← hmap]
    exact (Subgroup.card_map_of_injective K.subtype_injective).symm
  have hidx := MulAction.index_stabilizer K b
  have hcard := Subgroup.card_mul_index (MulAction.stabilizer K b)
  rw [hidx, horb, hstab, Set.ncard_coe_finset] at hcard
  rw [← hcard, mul_comm]

end M23Cert

/-!
# Verified Schreier–Sims certificate

The checker `chk` verifies a stabilizer chain given as a list of levels.  `card_chain` shows that
if the check passes, the subgroup generated by the generators of the first level has cardinality
equal to the product of the orbit lengths.
-/

namespace M23Cert

open MathieuM23

/-- Sifting a table through the remaining levels: succeeds iff it is a product of transversal
elements of the levels. -/
def sift (get : ℕ → Tab) : List Lvl → Tab → Bool
  | [], h => h == tid
  | L :: Ls, h =>
    match lk L.all (tget h L.b) with
    | none => false
    | some e => sift get Ls (tmul (get e.ki) h)

/-- Check the Schreier tree: every non-root entry is a generator times its (earlier) parent. -/
def treeOk (get : ℕ → Tab) (gens : List ℕ) : List Ent → List Ent → Bool
  | _, [] => true
  | done, e :: rest =>
    (match lk done e.p with
      | none => false
      | some q => gens.contains e.s && (get e.k == tmul (get e.s) (get q.k))) &&
    treeOk get gens (done ++ [e]) rest

/-- The recorded inverses are inverses. -/
def invOk (get : ℕ → Tab) (N : ℕ) (L : Lvl) : Bool :=
  L.all.all (fun e => decide (e.ki < N) && (tmul (get e.k) (get e.ki) == tid))

/-- The generators lie in range and fix the earlier base points. -/
def gensOk (get : ℕ → Tab) (N : ℕ) (prev : List ℕ) (L : Lvl) : Bool :=
  L.gens.all (fun s => decide (s < N) && prev.all (fun p => tget (get s) p == p))

/-- The generators of the next level are among those of this level. -/
def nested (L : Lvl) : List Lvl → Bool
  | [] => true
  | L' :: _ => L'.gens.all (fun s => L.gens.contains s)

/-- All Schreier generators of the level sift through the lower levels. -/
def schreier (get : ℕ → Tab) (L : Lvl) (Ls : List Lvl) : Bool :=
  L.gens.all (fun s => L.all.all (fun e =>
    match lk L.all (tget (get s) e.x) with
    | none => false
    | some f => sift get Ls (tmul (get f.ki) (tmul (get s) (get e.k)))))

def lvlOk (get : ℕ → Tab) (N : ℕ) (prev : List ℕ) (L : Lvl) (Ls : List Lvl) : Bool :=
  entOk get N prev L && invOk get N L && (get 0 == tid) &&
  treeOk get L.gens [⟨L.b, 0, 0, 0, L.b⟩] L.tr && gensOk get N prev L && nested L Ls &&
  schreier get L Ls

def chk (get : ℕ → Tab) (N : ℕ) : List ℕ → List Lvl → Bool
  | _, [] => true
  | prev, L :: Ls => lvlOk get N prev L Ls && chk get N (prev ++ [L.b]) Ls

/-- The generators of a level, as permutations. -/
def Ggen (prog : List (ℕ × ℕ × ℕ)) (L : Lvl) : Set (Equiv.Perm (Fin 23)) :=
  {g | ∃ s ∈ L.gens, g = P prog s}

/-- The subgroup generated by the generators of a level. -/
def KL (prog : List (ℕ × ℕ × ℕ)) (L : Lvl) : Subgroup (Equiv.Perm (Fin 23)) :=
  Subgroup.closure (Ggen prog L)

/-- The subgroup attached to a chain of levels. -/
def Kls (prog : List (ℕ × ℕ × ℕ)) : List Lvl → Subgroup (Equiv.Perm (Fin 23))
  | [] => ⊥
  | L :: _ => KL prog L

section Soundness

variable {prog : List (ℕ × ℕ × ℕ)} {get : ℕ → Tab} {N : ℕ}

theorem tget_P (hget : ∀ k < N, tab (P prog k) = get k) {k i : ℕ} (hk : k < N) (hi : i < 23) :
    tget (get k) i = ((P prog k) (fo i) : ℕ) := by
  have := tget_tab (P prog k) (fo i)
  rw [fo_val hi] at this
  rw [← hget k hk]
  exact this

theorem P_eq_of_tab (hget : ∀ k < N, tab (P prog k) = get k) {k : ℕ} (hk : k < N)
    (h : get k = tid) : P prog k = 1 := by
  apply tab_inj
  rw [hget k hk, h, tab_one]

theorem P_mul_of_tab (hget : ∀ k < N, tab (P prog k) = get k) {a b c : ℕ} (ha : a < N)
    (hb : b < N) (hc : c < N) (h : get c = tmul (get a) (get b)) :
    P prog c = P prog a * P prog b := by
  apply tab_inj
  rw [tab_mul, hget a ha, hget b hb, hget c hc, h]

/-- Facts extracted from a successful level check. -/
structure LvlFacts (prog : List (ℕ × ℕ × ℕ)) (get : ℕ → Tab) (N : ℕ) (prev : List ℕ) (L : Lvl)
    (Ls : List Lvl) : Prop where
  hb : L.b < 23
  hnp : L.b ∉ prev
  hnd : (L.all.map (·.x)).Nodup
  hx : ∀ e ∈ L.all, e.x < 23
  hmap : ∀ e ∈ L.all, P prog e.k (fo L.b) = fo e.x
  hinv : ∀ e ∈ L.all, P prog e.ki * P prog e.k = 1
  hmem : ∀ e ∈ L.all, P prog e.k ∈ KL prog L
  hroot : P prog 0 = 1
  hgfix : ∀ s ∈ L.gens, ∀ p ∈ prev, P prog s (fo p) = fo p
  hnest : Kls prog Ls ≤ KL prog L
  hsch : ∀ s ∈ L.gens, ∀ e ∈ L.all, ∃ f ∈ L.all, (f.x : ℕ) = (P prog s (fo e.x) : ℕ) ∧
    sift get Ls (tmul (get f.ki) (tmul (get s) (get e.k))) = true
  hkN : ∀ e ∈ L.all, e.k < N ∧ e.ki < N
  hsN : ∀ s ∈ L.gens, s < N

theorem tree_sound (hget : ∀ k < N, tab (P prog k) = get k) (gens : List ℕ)
    (hgens : ∀ s ∈ gens, s < N) :
    ∀ (todo done : List Ent), treeOk get gens done todo = true →
      (∀ q ∈ done ++ todo, q.k < N) →
      (∀ q ∈ done, P prog q.k ∈ Subgroup.closure {g | ∃ s ∈ gens, g = P prog s}) →
      ∀ e ∈ todo, P prog e.k ∈ Subgroup.closure {g | ∃ s ∈ gens, g = P prog s} := by
  intro todo
  induction todo with
  | nil => intro done _ _ _ e he; simp at he
  | cons e rest ih =>
    intro done hok hN hdone e' he'
    simp only [treeOk, Bool.and_eq_true] at hok
    obtain ⟨hmatch, hrest⟩ := hok
    cases hl : lk done e.p with
    | none => simp [hl] at hmatch
    | some q =>
      simp only [hl, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hmatch
      obtain ⟨hs, hk⟩ := hmatch
      obtain ⟨hq, -⟩ := lk_some hl
      have hqN := hN q (by simp [hq])
      have heN := hN e (by simp)
      have hPe : P prog e.k = P prog e.s * P prog q.k :=
        P_mul_of_tab hget (hgens _ hs) hqN heN hk
      have hmemE : P prog e.k ∈ Subgroup.closure {g | ∃ s ∈ gens, g = P prog s} := by
        rw [hPe]
        exact mul_mem (Subgroup.subset_closure ⟨e.s, hs, rfl⟩) (hdone q hq)
      rcases List.mem_cons.mp he' with rfl | he''
      · exact hmemE
      · refine ih (done ++ [e]) hrest ?_ ?_ e' he''
        · intro q hq
          apply hN
          simp only [List.mem_append, List.mem_cons] at hq ⊢
          tauto
        · intro q hq
          rcases List.mem_append.mp hq with hq | hq
          · exact hdone q hq
          · rw [List.mem_singleton.mp hq]; exact hmemE

theorem lvl_facts (hget : ∀ k < N, tab (P prog k) = get k) {prev : List ℕ}
    (hprev : ∀ p ∈ prev, p < 23) {L : Lvl} {Ls : List Lvl}
    (h : lvlOk get N prev L Ls = true) : LvlFacts prog get N prev L Ls := by
  simp only [lvlOk, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hent, hinv⟩, h0⟩, htree⟩, hgens⟩, hnest⟩, hsch⟩ := h
  simp only [entOk, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.all_eq_true,
    beq_iff_eq] at hent
  obtain ⟨⟨⟨hb, hnp⟩, hnd⟩, hall⟩ := hent
  simp only [invOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hinv
  simp only [gensOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hgens
  have hroot_mem : (⟨L.b, 0, 0, 0, L.b⟩ : Ent) ∈ L.all := by simp [Lvl.all]
  have hr := hall _ hroot_mem
  have hN0 : 0 < N := hr.1.1.2
  have hP0 : P prog 0 = 1 := P_eq_of_tab hget hN0 (by simpa using h0)
  have hmemAll : ∀ e ∈ L.all, P prog e.k ∈ KL prog L := by
    intro e he
    have hN' : ∀ q ∈ [(⟨L.b, 0, 0, 0, L.b⟩ : Ent)] ++ L.tr, q.k < N := by
      intro q hq
      exact (hall q (by simpa [Lvl.all] using hq)).1.1.2
    have := tree_sound hget L.gens (fun s hs => (hgens s hs).1) L.tr
      [⟨L.b, 0, 0, 0, L.b⟩] htree hN' (by
        intro q hq
        simp only [List.mem_singleton] at hq
        subst hq
        simp [hP0, one_mem])
    simp only [Lvl.all, List.mem_cons] at he
    rcases he with rfl | he
    · simp [hP0, KL, one_mem]
    · exact this _ he
  refine ⟨hb, by simpa using hnp, hnd, fun e he => (hall e he).1.1.1, ?_, ?_, hmemAll, hP0, ?_, ?_, ?_,
    fun e he => ⟨(hall e he).1.1.2, (hinv e he).1⟩, fun s hs => (hgens s hs).1⟩
  · intro e he
    have h1 := (hall e he).1
    have := tget_P hget h1.1.2 hb
    rw [h1.2] at this
    apply Fin.ext
    rw [fo_val h1.1.1]
    exact this.symm
  · intro e he
    have h1 := (hinv e he).2
    have h2 : P prog e.k * P prog e.ki = 1 := by
      apply tab_inj
      rw [tab_mul, hget _ (hall e he).1.1.2, hget _ (hinv e he).1, h1, tab_one]
    exact mul_eq_one_comm.mp h2
  · intro s hs p hp
    have h1 := (hgens s hs).2 p hp
    have := tget_P hget (hgens s hs).1 (hprev p hp)
    rw [h1] at this
    apply Fin.ext
    rw [fo_val (hprev p hp)]
    exact this.symm
  · cases Ls with
    | nil => exact bot_le
    | cons L' Ls' =>
      simp only [nested, List.all_eq_true, List.contains_iff_mem] at hnest
      apply Subgroup.closure_mono
      rintro g ⟨s, hs, rfl⟩
      exact ⟨s, hnest s hs, rfl⟩
  · intro s hs e he
    simp only [schreier, List.all_eq_true] at hsch
    have h1 := hsch s hs e he
    have hxe := (hall e he).1.1.1
    have hsN := (hgens s hs).1
    rw [tget_P hget hsN hxe] at h1
    cases hl : lk L.all (↑(P prog s (fo e.x))) with
    | none => rw [hl] at h1; simp at h1
    | some f =>
      rw [hl] at h1
      obtain ⟨hf, hfx⟩ := lk_some hl
      exact ⟨f, hf, hfx, h1⟩

theorem sift_sound (hget : ∀ k < N, tab (P prog k) = get k) :
    ∀ (ls : List Lvl) (prev : List ℕ), (∀ p ∈ prev, p < 23) → chk get N prev ls = true →
      ∀ h : Equiv.Perm (Fin 23), sift get ls (tab h) = true → h ∈ Kls prog ls := by
  intro ls
  induction ls with
  | nil =>
    intro prev _ _ h hs
    simp only [sift, beq_iff_eq] at hs
    rw [Kls, Subgroup.mem_bot]
    apply tab_inj
    rw [hs, tab_one]
  | cons L Ls ih =>
    intro prev hprev hchk h hs
    simp only [chk, Bool.and_eq_true] at hchk
    obtain ⟨hl, hrest⟩ := hchk
    have F := lvl_facts hget hprev hl
    have hprev' : ∀ p ∈ prev ++ [L.b], p < 23 := by
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hprev p hp
      · rw [List.mem_singleton.mp hp]; exact F.hb
    have ht : tget (tab h) L.b = (h (fo L.b) : ℕ) := by
      have := tget_tab h (fo L.b)
      rwa [fo_val F.hb] at this
    simp only [sift] at hs
    rw [ht] at hs
    cases hl' : lk L.all (↑(h (fo L.b))) with
    | none => rw [hl'] at hs; simp at hs
    | some e =>
      rw [hl'] at hs
      obtain ⟨he, -⟩ := lk_some hl'
      have hs' : sift get Ls (tab (P prog e.ki * h)) = true := by
        rw [tab_mul, hget _ (F.hkN e he).2]; exact hs
      have h1 := ih _ hprev' hrest _ hs'
      have h2 : h = P prog e.k * (P prog e.ki * h) := by
        rw [← mul_assoc, mul_eq_one_comm.mp (F.hinv e he), one_mul]
      show h ∈ KL prog L
      rw [h2]
      exact mul_mem (F.hmem e he) (F.hnest h1)

/-- The orbit of the base point recorded at a level. -/
def lvlOrb (L : Lvl) : Finset (Fin 23) := (L.all.map (fun e => fo e.x)).toFinset

/-- The transversal function recorded at a level. -/
def lvlT (prog : List (ℕ × ℕ × ℕ)) (L : Lvl) (y : Fin 23) : Equiv.Perm (Fin 23) :=
  match lk L.all y.val with
  | some e => P prog e.k
  | none => 1

theorem mem_lvlOrb {L : Lvl} {y : Fin 23} : y ∈ lvlOrb L ↔ ∃ e ∈ L.all, fo e.x = y := by
  simp [lvlOrb]

theorem lvlT_eq {prog : List (ℕ × ℕ × ℕ)} {N : ℕ} {get : ℕ → Tab} {prev : List ℕ} {L : Lvl}
    {Ls : List Lvl} (F : LvlFacts prog get N prev L Ls) {e : Ent} (he : e ∈ L.all) :
    lvlT prog L (fo e.x) = P prog e.k := by
  have : lk L.all (fo e.x).val = some e := by
    rw [fo_val (F.hx e he)]; exact lk_of_mem he F.hnd
  show (match lk L.all (fo e.x).val with
    | some e => P prog e.k
    | none => 1) = P prog e.k
  rw [this]

theorem lvlOrb_card {prog : List (ℕ × ℕ × ℕ)} {N : ℕ} {get : ℕ → Tab} {prev : List ℕ}
    {L : Lvl} {Ls : List Lvl} (F : LvlFacts prog get N prev L Ls) :
    (lvlOrb L).card = L.all.length := by
  classical
  show (L.all.map (fun e => fo e.x)).toFinset.card = L.all.length
  rw [← List.length_map (f := fun e : Ent => fo e.x)]
  apply List.toFinset_card_of_nodup
  have h1 := List.Nodup.map_on (f := fo) ?_ F.hnd
  · simpa [List.map_map, Function.comp_def] using h1
  · intro a ha b hb hab
    simp only [List.mem_map] at ha hb
    obtain ⟨e1, he1, rfl⟩ := ha
    obtain ⟨e2, he2, rfl⟩ := hb
    have := congrArg Fin.val hab
    rwa [fo_val (F.hx e1 he1), fo_val (F.hx e2 he2)] at this

theorem prev_succ {prev : List ℕ} (hprev : ∀ p ∈ prev, p < 23) {b : ℕ} (hb : b < 23) :
    ∀ p ∈ prev ++ [b], p < 23 := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · exact hprev p hp
  · rw [List.mem_singleton.mp hp]; exact hb

/-- The hypotheses of `level_step` for the data of a level. -/
theorem lvl_setup (hget : ∀ k < N, tab (P prog k) = get k) {prev : List ℕ}
    (hprev : ∀ p ∈ prev, p < 23) {L : Lvl} {Ls : List Lvl}
    (hl : lvlOk get N prev L Ls = true) (hrest : chk get N (prev ++ [L.b]) Ls = true) :
    fo L.b ∈ lvlOrb L ∧ lvlT prog L (fo L.b) = 1 ∧
    (∀ y ∈ lvlOrb L, lvlT prog L y ∈ KL prog L ∧ lvlT prog L y (fo L.b) = y) ∧
    (∀ s ∈ Ggen prog L, ∀ y ∈ lvlOrb L,
      s y ∈ lvlOrb L ∧ (lvlT prog L (s y))⁻¹ * s * lvlT prog L y ∈ Kls prog Ls) := by
  have F := lvl_facts hget hprev hl
  have hprev' := prev_succ hprev F.hb
  have hroot_mem : (⟨L.b, 0, 0, 0, L.b⟩ : Ent) ∈ L.all := by simp [Lvl.all]
  refine ⟨mem_lvlOrb.mpr ⟨_, hroot_mem, rfl⟩, (lvlT_eq F hroot_mem).trans F.hroot, ?_, ?_⟩
  · intro y hy
    obtain ⟨e, he, rfl⟩ := mem_lvlOrb.mp hy
    rw [lvlT_eq F he]
    exact ⟨F.hmem e he, F.hmap e he⟩
  · intro s hs y hy
    obtain ⟨s0, hs0, rfl⟩ := hs
    obtain ⟨e, he, rfl⟩ := mem_lvlOrb.mp hy
    obtain ⟨f, hf, hfx, hsift⟩ := F.hsch s0 hs0 e he
    have hsy : P prog s0 (fo e.x) = fo f.x :=
      Fin.ext (by rw [fo_val (F.hx f hf)]; exact hfx.symm)
    refine ⟨?_, ?_⟩
    · rw [hsy]; exact mem_lvlOrb.mpr ⟨f, hf, rfl⟩
    · rw [hsy, lvlT_eq F hf, lvlT_eq F he]
      have hinv' : (P prog f.k)⁻¹ = P prog f.ki :=
        (eq_inv_of_mul_eq_one_left (F.hinv f hf)).symm
      rw [hinv']
      have := sift_sound hget Ls (prev ++ [L.b]) hprev' hrest
        (P prog f.ki * (P prog s0 * P prog e.k)) (by
          rw [tab_mul, tab_mul, hget _ (F.hkN f hf).2, hget _ (F.hsN s0 hs0),
            hget _ (F.hkN e he).1]
          exact hsift)
      rwa [← mul_assoc] at this

theorem card_chain (hget : ∀ k < N, tab (P prog k) = get k) :
    ∀ (ls : List Lvl) (prev : List ℕ), (∀ p ∈ prev, p < 23) → chk get N prev ls = true →
      Nat.card (Kls prog ls) = (ls.map (fun L => L.all.length)).prod := by
  classical
  intro ls
  induction ls with
  | nil => intro prev _ _; simp [Kls]
  | cons L Ls ih =>
    intro prev hprev hchk
    simp only [chk, Bool.and_eq_true] at hchk
    obtain ⟨hl, hrest⟩ := hchk
    have F := lvl_facts hget hprev hl
    have hprev' := prev_succ hprev F.hb
    have IH := ih _ hprev' hrest
    obtain ⟨h1, h2, h3, h4⟩ := lvl_setup hget hprev hl hrest
    have key := level_step (Ggen prog L) (Kls prog Ls) (fo L.b) (lvlOrb L) (lvlT prog L)
      h1 h2 h3 h4 F.hnest
      (by
        intro g hg
        cases Ls with
        | nil =>
          simp only [Kls, Subgroup.mem_bot] at hg
          rw [hg]; rfl
        | cons L' Ls' =>
          simp only [chk, Bool.and_eq_true] at hrest
          have F' := lvl_facts hget hprev' hrest.1
          have hle : KL prog L' ≤ MulAction.stabilizer (Equiv.Perm (Fin 23)) (fo L.b) := by
            apply (Subgroup.closure_le _).mpr
            rintro g ⟨s, hs, rfl⟩
            exact F'.hgfix s hs L.b (by simp)
          exact hle hg)
    show Nat.card (KL prog L) = _
    simp only [List.map_cons, List.prod_cons]
    rw [← IH, ← lvlOrb_card F]
    exact key

/-- Completeness: every element of the group sifts successfully. -/
theorem sift_complete (hget : ∀ k < N, tab (P prog k) = get k) :
    ∀ (ls : List Lvl) (prev : List ℕ), (∀ p ∈ prev, p < 23) → chk get N prev ls = true →
      ∀ h ∈ Kls prog ls, sift get ls (tab h) = true := by
  intro ls
  induction ls with
  | nil =>
    intro prev _ _ h hh
    simp only [Kls, Subgroup.mem_bot] at hh
    subst hh
    simp [sift, tab_one]
  | cons L Ls ih =>
    intro prev hprev hchk h hh
    simp only [chk, Bool.and_eq_true] at hchk
    obtain ⟨hl, hrest⟩ := hchk
    have F := lvl_facts hget hprev hl
    have hprev' := prev_succ hprev F.hb
    obtain ⟨h1, h2, h3, h4⟩ := lvl_setup hget hprev hl hrest
    obtain ⟨horb, hfac⟩ := level_factor (Ggen prog L) (Kls prog Ls) (fo L.b) (lvlOrb L)
      (lvlT prog L) h1 h2 h4
    have hh' : h ∈ Subgroup.closure (Ggen prog L) := hh
    obtain ⟨e, he, hex⟩ := mem_lvlOrb.mp (horb h hh' (fo L.b) h1)
    have hfh := hfac h hh'
    rw [← hex, lvlT_eq F he] at hfh
    have hinv' : (P prog e.k)⁻¹ = P prog e.ki :=
      (eq_inv_of_mul_eq_one_left (F.hinv e he)).symm
    rw [hinv'] at hfh
    have hih := ih _ hprev' hrest _ hfh
    have ht : tget (tab h) L.b = (h (fo L.b) : ℕ) := by
      have := tget_tab h (fo L.b)
      rwa [fo_val F.hb] at this
    simp only [sift]
    rw [ht, ← hex, fo_val (F.hx e he)]
    have hlk : lk L.all e.x = some e := lk_of_mem he F.hnd
    rw [hlk]
    show sift get Ls (tmul (get e.ki) (tab h)) = true
    rw [← hget e.ki (F.hkN e he).2, ← tab_mul]
    exact hih

end Soundness

/-- The two initial generators are among the generators of the first level. -/
def topGens : List Lvl → Bool
  | [] => false
  | L :: _ => L.gens.contains 1 && L.gens.contains 2

theorem Kls_top (prog : List (ℕ × ℕ × ℕ)) (get : ℕ → Tab)
    (hget : ∀ k < 4 + prog.length, tab (P prog k) = get k)
    (hbase : ∀ k < 4, get k = tab (basePerms.getD k 1)) (L : Lvl) (Ls : List Lvl)
    (hL1 : 1 ∈ L.gens) (hL2 : 2 ∈ L.gens) : Kls prog (L :: Ls) = M23 := by
  have h1 : P prog 1 = g₁ := by
    apply tab_inj
    rw [hget 1 (by omega), hbase 1 (by omega)]
    rfl
  have h2 : P prog 2 = g₂ := by
    apply tab_inj
    rw [hget 2 (by omega), hbase 2 (by omega)]
    rfl
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨s, hs, rfl⟩
    exact P_mem prog s
  · apply (Subgroup.closure_le _).mpr
    rintro g (rfl | rfl)
    · exact Subgroup.subset_closure ⟨1, hL1, h1.symm⟩
    · exact Subgroup.subset_closure ⟨2, hL2, h2.symm⟩

/-- The full check: the table function is that of the program, the chain is valid. -/
def topChk (get : ℕ → Tab) (prog : List (ℕ × ℕ × ℕ)) (ls : List Lvl) : Bool :=
  slpChk get 3 prog && (List.range 4).all (fun k => get k == tab (basePerms.getD k 1)) &&
    chk get (4 + prog.length) [] ls && topGens ls

theorem card_of_check (get : ℕ → Tab) (prog : List (ℕ × ℕ × ℕ)) (ls : List Lvl)
    (h : topChk get prog ls = true) :
    Nat.card M23 = (ls.map (fun L => L.all.length)).prod := by
  simp only [topChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨hslp, hbase⟩, hchk⟩, htop⟩ := h
  have hget : ∀ k < 4 + prog.length, tab (P prog k) = get k :=
    slp_tab get prog (fun k hk => (hbase k hk).symm) hslp
  cases ls with
  | nil => simp [topGens] at htop
  | cons L Ls =>
    simp only [topGens, Bool.and_eq_true, List.contains_iff_mem] at htop
    rw [← Kls_top prog get hget hbase L Ls htop.1 htop.2]
    exact card_chain hget (L :: Ls) [] (by simp) hchk

/-- Membership test: a permutation whose table sifts through a certified chain lies in `M23`. -/
theorem mem_M23_of_sift (get : ℕ → Tab) (prog : List (ℕ × ℕ × ℕ)) (ls : List Lvl)
    (h : topChk get prog ls = true) (g : Equiv.Perm (Fin 23))
    (hg : sift get ls (tab g) = true) : g ∈ M23 := by
  simp only [topChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨hslp, hbase⟩, hchk⟩, htop⟩ := h
  have hget : ∀ k < 4 + prog.length, tab (P prog k) = get k :=
    slp_tab get prog (fun k hk => (hbase k hk).symm) hslp
  cases ls with
  | nil => simp [topGens] at htop
  | cons L Ls =>
    simp only [topGens, Bool.and_eq_true, List.contains_iff_mem] at htop
    rw [← Kls_top prog get hget hbase L Ls htop.1 htop.2]
    exact sift_sound hget (L :: Ls) [] (by simp) hchk g hg

/-- Membership in `M23` is decided by sifting through a certified chain. -/
theorem mem_M23_iff_sift (get : ℕ → Tab) (prog : List (ℕ × ℕ × ℕ)) (ls : List Lvl)
    (h : topChk get prog ls = true) (g : Equiv.Perm (Fin 23)) :
    g ∈ M23 ↔ sift get ls (tab g) = true := by
  refine ⟨fun hg => ?_, mem_M23_of_sift get prog ls h g⟩
  simp only [topChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨hslp, hbase⟩, hchk⟩, htop⟩ := h
  have hget : ∀ k < 4 + prog.length, tab (P prog k) = get k :=
    slp_tab get prog (fun k hk => (hbase k hk).symm) hslp
  cases ls with
  | nil => simp [topGens] at htop
  | cons L Ls =>
    simp only [topGens, Bool.and_eq_true, List.contains_iff_mem] at htop
    rw [← Kls_top prog get hget hbase L Ls htop.1 htop.2] at hg
    exact sift_complete hget (L :: Ls) [] (by simp) hchk g hg

end M23Cert

set_option maxRecDepth 100000

namespace M23Cert

/-- Straight-line program `full`: entries `(n, i, j)` say that entry `n` is the product of the
earlier entries `i` and `j`; entries `0..3` are `1, g₁, g₂, g₂⁻¹`. -/
def fullProg : List (ℕ × ℕ × ℕ) :=
  [(4, 2, 3), (5, 2, 2), (6, 1, 2), (7, 6, 4), (8, 3, 3), (9, 7, 8), (10, 2, 5), (11, 4, 10), (12, 10, 8), (13, 8, 8), (14, 11, 12), (15, 9, 1), (16, 13, 1), (17, 16, 1), (18, 5, 1), (19, 14, 12), (20, 15, 12), (21, 5, 5), (22, 1, 21), (23, 1, 22), (24, 12, 23), (25, 18, 17), (26, 24, 19), (27, 19, 25), (28, 25, 1), (29, 1, 8), (30, 23, 29), (31, 8, 3), (32, 5, 31), (33, 31, 4), (34, 32, 33), (35, 32, 34), (36, 30, 35), (37, 1, 36), (38, 17, 32), (39, 35, 38), (40, 20, 39), (41, 37, 39), (42, 40, 23), (43, 17, 28), (44, 3, 1), (45, 4, 44), (46, 5, 45), (47, 1, 46), (48, 32, 47), (49, 26, 48), (50, 17, 49), (51, 26, 50), (52, 43, 51), (53, 42, 39), (54, 52, 53), (55, 27, 1), (56, 26, 55), (57, 28, 56), (58, 1, 30), (59, 58, 23), (60, 53, 59), (61, 51, 60), (62, 42, 61), (63, 57, 54), (64, 41, 27), (65, 62, 54), (66, 27, 61), (67, 54, 64), (68, 41, 58), (69, 61, 68), (70, 66, 69), (71, 65, 51), (72, 36, 56), (73, 70, 72), (74, 73, 64), (75, 63, 64), (76, 71, 64), (77, 75, 74), (78, 74, 77), (79, 78, 77), (80, 54, 36), (81, 63, 80), (82, 64, 81), (83, 72, 82), (84, 72, 69), (85, 83, 84), (86, 51, 85), (87, 77, 79), (88, 85, 83), (89, 85, 88), (90, 67, 89), (91, 89, 85), (92, 79, 91), (93, 92, 90), (94, 54, 50), (95, 61, 94), (96, 53, 95), (97, 72, 96), (98, 64, 97), (99, 87, 76), (100, 76, 99), (101, 93, 90), (102, 72, 61), (103, 79, 102), (104, 99, 103), (105, 87, 89), (106, 103, 105), (107, 103, 106), (108, 98, 107), (109, 77, 53), (110, 90, 109), (111, 97, 91), (112, 111, 97), (113, 104, 112), (114, 110, 101), (115, 86, 103), (116, 107, 115), (117, 101, 116), (118, 114, 107), (119, 100, 118), (120, 113, 108), (121, 120, 118), (122, 117, 86), (123, 114, 119), (124, 122, 108), (125, 124, 109), (126, 76, 72), (127, 101, 126), (128, 123, 127), (129, 108, 121), (130, 119, 129), (131, 117, 112), (132, 131, 116), (133, 108, 132), (134, 129, 133), (135, 130, 128), (136, 134, 135), (137, 128, 135), (138, 121, 86), (139, 137, 138), (140, 138, 86), (141, 90, 111), (142, 100, 141), (143, 127, 142), (144, 117, 143), (145, 109, 144), (146, 144, 127), (147, 146, 131), (148, 133, 147), (149, 148, 133), (150, 145, 149), (151, 136, 150), (152, 140, 109), (153, 152, 148), (154, 86, 150), (155, 153, 154), (156, 151, 125), (157, 125, 154), (158, 139, 109), (159, 139, 158), (160, 135, 157), (161, 160, 156), (162, 154, 156), (163, 161, 156), (164, 2, 1), (165, 2, 6), (166, 1, 165), (167, 109, 118), (168, 127, 167), (169, 86, 168), (170, 158, 169), (171, 159, 170), (172, 128, 146), (173, 148, 172), (174, 139, 173), (175, 169, 174), (176, 170, 148), (177, 175, 176), (178, 175, 177), (179, 162, 178), (180, 154, 150), (181, 157, 180), (182, 156, 181), (183, 44, 3), (184, 183, 1), (185, 184, 155), (186, 185, 1), (187, 185, 164), (188, 2, 186), (189, 185, 186), (190, 185, 185), (191, 185, 190), (192, 182, 181), (193, 109, 145), (194, 86, 193), (195, 135, 194), (196, 158, 195), (197, 192, 196), (198, 155, 179), (199, 1, 3), (200, 196, 166), (201, 199, 200), (202, 201, 197), (203, 200, 200), (204, 203, 202), (205, 204, 1), (206, 204, 164), (207, 185, 205), (208, 204, 205), (209, 204, 185), (210, 204, 190), (211, 185, 209), (212, 204, 209), (213, 204, 210), (214, 204, 204), (215, 204, 214), (216, 171, 179), (217, 163, 197), (218, 197, 157), (219, 199, 216), (220, 171, 175), (221, 171, 220), (222, 155, 221), (223, 222, 187), (224, 223, 190), (225, 200, 224), (226, 225, 224), (227, 226, 219), (228, 224, 224), (229, 228, 227), (230, 229, 1), (231, 229, 186), (232, 1, 230), (233, 2, 230), (234, 229, 185), (235, 229, 190), (236, 229, 234), (237, 185, 235), (238, 204, 235), (239, 229, 238), (240, 229, 204), (241, 229, 214), (242, 204, 240), (243, 229, 240), (244, 204, 241), (245, 204, 242), (246, 229, 244), (247, 229, 229), (248, 229, 247), (249, 229, 248), (250, 170, 222), (251, 157, 250), (252, 175, 158), (253, 163, 252), (254, 253, 196), (255, 217, 254), (256, 253, 181), (257, 256, 164), (258, 257, 212), (259, 258, 214), (260, 1, 259), (261, 260, 3), (262, 261, 251), (263, 203, 259), (264, 263, 224), (265, 264, 259), (266, 265, 262), (267, 228, 259), (268, 267, 224), (269, 268, 259), (270, 269, 266), (271, 259, 259), (272, 271, 259), (273, 272, 259), (274, 273, 270), (275, 274, 164), (276, 274, 186), (277, 274, 187), (278, 274, 185), (279, 274, 190), (280, 274, 204), (281, 274, 241), (282, 274, 229), (283, 274, 247), (284, 229, 282), (285, 274, 248), (286, 222, 178), (287, 198, 286), (288, 218, 287), (289, 1, 200), (290, 218, 170), (291, 290, 233), (292, 291, 239), (293, 292, 246), (294, 293, 249), (295, 289, 294), (296, 295, 255), (297, 203, 224), (298, 297, 224), (299, 298, 296), (300, 268, 299), (301, 259, 294), (302, 301, 259), (303, 302, 300), (304, 303, 1), (305, 303, 164), (306, 303, 190), (307, 303, 209), (308, 303, 306), (309, 303, 214), (310, 303, 240), (311, 303, 280), (312, 303, 215), (313, 303, 241), (314, 274, 309), (315, 229, 310), (316, 303, 229), (317, 303, 247), (318, 274, 316), (319, 303, 316), (320, 303, 284), (321, 303, 274), (322, 274, 303), (323, 303, 303), (324, 274, 321), (325, 303, 321), (326, 303, 322), (327, 255, 250), (328, 198, 327), (329, 260, 1), (330, 329, 328), (331, 200, 259), (332, 331, 259), (333, 332, 330), (334, 287, 276), (335, 334, 213), (336, 335, 244), (337, 336, 284), (338, 228, 337), (339, 338, 294), (340, 339, 333), (341, 272, 340), (342, 341, 1), (343, 341, 164), (344, 341, 185), (345, 341, 190), (346, 341, 209), (347, 185, 344), (348, 303, 344), (349, 341, 214), (350, 341, 240), (351, 341, 280), (352, 204, 349), (353, 341, 229), (354, 341, 247), (355, 229, 353), (356, 274, 353), (357, 341, 284), (358, 274, 355), (359, 341, 274), (360, 341, 321), (361, 274, 359), (362, 341, 323), (363, 341, 325), (364, 341, 360), (365, 341, 326), (366, 341, 341), (367, 1, 224), (368, 1, 337), (369, 288, 254), (370, 369, 232), (371, 370, 236), (372, 371, 314), (373, 372, 248), (374, 1, 373), (375, 199, 224), (376, 199, 294), (377, 199, 337), (378, 199, 373), (379, 289, 3), (380, 289, 200), (381, 289, 259), (382, 367, 200), (383, 367, 224), (384, 201, 294), (385, 200, 294), (386, 200, 373), (387, 203, 200), (388, 203, 294), (389, 203, 337), (390, 203, 373), (391, 225, 200), (392, 225, 337), (393, 225, 373), (394, 386, 200), (395, 386, 337), (396, 263, 200), (397, 389, 337), (398, 224, 259), (399, 224, 294), (400, 228, 224), (401, 228, 373), (402, 398, 224), (403, 398, 259), (404, 398, 337), (405, 398, 373), (406, 399, 337), (407, 399, 373), (408, 400, 337), (409, 267, 294), (410, 267, 337), (411, 401, 224), (412, 402, 224), (413, 404, 259), (414, 259, 337), (415, 259, 373), (416, 271, 294), (417, 271, 337), (418, 271, 373), (419, 414, 294), (420, 414, 337), (421, 415, 259), (422, 415, 294), (423, 272, 294), (424, 302, 337), (425, 302, 373), (426, 421, 294), (427, 294, 337), (428, 294, 373), (429, 337, 294), (430, 337, 337), (431, 427, 294), (432, 427, 337), (433, 427, 373), (434, 428, 294), (435, 429, 337), (436, 430, 373), (437, 432, 373), (438, 433, 373), (439, 435, 373), (440, 373, 373)]

/-- The value tables of all entries of `fullProg`, in chunks of 24. -/
def fullTabs : List (List Tab) :=
  [[[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22], [10, 22, 7, 15, 20, 5, 19, 2, 8, 9, 0, 11, 12, 13, 18, 3, 16, 21, 14, 6, 4, 17, 1], [1, 10, 22, 7, 17, 2, 11, 21, 5, 15, 9, 0, 6, 20, 12, 8, 3, 14, 19, 13, 16, 4, 18], [11, 0, 5, 16, 21, 8, 12, 3, 15, 10, 1, 6, 14, 19, 17, 9, 20, 4, 22, 18, 13, 7, 2], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22], [10, 9, 18, 21, 14, 22, 0, 4, 2, 8, 15, 1, 11, 16, 6, 5, 7, 12, 13, 20, 3, 17, 19], [22, 0, 1, 2, 21, 7, 11, 17, 5, 3, 9, 10, 19, 4, 12, 8, 15, 18, 6, 13, 16, 20, 14], [22, 0, 1, 2, 21, 7, 11, 17, 5, 3, 9, 10, 19, 4, 12, 8, 15, 18, 6, 13, 16, 20, 14], [6, 11, 8, 20, 7, 15, 14, 16, 9, 1, 0, 12, 17, 18, 4, 10, 13, 21, 2, 22, 19, 3, 5], [11, 10, 5, 16, 17, 8, 12, 15, 3, 0, 22, 19, 18, 6, 21, 9, 4, 20, 1, 14, 13, 2, 7], [9, 15, 19, 4, 12, 18, 1, 17, 22, 5, 8, 10, 0, 3, 11, 2, 21, 6, 20, 16, 7, 14, 13], [9, 15, 19, 4, 12, 18, 1, 17, 22, 5, 8, 10, 0, 3, 11, 2, 21, 6, 20, 16, 7, 14, 13], [1, 10, 22, 7, 17, 2, 11, 21, 5, 15, 9, 0, 6, 20, 12, 8, 3, 14, 19, 13, 16, 4, 18], [14, 12, 9, 19, 16, 10, 4, 13, 1, 11, 6, 17, 21, 2, 7, 0, 18, 3, 8, 5, 22, 20, 15], [15, 8, 13, 17, 6, 19, 10, 14, 18, 2, 5, 9, 1, 7, 0, 22, 4, 11, 16, 3, 21, 12, 20], [22, 7, 15, 9, 13, 8, 14, 5, 3, 0, 11, 19, 18, 6, 1, 16, 4, 2, 21, 12, 17, 20, 10], [6, 15, 13, 0, 22, 10, 5, 9, 1, 11, 14, 17, 21, 2, 8, 19, 18, 20, 7, 4, 16, 3, 12], [14, 12, 9, 19, 16, 10, 4, 13, 1, 11, 6, 17, 21, 2, 7, 0, 18, 3, 8, 5, 22, 20, 15], [15, 19, 4, 5, 3, 22, 20, 18, 2, 8, 10, 1, 11, 16, 13, 21, 7, 17, 6, 0, 14, 12, 9], [8, 5, 20, 14, 11, 13, 9, 12, 19, 22, 2, 15, 10, 21, 1, 18, 17, 0, 3, 7, 4, 6, 16], [7, 11, 10, 5, 2, 15, 19, 20, 8, 16, 0, 22, 14, 17, 18, 3, 9, 1, 12, 6, 4, 13, 21], [15, 8, 13, 17, 6, 19, 10, 14, 18, 2, 5, 9, 1, 7, 0, 22, 4, 11, 16, 3, 21, 12, 20], [3, 8, 13, 21, 19, 6, 0, 18, 14, 7, 5, 9, 22, 2, 10, 1, 20, 11, 16, 15, 17, 12, 4], [15, 8, 13, 17, 6, 19, 10, 14, 18, 2, 5, 9, 1, 7, 0, 22, 4, 11, 16, 3, 21, 12, 20]],
   [[8, 5, 20, 14, 11, 13, 9, 12, 19, 22, 2, 15, 10, 21, 1, 18, 17, 0, 3, 7, 4, 6, 16], [13, 11, 8, 0, 7, 10, 3, 16, 19, 1, 20, 17, 12, 4, 18, 15, 6, 5, 2, 22, 9, 14, 21], [19, 13, 4, 1, 15, 21, 22, 10, 7, 16, 20, 18, 2, 6, 5, 3, 0, 8, 14, 12, 11, 9, 17], [21, 15, 19, 8, 12, 2, 14, 17, 7, 5, 4, 0, 10, 11, 3, 18, 9, 13, 20, 16, 22, 1, 6], [20, 21, 16, 15, 9, 10, 22, 8, 19, 1, 13, 17, 12, 4, 2, 0, 6, 14, 18, 3, 7, 5, 11], [19, 11, 8, 4, 2, 3, 18, 16, 9, 22, 10, 12, 21, 14, 20, 0, 13, 17, 7, 1, 6, 15, 5], [3, 9, 18, 6, 13, 17, 16, 4, 2, 20, 5, 1, 12, 0, 21, 15, 7, 11, 14, 8, 10, 22, 19], [12, 6, 15, 13, 3, 9, 17, 20, 10, 0, 11, 14, 4, 22, 21, 1, 19, 7, 5, 2, 18, 16, 8], [11, 0, 5, 16, 21, 8, 12, 3, 15, 10, 1, 6, 14, 19, 17, 9, 20, 4, 22, 18, 13, 7, 2], [12, 6, 15, 13, 3, 9, 17, 20, 10, 0, 11, 14, 4, 22, 21, 1, 19, 7, 5, 2, 18, 16, 8], [14, 12, 9, 19, 16, 10, 4, 13, 1, 11, 6, 17, 21, 2, 7, 0, 18, 3, 8, 5, 22, 20, 15], [17, 14, 10, 18, 20, 1, 21, 19, 0, 6, 12, 4, 7, 5, 3, 11, 22, 16, 15, 8, 2, 13, 9], [11, 21, 5, 14, 10, 9, 22, 8, 3, 16, 12, 13, 4, 17, 6, 1, 19, 7, 15, 2, 18, 0, 20], [11, 17, 5, 18, 0, 9, 1, 8, 15, 16, 12, 13, 20, 21, 19, 22, 6, 2, 3, 7, 14, 10, 4], [17, 14, 10, 18, 20, 1, 21, 19, 0, 6, 12, 4, 7, 5, 3, 11, 22, 16, 15, 8, 2, 13, 9], [16, 3, 12, 15, 2, 14, 13, 8, 17, 21, 7, 20, 19, 1, 18, 4, 9, 22, 11, 0, 10, 5, 6], [9, 5, 14, 3, 10, 18, 17, 8, 1, 13, 20, 4, 6, 11, 12, 2, 16, 21, 22, 7, 0, 15, 19], [6, 18, 20, 22, 5, 19, 21, 15, 2, 10, 8, 14, 7, 17, 3, 0, 16, 4, 13, 11, 12, 9, 1], [2, 1, 11, 21, 17, 7, 20, 12, 22, 14, 18, 13, 5, 8, 9, 19, 10, 4, 16, 3, 15, 6, 0], [22, 20, 18, 0, 11, 6, 15, 1, 5, 12, 2, 3, 21, 16, 9, 14, 4, 7, 8, 19, 13, 10, 17], [1, 2, 3, 9, 13, 8, 18, 5, 15, 10, 11, 6, 14, 19, 22, 16, 20, 7, 17, 12, 21, 4, 0], [1, 2, 3, 9, 13, 8, 18, 5, 15, 10, 11, 6, 14, 19, 22, 16, 20, 7, 17, 12, 21, 4, 0], [9, 18, 21, 8, 16, 2, 13, 22, 5, 15, 1, 0, 6, 20, 19, 7, 3, 4, 12, 11, 17, 14, 10], [9, 14, 17, 8, 16, 7, 13, 1, 5, 3, 22, 10, 19, 4, 6, 2, 15, 20, 12, 11, 21, 18, 0]],
   [[10, 17, 4, 15, 20, 3, 19, 0, 8, 16, 2, 1, 18, 21, 12, 5, 9, 13, 14, 6, 7, 22, 11], [20, 8, 15, 3, 11, 1, 12, 19, 7, 0, 4, 13, 14, 9, 2, 21, 16, 6, 5, 22, 10, 17, 18], [22, 1, 0, 19, 17, 12, 21, 5, 13, 14, 16, 2, 7, 11, 9, 20, 18, 4, 10, 15, 6, 3, 8], [17, 13, 19, 12, 8, 2, 9, 21, 6, 5, 0, 4, 10, 18, 16, 11, 14, 15, 20, 3, 22, 1, 7], [7, 16, 19, 21, 5, 18, 12, 10, 15, 6, 22, 11, 2, 8, 4, 3, 9, 14, 13, 0, 17, 20, 1], [10, 21, 5, 19, 11, 9, 8, 22, 4, 6, 12, 15, 3, 1, 16, 17, 14, 0, 13, 2, 18, 7, 20], [22, 20, 18, 0, 11, 6, 15, 1, 5, 12, 2, 3, 21, 16, 9, 14, 4, 7, 8, 19, 13, 10, 17], [4, 6, 17, 18, 22, 2, 16, 19, 7, 5, 21, 0, 10, 11, 20, 8, 9, 1, 3, 14, 12, 13, 15], [15, 22, 8, 14, 17, 4, 0, 12, 10, 21, 9, 19, 20, 18, 11, 7, 16, 13, 1, 5, 2, 6, 3], [0, 11, 19, 2, 14, 9, 20, 12, 13, 5, 1, 3, 7, 18, 17, 8, 6, 4, 21, 10, 16, 22, 15], [15, 9, 14, 19, 13, 21, 16, 20, 7, 4, 5, 22, 12, 10, 17, 3, 2, 11, 18, 8, 0, 1, 6], [3, 7, 10, 11, 16, 8, 5, 17, 18, 14, 21, 4, 9, 20, 15, 6, 13, 22, 2, 19, 1, 12, 0], [19, 22, 12, 15, 14, 4, 9, 0, 13, 16, 7, 11, 6, 18, 17, 8, 1, 20, 5, 2, 21, 3, 10], [3, 7, 10, 11, 16, 8, 5, 17, 18, 14, 21, 4, 9, 20, 15, 6, 13, 22, 2, 19, 1, 12, 0], [21, 12, 18, 13, 10, 22, 7, 4, 16, 9, 6, 17, 14, 15, 19, 20, 8, 0, 11, 3, 1, 5, 2], [15, 16, 21, 0, 3, 20, 8, 11, 9, 7, 19, 2, 22, 6, 5, 17, 14, 12, 13, 10, 18, 1, 4], [9, 0, 11, 2, 7, 20, 3, 4, 15, 19, 5, 6, 8, 14, 22, 13, 10, 17, 12, 16, 1, 18, 21], [2, 1, 11, 21, 17, 7, 20, 12, 22, 14, 18, 13, 5, 8, 9, 19, 10, 4, 16, 3, 15, 6, 0], [8, 17, 4, 0, 9, 7, 2, 13, 20, 3, 1, 12, 5, 22, 18, 14, 11, 6, 19, 16, 15, 10, 21], [12, 22, 3, 18, 1, 13, 0, 11, 14, 19, 6, 15, 5, 9, 17, 16, 2, 7, 21, 4, 20, 8, 10], [0, 10, 3, 11, 17, 9, 16, 12, 15, 5, 19, 1, 7, 8, 4, 22, 20, 14, 13, 2, 6, 18, 21], [3, 21, 11, 4, 22, 14, 13, 9, 6, 8, 19, 7, 17, 18, 16, 0, 1, 15, 20, 10, 5, 2, 12], [0, 10, 12, 9, 21, 18, 22, 3, 2, 20, 16, 13, 6, 19, 11, 8, 17, 14, 15, 1, 7, 4, 5], [4, 8, 3, 5, 22, 11, 14, 6, 20, 7, 2, 17, 18, 16, 10, 13, 9, 19, 15, 21, 0, 1, 12]],
   [[1, 20, 3, 6, 7, 10, 11, 4, 12, 0, 16, 2, 18, 15, 13, 8, 19, 17, 21, 9, 5, 22, 14], [10, 7, 9, 22, 3, 16, 13, 21, 6, 0, 17, 12, 15, 8, 19, 2, 1, 14, 4, 20, 18, 5, 11], [0, 10, 12, 9, 21, 18, 22, 3, 2, 20, 16, 13, 6, 19, 11, 8, 17, 14, 15, 1, 7, 4, 5], [7, 15, 2, 21, 11, 18, 0, 3, 17, 10, 20, 8, 9, 5, 4, 6, 19, 12, 22, 14, 16, 13, 1], [7, 4, 17, 3, 6, 0, 5, 22, 13, 21, 11, 14, 20, 10, 12, 16, 2, 19, 18, 9, 8, 15, 1], [7, 20, 9, 10, 13, 22, 1, 21, 2, 16, 19, 5, 0, 14, 8, 17, 12, 4, 6, 15, 3, 11, 18], [3, 7, 20, 16, 19, 5, 10, 4, 12, 17, 1, 18, 0, 11, 2, 14, 6, 21, 22, 8, 9, 13, 15], [4, 9, 17, 1, 11, 15, 7, 13, 20, 6, 8, 5, 3, 2, 12, 21, 0, 19, 10, 14, 16, 18, 22], [3, 10, 6, 9, 2, 12, 17, 5, 0, 4, 21, 16, 11, 7, 15, 20, 19, 1, 14, 18, 8, 22, 13], [0, 19, 8, 7, 21, 22, 12, 20, 15, 3, 1, 14, 2, 11, 17, 18, 10, 16, 5, 13, 9, 4, 6], [9, 16, 15, 4, 18, 21, 8, 1, 13, 2, 0, 22, 11, 6, 17, 12, 5, 10, 20, 14, 19, 7, 3], [0, 19, 8, 7, 21, 22, 12, 20, 15, 3, 1, 14, 2, 11, 17, 18, 10, 16, 5, 13, 9, 4, 6], [6, 22, 2, 7, 14, 13, 15, 0, 11, 12, 9, 4, 17, 21, 19, 1, 20, 8, 5, 16, 10, 3, 18], [12, 6, 8, 20, 17, 11, 18, 0, 14, 2, 3, 21, 16, 4, 13, 19, 9, 15, 22, 10, 1, 7, 5], [10, 9, 6, 22, 15, 4, 20, 17, 16, 19, 12, 1, 14, 8, 18, 3, 5, 11, 7, 0, 13, 21, 2], [13, 16, 4, 20, 5, 17, 21, 14, 3, 1, 2, 22, 10, 9, 0, 11, 7, 15, 19, 8, 12, 6, 18], [12, 10, 14, 0, 7, 5, 16, 1, 19, 20, 6, 13, 8, 21, 15, 22, 3, 9, 11, 4, 2, 17, 18], [16, 3, 13, 12, 0, 11, 9, 6, 10, 1, 18, 4, 14, 7, 19, 5, 20, 2, 21, 17, 8, 15, 22], [2, 18, 9, 5, 12, 15, 19, 0, 6, 22, 21, 1, 17, 11, 4, 13, 20, 3, 8, 7, 14, 16, 10], [14, 9, 10, 8, 2, 4, 21, 16, 19, 13, 12, 15, 20, 0, 7, 17, 1, 5, 22, 18, 3, 6, 11], [12, 6, 8, 20, 17, 11, 18, 0, 14, 2, 3, 21, 16, 4, 13, 19, 9, 15, 22, 10, 1, 7, 5], [8, 22, 2, 11, 16, 19, 10, 12, 18, 5, 7, 6, 15, 21, 17, 4, 1, 20, 14, 0, 13, 9, 3], [17, 20, 22, 19, 7, 21, 10, 6, 16, 9, 4, 18, 1, 3, 12, 13, 8, 11, 2, 14, 15, 0, 5], [22, 1, 0, 19, 17, 12, 21, 5, 13, 14, 16, 2, 7, 11, 9, 20, 18, 4, 10, 15, 6, 3, 8]],
   [[20, 21, 10, 2, 0, 3, 7, 9, 1, 16, 14, 5, 22, 15, 6, 18, 13, 11, 12, 17, 8, 19, 4], [5, 22, 16, 3, 1, 6, 4, 0, 20, 19, 13, 10, 14, 8, 11, 21, 15, 2, 18, 17, 12, 9, 7], [20, 21, 10, 2, 0, 3, 7, 9, 1, 16, 14, 5, 22, 15, 6, 18, 13, 11, 12, 17, 8, 19, 4], [14, 5, 15, 20, 21, 13, 17, 18, 9, 6, 22, 0, 12, 2, 10, 7, 4, 8, 19, 1, 3, 11, 16], [12, 0, 16, 8, 15, 10, 19, 18, 21, 5, 1, 7, 20, 17, 11, 22, 6, 13, 9, 4, 3, 14, 2], [2, 14, 5, 19, 15, 4, 0, 8, 10, 3, 9, 22, 20, 6, 16, 21, 13, 11, 18, 12, 17, 1, 7], [6, 4, 16, 2, 19, 12, 10, 17, 21, 13, 22, 7, 0, 5, 8, 11, 15, 14, 3, 9, 20, 18, 1], [7, 11, 0, 17, 14, 3, 8, 19, 18, 2, 22, 13, 4, 15, 20, 5, 21, 12, 1, 6, 16, 10, 9], [18, 0, 14, 8, 10, 20, 9, 1, 19, 15, 16, 2, 21, 7, 3, 13, 11, 12, 5, 17, 4, 22, 6], [7, 20, 9, 10, 13, 22, 1, 21, 2, 16, 19, 5, 0, 14, 8, 17, 12, 4, 6, 15, 3, 11, 18], [19, 16, 2, 22, 15, 9, 11, 10, 0, 21, 6, 3, 7, 20, 18, 12, 4, 14, 8, 5, 17, 13, 1], [6, 21, 0, 9, 5, 2, 13, 22, 7, 10, 8, 17, 19, 16, 1, 4, 14, 20, 18, 3, 12, 15, 11], [7, 19, 20, 16, 3, 10, 15, 4, 9, 14, 1, 11, 17, 13, 21, 0, 6, 8, 12, 2, 22, 18, 5], [19, 11, 22, 15, 5, 16, 2, 18, 13, 1, 0, 17, 10, 20, 12, 4, 8, 7, 14, 9, 6, 21, 3], [7, 1, 10, 13, 15, 20, 9, 8, 11, 18, 2, 3, 21, 14, 17, 12, 6, 0, 4, 22, 19, 16, 5], [11, 19, 13, 20, 16, 1, 9, 15, 17, 8, 14, 21, 12, 5, 0, 2, 22, 6, 7, 18, 3, 4, 10], [1, 10, 22, 20, 19, 9, 16, 11, 3, 18, 5, 14, 0, 17, 21, 4, 2, 13, 7, 6, 12, 8, 15], [0, 16, 6, 4, 17, 15, 11, 2, 8, 5, 20, 3, 18, 12, 22, 10, 14, 7, 1, 9, 21, 19, 13], [10, 17, 20, 22, 12, 15, 7, 11, 2, 13, 18, 5, 19, 9, 6, 16, 14, 3, 4, 21, 0, 1, 8], [17, 1, 10, 11, 18, 22, 16, 0, 7, 6, 2, 8, 15, 3, 13, 4, 21, 14, 9, 20, 5, 12, 19], [20, 21, 8, 17, 18, 11, 14, 6, 22, 13, 0, 7, 4, 9, 16, 5, 15, 1, 10, 12, 2, 19, 3], [17, 1, 10, 11, 18, 22, 16, 0, 7, 6, 2, 8, 15, 3, 13, 4, 21, 14, 9, 20, 5, 12, 19], [7, 1, 10, 13, 15, 20, 9, 8, 11, 18, 2, 3, 21, 14, 17, 12, 6, 0, 4, 22, 19, 16, 5], [18, 0, 1, 17, 22, 3, 5, 21, 7, 9, 16, 8, 14, 11, 13, 20, 19, 12, 15, 2, 4, 6, 10]],
   [[2, 9, 21, 14, 4, 20, 10, 17, 5, 22, 16, 3, 7, 12, 19, 0, 11, 8, 18, 6, 13, 1, 15], [17, 9, 16, 12, 0, 13, 22, 5, 3, 18, 21, 14, 1, 19, 8, 7, 10, 2, 4, 15, 6, 11, 20], [2, 6, 16, 19, 4, 18, 5, 14, 21, 20, 15, 1, 13, 7, 9, 11, 22, 8, 0, 17, 3, 12, 10], [4, 10, 17, 3, 8, 22, 15, 1, 11, 13, 14, 2, 6, 5, 9, 0, 21, 19, 16, 20, 12, 7, 18], [14, 17, 3, 22, 19, 15, 11, 4, 20, 9, 6, 1, 8, 7, 12, 2, 5, 21, 13, 16, 10, 0, 18], [16, 1, 18, 2, 15, 5, 3, 13, 7, 17, 14, 21, 6, 10, 8, 19, 20, 4, 12, 9, 11, 0, 22], [4, 8, 3, 5, 22, 11, 14, 6, 20, 7, 2, 17, 18, 16, 10, 13, 9, 19, 15, 21, 0, 1, 12], [15, 10, 19, 4, 7, 22, 16, 0, 17, 8, 5, 11, 18, 13, 9, 6, 3, 12, 21, 1, 2, 14, 20], [0, 14, 20, 8, 1, 18, 21, 4, 19, 11, 22, 2, 16, 5, 13, 15, 3, 6, 7, 10, 17, 9, 12], [8, 14, 6, 17, 7, 13, 5, 10, 16, 12, 18, 21, 19, 2, 9, 4, 1, 20, 3, 0, 15, 11, 22], [7, 13, 5, 12, 21, 11, 3, 16, 19, 14, 15, 6, 2, 1, 9, 22, 0, 4, 17, 18, 20, 8, 10], [1, 2, 19, 5, 20, 6, 21, 8, 11, 9, 22, 13, 17, 14, 12, 18, 10, 3, 0, 16, 15, 7, 4], [15, 7, 11, 3, 0, 13, 12, 21, 4, 14, 1, 8, 20, 9, 10, 6, 18, 2, 22, 17, 19, 16, 5], [0, 4, 11, 16, 7, 13, 17, 18, 3, 21, 19, 9, 22, 14, 1, 15, 12, 20, 5, 8, 2, 6, 10], [8, 7, 21, 1, 10, 2, 20, 3, 17, 11, 0, 12, 22, 9, 14, 4, 19, 15, 13, 16, 6, 5, 18], [7, 9, 20, 19, 13, 17, 8, 21, 18, 6, 10, 5, 0, 11, 1, 22, 12, 3, 16, 15, 4, 14, 2], [3, 11, 6, 16, 9, 15, 17, 5, 13, 20, 0, 2, 8, 12, 7, 18, 22, 1, 19, 4, 10, 14, 21], [4, 11, 17, 10, 5, 6, 19, 9, 7, 21, 22, 18, 0, 2, 14, 12, 16, 8, 3, 15, 1, 13, 20], [21, 18, 22, 20, 7, 0, 6, 2, 10, 15, 1, 9, 8, 3, 4, 12, 13, 14, 5, 17, 19, 11, 16], [13, 3, 20, 1, 9, 4, 19, 17, 22, 12, 11, 21, 7, 10, 5, 0, 2, 14, 6, 8, 15, 18, 16], [1, 15, 6, 16, 12, 7, 19, 14, 13, 17, 8, 18, 4, 10, 5, 20, 0, 9, 2, 21, 3, 11, 22], [1, 7, 11, 14, 20, 18, 22, 13, 3, 6, 4, 16, 17, 15, 2, 9, 10, 19, 0, 8, 5, 12, 21], [0, 18, 7, 11, 3, 9, 2, 17, 8, 19, 15, 6, 13, 22, 16, 5, 1, 4, 12, 21, 10, 20, 14], [15, 21, 0, 11, 4, 8, 19, 12, 17, 1, 6, 16, 13, 20, 3, 22, 10, 7, 18, 14, 5, 2, 9]],
   [[4, 12, 17, 8, 18, 7, 20, 15, 14, 1, 16, 21, 3, 5, 11, 19, 2, 0, 9, 13, 22, 10, 6], [5, 10, 7, 13, 14, 18, 6, 4, 12, 11, 8, 21, 15, 16, 17, 9, 22, 19, 1, 20, 3, 0, 2], [19, 16, 13, 18, 15, 6, 2, 4, 0, 14, 7, 21, 9, 5, 1, 20, 8, 3, 10, 12, 17, 11, 22], [16, 13, 12, 6, 17, 2, 11, 0, 21, 14, 22, 5, 3, 1, 9, 10, 7, 18, 19, 8, 20, 4, 15], [12, 14, 22, 17, 20, 11, 9, 0, 6, 1, 10, 13, 16, 4, 21, 19, 18, 5, 8, 3, 2, 7, 15], [12, 20, 13, 18, 0, 4, 5, 8, 17, 7, 3, 1, 15, 21, 14, 19, 16, 2, 11, 6, 22, 9, 10], [15, 3, 16, 1, 5, 14, 18, 12, 19, 4, 13, 10, 9, 0, 17, 20, 22, 7, 21, 6, 2, 11, 8], [18, 16, 22, 11, 15, 7, 19, 8, 4, 9, 12, 0, 20, 3, 1, 10, 21, 5, 14, 17, 6, 2, 13], [21, 18, 22, 20, 7, 0, 6, 2, 10, 15, 1, 9, 8, 3, 4, 12, 13, 14, 5, 17, 19, 11, 16], [8, 4, 16, 14, 19, 9, 15, 21, 6, 18, 1, 3, 13, 7, 11, 17, 5, 0, 10, 20, 22, 2, 12], [3, 22, 5, 9, 4, 18, 7, 14, 0, 15, 8, 12, 19, 10, 11, 13, 2, 17, 21, 20, 6, 1, 16], [14, 12, 9, 18, 19, 10, 21, 11, 8, 17, 6, 13, 20, 1, 3, 7, 16, 0, 2, 22, 15, 4, 5], [21, 16, 14, 22, 10, 7, 11, 3, 8, 5, 1, 2, 19, 12, 4, 17, 6, 15, 20, 9, 0, 18, 13], [2, 22, 5, 17, 15, 12, 13, 8, 16, 19, 7, 6, 9, 14, 21, 10, 18, 4, 0, 11, 3, 1, 20], [8, 21, 16, 0, 4, 2, 20, 6, 10, 3, 13, 14, 11, 15, 7, 9, 22, 17, 5, 12, 19, 18, 1], [22, 18, 2, 13, 9, 20, 15, 19, 11, 1, 10, 5, 21, 0, 17, 12, 16, 14, 4, 7, 8, 6, 3], [20, 2, 17, 3, 22, 0, 11, 18, 12, 15, 21, 8, 6, 1, 14, 10, 16, 13, 7, 5, 19, 9, 4], [9, 16, 14, 4, 21, 18, 8, 3, 12, 0, 2, 17, 5, 6, 22, 13, 11, 10, 19, 15, 20, 7, 1], [1, 2, 11, 16, 8, 14, 12, 9, 0, 18, 22, 5, 20, 19, 4, 17, 7, 13, 6, 15, 3, 21, 10], [7, 11, 22, 1, 2, 3, 17, 4, 12, 18, 16, 14, 15, 5, 21, 10, 8, 13, 20, 0, 9, 19, 6], [9, 18, 21, 8, 16, 2, 13, 22, 5, 15, 1, 0, 6, 20, 19, 7, 3, 4, 12, 11, 17, 14, 10], [18, 1, 10, 22, 4, 21, 0, 14, 2, 7, 15, 9, 13, 17, 6, 5, 8, 19, 11, 20, 3, 16, 12], [14, 22, 0, 1, 20, 17, 10, 18, 7, 2, 3, 9, 13, 21, 19, 5, 8, 6, 11, 4, 15, 16, 12], [18, 11, 0, 20, 4, 6, 1, 13, 17, 14, 22, 15, 21, 12, 7, 10, 2, 19, 5, 3, 9, 8, 16]],
   [[21, 11, 15, 2, 7, 16, 10, 13, 12, 9, 20, 6, 14, 18, 0, 5, 19, 1, 22, 4, 8, 17, 3], [21, 1, 3, 6, 17, 5, 12, 8, 14, 19, 13, 20, 18, 7, 10, 4, 0, 9, 2, 15, 16, 11, 22], [18, 21, 0, 20, 17, 2, 11, 10, 7, 12, 15, 19, 5, 6, 13, 4, 8, 3, 16, 9, 22, 14, 1], [4, 6, 22, 8, 14, 2, 5, 10, 19, 21, 12, 7, 20, 15, 0, 9, 11, 13, 16, 1, 3, 17, 18], [10, 3, 5, 7, 15, 21, 20, 1, 0, 13, 4, 9, 11, 18, 14, 17, 19, 8, 22, 16, 6, 2, 12], [10, 17, 11, 0, 19, 7, 2, 14, 12, 4, 20, 1, 13, 8, 21, 5, 3, 6, 15, 18, 9, 22, 16], [11, 14, 21, 13, 8, 17, 20, 5, 7, 9, 15, 3, 10, 22, 18, 4, 1, 19, 0, 6, 12, 16, 2], [20, 10, 11, 7, 14, 9, 16, 5, 8, 19, 4, 6, 13, 22, 2, 17, 1, 15, 21, 12, 18, 0, 3], [5, 13, 1, 3, 22, 19, 12, 18, 11, 21, 15, 6, 8, 17, 14, 9, 16, 2, 7, 20, 0, 10, 4], [9, 22, 10, 7, 3, 12, 13, 21, 6, 0, 17, 16, 8, 15, 2, 19, 1, 11, 5, 18, 20, 4, 14], [19, 3, 4, 5, 7, 13, 22, 0, 16, 20, 15, 1, 8, 17, 11, 12, 10, 6, 9, 21, 18, 14, 2], [15, 16, 8, 14, 9, 19, 10, 1, 7, 3, 17, 2, 0, 13, 5, 20, 22, 12, 18, 21, 6, 4, 11], [13, 9, 2, 22, 18, 11, 21, 19, 20, 4, 10, 8, 15, 3, 17, 6, 16, 14, 1, 7, 5, 12, 0], [14, 19, 5, 20, 0, 6, 1, 11, 3, 15, 7, 16, 10, 17, 4, 13, 18, 21, 22, 8, 12, 9, 2], [4, 9, 7, 0, 21, 11, 16, 2, 22, 17, 3, 6, 1, 15, 10, 12, 20, 18, 13, 8, 19, 5, 14], [6, 1, 8, 20, 4, 15, 14, 9, 16, 11, 2, 18, 22, 12, 7, 10, 21, 13, 0, 17, 19, 5, 3], [2, 3, 9, 10, 19, 15, 17, 8, 16, 11, 6, 18, 22, 12, 0, 20, 21, 5, 7, 14, 4, 13, 1], [0, 22, 11, 7, 14, 6, 13, 18, 16, 5, 17, 12, 4, 3, 10, 8, 21, 2, 9, 1, 20, 19, 15], [17, 15, 18, 8, 20, 6, 1, 11, 16, 5, 0, 12, 4, 3, 9, 7, 21, 19, 10, 13, 14, 2, 22], [5, 9, 19, 16, 21, 11, 3, 15, 6, 8, 22, 0, 13, 20, 1, 18, 7, 14, 4, 12, 2, 10, 17], [14, 8, 19, 5, 16, 11, 10, 0, 3, 2, 1, 6, 17, 7, 15, 21, 4, 13, 9, 20, 12, 22, 18], [2, 8, 9, 16, 20, 13, 22, 12, 21, 6, 0, 4, 14, 7, 5, 18, 19, 1, 17, 3, 10, 11, 15], [0, 15, 12, 18, 10, 13, 3, 9, 21, 6, 2, 4, 14, 7, 17, 16, 19, 11, 5, 22, 20, 1, 8], [0, 8, 4, 9, 17, 3, 7, 5, 19, 13, 11, 14, 10, 18, 2, 21, 1, 12, 6, 15, 20, 22, 16]],
   [[10, 8, 11, 19, 4, 16, 9, 6, 0, 12, 2, 20, 3, 18, 21, 15, 13, 5, 14, 22, 1, 17, 7], [16, 0, 18, 20, 12, 14, 2, 5, 10, 17, 13, 21, 4, 8, 7, 1, 3, 9, 11, 6, 15, 19, 22], [5, 10, 7, 13, 14, 18, 6, 4, 12, 11, 8, 21, 15, 16, 17, 9, 22, 19, 1, 20, 3, 0, 2], [17, 10, 21, 11, 1, 16, 8, 13, 0, 5, 18, 14, 22, 12, 3, 6, 2, 15, 9, 4, 19, 7, 20], [17, 13, 18, 14, 21, 22, 10, 15, 8, 2, 5, 7, 1, 11, 0, 20, 16, 9, 3, 4, 12, 6, 19], [5, 18, 14, 21, 17, 7, 2, 15, 0, 11, 16, 6, 8, 20, 10, 1, 13, 12, 19, 4, 3, 9, 22], [7, 16, 8, 3, 17, 22, 6, 12, 11, 18, 0, 9, 14, 1, 10, 15, 5, 20, 2, 4, 21, 19, 13], [11, 10, 5, 16, 17, 8, 12, 15, 3, 0, 22, 19, 18, 6, 21, 9, 4, 20, 1, 14, 13, 2, 7], [0, 19, 17, 13, 12, 9, 5, 3, 15, 18, 14, 2, 11, 6, 4, 22, 8, 10, 7, 21, 20, 16, 1], [11, 14, 20, 6, 18, 0, 8, 16, 9, 1, 21, 5, 19, 12, 17, 7, 3, 22, 15, 2, 13, 4, 10], [0, 15, 17, 4, 22, 16, 20, 7, 11, 5, 3, 8, 9, 13, 21, 14, 12, 19, 2, 18, 6, 1, 10], [0, 21, 10, 6, 11, 18, 9, 13, 22, 7, 4, 17, 2, 5, 12, 1, 15, 14, 3, 16, 20, 8, 19], [0, 1, 14, 11, 19, 15, 20, 13, 17, 18, 6, 22, 7, 5, 8, 12, 2, 16, 10, 3, 9, 21, 4], [6, 4, 13, 12, 9, 15, 3, 14, 17, 18, 0, 22, 7, 5, 10, 11, 2, 21, 8, 20, 19, 16, 1], [18, 10, 21, 17, 2, 14, 5, 4, 15, 12, 1, 0, 20, 9, 3, 13, 11, 19, 7, 22, 16, 8, 6], [13, 14, 3, 4, 5, 8, 7, 10, 2, 9, 0, 15, 18, 6, 17, 12, 11, 19, 16, 20, 1, 21, 22], [20, 19, 5, 7, 18, 12, 11, 8, 16, 10, 0, 4, 13, 15, 6, 22, 14, 21, 17, 9, 3, 2, 1], [0, 4, 22, 13, 8, 20, 5, 10, 2, 15, 16, 7, 19, 11, 6, 17, 21, 14, 18, 1, 9, 3, 12], [0, 12, 7, 10, 6, 5, 11, 18, 21, 20, 14, 19, 8, 13, 16, 2, 3, 22, 15, 4, 9, 1, 17], [0, 14, 15, 3, 16, 20, 6, 17, 11, 8, 21, 18, 1, 12, 13, 2, 19, 10, 9, 22, 5, 7, 4], [0, 19, 4, 5, 17, 9, 15, 6, 14, 12, 2, 13, 3, 22, 20, 16, 21, 8, 10, 1, 18, 11, 7], [0, 7, 13, 6, 20, 15, 22, 10, 21, 9, 8, 3, 17, 5, 2, 14, 11, 4, 12, 19, 18, 1, 16], [0, 1, 8, 22, 3, 12, 9, 5, 16, 10, 20, 4, 13, 15, 17, 7, 14, 2, 6, 11, 18, 21, 19], [0, 1, 17, 4, 11, 7, 18, 15, 2, 6, 9, 19, 5, 12, 16, 13, 8, 14, 20, 22, 10, 21, 3]],
   [[9, 11, 19, 0, 21, 1, 12, 6, 10, 8, 13, 22, 4, 15, 2, 3, 18, 20, 16, 17, 5, 14, 7], [3, 20, 21, 19, 13, 4, 22, 10, 7, 14, 8, 17, 12, 9, 16, 11, 5, 15, 0, 2, 1, 18, 6], [14, 22, 7, 12, 1, 8, 20, 0, 13, 4, 15, 2, 11, 10, 9, 16, 19, 17, 5, 6, 21, 18, 3], [0, 19, 14, 11, 2, 10, 18, 12, 22, 3, 6, 7, 17, 9, 5, 16, 1, 13, 4, 20, 8, 21, 15], [3, 12, 7, 10, 0, 21, 11, 2, 19, 1, 14, 5, 15, 18, 22, 13, 6, 9, 17, 20, 16, 4, 8], [8, 20, 10, 12, 4, 17, 7, 22, 1, 6, 0, 2, 9, 16, 18, 15, 5, 21, 13, 3, 11, 14, 19], [8, 15, 6, 20, 19, 0, 11, 5, 12, 21, 14, 9, 17, 16, 2, 7, 10, 4, 1, 18, 13, 3, 22], [0, 21, 18, 10, 3, 9, 20, 7, 11, 12, 22, 8, 16, 13, 15, 1, 5, 2, 19, 17, 6, 14, 4], [0, 1, 16, 19, 22, 13, 10, 12, 14, 20, 18, 3, 15, 7, 2, 5, 17, 8, 9, 4, 6, 21, 11], [0, 19, 8, 21, 1, 6, 14, 11, 4, 20, 7, 13, 22, 3, 17, 9, 10, 15, 18, 12, 5, 16, 2], [0, 19, 10, 12, 2, 3, 7, 22, 17, 5, 18, 21, 9, 11, 8, 6, 15, 4, 20, 1, 14, 16, 13], [0, 1, 8, 21, 10, 18, 20, 9, 13, 12, 7, 22, 4, 5, 3, 15, 19, 11, 2, 14, 17, 16, 6], [0, 1, 17, 4, 11, 7, 18, 15, 2, 6, 9, 19, 5, 12, 16, 13, 8, 14, 20, 22, 10, 21, 3], [0, 1, 2, 21, 9, 20, 10, 6, 12, 5, 15, 3, 11, 7, 4, 13, 22, 19, 17, 16, 14, 8, 18], [15, 18, 6, 13, 14, 20, 16, 2, 12, 5, 0, 3, 11, 7, 17, 21, 22, 8, 4, 10, 9, 19, 1], [19, 13, 17, 12, 14, 10, 1, 3, 22, 20, 0, 11, 9, 21, 5, 6, 8, 16, 15, 7, 4, 2, 18], [3, 14, 19, 13, 18, 4, 16, 7, 12, 5, 10, 15, 11, 2, 21, 17, 1, 8, 20, 0, 9, 6, 22], [8, 19, 11, 20, 12, 16, 3, 22, 6, 2, 1, 7, 0, 21, 14, 4, 18, 5, 17, 9, 15, 13, 10], [0, 18, 3, 6, 4, 10, 7, 17, 22, 20, 19, 11, 9, 21, 15, 12, 8, 2, 5, 1, 14, 16, 13], [0, 13, 11, 17, 15, 7, 21, 5, 8, 10, 2, 9, 4, 6, 19, 22, 16, 3, 20, 18, 14, 1, 12], [0, 17, 21, 10, 9, 15, 6, 19, 18, 14, 16, 3, 5, 8, 13, 11, 12, 2, 20, 1, 4, 22, 7], [0, 3, 12, 2, 8, 18, 19, 6, 16, 17, 11, 5, 14, 13, 1, 15, 21, 7, 20, 9, 10, 22, 4], [0, 5, 22, 16, 12, 13, 21, 15, 17, 6, 14, 18, 19, 20, 3, 4, 2, 11, 9, 10, 8, 1, 7], [0, 20, 18, 22, 11, 7, 8, 13, 19, 10, 4, 17, 16, 14, 21, 9, 2, 3, 5, 15, 12, 1, 6]],
   [[0, 1, 4, 3, 16, 13, 14, 7, 19, 17, 10, 18, 6, 20, 12, 11, 2, 22, 15, 21, 5, 8, 9], [0, 1, 12, 18, 21, 11, 5, 20, 22, 15, 14, 9, 7, 13, 19, 6, 4, 2, 10, 3, 17, 8, 16], [0, 1, 19, 11, 2, 5, 8, 13, 3, 16, 6, 10, 20, 9, 7, 22, 14, 4, 12, 21, 15, 17, 18], [0, 1, 9, 21, 22, 7, 4, 6, 16, 19, 15, 17, 10, 14, 11, 3, 2, 18, 13, 8, 20, 12, 5], [0, 1, 7, 10, 21, 22, 15, 9, 4, 12, 8, 18, 13, 5, 3, 20, 19, 14, 6, 11, 16, 17, 2], [0, 1, 3, 22, 14, 15, 17, 5, 11, 2, 20, 6, 9, 18, 13, 4, 8, 19, 7, 21, 12, 16, 10], [0, 1, 6, 15, 8, 18, 13, 5, 9, 11, 12, 17, 7, 20, 21, 14, 16, 4, 10, 3, 22, 19, 2], [0, 1, 2, 8, 5, 14, 15, 10, 11, 20, 13, 21, 3, 6, 9, 7, 18, 16, 19, 22, 4, 12, 17], [0, 1, 2, 12, 20, 4, 13, 15, 3, 14, 7, 8, 21, 10, 5, 6, 17, 22, 16, 18, 9, 11, 19], [0, 1, 2, 11, 14, 9, 7, 13, 21, 4, 6, 12, 8, 15, 20, 10, 19, 18, 22, 17, 5, 3, 16], [7, 4, 11, 22, 9, 18, 19, 2, 5, 14, 13, 12, 3, 8, 0, 10, 15, 17, 21, 16, 6, 20, 1], [8, 15, 6, 20, 19, 0, 11, 5, 12, 21, 14, 9, 17, 16, 2, 7, 10, 4, 1, 18, 13, 3, 22], [8, 0, 1, 20, 14, 11, 18, 16, 4, 7, 22, 2, 6, 17, 5, 19, 3, 15, 9, 13, 12, 21, 10], [12, 7, 11, 9, 21, 14, 20, 8, 2, 4, 6, 22, 17, 13, 3, 0, 1, 10, 18, 5, 15, 19, 16], [10, 13, 18, 3, 19, 16, 6, 0, 2, 11, 14, 8, 7, 22, 12, 15, 1, 4, 9, 21, 17, 20, 5], [8, 9, 0, 19, 2, 5, 22, 3, 21, 17, 16, 7, 10, 6, 12, 11, 20, 13, 14, 18, 15, 1, 4], [3, 5, 14, 15, 12, 20, 7, 22, 9, 0, 8, 1, 6, 10, 21, 13, 18, 19, 16, 2, 17, 4, 11], [0, 16, 4, 9, 18, 14, 10, 11, 20, 13, 5, 3, 7, 17, 2, 22, 15, 12, 6, 1, 19, 21, 8], [0, 1, 18, 14, 12, 13, 22, 10, 2, 7, 4, 17, 9, 8, 19, 15, 21, 20, 5, 16, 6, 3, 11], [0, 1, 2, 11, 14, 9, 7, 13, 21, 4, 6, 12, 8, 15, 20, 10, 19, 18, 22, 17, 5, 3, 16], [10, 22, 7, 11, 18, 9, 2, 13, 17, 20, 19, 12, 8, 3, 4, 0, 6, 14, 1, 21, 5, 15, 16], [12, 10, 9, 6, 15, 17, 8, 11, 0, 19, 22, 2, 4, 21, 14, 20, 5, 18, 16, 1, 3, 13, 7], [0, 20, 8, 3, 1, 12, 2, 17, 4, 13, 14, 19, 18, 5, 9, 11, 22, 15, 10, 16, 21, 6, 7], [0, 21, 10, 17, 12, 7, 13, 5, 8, 11, 9, 2, 22, 1, 20, 4, 16, 3, 19, 14, 18, 6, 15]],
   [[0, 21, 16, 14, 15, 1, 9, 22, 20, 18, 19, 17, 4, 5, 10, 7, 3, 8, 11, 12, 13, 6, 2], [0, 21, 16, 17, 10, 18, 22, 5, 6, 15, 9, 4, 20, 7, 13, 19, 12, 11, 2, 8, 1, 14, 3], [0, 1, 6, 17, 21, 20, 16, 11, 10, 7, 13, 8, 2, 18, 15, 4, 3, 19, 9, 12, 14, 22, 5], [0, 1, 17, 19, 16, 6, 15, 12, 21, 11, 18, 5, 2, 13, 10, 9, 22, 20, 3, 14, 7, 4, 8], [0, 1, 22, 14, 8, 13, 18, 2, 10, 7, 3, 19, 9, 12, 17, 6, 20, 21, 11, 16, 15, 4, 5], [0, 1, 22, 19, 17, 7, 2, 12, 4, 8, 18, 9, 10, 6, 15, 3, 16, 11, 5, 21, 13, 14, 20], [0, 1, 2, 11, 14, 13, 16, 9, 18, 12, 6, 4, 22, 5, 3, 17, 19, 21, 8, 10, 15, 20, 7], [0, 1, 2, 12, 20, 4, 13, 15, 3, 14, 7, 8, 21, 10, 5, 6, 17, 22, 16, 18, 9, 11, 19], [0, 1, 2, 8, 5, 14, 15, 10, 11, 20, 13, 21, 3, 6, 9, 7, 18, 16, 19, 22, 4, 12, 17], [0, 1, 2, 21, 9, 20, 10, 6, 12, 5, 15, 3, 11, 7, 4, 13, 22, 19, 17, 16, 14, 8, 18], [0, 1, 2, 3, 4, 7, 22, 5, 17, 11, 10, 9, 18, 20, 21, 19, 16, 8, 12, 15, 13, 14, 6], [11, 12, 14, 17, 16, 2, 20, 6, 7, 19, 1, 0, 22, 13, 15, 5, 3, 4, 18, 9, 8, 21, 10], [8, 19, 12, 17, 13, 22, 1, 9, 16, 7, 0, 18, 4, 3, 11, 5, 14, 15, 10, 20, 21, 2, 6], [7, 11, 15, 16, 14, 9, 3, 19, 22, 17, 6, 0, 20, 13, 1, 12, 5, 21, 4, 18, 2, 10, 8], [0, 6, 9, 5, 21, 22, 20, 12, 16, 7, 8, 18, 4, 3, 10, 17, 14, 2, 11, 1, 13, 15, 19], [0, 19, 18, 12, 10, 20, 3, 11, 14, 22, 2, 4, 21, 5, 8, 16, 15, 9, 7, 6, 13, 1, 17], [0, 1, 21, 9, 15, 19, 13, 20, 8, 12, 22, 6, 5, 7, 17, 18, 2, 16, 10, 3, 11, 14, 4], [0, 1, 18, 12, 14, 9, 7, 13, 6, 19, 21, 11, 5, 20, 15, 22, 4, 2, 10, 3, 8, 17, 16], [0, 1, 2, 14, 11, 13, 10, 22, 18, 7, 19, 3, 9, 5, 4, 20, 6, 15, 8, 16, 21, 17, 12], [0, 1, 2, 17, 7, 21, 19, 10, 9, 13, 20, 14, 3, 22, 11, 5, 12, 16, 15, 6, 4, 18, 8], [0, 1, 2, 4, 3, 7, 15, 18, 17, 6, 16, 21, 5, 20, 9, 14, 10, 13, 12, 22, 8, 19, 11], [0, 1, 2, 18, 13, 4, 20, 19, 3, 21, 5, 17, 14, 10, 7, 22, 8, 6, 16, 12, 11, 9, 15], [18, 20, 19, 0, 5, 16, 22, 8, 10, 13, 7, 15, 12, 4, 9, 17, 14, 11, 21, 3, 1, 2, 6], [2, 21, 4, 7, 22, 5, 13, 11, 0, 1, 12, 15, 14, 17, 18, 20, 10, 9, 19, 3, 16, 8, 6]],
   [[7, 18, 1, 0, 3, 8, 10, 2, 14, 22, 11, 16, 9, 17, 5, 21, 15, 4, 6, 12, 19, 13, 20], [10, 6, 21, 13, 12, 9, 5, 15, 3, 14, 18, 7, 11, 19, 20, 1, 8, 0, 2, 17, 4, 16, 22], [5, 18, 14, 21, 17, 7, 2, 15, 0, 11, 16, 6, 8, 20, 10, 1, 13, 12, 19, 4, 3, 9, 22], [0, 4, 6, 3, 8, 13, 21, 22, 2, 14, 18, 15, 5, 9, 10, 17, 19, 7, 12, 11, 1, 20, 16], [0, 1, 12, 16, 15, 22, 2, 9, 11, 18, 8, 7, 19, 10, 20, 14, 6, 3, 13, 17, 5, 4, 21], [0, 1, 2, 14, 11, 13, 10, 22, 18, 7, 19, 3, 9, 5, 4, 20, 6, 15, 8, 16, 21, 17, 12], [0, 1, 2, 3, 4, 7, 22, 5, 17, 11, 10, 9, 18, 20, 21, 19, 16, 8, 12, 15, 13, 14, 6], [10, 6, 21, 13, 12, 15, 22, 9, 0, 7, 18, 14, 2, 4, 16, 17, 8, 3, 11, 1, 19, 20, 5], [0, 7, 10, 1, 21, 15, 5, 13, 20, 3, 8, 9, 18, 22, 2, 14, 19, 4, 16, 11, 17, 6, 12], [0, 21, 15, 16, 19, 5, 4, 2, 12, 20, 3, 6, 1, 13, 10, 18, 14, 22, 7, 11, 9, 8, 17], [0, 21, 14, 11, 17, 13, 3, 1, 10, 9, 7, 16, 18, 2, 15, 5, 22, 12, 20, 19, 4, 8, 6], [0, 1, 7, 21, 8, 5, 13, 2, 4, 11, 10, 9, 20, 6, 14, 15, 19, 17, 22, 16, 12, 3, 18], [0, 1, 2, 4, 10, 13, 12, 22, 8, 19, 3, 7, 15, 18, 17, 6, 16, 21, 5, 20, 9, 14, 11], [0, 1, 2, 11, 14, 13, 16, 9, 18, 12, 6, 4, 22, 5, 3, 17, 19, 21, 8, 10, 15, 20, 7], [0, 1, 2, 4, 3, 12, 9, 5, 20, 14, 16, 22, 18, 17, 15, 6, 10, 8, 7, 21, 13, 11, 19], [0, 1, 2, 3, 16, 17, 18, 19, 20, 21, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 22], [4, 22, 19, 9, 14, 17, 13, 2, 20, 21, 0, 5, 6, 7, 12, 3, 10, 15, 8, 18, 16, 11, 1], [21, 12, 15, 20, 10, 2, 7, 22, 17, 9, 1, 0, 18, 14, 13, 19, 3, 16, 6, 5, 11, 8, 4], [0, 9, 6, 12, 4, 7, 3, 21, 15, 18, 2, 16, 8, 19, 11, 10, 13, 5, 17, 22, 14, 1, 20], [0, 16, 22, 7, 20, 14, 17, 4, 2, 9, 10, 19, 13, 5, 18, 11, 15, 8, 12, 1, 21, 3, 6], [0, 21, 18, 6, 16, 19, 3, 15, 9, 12, 2, 10, 20, 13, 5, 4, 7, 17, 11, 22, 8, 1, 14], [0, 1, 20, 22, 3, 6, 21, 17, 10, 4, 14, 16, 7, 9, 11, 19, 8, 2, 18, 5, 12, 15, 13], [0, 1, 16, 3, 10, 7, 8, 19, 13, 11, 4, 12, 18, 14, 6, 5, 2, 22, 9, 15, 17, 20, 21], [0, 1, 15, 21, 9, 13, 7, 14, 20, 6, 22, 18, 17, 19, 11, 12, 2, 10, 4, 3, 5, 8, 16]],
   [[0, 1, 11, 16, 5, 19, 12, 9, 2, 18, 21, 13, 17, 6, 10, 7, 20, 8, 14, 22, 4, 15, 3], [0, 1, 6, 12, 15, 5, 17, 14, 22, 9, 8, 21, 19, 7, 13, 18, 16, 2, 4, 3, 11, 20, 10], [0, 1, 13, 6, 3, 22, 14, 8, 10, 4, 21, 16, 5, 11, 9, 15, 17, 2, 12, 7, 18, 19, 20], [0, 1, 22, 21, 15, 6, 12, 16, 7, 3, 9, 11, 17, 4, 10, 20, 2, 18, 5, 13, 19, 14, 8], [0, 1, 2, 15, 21, 14, 4, 18, 6, 17, 9, 3, 5, 19, 16, 7, 22, 13, 11, 10, 8, 20, 12], [0, 1, 2, 20, 17, 8, 9, 4, 5, 14, 7, 15, 3, 18, 21, 19, 12, 10, 13, 22, 16, 6, 11], [0, 1, 2, 19, 14, 21, 4, 12, 22, 8, 11, 3, 7, 15, 16, 5, 6, 20, 9, 10, 17, 13, 18], [0, 1, 2, 9, 15, 8, 16, 12, 18, 11, 21, 3, 17, 13, 10, 19, 22, 7, 5, 4, 20, 14, 6], [0, 1, 2, 16, 3, 19, 9, 12, 11, 18, 10, 15, 17, 14, 21, 8, 4, 7, 6, 22, 20, 13, 5], [0, 1, 2, 3, 16, 19, 22, 17, 11, 5, 4, 21, 12, 14, 15, 13, 10, 20, 6, 9, 7, 8, 18], [0, 1, 2, 3, 16, 8, 12, 15, 13, 14, 4, 7, 22, 5, 17, 11, 10, 9, 18, 20, 21, 19, 6], [0, 1, 2, 3, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 4, 5, 6, 7, 8, 9, 22], [0, 1, 2, 3, 16, 15, 6, 8, 9, 7, 4, 14, 18, 21, 19, 20, 10, 13, 22, 11, 5, 17, 12], [0, 1, 2, 3, 10, 13, 22, 11, 5, 17, 16, 15, 6, 8, 9, 7, 4, 14, 18, 21, 19, 20, 12], [0, 1, 2, 3, 10, 20, 6, 9, 7, 8, 16, 19, 22, 17, 11, 5, 4, 21, 12, 14, 15, 13, 18], [3, 2, 7, 4, 17, 14, 18, 0, 5, 12, 6, 10, 19, 21, 8, 16, 11, 13, 1, 20, 22, 15, 9], [3, 8, 12, 17, 20, 10, 2, 7, 22, 14, 6, 0, 4, 19, 11, 5, 9, 1, 16, 21, 13, 15, 18], [19, 16, 13, 0, 5, 9, 21, 7, 17, 20, 10, 12, 8, 3, 1, 11, 6, 15, 4, 2, 18, 14, 22], [0, 17, 8, 15, 18, 10, 13, 7, 22, 1, 21, 19, 5, 2, 12, 9, 20, 16, 6, 14, 3, 11, 4], [0, 19, 17, 2, 4, 18, 3, 6, 16, 12, 5, 11, 15, 22, 20, 14, 21, 7, 1, 10, 9, 13, 8], [0, 19, 17, 11, 20, 12, 6, 22, 13, 4, 3, 15, 16, 14, 9, 5, 10, 1, 8, 7, 18, 2, 21], [0, 1, 13, 5, 8, 3, 14, 22, 21, 19, 2, 7, 12, 17, 16, 4, 18, 10, 6, 9, 11, 15, 20], [0, 3, 14, 9, 17, 6, 21, 1, 10, 11, 2, 19, 22, 7, 15, 5, 18, 20, 12, 16, 8, 4, 13], [0, 1, 7, 21, 8, 5, 13, 2, 4, 11, 10, 9, 20, 6, 14, 15, 19, 17, 22, 16, 12, 3, 18]],
   [[0, 1, 2, 10, 3, 18, 15, 11, 8, 20, 4, 22, 6, 5, 21, 12, 16, 14, 13, 9, 19, 17, 7], [0, 1, 2, 3, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 4, 5, 6, 7, 8, 9, 22], [0, 1, 17, 4, 9, 19, 5, 12, 16, 13, 8, 14, 20, 22, 10, 21, 11, 7, 18, 15, 2, 6, 3], [0, 1, 17, 4, 9, 12, 3, 19, 7, 14, 8, 13, 18, 2, 6, 15, 11, 16, 20, 21, 22, 10, 5], [0, 1, 2, 12, 7, 4, 6, 5, 10, 21, 17, 19, 18, 16, 11, 9, 20, 8, 3, 14, 13, 15, 22], [0, 1, 2, 3, 10, 5, 15, 14, 13, 12, 16, 22, 19, 18, 21, 20, 4, 11, 8, 9, 6, 7, 17], [16, 17, 14, 20, 6, 5, 9, 2, 13, 12, 0, 22, 19, 18, 8, 3, 4, 7, 21, 15, 10, 11, 1], [12, 8, 7, 13, 4, 2, 18, 17, 5, 20, 1, 0, 15, 6, 9, 14, 3, 10, 19, 22, 11, 21, 16], [0, 17, 22, 14, 21, 15, 18, 8, 4, 5, 11, 19, 10, 3, 16, 13, 7, 2, 12, 1, 6, 9, 20], [0, 20, 19, 8, 16, 18, 3, 12, 7, 15, 2, 10, 21, 14, 11, 4, 9, 22, 5, 17, 6, 1, 13], [0, 10, 17, 18, 13, 6, 5, 16, 2, 20, 4, 14, 9, 22, 15, 11, 7, 21, 8, 1, 12, 3, 19], [0, 2, 15, 10, 19, 8, 9, 16, 14, 6, 12, 1, 17, 7, 21, 3, 18, 11, 4, 22, 13, 5, 20], [0, 11, 22, 8, 15, 9, 12, 20, 16, 17, 5, 13, 4, 3, 10, 7, 19, 2, 6, 1, 18, 21, 14], [0, 1, 13, 17, 3, 19, 12, 5, 4, 16, 6, 10, 18, 20, 11, 14, 21, 2, 15, 22, 8, 7, 9], [0, 1, 10, 3, 4, 18, 21, 14, 9, 11, 16, 8, 15, 6, 19, 22, 2, 17, 20, 7, 5, 13, 12], [0, 1, 7, 12, 20, 9, 18, 6, 13, 19, 17, 15, 5, 14, 11, 8, 2, 4, 16, 3, 22, 21, 10], [0, 1, 5, 16, 11, 3, 7, 15, 19, 2, 20, 6, 10, 9, 22, 8, 21, 14, 12, 4, 17, 13, 18], [0, 1, 2, 7, 12, 6, 16, 15, 19, 5, 20, 3, 22, 14, 10, 18, 17, 9, 11, 4, 21, 13, 8], [0, 1, 2, 13, 5, 21, 20, 16, 22, 6, 18, 7, 3, 15, 12, 14, 8, 4, 9, 17, 10, 19, 11], [0, 1, 2, 6, 11, 10, 22, 13, 16, 20, 14, 21, 18, 4, 15, 17, 19, 5, 3, 9, 8, 7, 12], [0, 1, 2, 5, 18, 22, 16, 19, 15, 7, 13, 3, 6, 21, 10, 12, 8, 11, 9, 4, 14, 20, 17], [0, 1, 2, 10, 3, 14, 20, 8, 11, 15, 4, 7, 5, 6, 12, 21, 16, 18, 19, 17, 13, 9, 22], [0, 1, 2, 22, 9, 10, 6, 20, 16, 13, 21, 14, 12, 4, 19, 8, 15, 7, 3, 11, 17, 5, 18], [0, 1, 2, 3, 10, 14, 17, 5, 11, 22, 16, 12, 8, 6, 7, 9, 4, 13, 19, 20, 18, 21, 15]],
   [[0, 1, 2, 3, 4, 9, 17, 11, 22, 5, 10, 7, 19, 21, 20, 18, 16, 6, 15, 12, 14, 13, 8], [0, 1, 2, 3, 10, 21, 8, 7, 9, 6, 16, 18, 17, 22, 5, 11, 4, 20, 15, 13, 12, 14, 19], [0, 1, 2, 3, 16, 22, 19, 18, 21, 20, 4, 11, 8, 9, 6, 7, 10, 5, 15, 14, 13, 12, 17], [0, 1, 2, 3, 16, 18, 17, 22, 5, 11, 4, 20, 15, 13, 12, 14, 10, 21, 8, 7, 9, 6, 19], [0, 1, 2, 3, 10, 12, 11, 22, 17, 5, 16, 14, 9, 7, 6, 8, 4, 15, 20, 19, 21, 18, 13], [0, 1, 2, 3, 16, 6, 15, 12, 14, 13, 4, 9, 17, 11, 22, 5, 10, 7, 19, 21, 20, 18, 8], [0, 1, 2, 3, 16, 5, 20, 21, 18, 19, 4, 17, 9, 8, 7, 6, 10, 22, 13, 12, 15, 14, 11], [10, 22, 16, 6, 1, 13, 0, 12, 18, 4, 14, 15, 3, 2, 7, 5, 21, 8, 9, 20, 19, 17, 11], [10, 22, 7, 15, 0, 11, 12, 13, 18, 3, 16, 21, 14, 6, 4, 17, 20, 5, 19, 2, 8, 9, 1], [11, 17, 6, 0, 12, 15, 10, 7, 1, 16, 5, 14, 2, 20, 9, 21, 18, 3, 22, 13, 4, 19, 8], [0, 9, 13, 20, 22, 12, 18, 7, 2, 15, 5, 21, 14, 6, 19, 3, 17, 1, 4, 11, 16, 10, 8], [0, 1, 10, 5, 15, 3, 18, 11, 4, 19, 17, 20, 12, 2, 6, 21, 14, 13, 16, 9, 22, 8, 7], [0, 1, 2, 18, 5, 7, 6, 4, 17, 15, 8, 14, 3, 20, 19, 21, 13, 10, 12, 11, 16, 9, 22], [0, 1, 2, 3, 16, 5, 20, 21, 18, 19, 4, 17, 9, 8, 7, 6, 10, 22, 13, 12, 15, 14, 11], [10, 22, 7, 15, 16, 5, 4, 17, 14, 6, 20, 21, 9, 8, 2, 19, 0, 1, 13, 12, 3, 18, 11], [11, 10, 4, 14, 7, 6, 22, 18, 21, 13, 1, 16, 9, 15, 5, 8, 20, 3, 0, 17, 12, 2, 19], [11, 10, 5, 16, 17, 15, 7, 8, 20, 19, 22, 0, 1, 13, 2, 14, 4, 3, 18, 9, 6, 21, 12], [11, 10, 5, 16, 22, 19, 18, 6, 21, 9, 4, 20, 1, 14, 13, 2, 17, 8, 12, 15, 3, 0, 7], [11, 10, 5, 16, 4, 8, 13, 2, 1, 14, 17, 20, 0, 3, 15, 12, 22, 7, 6, 18, 9, 21, 19], [7, 10, 9, 8, 16, 3, 11, 13, 1, 18, 6, 5, 20, 17, 0, 14, 4, 12, 22, 2, 19, 15, 21], [10, 17, 0, 19, 11, 14, 9, 13, 1, 2, 20, 21, 7, 5, 12, 22, 3, 18, 15, 16, 4, 8, 6], [10, 6, 21, 7, 20, 14, 15, 19, 16, 12, 5, 11, 3, 1, 4, 18, 17, 2, 22, 0, 9, 13, 8], [10, 20, 8, 2, 3, 4, 13, 6, 5, 9, 7, 16, 15, 0, 1, 11, 18, 14, 12, 17, 19, 21, 22], [10, 22, 21, 20, 11, 2, 14, 3, 7, 19, 9, 6, 5, 12, 16, 13, 8, 18, 4, 1, 0, 17, 15]],
   [[11, 14, 20, 6, 18, 16, 10, 0, 22, 5, 21, 1, 15, 13, 4, 2, 3, 9, 19, 7, 12, 17, 8], [0, 19, 17, 13, 12, 3, 1, 9, 10, 2, 14, 18, 7, 20, 16, 21, 8, 15, 11, 22, 6, 4, 5], [0, 19, 17, 13, 8, 9, 20, 16, 7, 21, 12, 10, 18, 15, 3, 5, 14, 1, 6, 11, 22, 4, 2], [0, 16, 14, 5, 2, 7, 18, 6, 1, 3, 12, 10, 17, 9, 11, 19, 22, 4, 13, 8, 20, 15, 21], [0, 21, 10, 6, 11, 13, 19, 18, 14, 17, 4, 7, 3, 20, 8, 16, 15, 22, 2, 1, 5, 12, 9], [0, 21, 10, 6, 4, 17, 2, 5, 12, 1, 15, 14, 3, 16, 20, 8, 11, 18, 9, 13, 22, 7, 19], [0, 21, 10, 6, 15, 18, 20, 8, 3, 16, 11, 14, 7, 22, 13, 9, 4, 19, 5, 2, 1, 12, 17], [0, 12, 15, 3, 22, 20, 6, 21, 9, 18, 17, 8, 13, 14, 1, 2, 4, 7, 11, 16, 5, 10, 19], [0, 19, 8, 21, 7, 13, 22, 3, 17, 9, 10, 15, 18, 12, 5, 16, 1, 6, 14, 11, 4, 20, 2], [0, 19, 8, 21, 10, 6, 5, 16, 18, 12, 1, 15, 20, 4, 11, 14, 7, 2, 3, 22, 9, 17, 13], [0, 11, 1, 15, 18, 21, 9, 13, 5, 6, 3, 17, 10, 20, 8, 2, 7, 12, 16, 4, 22, 14, 19], [0, 19, 17, 13, 12, 10, 18, 15, 3, 5, 14, 1, 6, 11, 22, 4, 8, 9, 20, 16, 7, 21, 2], [0, 14, 3, 1, 22, 11, 7, 17, 4, 19, 20, 10, 2, 13, 12, 15, 8, 9, 5, 6, 18, 16, 21], [0, 21, 10, 6, 15, 14, 3, 16, 20, 8, 11, 18, 9, 13, 22, 7, 4, 17, 2, 5, 12, 1, 19], [0, 1, 16, 3, 2, 20, 12, 7, 21, 22, 10, 15, 14, 5, 6, 18, 4, 9, 11, 8, 13, 19, 17], [0, 1, 16, 19, 22, 12, 11, 13, 8, 3, 18, 20, 9, 6, 21, 4, 17, 14, 15, 5, 7, 2, 10], [0, 1, 8, 22, 3, 12, 9, 5, 16, 10, 20, 4, 13, 15, 17, 7, 14, 2, 6, 11, 18, 21, 19], [0, 1, 17, 4, 8, 7, 10, 21, 20, 22, 11, 14, 6, 2, 15, 18, 9, 3, 12, 5, 13, 16, 19], [0, 1, 4, 8, 17, 5, 10, 14, 6, 13, 11, 3, 18, 7, 16, 20, 9, 21, 22, 2, 12, 19, 15], [0, 1, 16, 15, 6, 22, 7, 5, 19, 2, 12, 14, 21, 18, 13, 10, 8, 11, 17, 9, 20, 3, 4], [0, 1, 16, 3, 10, 15, 14, 5, 6, 18, 4, 9, 11, 8, 13, 19, 2, 20, 12, 7, 21, 22, 17], [0, 1, 16, 3, 4, 20, 13, 19, 11, 8, 2, 9, 22, 21, 7, 12, 10, 17, 5, 14, 18, 6, 15], [0, 1, 16, 19, 18, 20, 9, 6, 21, 4, 17, 14, 15, 5, 7, 2, 22, 12, 11, 13, 8, 3, 10], [0, 1, 16, 19, 17, 12, 7, 2, 15, 5, 22, 14, 3, 8, 13, 11, 18, 10, 6, 9, 4, 21, 20]],
   [[0, 1, 8, 22, 20, 4, 13, 15, 17, 7, 14, 2, 6, 11, 18, 21, 3, 12, 9, 5, 16, 10, 19], [0, 1, 17, 19, 16, 12, 8, 6, 20, 5, 18, 11, 3, 7, 4, 14, 22, 21, 2, 9, 13, 10, 15], [0, 1, 17, 19, 18, 5, 2, 13, 10, 9, 22, 20, 3, 14, 7, 4, 16, 6, 15, 12, 21, 11, 8], [0, 1, 9, 5, 19, 2, 11, 6, 15, 13, 12, 4, 18, 21, 17, 7, 3, 20, 22, 8, 10, 16, 14], [0, 1, 9, 2, 15, 7, 11, 18, 16, 12, 22, 8, 20, 14, 4, 5, 21, 6, 13, 17, 10, 19, 3], [0, 1, 16, 9, 13, 18, 5, 8, 22, 10, 14, 11, 6, 19, 21, 4, 7, 12, 17, 20, 15, 3, 2], [0, 1, 2, 11, 6, 12, 8, 15, 20, 10, 19, 18, 22, 17, 5, 3, 14, 9, 7, 13, 21, 4, 16], [0, 1, 2, 11, 19, 9, 5, 3, 22, 17, 14, 18, 4, 21, 13, 7, 6, 16, 15, 8, 10, 20, 12], [0, 1, 2, 12, 20, 15, 19, 4, 22, 8, 7, 14, 16, 9, 11, 18, 17, 3, 21, 6, 10, 5, 13], [0, 1, 2, 12, 7, 8, 21, 10, 5, 6, 17, 22, 16, 18, 9, 11, 20, 4, 13, 15, 3, 14, 19], [0, 1, 2, 12, 17, 4, 9, 11, 16, 18, 20, 22, 14, 3, 15, 13, 7, 19, 10, 21, 6, 5, 8], [0, 1, 2, 11, 6, 15, 16, 12, 9, 18, 19, 10, 7, 21, 4, 13, 14, 20, 22, 3, 17, 5, 8], [0, 1, 2, 11, 19, 18, 22, 17, 5, 3, 14, 9, 7, 13, 21, 4, 6, 12, 8, 15, 20, 10, 16], [0, 1, 2, 18, 13, 17, 3, 21, 20, 19, 5, 4, 22, 7, 10, 14, 8, 15, 12, 16, 9, 11, 6], [0, 1, 2, 11, 19, 3, 12, 9, 16, 18, 14, 17, 15, 10, 20, 8, 6, 22, 4, 7, 21, 13, 5], [0, 1, 2, 8, 5, 10, 17, 14, 16, 21, 13, 20, 19, 4, 12, 22, 18, 11, 3, 7, 6, 9, 15], [0, 1, 2, 4, 16, 22, 18, 17, 15, 6, 10, 8, 7, 21, 13, 11, 3, 12, 9, 5, 20, 14, 19], [0, 1, 2, 4, 10, 12, 13, 11, 7, 21, 3, 8, 14, 20, 5, 9, 16, 19, 17, 18, 6, 15, 22], [0, 1, 2, 18, 13, 21, 6, 17, 15, 4, 5, 19, 12, 9, 11, 16, 8, 20, 22, 14, 7, 10, 3], [0, 1, 2, 3, 10, 9, 18, 20, 21, 19, 16, 8, 12, 15, 13, 14, 4, 7, 22, 5, 17, 11, 6], [0, 1, 2, 3, 16, 7, 13, 14, 12, 15, 4, 8, 11, 17, 5, 22, 10, 6, 20, 18, 19, 21, 9], [0, 1, 2, 3, 10, 13, 22, 11, 5, 17, 16, 15, 6, 8, 9, 7, 4, 14, 18, 21, 19, 20, 12], [0, 1, 2, 3, 16, 17, 18, 19, 20, 21, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 22], [0, 1, 2, 3, 10, 20, 6, 9, 7, 8, 16, 19, 22, 17, 11, 5, 4, 21, 12, 14, 15, 13, 18]],
   [[0, 1, 2, 3, 16, 8, 12, 15, 13, 14, 4, 7, 22, 5, 17, 11, 10, 9, 18, 20, 21, 19, 6], [0, 1, 2, 3, 4, 9, 17, 11, 22, 5, 10, 7, 19, 21, 20, 18, 16, 6, 15, 12, 14, 13, 8], [0, 1, 2, 3, 16, 14, 9, 7, 6, 8, 4, 15, 20, 19, 21, 18, 10, 12, 11, 22, 17, 5, 13], [0, 1, 2, 3, 16, 15, 6, 8, 9, 7, 4, 14, 18, 21, 19, 20, 10, 13, 22, 11, 5, 17, 12], [0, 1, 2, 3, 10, 17, 14, 15, 12, 13, 16, 11, 21, 20, 19, 18, 4, 22, 7, 6, 9, 8, 5], [0, 1, 2, 3, 10, 8, 21, 19, 18, 20, 16, 9, 14, 13, 15, 12, 4, 6, 5, 22, 11, 17, 7], [0, 1, 2, 3, 16, 9, 14, 13, 15, 12, 4, 6, 5, 22, 11, 17, 10, 8, 21, 19, 18, 20, 7], [0, 1, 2, 3, 10, 15, 5, 17, 22, 11, 16, 13, 7, 9, 8, 6, 4, 12, 21, 18, 20, 19, 14], [0, 1, 2, 3, 10, 5, 15, 14, 13, 12, 16, 22, 19, 18, 21, 20, 4, 11, 8, 9, 6, 7, 17]]]

/-- Stabilizer chain data. -/
def fullLvls : List Lvl :=
  [⟨0, [1, 2, 185, 204, 229, 274, 303, 341],
    [⟨10, 1, 1, 1, 0⟩, ⟨1, 2, 3, 2, 0⟩, ⟨9, 164, 199, 2, 10⟩, ⟨17, 186, 289, 185, 10⟩, ⟨6, 205, 367, 204, 10⟩, ⟨15, 230, 260, 229, 10⟩, ⟨4, 304, 368, 303, 10⟩, ⟨16, 342, 374, 341, 10⟩, ⟨22, 6, 44, 1, 1⟩, ⟨5, 187, 201, 185, 9⟩, ⟨18, 206, 375, 204, 9⟩, ⟨11, 275, 376, 274, 9⟩, ⟨21, 305, 377, 303, 9⟩, ⟨12, 343, 378, 341, 9⟩, ⟨14, 188, 379, 2, 17⟩, ⟨2, 189, 380, 185, 17⟩, ⟨19, 231, 381, 229, 17⟩, ⟨8, 276, 295, 274, 17⟩, ⟨13, 207, 382, 185, 6⟩, ⟨20, 208, 383, 204, 6⟩, ⟨3, 232, 329, 1, 15⟩, ⟨7, 277, 384, 274, 5⟩]⟩,
   ⟨1, [185, 204, 229, 274, 303, 341],
    [⟨22, 185, 200, 185, 1⟩, ⟨15, 190, 203, 185, 22⟩, ⟨4, 209, 225, 204, 22⟩, ⟨18, 234, 331, 229, 22⟩, ⟨6, 278, 385, 274, 22⟩, ⟨17, 344, 386, 341, 22⟩, ⟨8, 191, 387, 185, 15⟩, ⟨12, 210, 297, 204, 15⟩, ⟨13, 235, 263, 229, 15⟩, ⟨19, 279, 388, 274, 15⟩, ⟨9, 306, 389, 303, 15⟩, ⟨20, 345, 390, 341, 15⟩, ⟨14, 211, 391, 185, 4⟩, ⟨16, 307, 392, 303, 4⟩, ⟨10, 346, 393, 341, 4⟩, ⟨2, 347, 394, 185, 17⟩, ⟨11, 348, 395, 303, 17⟩, ⟨7, 213, 298, 204, 12⟩, ⟨3, 237, 396, 185, 13⟩, ⟨5, 238, 264, 204, 13⟩, ⟨21, 308, 397, 303, 9⟩]⟩,
   ⟨2, [204, 229, 274, 303, 341],
    [⟨14, 204, 224, 204, 2⟩, ⟨8, 214, 228, 204, 14⟩, ⟨4, 240, 398, 229, 14⟩, ⟨21, 280, 399, 274, 14⟩, ⟨17, 215, 400, 204, 8⟩, ⟨12, 241, 267, 229, 8⟩, ⟨20, 309, 338, 303, 8⟩, ⟨13, 349, 401, 341, 8⟩, ⟨19, 242, 402, 204, 4⟩, ⟨9, 243, 403, 229, 4⟩, ⟨16, 310, 404, 303, 4⟩, ⟨10, 350, 405, 341, 4⟩, ⟨15, 311, 406, 303, 21⟩, ⟨7, 351, 407, 341, 21⟩, ⟨11, 312, 408, 303, 17⟩, ⟨18, 281, 409, 274, 12⟩, ⟨6, 313, 410, 303, 12⟩, ⟨5, 352, 411, 204, 13⟩, ⟨3, 245, 412, 204, 19⟩, ⟨22, 315, 413, 229, 16⟩]⟩,
   ⟨3, [229, 274, 303, 341],
    [⟨21, 229, 259, 229, 3⟩, ⟨8, 247, 271, 229, 21⟩, ⟨14, 282, 301, 274, 21⟩, ⟨15, 316, 414, 303, 21⟩, ⟨7, 353, 415, 341, 21⟩, ⟨12, 248, 272, 229, 8⟩, ⟨17, 283, 416, 274, 8⟩, ⟨20, 317, 417, 303, 8⟩, ⟨13, 354, 418, 341, 8⟩, ⟨4, 284, 302, 229, 14⟩, ⟨19, 318, 419, 274, 15⟩, ⟨9, 319, 420, 303, 15⟩, ⟨6, 355, 421, 229, 7⟩, ⟨5, 356, 422, 274, 7⟩, ⟨11, 249, 273, 229, 12⟩, ⟨18, 285, 423, 274, 12⟩, ⟨16, 320, 424, 303, 4⟩, ⟨10, 357, 425, 341, 4⟩, ⟨22, 358, 426, 274, 6⟩]⟩,
   ⟨5, [274, 303, 341],
    [⟨7, 274, 294, 274, 5⟩, ⟨17, 303, 337, 303, 5⟩, ⟨19, 321, 427, 303, 7⟩, ⟨14, 359, 428, 341, 7⟩, ⟨8, 322, 429, 274, 17⟩, ⟨11, 323, 430, 303, 17⟩, ⟨15, 324, 431, 274, 19⟩, ⟨13, 325, 432, 303, 19⟩, ⟨9, 360, 433, 341, 19⟩, ⟨21, 361, 434, 274, 14⟩, ⟨20, 326, 435, 303, 8⟩, ⟨22, 362, 436, 341, 11⟩, ⟨18, 363, 437, 341, 13⟩, ⟨12, 364, 438, 341, 9⟩, ⟨6, 365, 439, 341, 20⟩]⟩,
   ⟨4, [341],
    [⟨10, 341, 373, 341, 4⟩, ⟨16, 366, 440, 341, 10⟩]⟩]

end M23Cert

/-!
# Certified facts about `M₂₃` (reusable)

* `M23Cert.fullOk` : the Schreier–Sims certificate `fullLvls` (base `0,1,2,3,5,4`, orbit lengths
  `23,22,21,20,16,3`) passes the verified checker (`decide +kernel`).
* `M23Cert.card_M23_certified` : `|M₂₃| = 10200960`.
* `M23Cert.mem_M23_iff_sift_full` : a permutation of `Fin 23` belongs to `M₂₃` iff its table
  sifts through the certified chain; the right-hand side is decidable by `decide +kernel`
  (this gives both membership and non-membership certificates).
-/

set_option maxRecDepth 100000

namespace M23Cert

open MathieuM23

theorem fullOk : topChk (Tget fullTabs) fullProg fullLvls = true := by decide +kernel

theorem card_M23_certified : Nat.card M23 = 10200960 := by
  rw [card_of_check (Tget fullTabs) fullProg fullLvls fullOk]
  decide +kernel

/-- Membership in `M₂₃` by sifting through the certified stabilizer chain (both directions). -/
theorem mem_M23_iff_sift_full (g : Equiv.Perm (Fin 23)) :
    g ∈ M23 ↔ sift (Tget fullTabs) fullLvls (tab g) = true :=
  mem_M23_iff_sift _ _ _ fullOk g

theorem mem_M23_of_sift_full (g : Equiv.Perm (Fin 23))
    (hg : sift (Tget fullTabs) fullLvls (tab g) = true) : g ∈ M23 :=
  (mem_M23_iff_sift_full g).mpr hg

example : g₃ ∈ M23 := mem_M23_of_sift_full g₃ (by decide +kernel)

/-- A non-member (a transposition), certified by the failing sift. -/
example : Equiv.swap (0 : Fin 23) 1 ∉ M23 := by
  rw [mem_M23_iff_sift_full]
  decide +kernel

end M23Cert

open Finset in
theorem card_conjClasses_of_reps {G : Type*} [Group G] [Finite G] {n : ℕ} (r : Fin n → G)
    (c : Fin n → ℕ) (hc : ∀ i, 0 < c i)
    (hcent : ∀ i, Nat.card (Subgroup.centralizer {r i}) ≤ c i)
    (hsum : Nat.card G ≤ ∑ i, Nat.card G / c i)
    (hnc : ∀ i j, i ≠ j → ¬ IsConj (r i) (r j)) : Nat.card (ConjClasses G) = n := by
  classical
  have := Fintype.ofFinite G
  let cl : Fin n → Finset G := fun i => univ.filter (fun h => IsConj (r i) h)
  have hcard : ∀ i, Nat.card G ≤ (cl i).card * c i := by
    intro i
    have h1 : (cl i).card = Fintype.card G / Fintype.card (MulAction.stabilizer (ConjAct G) (r i)) := by
      rw [← ConjClasses.card_carrier]
      rw [Fintype.card_subtype]
      congr 1
      ext h
      simp only [cl, ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, mem_filter, mem_univ, true_and]
      exact isConj_comm
    have h2 : Fintype.card (MulAction.stabilizer (ConjAct G) (r i)) ∣ Fintype.card G := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
      exact Subgroup.card_subgroup_dvd_card _
    have h3 : Fintype.card (MulAction.stabilizer (ConjAct G) (r i)) ≤ c i := by
      rw [← Nat.card_eq_fintype_card, ← Subgroup.nat_card_centralizer_nat_card_stabilizer]
      exact hcent i
    rw [h1, Nat.card_eq_fintype_card]
    calc Fintype.card G = Fintype.card G / Fintype.card (MulAction.stabilizer (ConjAct G) (r i)) *
          Fintype.card (MulAction.stabilizer (ConjAct G) (r i)) := (Nat.div_mul_cancel h2).symm
      _ ≤ _ := Nat.mul_le_mul_left _ h3
  have hlow : ∀ i, Nat.card G / c i ≤ (cl i).card := by
    intro i
    exact (Nat.div_le_iff_le_mul_add_pred (hc i)).2 (by
      have := hcard i
      have h4 := hc i
      nlinarith) 
  have hdisj : Set.PairwiseDisjoint (↑(univ : Finset (Fin n))) cl := by
    intro i _ j _ hij
    rw [Function.onFun, Finset.disjoint_left]
    intro h hi hj
    simp only [cl, mem_filter, mem_univ, true_and] at hi hj
    exact hnc i j hij (hi.trans hj.symm)
  have hU : (univ.biUnion cl).card = ∑ i, (cl i).card := Finset.card_biUnion (fun i hi j hj hij => hdisj hi hj hij)
  have hUeq : univ.biUnion cl = univ := by
    apply Finset.eq_univ_of_card
    rw [← Nat.card_eq_fintype_card]
    apply le_antisymm
    · rw [Nat.card_eq_fintype_card]; exact Finset.card_le_univ _
    · rw [hU]
      calc Nat.card G ≤ ∑ i, Nat.card G / c i := hsum
        _ ≤ _ := Finset.sum_le_sum (fun i _ => hlow i)
  let f : Fin n → ConjClasses G := fun i => ConjClasses.mk (r i)
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      by_contra hne
      exact hnc i j hne (ConjClasses.mk_eq_mk_iff_isConj.mp hij)
    · intro x
      obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective x
      have : g ∈ univ.biUnion cl := by rw [hUeq]; exact mem_univ g
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp this
      simp only [cl, mem_filter, mem_univ, true_and] at hi
      exact ⟨i, ConjClasses.mk_eq_mk_iff_isConj.mpr hi⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_fin]

/-!
# A certified search for conjugators in `M₂₃`

`cnt get r ls prev s` counts (an upper bound for) the elements `k` of the chain subgroup
`Kls ls` with `k r = s k`: it branches over the transversal of the first level, conjugates `s`
by the chosen transversal element and prunes with a necessary consistency condition on the orbits
of the earlier base points.
-/

set_option maxRecDepth 100000

namespace M23Cert

open MathieuM23

/-! ### Permutations coded by natural numbers (digits in base 32), for fast kernel evaluation -/

/-- Forces the evaluation of `v` to a literal before continuing (a kernel-evaluation device). -/
def strict {α : Type} (v : ℕ) (k : ℕ → α) : α :=
  match v with
  | 0 => k 0
  | n + 1 => k (Nat.succ n)

theorem strict_eq {α : Type} (v : ℕ) (k : ℕ → α) : strict v k = k v := by
  cases v <;> rfl

/-- Horner encoding of a table into a natural number (base 32). -/
def encL : List ℕ → ℕ
  | [] => 0
  | x :: t => Nat.add x (Nat.mul 32 (encL t))

/-- The `i`-th digit of a code. -/
def pw (a : ℕ) : ℕ := Nat.pow 32 a

theorem pw_eq (a : ℕ) : pw a = 32 ^ a := rfl

def cget (c i : ℕ) : ℕ := Nat.mod (Nat.div c (pw i)) 32

theorem cget_def (c i : ℕ) : cget c i = c / 32 ^ i % 32 := rfl

/-- Composition of coded permutations. -/
def tmulC (p q : ℕ) : ℕ :=
  strict p (fun p' => strict q (fun q' => encL ((List.range 23).map (fun j => cget p' (cget q' j)))))

/-- The code of a permutation. -/
def ctab (p : Equiv.Perm (Fin 23)) : ℕ := encL (tab p)

theorem cget_encL : ∀ (t : List ℕ), (∀ x ∈ t, x < 32) → ∀ i, cget (encL t) i = t.getD i 0 := by
  intro t
  induction t with
  | nil => intro _ i; simp [encL, cget_def]
  | cons x t ih =>
    intro h i
    have hx : x < 32 := h x (by simp)
    cases i with
    | zero => simp [encL, cget_def]; omega
    | succ i =>
      have := ih (fun y hy => h y (by simp [hy])) i
      simp only [cget_def, encL, Nat.add_eq, Nat.mul_eq] at this ⊢
      rw [pow_succ', ← Nat.div_div_eq_div_mul]
      have e : (x + 32 * encL t) / 32 = encL t := by omega
      rw [e, this]; simp

theorem tab_lt (p : Equiv.Perm (Fin 23)) : ∀ x ∈ tab p, x < 32 := by
  intro x hx
  simp only [tab, List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  have := (p i).2
  omega

theorem cget_ctab (p : Equiv.Perm (Fin 23)) {i : ℕ} (hi : i < 23) :
    cget (ctab p) i = (p (fo i)).val := by
  unfold ctab
  rw [cget_encL _ (tab_lt p), ← tget_tab p (fo i), fo_val hi]
  rfl

theorem ctab_mul (a b : Equiv.Perm (Fin 23)) : ctab (a * b) = tmulC (ctab a) (ctab b) := by
  unfold tmulC ctab
  simp only [strict_eq]
  congr 1
  apply List.ext_getElem
  · simp [tab]
  · intro i h1 h2
    have hi : i < 23 := by simpa [tab] using h1
    simp only [List.getElem_map, List.getElem_range]
    have := cget_ctab a (i := (b (fo i)).val) (b (fo i)).2
    have h3 := cget_ctab b hi
    unfold ctab at h3 this
    rw [h3, this]
    simp only [tab, List.getElem_ofFn, fo_val', Equiv.Perm.coe_mul, Function.comp]
    rw [show (⟨i, hi⟩ : Fin 23) = fo i from Fin.ext (by rw [fo_val hi])]

theorem ctab_inj {a b : Equiv.Perm (Fin 23)} (h : ctab a = ctab b) : a = b := by
  ext i
  have h1 := cget_ctab a i.2
  have h2 := cget_ctab b i.2
  rw [h, h2] at h1
  rw [fo_val'] at h1
  exact h1.symm

theorem cget_zero (i : ℕ) : cget 0 i = 0 := by simp [cget_def]

theorem cget_add (F a v i : ℕ) (h0 : cget F a = 0) (hv : v < 32) :
    cget (F + v * 32 ^ a) i = if i = a then v else cget F i := by
  simp only [cget_def] at *
  have hP : 0 < 32 ^ a := by positivity
  obtain ⟨m, hm⟩ : ∃ m, F / 32 ^ a = 32 * m := by
    refine ⟨F / 32 ^ a / 32, ?_⟩
    have := Nat.div_add_mod (F / 32 ^ a) 32
    omega
  obtain ⟨low, hlow⟩ : ∃ low, low = F % 32 ^ a := ⟨_, rfl⟩
  have hlowlt : low < 32 ^ a := hlow ▸ Nat.mod_lt _ hP
  have hF : F = low + 32 ^ a * (32 * m) := by
    have := Nat.mod_add_div F (32 ^ a)
    rw [hm] at this; omega
  have hF' : F + v * 32 ^ a = low + 32 ^ a * (32 * m + v) := by rw [hF]; ring
  have key : ∀ Z j, (low + 32 ^ a * Z) / 32 ^ j % 32 =
      if j < a then low / 32 ^ j % 32
      else if j = a then Z % 32 else Z / 32 ^ (j - a) % 32 := by
    intro Z j
    rcases lt_trichotomy j a with hj | hj | hj
    · rw [if_pos hj]
      obtain ⟨d, rfl⟩ : ∃ d, a = j + d + 1 := ⟨a - j - 1, by omega⟩
      have : 32 ^ (j + d + 1) * Z = 32 ^ j * (32 * (32 ^ d * Z)) := by ring
      rw [this, Nat.add_mul_div_left _ _ (by positivity)]
      omega
    · subst hj
      rw [if_neg (lt_irrefl _), if_pos rfl, Nat.add_mul_div_left _ _ hP,
        Nat.div_eq_of_lt hlowlt]
      simp
    · rw [if_neg (by omega), if_neg (by omega)]
      obtain ⟨d, rfl⟩ : ∃ d, j = a + d + 1 := ⟨j - a - 1, by omega⟩
      have e1 : 32 ^ (a + d + 1) = 32 ^ a * 32 ^ (d + 1) := by ring
      have e2 : a + d + 1 - a = d + 1 := by omega
      rw [e1, e2, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hP,
        Nat.div_eq_of_lt hlowlt]
      simp
  have hFi : F / 32 ^ i % 32 = if i < a then low / 32 ^ i % 32
      else if i = a then (32 * m) % 32 else (32 * m) / 32 ^ (i - a) % 32 := by
    conv_lhs => rw [hF]
    exact key _ _
  rw [hF', key, hFi]
  rcases lt_trichotomy i a with hj | hj | hj
  · have h2 : i ≠ a := hj.ne
    simp only [hj, h2, if_true, if_false]
  · subst hj
    simp only [lt_irrefl, if_false, if_true]
    omega
  · have h1 : ¬ i < a := by omega
    have h2 : i ≠ a := by omega
    simp only [h1, h2, if_false]
    obtain ⟨d, hd⟩ : ∃ d, i - a = d + 1 := ⟨i - a - 1, by omega⟩
    rw [hd, pow_succ', ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
    have e1 : (32 * m + v) / 32 = 32 * m / 32 := by omega
    rw [e1]

/-- `F` and `G` are partial tables (digit `0` = undefined, `v + 1` = value `v`; coded as natural
numbers) that are contained in the graph of `φ` and of its inverse. -/
def Inv (F G : ℕ) (φ : Equiv.Perm (Fin 23)) : Prop :=
  (∀ y : Fin 23, cget F y = 0 ∨ cget F y = (φ y).val + 1) ∧
  (∀ z : Fin 23, cget G z = 0 ∨ cget G z = (φ.symm z).val + 1)

theorem inv_init (φ : Equiv.Perm (Fin 23)) : Inv 0 0 φ :=
  ⟨fun _ => Or.inl (cget_zero _), fun _ => Or.inl (cget_zero _)⟩

/-- Insert the pair `(a, b)` into the partial tables, failing on a conflict. -/
def ins (F G a b : ℕ) : Option (ℕ × ℕ) :=
  strict (cget F a) (fun fa => strict (cget G b) (fun ga =>
    if ((Nat.beq fa 0 || Nat.beq fa (Nat.succ b)) && (Nat.beq ga 0 || Nat.beq ga (Nat.succ a))) = true
    then some (if Nat.beq fa 0 = true then Nat.add F (Nat.mul (Nat.succ b) (pw a)) else F,
               if Nat.beq ga 0 = true then Nat.add G (Nat.mul (Nat.succ a) (pw b)) else G)
    else none))

/-- Insert the pairs `(r^m st, s^m x)` for `m = 0, …, cycle length`. -/
def insOrb (r s st : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → Option (ℕ × ℕ)
  | 0, _, _, F, G => some (F, G)
  | n + 1, a, b, F, G =>
    strict (cget r a) (fun a' => strict (cget s b) (fun b' =>
      match ins F G a b with
      | none => none
      | some (F', G') =>
        if Nat.beq a' st = true then ins F' G' st b' else insOrb r s st n a' b' F' G'))

theorem ins_sound {φ : Equiv.Perm (Fin 23)} {F G : ℕ} (h : Inv F G φ) (y : Fin 23) :
    ∃ F' G', ins F G y.val (φ y).val = some (F', G') ∧ Inv F' G' φ := by
  obtain ⟨hFi, hGi⟩ := h
  have h1 := hFi y
  have h2 := hGi (φ y)
  rw [Equiv.symm_apply_apply] at h2
  have hc : ((Nat.beq (cget F y.val) 0 || Nat.beq (cget F y.val) ((φ y).val + 1)) &&
      (Nat.beq (cget G (φ y).val) 0 || Nat.beq (cget G (φ y).val) (y.val + 1))) = true := by
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h1, h2]
  have hy23 : (φ y).val + 1 < 32 := by have := (φ y).2; omega
  have hz23 : y.val + 1 < 32 := by have := y.2; omega
  refine ⟨if Nat.beq (cget F y.val) 0 = true then F + ((φ y).val + 1) * pw y.val else F,
    if Nat.beq (cget G (φ y).val) 0 = true then G + (y.val + 1) * pw (φ y).val else G, ?_, ?_, ?_⟩
  · simp only [ins, strict_eq]
    rw [if_pos hc]
    rfl
  · intro y'
    by_cases hF0 : cget F y.val = 0
    · simp only [Nat.beq_refl, hF0, if_true]
      rw [pw_eq, cget_add F y.val _ y'.val hF0 hy23]
      by_cases hyy : y'.val = y.val
      · have : y' = y := Fin.ext hyy
        subst this; simp
      · simp only [hyy, if_false]; exact hFi y'
    · have hb : Nat.beq (cget F y.val) 0 = false := Bool.eq_false_iff.mpr
        (fun hh => hF0 (Nat.eq_of_beq_eq_true hh))
      simp only [hb, Bool.false_eq_true, if_false]
      exact hFi y'
  · intro z
    by_cases hG0 : cget G (φ y).val = 0
    · simp only [hG0, Nat.beq_refl, if_true]
      rw [pw_eq, cget_add G (φ y).val _ z.val hG0 hz23]
      by_cases hzz : z.val = (φ y).val
      · have : z = φ y := Fin.ext hzz
        subst this; simp
      · simp only [hzz, if_false]; exact hGi z
    · have hb : Nat.beq (cget G (φ y).val) 0 = false := Bool.eq_false_iff.mpr
        (fun hh => hG0 (Nat.eq_of_beq_eq_true hh))
      simp only [hb, Bool.false_eq_true, if_false]
      exact hGi z

theorem insOrb_sound {k rP sP : Equiv.Perm (Fin 23)} (h : k * rP = sP * k) (st : ℕ) :
    ∀ (n : ℕ) (y : Fin 23) (F G : ℕ), Inv F G k →
      ∃ F' G', insOrb (ctab rP) (ctab sP) st n y.val (k y).val F G = some (F', G') ∧
        Inv F' G' k := by
  intro n
  induction n with
  | zero => intro y F G hI; exact ⟨F, G, rfl, hI⟩
  | succ n ih =>
    intro y F G hI
    obtain ⟨F1, G1, hins, hI1⟩ := ins_sound hI y
    have hk : k (rP y) = sP (k y) := by
      have := congrArg (fun f => f y) h
      simpa using this
    have e1 : cget (ctab rP) y.val = (rP y).val := by
      have := cget_ctab rP y.2; rwa [fo_val'] at this
    have e2 : cget (ctab sP) (k y).val = (k (rP y)).val := by
      rw [hk]; have := cget_ctab sP (k y).2; rwa [fo_val'] at this
    simp only [insOrb, strict_eq, e1, e2, hins]
    by_cases hc : (rP y).val = st
    · subst hc
      simp only [Nat.beq_refl, if_true]
      exact ins_sound hI1 (rP y)
    · have hc' : Nat.beq (rP y).val st = false :=
        Bool.eq_false_iff.mpr (fun hh => hc (Nat.eq_of_beq_eq_true hh))
      simp only [hc', Bool.false_eq_true, if_false]
      exact ih (rP y) F1 G1 hI1

/-- `U` commutes with `r` and `s` on the first `n` points: `U (r y) = s (U y)`. -/
def commOk (U : ℕ → ℕ) (r s : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => Nat.beq (U (cget r n)) (cget s (U n)) && commOk U r s n

/-- Upper bound for the number of `k' ∈ Kls ls` with `(U k') r = s (U k')`, by a pruned search
(permutations coded by natural numbers; `U` is given as a function on points).  `F`, `G` record
the partial map forced by the images `U b` of the earlier base points `b`. -/
def cnt (get : ℕ → ℕ) (r s : ℕ) : List Lvl → ℕ → ℕ → (ℕ → ℕ) → ℕ
  | [], _, _, U => if commOk U r s 23 = true then 1 else 0
  | L :: Ls, F, G, U =>
    (L.all.map (fun e => strict (U e.x) (fun x =>
      match insOrb r s L.b 24 L.b x F G with
      | none => 0
      | some (F', G') =>
        strict (get e.k) (fun u => cnt get r s Ls F' G' (fun y => U (cget u y)))))).sum

/-- Top-level entry: forces `r` and `s` first. -/
def cntTop (get : ℕ → ℕ) (r s : ℕ) (ls : List Lvl) : ℕ :=
  strict r (fun r' => strict s (fun s' => cnt get r' s' ls 0 0 (fun y => y)))

/-- `U` is the function on points given by `Up`. -/
def UR (U : ℕ → ℕ) (Up : Equiv.Perm (Fin 23)) : Prop := ∀ y, y < 23 → U y = (Up (fo y)).val

theorem commOk_sound {U : ℕ → ℕ} {Up rP sP : Equiv.Perm (Fin 23)} (hU : UR U Up)
    (h : Up * rP = sP * Up) : ∀ n, n ≤ 23 → commOk U (ctab rP) (ctab sP) n = true := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hn' : n < 23 := hn
    simp only [commOk, Bool.and_eq_true]
    refine ⟨?_, ih (by omega)⟩
    have e1 : cget (ctab rP) n = (rP (fo n)).val := cget_ctab rP hn'
    have e2 : cget (ctab sP) (U n) = (sP (Up (fo n))).val := by
      rw [hU n hn']
      have := cget_ctab sP (i := (Up (fo n)).val) (Up (fo n)).2
      rwa [fo_val'] at this
    rw [Nat.beq_eq, e1, e2, hU _ (rP (fo n)).2, fo_val']
    have := congrArg (fun f => f (fo n)) h
    simp only [Equiv.Perm.coe_mul, Function.comp] at this
    rw [this]

section Sound

variable {prog : List (ℕ × ℕ × ℕ)} {get : ℕ → Tab} {getC : ℕ → ℕ} {N : ℕ}

theorem kls_fix (hget : ∀ k < N, tab (P prog k) = get k) :
    ∀ (ls : List Lvl) (pv : List ℕ), (∀ p ∈ pv, p < 23) → chk get N pv ls = true →
      ∀ g ∈ Kls prog ls, ∀ p ∈ pv, g (fo p) = fo p := by
  intro ls pv hpv hchk g hg p hp
  cases ls with
  | nil => simp only [Kls, Subgroup.mem_bot] at hg; subst hg; rfl
  | cons L Ls =>
    simp only [chk, Bool.and_eq_true] at hchk
    have F := lvl_facts hget hpv hchk.1
    change g ∈ Subgroup.closure (Ggen prog L) at hg
    clear hchk
    induction hg using Subgroup.closure_induction with
    | mem x hx => obtain ⟨s, hs, rfl⟩ := hx; exact F.hgfix s hs p hp
    | one => rfl
    | mul x y _ _ hx hy => simp only [Equiv.Perm.coe_mul, Function.comp]; rw [hy, hx]
    | inv x _ hx => rw [Equiv.Perm.inv_eq_iff_eq]; exact hx.symm

theorem step_factor (hget : ∀ k < N, tab (P prog k) = get k) {prev : List ℕ}
    (hprev : ∀ p ∈ prev, p < 23) {L : Lvl} {Ls : List Lvl}
    (hl : lvlOk get N prev L Ls = true) (hrest : chk get N (prev ++ [L.b]) Ls = true)
    (h : Equiv.Perm (Fin 23)) (hh : h ∈ Kls prog (L :: Ls)) :
    ∃ e ∈ L.all, P prog e.ki * h ∈ Kls prog Ls ∧ h = P prog e.k * (P prog e.ki * h) := by
  have F := lvl_facts hget hprev hl
  obtain ⟨h1, h2, h3, h4⟩ := lvl_setup hget hprev hl hrest
  obtain ⟨horb, hfac⟩ := level_factor (Ggen prog L) (Kls prog Ls) (fo L.b) (lvlOrb L)
    (lvlT prog L) h1 h2 h4
  have hh' : h ∈ Subgroup.closure (Ggen prog L) := hh
  obtain ⟨e, he, hex⟩ := mem_lvlOrb.mp (horb h hh' (fo L.b) h1)
  have hfh := hfac h hh'
  rw [← hex, lvlT_eq F he] at hfh
  have hinv' : (P prog e.k)⁻¹ = P prog e.ki :=
    (eq_inv_of_mul_eq_one_left (F.hinv e he)).symm
  rw [hinv'] at hfh
  refine ⟨e, he, hfh, ?_⟩
  rw [← mul_assoc, mul_eq_one_comm.mp (F.hinv e he), one_mul]

theorem ncard_le_sum_list {α β : Type*} [Finite β] (es : List α) (G : α → Set β) (F : Set β)
    (hF : F ⊆ ⋃ e ∈ es, G e) : F.ncard ≤ (es.map (fun e => (G e).ncard)).sum := by
  induction es generalizing F with
  | nil => simp at hF; subst hF; simp
  | cons e es ih =>
    simp only [List.mem_cons, Set.iUnion_iUnion_eq_or_left, List.map_cons, List.sum_cons] at hF ⊢
    calc F.ncard ≤ (G e ∪ ⋃ x ∈ es, G x).ncard := Set.ncard_le_ncard hF (Set.toFinite _)
      _ ≤ (G e).ncard + (⋃ x ∈ es, G x).ncard := Set.ncard_union_le _ _
      _ ≤ _ := Nat.add_le_add_left (ih _ subset_rfl) _

theorem cnt_sound (hget : ∀ k < N, tab (P prog k) = get k)
    (hgetC : ∀ k < N, ctab (P prog k) = getC k) :
    ∀ (ls : List Lvl) (prev : List ℕ), (∀ p ∈ prev, p < 23) → chk get N prev ls = true →
      ∀ (rP sP Up : Equiv.Perm (Fin 23)) (F G : ℕ) (U : ℕ → ℕ), UR U Up →
        (∀ k' ∈ Kls prog ls, (Up * k') * rP = sP * (Up * k') → Inv F G (Up * k')) →
        {k' | k' ∈ Kls prog ls ∧ (Up * k') * rP = sP * (Up * k')}.ncard ≤
          cnt getC (ctab rP) (ctab sP) ls F G U := by
  intro ls
  induction ls with
  | nil =>
    intro prev _ _ rP sP Up F G U hU _
    simp only [cnt, Kls, Subgroup.mem_bot]
    by_cases hc : Up * rP = sP * Up
    · have hb : commOk U (ctab rP) (ctab sP) 23 = true := commOk_sound hU hc 23 le_rfl
      rw [if_pos hb]
      calc _ ≤ ({1} : Set (Equiv.Perm (Fin 23))).ncard :=
            Set.ncard_le_ncard (fun k hk => hk.1) (Set.toFinite _)
        _ ≤ _ := by simp
    · have : {k' : Equiv.Perm (Fin 23) | k' = 1 ∧ (Up * k') * rP = sP * (Up * k')} = ∅ := by
        ext k
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
        rintro rfl; simpa using hc
      rw [this]; simp
  | cons L Ls ih =>
    intro prev hprev hchk rP sP Up F G U hU hold
    simp only [chk, Bool.and_eq_true] at hchk
    obtain ⟨hl, hrest⟩ := hchk
    have F0 := lvl_facts hget hprev hl
    have hprev' := prev_succ hprev F0.hb
    -- the partial tables after inserting the base point `L.b` with image `U (e.x)`
    have hins : ∀ e ∈ L.all, ∀ k'' ∈ Kls prog Ls,
        ((Up * P prog e.k) * k'') * rP = sP * ((Up * P prog e.k) * k'') →
        Inv F G ((Up * P prog e.k) * k'') →
        ∃ F' G', insOrb (ctab rP) (ctab sP) L.b 24 L.b (U e.x) F G = some (F', G') ∧
          Inv F' G' ((Up * P prog e.k) * k'') := by
      intro e he k'' hk'' hc hI
      have hfixL : k'' (fo L.b) = fo L.b :=
        kls_fix hget Ls (prev ++ [L.b]) hprev' hrest _ hk'' L.b (by simp)
      have := insOrb_sound hc L.b 24 (fo L.b) F G hI
      have e1 : (fo L.b).val = L.b := fo_val F0.hb
      have e2 : (((Up * P prog e.k) * k'') (fo L.b)).val = U e.x := by
        have e3 : ((Up * P prog e.k) * k'') (fo L.b) = Up (P prog e.k (fo L.b)) := by
          simp only [Equiv.Perm.coe_mul, Function.comp, hfixL]
        rw [e3, F0.hmap e he, hU e.x (F0.hx e he)]
      rw [e1, e2] at this
      exact this
    have hmemL : ∀ e ∈ L.all, ∀ k'' ∈ Kls prog Ls, P prog e.k * k'' ∈ Kls prog (L :: Ls) :=
      fun e he k'' hk'' => mul_mem (F0.hmem e he) (F0.hnest hk'')
    let G' : Ent → Set (Equiv.Perm (Fin 23)) := fun e =>
      match insOrb (ctab rP) (ctab sP) L.b 24 L.b (U e.x) F G with
      | none => ∅
      | some _ => (fun k' => P prog e.k * k') ''
          {k' | k' ∈ Kls prog Ls ∧ ((Up * P prog e.k) * k') * rP = sP * ((Up * P prog e.k) * k')}
    have hsub : {k | k ∈ Kls prog (L :: Ls) ∧ (Up * k) * rP = sP * (Up * k)} ⊆
        ⋃ e ∈ L.all, G' e := by
      rintro k ⟨hk, hkc⟩
      obtain ⟨e, he, hk', hkeq⟩ := step_factor hget hprev hl hrest k hk
      refine Set.mem_biUnion he ?_
      have hUk : Up * k = (Up * P prog e.k) * (P prog e.ki * k) := by
        rw [mul_assoc, ← hkeq]
      have hc'' : ((Up * P prog e.k) * (P prog e.ki * k)) * rP =
          sP * ((Up * P prog e.k) * (P prog e.ki * k)) := by
        rw [← hUk]; exact hkc
      have hI : Inv F G ((Up * P prog e.k) * (P prog e.ki * k)) := by
        rw [← hUk]; exact hold k hk hkc
      obtain ⟨F', G'', hres, -⟩ := hins e he _ hk' hc'' hI
      simp only [G', hres]
      exact ⟨P prog e.ki * k, ⟨hk', hc''⟩, hkeq.symm⟩
    refine (ncard_le_sum_list L.all G' _ hsub).trans ?_
    simp only [cnt, strict_eq]
    apply List.sum_le_sum
    intro e he
    cases hres : insOrb (ctab rP) (ctab sP) L.b 24 L.b (U e.x) F G with
    | none => simp [G', hres]
    | some FG =>
      obtain ⟨F', G''⟩ := FG
      simp only [G', hres]
      calc _ ≤ ({k' | k' ∈ Kls prog Ls ∧
            ((Up * P prog e.k) * k') * rP = sP * ((Up * P prog e.k) * k')}).ncard :=
            Set.ncard_image_le (Set.toFinite _)
        _ ≤ _ := by
          have hUR : UR (fun y => U (cget (getC e.k) y)) (Up * P prog e.k) := by
            intro y hy
            have h1 : cget (getC e.k) y = (P prog e.k (fo y)).val := by
              rw [← hgetC _ (F0.hkN e he).1]; exact cget_ctab _ hy
            simp only [h1]
            rw [hU _ (P prog e.k (fo y)).2, fo_val']
            rfl
          refine ih (prev ++ [L.b]) hprev' hrest rP sP (Up * P prog e.k) F' G''
            (fun y => U (cget (getC e.k) y)) hUR ?_
          intro k'' hk'' hc
          have hI0 : Inv F G ((Up * P prog e.k) * k'') := by
            have := hold (P prog e.k * k'') (hmemL e he k'' hk'') (by rwa [← mul_assoc])
            rwa [← mul_assoc] at this
          obtain ⟨F2, G2, hres2, hI2⟩ := hins e he k'' hk'' hc hI0
          rw [hres] at hres2
          obtain ⟨rfl, rfl⟩ := Option.some.inj hres2 |> Prod.mk.inj
          exact hI2

end Sound

end M23Cert

set_option maxRecDepth 100000

namespace M23Cert

open MathieuM23

/-- Representatives of the 17 conjugacy classes, as products of transversal entries
(indices into the straight-line program `fullProg`). -/
def repIdx : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0], [232, 235, 310, 354, 363, 341], [0, 347, 311, 282, 323, 0],
   [2, 348, 351, 358, 361, 341], [304, 346, 349, 316, 274, 0], [2, 238, 0, 0, 361, 341],
   [304, 345, 215, 320, 364, 366], [232, 238, 280, 316, 362, 366], [0, 237, 349, 318, 323, 366],
   [2, 348, 245, 0, 303, 366], [207, 209, 309, 282, 303, 341], [276, 185, 309, 316, 274, 0],
   [342, 213, 352, 318, 0, 366], [0, 211, 243, 229, 359, 0], [2, 348, 241, 282, 322, 341],
   [275, 185, 313, 320, 303, 341], [230, 238, 309, 355, 365, 0]]

/-- Upper bounds for the centralizer orders. -/
def centB : List ℕ := [10200960, 2688, 180, 32, 15, 12, 14, 8, 11, 14, 15, 23, 14, 11, 14, 15, 23]

def repPerm (i : ℕ) : Equiv.Perm (Fin 23) := ((repIdx.getD i []).map (P fullProg)).prod

theorem fullGet : ∀ k < 4 + fullProg.length, tab (P fullProg k) = Tget fullTabs k := by
  have h := fullOk
  simp only [topChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨hslp, hbase⟩, hchk⟩, htop⟩ := h
  exact slp_tab _ fullProg (fun k hk => (hbase k hk).symm) hslp

theorem fullChk : chk (Tget fullTabs) (4 + fullProg.length) [] fullLvls = true := by
  have h := fullOk
  simp only [topChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h.1.2

theorem fullKls : Kls fullProg fullLvls = M23 := by
  have h := fullOk
  simp only [topChk, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨⟨⟨hslp, hbase⟩, hchk⟩, htop⟩ := h
  cases hls : fullLvls with
  | nil => rw [hls] at htop; simp [topGens] at htop
  | cons L Ls =>
    rw [hls] at htop
    simp only [topGens, Bool.and_eq_true, List.contains_iff_mem] at htop
    exact Kls_top fullProg (Tget fullTabs) fullGet hbase L Ls htop.1 htop.2

/-- The codes of the tables of `fullProg`, as a tree of branching 8. -/
def fullTree : List (List (List ℕ)) :=
  [[[29435622565346244453937714881988640, 1993002591082914594162387435626186, 23548416599299366501131435658959169, 2897322088946815921951284934480907, 29435622565346244453937714881988640, 25357623804097502780965178126813482, 19005140924109921414306583781901334, 19005140924109921414306583781901334],
    [6637025706359898631286187361968486, 9184685212644434615046648884630859, 17452404655032788992141488046624233, 17452404655032788992141488046624233, 23548416599299366501131435658959169, 20310506028609197610040528879592846, 26475021866259959033960340516287759, 13814090039215768412795220274756854],
    [15719035360935880476652635617768934, 20310506028609197610040528879592846, 12187200965161868071642076177142383, 21017927985406688392685649841836200, 27792224348872905788356940733262183, 26475021866259959033960340516287759, 5701239217255922393259579904013571, 26475021866259959033960340516287759],
    [21017927985406688392685649841836200, 27839749018549664091963712536060269, 22446782187981367507068313456906675, 7857557518792918899668078171540981, 14490655685228214146336499988677300, 7106498217936820676958782656487795, 25568847285009853601916416701974819, 11056534246885689838571145408199884],
    [2897322088946815921951284934480907, 11056534246885689838571145408199884, 20310506028609197610040528879592846, 12212882010335098787369434621749713, 25984400094555818748299522399999659, 5615973256879147448901594851644971, 12212882010335098787369434621749713, 8003960369318007870300379041738864],
    [25272187731230747322815921302649001, 1678821416906010464264703841096262, 262542491092132987172541616008226, 22490152145888449466933565247736470, 189376648998812875847933942336577, 189376648998812875847933942336577, 13570650444274406543744932954527305, 757238810439775956775967910020553],
    [15180371467378470520930986225013290, 24068492247673654638818428581952788, 10514500846181972107329032433532982, 9155116833537318204072036424633777, 2130937304801620934879515472743943, 26268351076898528320714094333761194, 22490152145888449466933565247736470, 20014226037253222770264585664021700],
    [4140346691225803112548154159342287, 20384243951542358694197017215847776, 7829349730673839542910459267627311, 488801491556775945050079755610339, 13129143459670905893064478569247443, 488801491556775945050079755610339, 2800372645938348881368060818540949, 5256092104380188955541394800268815]],
    [[27991642254482648104785059010128905, 262542491092132987172541616008226, 27684879050508077368182731676062248, 13330798438908020461938474099478220, 27997427044637145258821186393312576, 15664779948146480400490643784347299, 6661562649847624382170812812407104, 15618306606029549678747350382841092],
    [19072186484849240362026683044400769, 14505255944102695601531301916255466, 6661562649847624382170812812407104, 1846281593179462554517864437156327, 1917067255260876666460404795425927, 23815953635248656492352279141492359, 20010209692116900845008642278707427, 29308649589649156896160473641174308],
    [17778262464652643349667109451110723, 7962635224549825325682815090795104, 4202841489069509474376063303958025, 7962635224549825325682815090795104, 23500347175755758090441532069087942, 6776016425611361719837955110609100, 3464498187725442338169355159410986, 23624277608526873374217789194768909],
    [24057645517443841595093076197521740, 29176945752736493452186584787334256, 13647813704877900989224149481334338, 14526748711446359922977408765143342, 6776016425611361719837955110609100, 4275803580823796205877437269379784, 6509943340908337159485192473795217, 10514500846181972107329032433532982],
    [5973858364882867056948754310572724, 9467510501118291045018980194566853, 5973858364882867056948754310572724, 21219266846759394692124581574622382, 3168028958767196758880111432056844, 9149132475813340730107877717022146, 2053954773079015886009426831818886, 12108837945635651264386724744692071],
    [8686622019866044726074771559954450, 23815953635248656492352279141492359, 1847175445368944535002164603062803, 14902642372237938547562612759233190, 7248520532311858182683743250567783, 4754063889384547429467705631562099, 7164370011165051385857505410590759, 13147526352795752836045953099773547],
    [19811090435942115327635248547256641, 17672675070581670568966123630500352, 10425995517337256279887626812215850, 25157330151767509767270730649937969, 4667977315443453649035739062117044, 25157330151767509767270730649937969, 7164370011165051385857505410590759, 13229299949213359487925882414728210],
    [19528417786730199857003302272587042, 26415902460269968957810525889511729, 13471996704514609820562057780117698, 23665314254151515012048497003316548, 23378663106462403810237061692853806, 28571948440204490461127825417127984, 15618306606029549678747350382841092, 26531993141691015375285708739726671]],
    [[15963929051389708677684530519495104, 29022864981128717898219403070708168, 13331347966027662785792857358079399, 5495899306130349924294340118760513, 7164194315322711978555381225991407, 13226990253919640237272890802187392, 23576416384987221069939675609748712, 3169740650226770683348067760591143],
    [27840324525368880258644803772225891, 26490692847306057502985385749595492, 21240165993678543916790975007709781, 21518693823187386419493925349806189, 29008483405541543589836241941043681, 27752992250905785019333593923005665, 18997858802167158744929022720187968, 11770712986901490486788398002832047],
    [8222507920745818738053286547703172, 2600745662617235588406370319637829, 29025883668286487123412654679995923, 19659066647042393074213434875392432, 19757731216852823652483265672567244, 13373965231684980771988011473254028, 10833606008950227322579766079438959, 16964391321990764106247131857541650],
    [21240165993678543916790975007709781, 15686713194949776911119735577854088, 20818177095891952281645512321701571, 6672519114279774657943478436701582, 17605513409687127066708486942046741, 26006287995482233141830198813562562, 2052808565045640447557242420478632, 4148035575690745612298038413789782],
    [5581672851441770511568350501520468, 1607999093840771448462540425804297, 13837008452373526757543716200131649, 8570610979931176234719647289629031, 13570650444274406543744932954527305, 16230537278582521420246621524535346, 16245114757587500350018937830802126, 21105240612975030052747606416294258],
    [4594151528077788080434970740473205, 29024725178258313365534161249700917, 1894246456407893967284547138224818, 24058800679405363598697190369024196, 15666287510715484949289823305438314, 21673754170619787839920090062532138, 3260635764683562646849939453695435, 3917542302559888555257159963880788],
    [5598746094884519563157715437061541, 18361370964340037891122317034236617, 3187716890810507777977531212402803, 14449536211614309696208383096857103, 493395181186072671601735949289773, 2976788591322107288613171571070574, 18400282189168813894316850668379428, 4121806069410450400008831679209510],
    [1831050949019058833102872482489442, 20267248655063390153905342993641152, 28657037591905623532150405623728625, 22475926013524952188694326781955365, 24273777624815821544689368123493646, 19930142686354076969953052152308994, 10451389696905663106860252301701600, 21687568573796476728883190737178880]],
    [[9778278130244851736893056067677450, 29347630699555470918752987148601360, 2600745662617235588406370319637829, 26269693569247909015581603751384401, 24922173338901571457549505763166641, 28926701503787624226441305997883973, 17672478730322550090582843423040007, 9184685212644434615046648884630859],
    [1973305292605561554537371257980512, 13159579533227894841314593686639051, 13029629148576644653004374281438688, 25013919742608442424607226759162528, 6055698760785272636432193821194272, 1971999683743923563882573687305350, 8134127175252357077302522757567826, 29411574413359663789215618450984397],
    [1383385206722881159148405572998772, 15710056353266374037042547967580288, 22119413203613483973050607232949632, 5483471907152305588999454206311872, 9555602553503385576495385045799520, 20833337655547238260263570865599712, 25538532269313278756529543577280544, 4759657173625854294317850959168544],
    [9661459266350782188587774014147945, 8519959499060270799764868669494915, 4651254607665819277554726227812046, 20333913365778883932261479963015776, 10567949086050302454864292924956035, 25245397458040785887852494399613576, 28696521095868283675450406791158248, 5768507274752429181012632828988064],
    [15138453395939177884432970719805472, 3252022034215069714898342106538592, 17541813551953208808450603839007328, 8459589977422547927223565302800416, 4759657173625854294317850959168544, 23708257157868514132592263641597984, 2080616064442329435435540484102735, 23451832600766421419052596736705971],
    [28812455562749268701882274141359555, 13527477342104632902557329980534376, 17541794897254192643883069283176000, 15635940451731881362808043491339680, 9984080592589156877362525765981728, 6097780969385069642864852685893728, 9137633236833160501774204516456608, 7844822433971405651874741206338176],
    [12014376057102028539791049515700256, 21115387352102329983176750619242528, 24074799472428398258972836283927584, 7002835620417282689947626189268000, 3306476513256964730767715098500128, 13645832367008779049903525620026400, 3394899703695124648751316452481056, 22560005753315961594005678508476448],
    [25121765677094564928853028381263904, 20897921538537424095616517590583328, 2117637000589703745543420556029063, 28696521095868283675450406791158248, 13848341866045382009838666328441864, 21559154499477720114645142751980780, 7324060711218336435665775050738090, 5252607348890358647663748916543784]],
    [[14462725490510869586566408730818723, 11260587806744389702353899045032448, 14408757536883754044462251261773856, 20897921538537424095616517590583328, 21384831657753605664594378298334922, 9617725228212249755890816294004044, 9357175892292229123373438510146176, 19737898099126359750944643399330464],
    [2856506102017953999881965602816672, 4463717592716158554601317967905440, 7401031453391009478441223480449056, 10556285659719374942634984879014944, 6672293388465582202347776855463968, 26546709749801928622227327295281184, 9917237525932059165906816299534368, 25121765677094564928853028381263904],
    [22560005753315961594005678508476448, 23708257157868514132592263641597984, 8373441610577957626865481265809440, 13843123522720677275271432073951627, 7897000847258528436804139215270504, 10793496034463740979136915191643495, 25288415150325015239568398019110080, 22124552642769745346951512720820832],
    [5774280327771975547530288506917920, 21469061870166002558154598718523424, 16293757481852305205111482387728416, 11120087952469986671746920111179808, 15060576011322167557777587317114912, 19850636167614508610047181871188000, 7870987858921551846388790379695762, 8133388975206205074503913131184802],
    [26513395274065030117955645576578631, 29212416356654279398289992290063562, 28926701503787624226441305997883973, 21582202373483265730328333222254720, 27428845693603423098429775950655520, 16293757481852305205111482387728416, 8373441610577957626865481265809440, 7325806176530193934836032445273290],
    [15842285291230834305839481092090080, 22403634347008647825748932670537376, 8118812361236833727395637799271072, 23502903869421044955754957988600864, 14858931988588805061681549274122272, 9917237525932059165906816299534368, 25126943430229708976300950635546656, 29184382394771978601598052101883936],
    [1765293185002058848020717956812484, 5530965690172768012738447985491349, 26020688984588614853097768949782816, 7936815205446589006278356826839552, 18224630822284763252777655050914464, 17498869326651257385646350759841824, 28093011158035146873162447085223968, 21100168424543975781496195521362976],
    [4508654709299816760893743241374752, 13806106578499289909379877951641632, 26755325820766993982283889572525088, 10977108419659453403559512833185824, 16398738452498936838519270382471200, 14543375690933047643478067710134304, 23914636636752897739192574161815584, 8381870712860134352223933289498656]],
    [[7043945948258582586621468635301920, 23699092711949447406008935653672992, 8586612440587390158688693900118048, 28933142224899669675469064435238944, 16273294260485678618122198460762144, 16413127046491843911491635294341152, 23912263541959550958413402859472928, 12319822569409144906951666366028867],
    [23991139361834815131529944574243075, 29148442669525395786860596663694867, 5642875489896478409739062240322080, 10923742897659435396793324137432672, 27363793109590613976190866338203232, 26584265100545322183218455763924000, 17048014748129891676530412577142880, 23502903869421044955754957988600864],
    [9800579971736178492832022745384992, 28933142224899669675469064435238944, 4140763639388527668487363230843936, 6924764865795840677690815888376864, 29183143112828921619426670913390624, 22359188148235788299642593781844000, 1757584215634563108047577877723696, 21635888215766403288063208107449612],
    [26334228124846837823005346336561696, 16923816004257182887523538084056704, 24800366681761382611874981428675904, 26181664755502396259232036899077184, 19047765061368085065372752650983776, 11977653053145902784872210253788192, 16110874196597457309168550354724896, 13860630469655957584885946211769376],
    [23914402452225805291685250707493920, 10938729472449595849484464029927456, 15062909177711087310785793653901344, 15871345972466705679027133935192096, 22896475174786891510526944762562592, 28939893229344203939075929784256544, 23590149777619162763576784275048480, 20346608444246320761326360133208096],
    [10930177665404468784645474428749856, 25247063685272879722682944954927136, 22571092309091080698281190446172192, 24918495875806398310792903851608096, 17632530210348794815662275719956512, 11140969174476761400187970167867424, 14866230914480321566569876288538656, 14993307407054453979308311513875146],
    [1673401759578373511899746874662602, 11160938240768805663316580482685483, 10810965084773697393435491703600416, 9439303223709970794708858821584928, 28943449517974062157464458378151968, 14866230914480321566569876288538656, 15013277560104610517748889839705802, 24760425103583241761890914593608011],
    [16436736613635572730684120673817931, 9090931850864134141992198140859723, 25527400915765638651798572549805387, 27892223089257883555655981614769479, 8118687539075830956979647770362410, 10923372555455292314503603074356426, 29434268145137299805802235157357194, 20160760418394317623634315039102666]],
    [[11089708622104287858807136959287755, 6661121971495999933928947700909664, 2786739257639311056533250829108832, 27893716995362538688210411509168640, 12175826974985792635843419124738720, 24975778960179165631925292179335840, 22555393287942376358603182065265312, 25076044241467509177200383233211776],
    [3412968735802285078015354968121952, 17576850882147971336537202831827552, 25259384596289104230056858816578912, 3457542128942825547095403816994400, 27931657558039921840484102757715392, 24719387913519102901150238981171872, 22854803555198881887676868499456032, 13070962540786795050849447422050336],
    [25538532269313278756529543577280544, 25329139696482030686183121494361120, 20257163878543714767313939092213792, 5339722335480405163197005952434208, 22986601264651586835586643935739936, 19737881302598643903102676027686944, 13113106900065486840040467640991776, 26818780461848113227206730112942112],
    [25089550360253068786830066001322016, 19893600711521405113047039850693664, 10857921580646930752461086063707168, 18835097543146574049892166892954656, 4678320505139404932754388601087008, 2737671445365169699738400889028640, 20958591387425424911968156122449952, 16401199574007633148947274327754784],
    [17090729210807332475519003997374496, 25235730982530628607636029614458912, 10595868735812675655751411273435168, 10609114741368805260692481005422624, 21200793224613545603327167198234656, 8246716425562012499353752682694688, 7044617494460789922132000712788000, 19844083956509647905629035218339872],
    [25256880239099873090529324727142432, 29174445766812146763965998752204832, 4309327005995942959117254493014048, 8256433940553515184761578939582496, 12559352553765177953225903985231904, 16413127046491843911491635294341152, 29184382394771978601598052101883936, 23912263541959550958413402859472928],
    [8586612440587390158688693900118048, 10930177665404468784645474428749856, 17100224550628986149346542520207392, 16273294260485678618122198460762144, 6826545688919527915135599934277664, 9790943522471481802752214624733216, 9921412583901147809757949742647328, 18969863101318355069284809711912992],
    [22359188148235788299642593781844000, 0, 0, 0, 0, 0, 0, 0]],
    [[0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0]]]

/-- The code of the `k`-th table. -/
def fullC (k : ℕ) : ℕ :=
  nthD 0 (nthD [] (nthD [] fullTree (k / 64)) (k / 8 % 8)) (k % 8)

theorem fullC_eq : ∀ k < 441, fullC k = encL (Tget fullTabs k) := by decide +kernel

theorem fullProg_length : fullProg.length = 437 := by decide +kernel

theorem fullGetC : ∀ k < 4 + fullProg.length, ctab (P fullProg k) = fullC k := by
  intro k hk
  have hk' : k < 441 := by rw [fullProg_length] at hk; omega
  rw [fullC_eq k hk']
  unfold ctab
  rw [fullGet k hk]

theorem cent_bound (rP sP : Equiv.Perm (Fin 23)) :
    {k | k ∈ M23 ∧ k * rP = sP * k}.ncard ≤
      cntTop fullC (ctab rP) (ctab sP) fullLvls := by
  have := cnt_sound fullGet fullGetC fullLvls [] (by simp) fullChk rP sP 1 _ _ (fun y => y) (fun y hy => by simp [Nat.mod_eq_of_lt hy]) (fun _ _ _ => inv_init _)
  rw [fullKls] at this
  simpa [cntTop, strict_eq, ctab, tab_one] using this

theorem ctab_listProd (l : List ℕ) (hl : ∀ k ∈ l, k < 4 + fullProg.length) :
    ctab ((l.map (P fullProg)).prod) = (l.map fullC).foldr tmulC (encL tid) := by
  induction l with
  | nil => simp [ctab, tab_one]
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, List.foldr_cons, ctab_mul]
    rw [fullGetC a (hl a (by simp)), ih (fun k hk => hl k (by simp [hk]))]

theorem repPerm_mem (i : ℕ) : repPerm i ∈ M23 := by
  unfold repPerm
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
  exact P_mem _ _

/-- The code of the `i`-th representative. -/
def repC (i : ℕ) : ℕ := ((repIdx.getD i []).map fullC).foldr tmulC (encL tid)

/-- Precomputed codes of the representatives (checked against `repC`). -/
def repCodes : List ℕ := [29435622565346244453937714881988640, 29312703784911004155238613436597315, 15155501594381821354833953503087680, 10894636817779802511622171828240385, 10773037850882612366204075077895172, 6832809404187156614967410336843841, 28942256553246469211824200366491140, 21526355563711589323412800633223299, 21269497785087757613159045909328992, 28094562770007678689776954747786241, 23501869977593134650091927154009261, 12252322928281208154781441931728072, 29258974306638206245631680986811472, 17657837092513580079886390749340096, 25582640500068652059371615098848257, 24844156992300725307958335906690379, 10487406499594525615834053108904591]

def rcode (i : ℕ) : ℕ := nthD 0 repCodes i

theorem rcode_eq : ∀ i < 17, rcode i = repC i := by decide +kernel

theorem repIdx_lt : ∀ l ∈ repIdx, ∀ k ∈ l, k < 4 + fullProg.length := by decide +kernel

theorem ctab_repPerm (i : ℕ) : ctab (repPerm i) = repC i := by
  unfold repPerm repC
  apply ctab_listProd
  intro k hk
  by_cases hi : i < repIdx.length
  · exact repIdx_lt _ (List.getD_eq_getElem _ _ hi ▸ List.getElem_mem hi) k hk
  · rw [List.getD_eq_default _ _ (by omega)] at hk; simp at hk


def cB (i : ℕ) : ℕ := centB.getD i 1

/-- All centralizer searches stay below the claimed bounds. -/
def centOk : Bool :=
  (List.range 17).all (fun i => Nat.beq i 0 || Nat.ble (cntTop fullC (rcode i) (rcode i) fullLvls) (cB i))

/-- No two representatives are conjugate. -/
def ncOk : Bool :=
  (List.range 17).all (fun i => (List.range 17).all (fun j =>
    Nat.beq i j ||
      (if Nat.beq i 0 then !(Nat.beq (rcode j) (encL tid))
       else Nat.beq j 0 || Nat.beq (cntTop fullC (rcode i) (rcode j) fullLvls) 0)))


theorem ctab_repPerm' (i : ℕ) (hi : i < 17) : ctab (repPerm i) = rcode i := by
  rw [ctab_repPerm, rcode_eq i hi]

end M23Cert

set_option maxRecDepth 100000

namespace M23Cert

open MathieuM23

theorem rcode_zero : rcode 0 = encL tid := by decide +kernel

theorem centOk_true : centOk = true := by decide +kernel

theorem ncOk_true : ncOk = true := by decide +kernel

/-- The `i`-th representative as an element of `M23`. -/
def rep (i : Fin 17) : M23 := ⟨repPerm i.val, repPerm_mem i.val⟩

theorem repPerm_zero : repPerm 0 = 1 := by
  apply ctab_inj
  rw [ctab_repPerm' 0 (by norm_num), rcode_zero]
  simp [ctab, tab_one]

theorem hcent_aux (i : Fin 17) (hi : i.val ≠ 0) :
    Nat.card (Subgroup.centralizer {rep i}) ≤ cB i.val := by
  have hc := centOk_true
  simp only [centOk, List.all_eq_true, List.mem_range, Bool.or_eq_true] at hc
  have h1 := hc i.val i.2
  rcases h1 with h1 | h1
  · exact absurd (Nat.eq_of_beq_eq_true h1) hi
  have h2 := Nat.le_of_ble_eq_true h1
  have h3 := cent_bound (repPerm i.val) (repPerm i.val)
  rw [ctab_repPerm' _ i.2] at h3
  have h4 : Nat.card (Subgroup.centralizer {rep i}) ≤
      {k | k ∈ M23 ∧ k * repPerm i.val = repPerm i.val * k}.ncard := by
    rw [← Nat.card_coe_set_eq]
    refine Nat.card_le_card_of_injective
      (fun x : (Subgroup.centralizer {rep i} : Subgroup M23) =>
        (⟨(x.1 : Equiv.Perm (Fin 23)), x.1.2, ?_⟩ :
          {k | k ∈ M23 ∧ k * repPerm i.val = repPerm i.val * k})) ?_
    · have := Subgroup.mem_centralizer_iff.mp x.2 (rep i) (by simp)
      have h5 := congrArg (fun z : M23 => (z : Equiv.Perm (Fin 23))) this
      exact h5.symm
    · intro x y hxy
      have := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext this)
  exact h4.trans (h3.trans h2)

theorem hcent (i : Fin 17) : Nat.card (Subgroup.centralizer {rep i}) ≤ cB i.val := by
  by_cases hi : i.val = 0
  · have : cB i.val = Nat.card M23 := by rw [hi, card_M23_certified]; rfl
    rw [this]
    exact Subgroup.card_le_card_group _
  · exact hcent_aux i hi

theorem hnc_aux (i j : Fin 17) (hi : i.val ≠ 0) (hj : j.val ≠ 0) (hij : i ≠ j) :
    ¬ IsConj (rep i) (rep j) := by
  rintro hconj
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hok := ncOk_true
  simp only [ncOk, List.all_eq_true, List.mem_range, Bool.or_eq_true] at hok
  have h1 := hok i.val i.2 j.val j.2
  rcases h1 with h1 | h1
  · exact hij' (Nat.eq_of_beq_eq_true h1)
  have hbi : Nat.beq i.val 0 = false := Bool.eq_false_iff.mpr (fun hh => hi (Nat.eq_of_beq_eq_true hh))
  rw [hbi] at h1
  simp only [Bool.false_eq_true, if_false, Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · exact hj (Nat.eq_of_beq_eq_true h1)
  have h3 := cent_bound (repPerm i.val) (repPerm j.val)
  rw [ctab_repPerm' _ i.2, ctab_repPerm' _ j.2] at h3
  have h4 : Nat.beq (cntTop fullC (rcode i.val) (rcode j.val) fullLvls) 0 = true := h1
  have h5 : cntTop fullC (rcode i.val) (rcode j.val) fullLvls = 0 := Nat.eq_of_beq_eq_true h4
  rw [h5] at h3
  have h6 : (c : Equiv.Perm (Fin 23)) ∈ {k | k ∈ M23 ∧ k * repPerm i.val = repPerm j.val * k} := by
    refine ⟨c.2, ?_⟩
    have := congrArg (fun z : M23 => (z : Equiv.Perm (Fin 23))) (mul_inv_eq_iff_eq_mul.mp hc)
    exact this
  have h7 : ({k | k ∈ M23 ∧ k * repPerm i.val = repPerm j.val * k} : Set (Equiv.Perm (Fin 23))).ncard = 0 :=
    Nat.le_zero.mp h3
  rw [Set.ncard_eq_zero (Set.toFinite _)] at h7
  rw [h7] at h6
  exact h6

theorem hnc0 (i j : Fin 17) (hi : i.val = 0) (hj : j.val ≠ 0) : ¬ IsConj (rep i) (rep j) := by
  intro hconj
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  have hri : rep i = 1 := Subtype.ext (by simp only [rep, hi]; exact repPerm_zero)
  rw [hri, isConj_one_right] at hconj
  have h1 : repPerm j.val = 1 := congrArg Subtype.val hconj
  have h2 : rcode j.val = encL tid := by
    rw [← ctab_repPerm' _ j.2, h1]; simp [ctab, tab_one]
  have hok := ncOk_true
  simp only [ncOk, List.all_eq_true, List.mem_range, Bool.or_eq_true] at hok
  have h3 := hok i.val i.2 j.val j.2
  have hbi : Nat.beq i.val 0 = true := by rw [hi]; rfl
  rcases h3 with h3 | h3
  · exact hij (Fin.ext (Nat.eq_of_beq_eq_true h3))
  · rw [hbi] at h3
    simp only [if_true, Bool.not_eq_true'] at h3
    rw [h2] at h3
    simp [Nat.beq_refl] at h3

theorem hnc (i j : Fin 17) (hij : i ≠ j) : ¬ IsConj (rep i) (rep j) := by
  by_cases hi : i.val = 0
  · by_cases hj : j.val = 0
    · exact absurd (Fin.ext (hi.trans hj.symm)) hij
    · exact hnc0 i j hi hj
  · by_cases hj : j.val = 0
    · intro hconj
      exact hnc0 j i hj hi hconj.symm
    · exact hnc_aux i j hi hj hij

theorem hsum : Nat.card M23 ≤ ∑ i : Fin 17, Nat.card M23 / cB i.val := by
  rw [card_M23_certified]
  decide +kernel

theorem hpos (i : Fin 17) : 0 < cB i.val := by
  revert i; decide +kernel

end M23Cert

open MathieuM23 M23Cert

theorem solution : Nat.card (ConjClasses M23) = 17 :=
  card_conjClasses_of_reps (G := M23) (n := 17) rep (fun i => cB i.val) hpos hcent hsum hnc

