-- Prove2me | solution 1 for MathieuM23.nielsenClass_ncard
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-05T12:45:46.683656+00:00
-- url     : https://prove2.me/submissions/e13392b8-de68-4a81-abf1-8ab8efbbff5f

import Definitions.Def_MathieuM23_Group
import Definitions.Def_MathieuM23_Nielsen

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

open MathieuM23

set_option maxRecDepth 100000

namespace NCls

open M23Cert

/-! ## Packed tables

A permutation of `Fin 23` is represented by the natural number `∑ᵢ p(i) · 23^i`; composition on these
numbers only uses (fast) natural number arithmetic. -/

def G1 : ℕ := 1586224160279461989606459393221

def G2 : ℕ := 16527614291122206802551906874825

def G2I : ℕ := 2115719123459975868805298216933

def G3I : ℕ := 13527732361771234282513882565521

def IDP : ℕ := 20837326537038308910317109288851

def n0 : ℕ := 3616

/-- The 165 `⟨g₂⟩`-orbits of the class of `g₁`, `23·i + j ↦ g₂^j r_i g₂^{-j}`, packed in base 23. -/
def EN : List (List ℕ) := [
  [6855343182708678492633300527465, 20706386068700864256680892489575, 856720294803734948226409442453, 9927668122594507171917192844693, 19957953916746004449040486360757, 311758890814377986359462828691, 20157524729753222408820070552727, 20337251764159577605989750983237, 19994693511946312611488035708555, 3579662167671282570576185699135, 19968914964207364763874601227981, 14403562140002319923958151772819, 5522170507053198603570043432651, 19962736316378685228062291310661, 20822133037679542660306646902229, 19024916968719817408557447130361, 1755383370781449335869019452001, 20427661603644022378965615385535, 20047148635386363527422898256239, 826947286344128911900024587281, 2028202273007761734907748126127, 16415848510471329568999669934571, 16298023694605537122723163168281, 6023150205869982454992009926045, 20079509125665217162206353222603, 4468929048377138849310479805649, 6277457274997437928800130269881, 3018084661948843733735045237857, 13809931142884570690560319377875, 20734472139734803493951861562015, 20582290405224691857753855794297, 20200633100073443621726197125787],
  [19025064271106721449485777605395, 15863901166904960949553662158941, 11126110015789060290280714946063, 7732199089290325780815276305043, 16259700542316837550771380579861, 20820597364594605057263081857141, 12633577280498679704045732248385, 10847589892394659339081241951757, 20466354652339197173106094553807, 20362324348853374712095941896303, 2144956372907263242218473645921, 16989716900840202130617760684259, 9469436817236846620108232771543, 13574076755308749321498278995397, 8784373426626392339918917525573, 20559374114934762628627479498983, 2655549178702520891042422327421, 17176777543048646640554008825473, 10938468275352346903846079866601, 14679272826771940910870655295955, 20390479304597020520843318123351, 20671680780048061645817451826365, 20488946541874660081708650562795, 2652938602368831230983306208299, 16653351461837893080570248897105, 193616668333928043545633441567, 10337380480428428678159792781359, 7522659240478040558407192438853, 20829074570029128481130370577853, 13564703340517564979102624132065, 12647811394464100413919695332173, 20280328528999634637275984462531],
  [20166085776304175597585383177523, 19934626735034224337767386523505, 4631621088528575092173032079731, 4298531964250664482531529637055, 18114007974144565551224803300093, 7800873250794777661730660945705, 19980101805025402219675490444747, 8110762449764866300470009277505, 12635774559533460170166356089053, 14556650412218696066956273666965, 12074362371170007313794808402643, 20359345327489765666008108649887, 20499017609412846073061554494421, 20612508883390586926974324395611, 1750241242446973124869794530471, 7930091196398516599442237766341, 6034694162120900325827265730715, 1179185061836991976897297685947, 12368368466613801185765313714369, 20833152093617796799977229801649, 9017935946388394265983522644997, 7199026370801394607020825402329, 20695790650482797728688654398103, 20638849413963400260827436276851, 6557193296572179645183210570797, 15261544599849791374433012354171, 16020626057053997360932152923127, 9034413955077383771330080919237, 16260268267988212758498838415577, 20586307044292305767058470182067, 1760013971603571921043913675393, 1765659162055053254339594239457],
  [1401089559394720224172139334437, 10968658300294072815965944217747, 20263344558019868146812946770707, 20145117616689464237448868472753, 20343071756242883272285305685007, 7187022561095878979247076888295, 7101223689219847471143768728501, 7100105759321091513964655424935, 745180153661674527060931961107, 5787181105307343423061850842845, 20826334765096651755542179325361, 14470684726323743681856696329561, 13565941815054080200146369297689, 19990197580031345565803055561575, 20007453224581377271381276651127, 18196161722063474900973040068305, 19934621106311476727457506374691, 2047612149742440638134435153023, 17205804824835359086158199443257, 12961105021502517507196196627813, 20748216131924011095119096016411, 10829449461018724884585375201525, 7214423508727675144531263967649, 8881251657695530805544807689273, 6389597693156157778580567829203, 20699222467539388693674473493719, 20431193535628715108784222036725, 20569605640163464579168420599279, 15379948772659070586992393073059, 8285312407216292269706780285753, 3666282327092631990302719674635, 11442265640636239944347840289427],
  [915776652444526343003790285017, 20805812720123718983027416347417, 15365474640545843984619521460465, 9910513665413966274875018238777, 20223734284647033532419841127435, 20521255335800886639987033133851, 1310903088127105642985658127285, 6680730996083891311826180884019, 1653399864572837149867661840475, 3587096974670666482221461853005, 13985429312297033096706162254545, 20608000781004776360164737035011, 15354878962502394948097766144437, 19025015814285904623368349020741, 18747863028697308157092190078109, 5994810580356329065748021089427, 20571820432467930495306657940555, 20798153278512918795887376814761, 20799569338957057620478977459451, 8110312840763562205457233946415, 11166744235796327863418338553509, 5047385492662844636280761767751, 12310813135207280262522366711859, 17479039063373634925103265823109, 20804478681013395841017885694145, 16296453487618617395967205178649, 8105153428346647091653520413589, 20610229513573943268588571664975, 20322927421266946123107386363063, 11940773292904433740623103768745, 8755593758953430455784786835107, 13416435726972507455585953738551],
  [14481559708715846918989617407905, 11186522315780876485806002991065, 20131350630841678442357579551555, 6280293926244558047131286656377, 15357617872204381678663980166297, 10066982302383713344629414639117, 4258307390776664867080831732307, 20503046122052778238718947299787, 20296362635207888466868037827981, 20305318091067939036654783187919, 11734833885895791931050581208407, 12942968636767285343063170219545, 12981864906840097520417190975719, 15547145502214919251665540606479, 4028310949416365109871999034497, 20802477972067031822414339111869, 2645701274035483006046292750821, 17190508277863683534378459996869, 20300098291322108213073203913587, 20600049310428358763109421026459, 10602171044811592574819116456853, 13093971363362986531808183910803, 8599771140844172490031812652011, 11757881186912701568924917989521, 12128626840060120515614917081973, 20517829549212569352713467055259, 5376252708776814414621217163501, 13548760680116030391608242807865, 17657494077098698246583118070705, 3389900163146582700590361600467, 20243575267639645586621583437591, 20724208051479450567137551800689],
  [20531848307697572496985273731671, 5398789044291665983361229800015, 10140473770122770315577042452933, 17877123181247390651644810457591, 2521152768940235667635099719611, 16809594700252696386641571101765, 20818376727788088469467739479693, 11729237584563985819530865630457, 9023270805350846881201746455701, 20119366768650590577966878262071, 20086545586434676650455884022711, 4305597974522103287177508949733, 7543980327508142141405759262571, 14718815077284404470532677937639, 9941850358580116845388569761085, 10768794300985977034896820758957, 20181472785526892135809623474683, 11752371035789896914061846351385, 16275746100546701752399813470293, 647859467556408368424253775597, 8600557994888373159627546595283, 20409321053640910645593023304983, 20544758957247897130450866329309, 20078783305925433666388045992351, 4465198303315430241059642398123, 14877114268473241188577034845313, 10376935003093713357374338500695, 19967995787331433037857177994675, 13233366438283074269746822799273, 20809699599220956742698381586805, 9923321465797985805669122969637, 6298025130619177059431780099009],
  [20368494763884221538826353021383, 20243834985822310289349094490615, 7351773732838265382299482552113, 3689452812604518575981725301227, 3350143163984247278079049630727, 12666298729502213996113169930861, 19963164542614697555225875619929, 20218196542524295010375951574347, 12633952628564996737245158018009, 3584816018276099090538907791037, 2271693239835271027586039534657, 17127159773774157834409086814355, 20301812288203547380989477161735, 20634372908818548844196911949457, 20035879633149538680307577501083, 13567689047227875308589118587683, 5127615384053072433363333929205, 8639585135951578603312646837951, 17561397618229013381923192308283, 9236990025280198903074149701729, 20835653873629367328558425559125, 833515264673475736782870444125, 15361018163054458105936829567925, 20574034439748304137106698707999, 20125942547623199057220813764599, 3263889132908867935424369604517, 9757789319282372004556220191407, 11680038916121225529013399832523, 8127138354164128495094346391273, 18866112879010780270107269941925, 20307326368481698425591310226507, 19023871328236238105193646011005],
  [10833845604306056734760718396509, 13535547345454207749034128170533, 9468147690102012945091206648467, 20798569932633637338144583021895, 20186603673021493816125744002969, 20447757182652170289846960980827, 16272352637534805835166001289871, 5956525414822261968382820539985, 2837739157819812949275513965651, 4257806982034382216273869447291, 5309694702795616790759967957653, 20819738204286710696255385205937, 18108862987711820326726495652705, 11734819771446192788143096517549, 20361987022755864077524546511447, 20205184246010461291689797362331, 14058509735676240306995992369197, 15831268185478590574687626839027, 13770853094553494707722899337151, 6311228549198207178721280340149, 17693549794884475527593784995261, 20799181724043856304162581377359, 3586600405541525925995509873201, 840641111524450111186899334637, 9835145551984400418076446413625, 1416606355462042913295590350547, 20121365564495437839289676167811, 20393811320633099390501672334529, 20653698377530023742080621406699, 9922575082210816373330459197743, 3193498464950887219906486057153, 19968617539812931957135934006351],
  [7140788399183389309630942441243, 10706719448230302327195858507377, 20831000780046421764953160082625, 3573171372327288769082570219717, 14472068813566506737078435939537, 20739622418221456141407488344883, 20441566073367865800373263304667, 9148589590296659941527382850513, 18196131246213523109176889919227, 4653670982252506434319101842367, 4494843969513073023967950323889, 16558814075333313125654379573209, 20473430032675872103955267047631, 16283918079874589331029410260605, 2668370866518967388423295659129, 16724907857836073861522284146353, 19968880232402298176323595233235, 20031955070156949018245455794947, 20272562219598431221885577496281, 20159443875780436018283935084939, 6298052420342376513634751338391, 2206715638572144800925019290425, 16651933899944465695213997762747, 13811311924644396830512631223371, 57629763152643027080769921821, 20824213213020197625396635282905, 6304246310960499937758732130517, 19025043190111497333224603264641, 20195776243299368737221794688695, 20283530461146977012522642615287, 15609916578173877686209300288053, 826934690540976357261452035043],
  [19968373727614912242588515374871, 2679678907840263575881216592681, 5283889738720974270402886755393, 20420845666151773670845567344443, 18084835798333312693317154503729, 5393621678181756775541937122037, 6507448029874155127856066908109, 17995606036817832603069528526547, 20649130660407333115922975338199, 20006781109035918042198350796557, 20116540362434485635775771478663, 14453225834366721033169234569983, 9785251050683153774427078973373, 1968835512478919208248272373687, 16376751341930547006628259872483, 18867108835451075332693201731089, 20811129043242923855822537370713, 1759343675893959733005770741773, 3581353723396589663280531121997, 20798789185989354139252063387427, 20758532525615180001834740406707, 4830739122142346416027477763717, 1096334458392257722953083908403, 17758739020270860367904440917339, 7218867215488347720446496432785, 8792375299529505925455667913867, 20245241620831352723632642945403, 20525879866733934626632522421169, 20324193453486116273143593301245, 11333253991406456071840484958109, 15390206915848769502003318406715, 13337077712966763128991532058507],
  [20836411685362389147653719163187, 20487975206092562054891461236549, 8100017917537509490317982082375, 11724496760039720295511126640441, 9034015397883911467218037133689, 12152971375069491390544257180395, 9346848960902059597766034375237, 7857784845126870876045230052437, 13543321184528686443544553079211, 15366648318705846011326640861643, 12442589730990488738800998224369, 11241410300839992524261307506825, 3237884317313355249247538530733, 20532932137801025021585872331691, 13473450960892039560224169095015, 20607340669714705505901213925585, 20814402624573023723715536494009, 20638325696137764821135942495329, 2371489771429887731267127690361, 16663647084539991809120893480347, 20560952470210633806356869270257, 20126388212124622148408309143643, 13049409821654352904883331821197, 20672556699687509020571835290073, 20836354337659176810795707370525, 13574554351005635429024005774109, 4816992382798980616477489123011, 4731898216268756369175017506223, 18113957335324130782840530060209, 18079671315162774286496499278691, 7888989093925266163032948778433, 20835642800853364285009102908805],
  [8097031625705930842064155133449, 12400662242507383290696403002971, 11043679330879583036199266533565, 11955955659460015543602812751707, 5242028626291333302960395631341, 11578390655036790892191908461361, 17884006591338898316944121841841, 19955188549323506350352502527935, 20529043134911896583868111553311, 15113797925433690521550872689769, 18511885171754596703676055692935, 1876333499181033445233534526013, 16888985076929854300762160557307, 13547024065898099833692732736827, 20799103815848606345408267836847, 20034911688967591889949813821253, 20830459959808849076907291833777, 20210928446662881211670959097371, 509460622636125516065718537111, 20284666807466085341039931591647, 7455787130966994668108407426477, 7890602939273289857865386971421, 854813134059717377068676573399, 12665383267736605205112219218873, 12662611261320434906884258866659, 11755212533901215960941953742699, 19960108150728590021851649909725, 9012370468196933498774906691767, 20617499940789381039273382076195, 14251615874545707502614109984963, 14008327197967746920536658234903, 20810281881619546311238352793805],
  [12365335379623506884744464017507, 3071687828591387948791209330431, 19024804913923371006246386218415, 6232981049896014528215578815899, 13116841049325632687285770953961, 20633383443898022147609588150855, 20798600813811996174700824207645, 2663234799042558925838564100707, 16895327547785680070569634439143, 20442539229241241569351857395873, 10495322253043322529737089014685, 20193707445273322486000448739953, 7882438423431541835539568802611, 16298052814558884362384004265883, 20817165688330157383183730138949, 12113584132067710867715896682861, 11084419432129470206778714411971, 20821616539080393037164620184101, 9192611776423580772206787705737, 4473751484408886505282844933337, 7897210035520408583979195788965, 20812751229118305498703499589125, 20452159752680932906623113488665, 19953506228035894282932357754373, 11027733442595295524131060158131, 20402951165436948035114273012465, 20678843836977413580141250404143, 6732241477610229443884631369177, 20686313786754855894148070151025, 20836205994635944498851733455977, 14482400931170283733401550604185, 10051254693527601055129630691139],
  [5797549951213600610387535125739, 14481034579533861815719464404689, 19023613727685110937463760758431, 12725722984274899270268298022409, 20818951660413274544119979797993, 19024094945078992372665555682749, 826943064381840026919272905755, 4618404858434993348329804355169, 3863819852793609408466812439031, 18076252547649699922763770732921, 15933880661858938882710893680185, 1534065362938433197070193184673, 15736905636854091172273510793931, 20159954687089890434908730349931, 19968427528724833903480567228353, 8089675180653197363514025313339, 19953315087482933989100862610093, 9547137524567361608338048269571, 12652801231127258565750569725003, 20478355677636391433222523875731, 20349714452875611218958725091965, 20811583289003860246185637249289, 20025583470948123215537313893563, 3390886384649565130011569435219, 20047858038697407914331534974963, 6232988232567394156911570262085, 9666844389501805170243361596209, 2673802905613469343933938238179, 17205653749922179165746589147241, 847472042295536830551845298371, 14456156271686209542321115276955, 457271970140018330363372724869],
  [3580279910339013356071421950763, 20196490851855214799826253926563, 18946271989007286002664256666643, 10573923041454516063435262724643, 20818241478803033732381563107173, 19947013180502797405344853261319, 19955176954124766105340605556991, 9924097177300793146715210129007, 6469491765028115343631938263723, 4363657983682260474585036077349, 20033043211480489269136637421259, 20061250394721254689834247199101, 4485792561894575135521160258547, 2774783284355520905865330969179, 20047486057538323290811032803961, 8048681384474024012949065704913, 19984353786243287087058322170161, 424101008370911671500736310759, 12666652473901011979134510867659, 20833228892814132954629010196865, 430293717752369943680547528497, 461353202365288971827955381923, 20814289490799445433048296225889, 10652984068451382040834571733041, 1763912234153973637690509998401, 19959000417314191333153075489049, 16889957270848750462764546065283, 20809794271894803033669254107433, 4552276023214024639415858408267, 5194514258548008599371788315815, 18107093586563261936444921260271, 17521919605211809259806218805547],
  [9665210469050353832722986836529, 20283051205382809084907262997147, 20136834926939161035681663704689, 9006146346936323077539512233427, 1036310345137930811299787998991, 20125991212532083043253982365725, 3429612349298317296936731356205, 20648514273483458265844927961777, 15290859448803522824174954108419, 9035273449880628321487636543859, 20831273375297704732986691568285, 6903036556548316964918881259209, 7981612935359601849722197329719, 20805274189264658122207949358225, 14994263096639616253424885598641, 12656363025543495172375504395473, 2084000588031809696454601412885, 20810892600447496512992703031421, 20194513463958017957580314399189, 2750760207312176757617955380741, 15829548791733271086341345522411, 20758518543842068194166488677381, 20007900680578045005710265525023, 19963803641166197491367381478401, 20585005213726740962200825042265, 20837177488683423107727382437113, 10851014061090957969586171840941, 1364047921363097892819612191411, 11283834086820135155959671670643, 5403149801591039128330747103045, 1753023592386747746554302229779, 17303959567548970654421623548437],
  [20803957130922995499411674752701, 6310140874533719135351765033873, 6449053319421412867260297315683, 4347093278488824675385219240749, 9428916335792987614352690825159, 6491577104059488598686187285385, 735702397642067929505756668025, 13391468694639895196867146850321, 11591276394866495912853707305251, 20600457490727873820475621826531, 19997528702834858576357450651201, 20442608978601239601346650932105, 19936343738098239440712691132825, 11758814474045306508003288965235, 7298385304140841767997537848275, 20836687437164830332341281505035, 20309197244056445221167122890449, 12634101600546275360589134759219, 1769123430035436602394007068449, 13574305275034499476365688658525, 9152972015559713847336522486707, 4867497327457472623449130146561, 1554248151192898457612807049581, 18079659825822262035802474336175, 13548048843502118718994791386223, 6941667834980104345228005060505, 3448275366890448057425453363009, 597544282975264965763549972065, 20724153713120201684724346329147, 6498171242474618823708674187611, 20713773448113582592999952557673, 17820548296061897562112879978563],
  [20284706542923601101251185473755, 20164666511841135437461792332673, 20245250923146004237910258675141, 8374602466770932761829262030921, 9035310700230225646939767373739, 15586776052252140326762988091715, 20836492786563863063605966651339, 20648027647758386766240778240373, 15359357159027977959492605306451, 15374753191715996549540440239869, 8126532300578815496355356326469, 7810766216000038437596884676935, 8690781079853429223475236897073, 12164312791733148773648233797089, 12662461892539888430844506639855, 2676746920560565371662686008939, 16582765378305895988280753548813, 14775792806234928564525280128849, 6091616909271373819967971027069, 20627035063573196619904024222103, 5079880769491175200841260305179, 20533513558328255459328074383685, 12028287114029473185967703897559, 20280477260301891291884109910267, 15626854309248039786028650872201, 4820429352979660195551037416891, 14696346371492578475826831962593, 17916602693241834177602287664999, 9018965452949723907967348894547, 20519901083418237101352076998211, 20532746166396572338701009328141, 20808151751384167899317738768289],
  [20332775113888032937703515930691, 14679759448037602752374114115971, 20245202841913797397702935576815, 2521616681613841728881535608697, 16890178702009799839123014773801, 6284253008733757260537931068923, 2679927300896372600311525034297, 17192522989646983466831666127695, 2673461870330775876799940454555, 16596270678401441732506749991241, 8115391945110250929283924135367, 20277367492719009758311726184971, 8351024319869134255078471549123, 20809396629873085439696680616537, 20271293439609515853873520480965, 5633902050842236751422235877341, 926461959463516711176461045867, 20243808662029354780889375628401, 20283977214060199809209536824735, 1084370519936189927615270611273, 20185159490394548485807226096413, 20836579888555301222684612025713, 16298095067853115872656699183577, 6567477821867286242998003519859, 1653624011077973345464944694463, 16296949881533983007946320653845, 7203424915585230376360719384531, 8906098523172182226639951124061, 20815603678811673736747484356901, 2664131035599511007484805171805, 16721997730178918079820421415219, 6359764545116379231430444347257],
  [15271393982995740084422307450191, 2193556859472047481098112025193, 16369289956368017808743779783553, 5985641251448238900401754162389, 20826874177239950443961271469689, 20422536993859805484072630945521, 12810865708110357665587996020329, 4458313499748947616410250543387, 20007450092643070888205999330861, 20086991385413619181460256546719, 3672334922198150576850638057649, 20458052900499216356338408103273, 20836952299878431100160610014621, 5403936299290617756654184540353, 9682261728386358183638815769267, 17679794425773975850597917123647, 1772235032572707033404544931625, 863037196690262455414875038827, 11298131098740748822566775468073, 20807441332467392626289491322713, 3567053145788634702335500954985, 10131910709311513038411935672639, 14370942153600474558179905255777, 7060368686329748421095137803767, 10726418073538692983970165301109, 19948895625827286143135778085825, 18510546318833452050771418437425, 13179514736228437709782793925483, 20831412872010762748396573584593, 6442955308938144044878368776919, 4357091735280885548053174286999, 3552798757044125013110721236927],
  [8640197622199715251448450348051, 7130529411527070739534280088977, 20694072283974541126959871361995, 20594229726792697685237471747969, 9912277938322085942456184090659, 14551016871366360528421856019563, 20402791963960370273221695257717, 11363249975067693058153652566657, 20495772315171063141753695977793, 9086208292596407844090177774035, 3588214943965686336758284780787, 20804384442287904211569118220049, 10772221777946852379551617478157, 1154676911941180870077576860471, 20830809373020813996866403377021, 3074365117921838981330568358837, 9924255919238499522857380786821, 1673132280492037023662393780093, 18669776003987057057874211215627, 20571166959833327390627966441583, 13731246648139759056629496868177, 3771838815972460026926739310451, 10812212545053684704090944506549, 11600544871386013538860852534723, 19023681996044404120116216205587, 20023264563849424320219483762451, 20462010687510382160859531290745, 20804718441973614731591734366861, 20799570225398011705965799753723, 14048213996391410547841243063147, 20087332020402118509650399921387, 3981915219260382907484217700937],
  [509457610371181285752857897869, 19024635631536568395033991213499, 13573876194681069170919077589329, 10825776260259191863450260599619, 5394327941518127774321235789119, 14443251033230276816782348070693, 18079655447394473602654443778979, 20383198489531724410430545469219, 19967310140069931491179893105859, 14944044343000519275081205543055, 20198493581168524314862955856763, 10336989413886627354839779848309, 15958237819022155753392436503099, 5730364708183520924794207136369, 12902992976599615478114817391859, 10830699047723165181805554166319, 20386664884402746163065706056347, 20226748040291919869258479092041, 20803003095914885493675474202481, 20068486231491400750647002103899, 4022431695605185718188209222335, 20205778085073279461044117546271, 10613811904630969763772700706357, 15548076574227578671055943544389, 4470706780197223398906032174963, 6311258136555040053863871295089, 11739588688777320917355210400439, 9018420852843355683193089213731, 2221577481003999134126428928753, 17187971415374815047490464812483, 20054687782130605879760699756663, 3991093163770625975100823380563],
  [9271094790657296178544149733315, 20802450078967942120293679788381, 18511636409654750332919005385955, 1007139429904911019180822737995, 4469126358985747123727127458723, 13336976212128999669709715543947, 3550096305270746018676669090673, 20342066204639598701314490910331, 20734504372867712323446669117977, 11724537772452784994886699109967, 6859198690464197153769000949223, 20718324579252837792527679771089, 5876476076923824998810344775153, 20567866799701785855438003173977, 2273967053082653390690319164403, 17205952057331529427168497931667, 20820091348331961571112213031353, 11245283855912807240943164139125, 10010060464141335100682783685719, 20829804501609310273663687283897, 12941665567434490408657720237917, 14449775069712621149025132193741, 15725612696347448765283015060249, 4282764685903093813548263096123, 20442607492448974610717431989695, 20308376050523711672087103658109, 20561023093351703731349907142641, 4906249838962193523131168966237, 13574501567361987939192238667099, 17640331332884580275629236690479, 20836340312126631946287580801019, 20401496300298859265025822528289],
  [6277460443628576143983603180707, 9913971587981120689353216507065, 6310336630320612494223972715637, 1969588157466132713151318497095, 16950545019150112425847817014913, 10667316227029121875394650493781, 8109807022549525829686469899283, 3574845184722567293383409682767, 11119148092592886454903098508061, 12568997963079788329880803233013, 15662526969478624069518110954417, 20279339510425905268925433063075, 15593948857017929766792356355731, 20065041565930574785643487588381, 19946267802837755152076030353175, 20639921252324909231990274797123, 20576321903352316322588385738181, 20482080838777714674884552933813, 2390365813503681185816604078173, 17205952865172526816600624532147, 11324601839051709557539206517391, 20836839913036656150380705244707, 20035284558474100446180120246149, 2673533239981024724131192045011, 17173345601618671928230261460461, 5403865737475651571500813203777, 10297913973842543836686754664259, 17430922661406005952816785618581, 13961045170229595534223904197641, 863030483789841481325070891119, 8107496834701173145275431796723, 12992064513028829777728268155429],
  [18352761065990550902502481683661, 11946661021253681750648036921769, 20082746295672174179949736983207, 4303657994119944365761476803831, 20799567913537821186719651650885, 14003578147337087298718283407655, 20243576803482794072980180648939, 2442522433873008690942134404085, 16821532470358661221999160798075, 18630277018677128218434768845537, 5600840051151321643205236741043, 11745630284908615719624157009699, 20671119541086071971063376668563, 20798974105135556799322968381773, 20820164197477278748874099048225, 20252115376832113808819816988067, 8364305914822079505650788255703, 20482070714648908282966242441467, 9310802778366592433994581341109, 13969240858218145778500235996741, 16266873360955803699042721354299, 15389188254941204459851031935009, 13548241750887520192871611797827, 19024151040066098429232912583731, 3256049719692660735943750883561, 5375249021227397389679304813803, 20724157440177258096887575680699, 18076255556846081710061966486467, 8797863942861384836353016619643, 20805379409121348819134868939197, 15119989038390903229769516888523, 18669773022860457061372186697495],
  [11727067830026338547673062053907, 15073241666298274980302671604627, 11217627514878610176676200388337, 20798636658362675499030507015119, 20488347787378214952356877115277, 13547094554118848773066841080179, 4779236819337149073834739841867, 20481060333359357766742583601297, 17600878087702273351292671354461, 20210912589265135185086127949317, 13967627153641234249804899068699, 13574520201166750220474742690467, 20807085689439469206713487646349, 13336755499477578225767778841289, 18314557996070604397689355647335, 20802025249585947354544114295837, 8876243173003616855205539994281, 11724529340880097712293616476997, 14443785569953054390828681415377, 20822583631174903502390498949169, 20534012611770875373871711143389, 12395555918369947816262068609409, 3229572552307877739808070714807, 20047633648314188135093602233737, 20758531749561230549181415353107, 11499721531779702588150486969497, 20634781672687795360358663362893, 20836727904962040019304810398901, 8127475035795207910385097534257, 11449911961758124786858521608387, 468681701146922365261560240631, 12666054994709304890219033500941],
  [8123376828600122139820382392263, 13936397939082953418044163590893, 20827444817899175814528276878277, 12643351814447348990417961249953, 13373771343483178306365042819595, 18511692088926771711322930629133, 19967973798718914529516252498091, 9643316823756107564103176811677, 13342695902686542422466652512989, 8089401452611824048978355121425, 4890125269142101770543875141655, 20827872236317605317990991783429, 17315996453907887949882643562115, 13148932142938960384030871786787, 15388585831511942835970155227179, 19967930747545304703099182163011, 19938836229439457094159216945893, 20487036325302011513568449170219, 20099230486322689785988537073045, 850975590387370571878107921359, 14310731264520563676880796221271, 20599792991724350796886669800977, 9350050236070824753049097634113, 20039283186743944908931146558129, 18235333388867215491099623759299, 11758854584688423570267822634579, 20810350293567117776281882401209, 19968354676500894602913552781841, 3550443428819104868651168439047, 20804534866816657327736852799961, 785909023159543789233661245917, 850920571998384580031814982925],
  [8674203830257409231295673799645, 15923749266913813705067927653227, 20324182255790893683035924950595, 20025061670128206967483638882309, 20639966531181440975336545799905, 12809148429747307525106564062509, 4496069737287835506210092179443, 14205127302486044795494184676203, 20836921014231826031942888574067, 20328298241486183269423759120321, 840678695365244757865665346019, 19025009525803498520619821334753, 14481723480093499897042741904873, 5165881353675835826905614533571, 5867918854460654631755695464137, 18076231196377583901348964262569, 19023631709152084457097041443551, 11757212198105401037403310573579, 19950557328780022121673664697617, 7742415159144163594530904939469, 10813069145009726824506654474933, 20092903284445640431953620099595, 12020088941342038074817687098359, 20676014879985828759692321404973, 20824156774525527007079374133573, 20751667436606546943245561447057, 10959133489818008659038469362053, 70086290867322402613020910115, 20284071144373338907349008756877, 20165636939086025321092557652319, 9081657258488732474217240675645, 20434000260738587707398493813853],
  [20837027039786829100360628046473, 864702712972053780004826933309, 325776889515648815310941759159, 19968224910722570018952823694627, 3587525200790962716332225453561, 13565789646595781166201883426503, 1685157177642056633876904885133, 20822601285393238972701229901237, 9937275057479637364787937706301, 19934599359623822273267116322755, 19948013845487731764302869566173, 1890771724688726046968253079451, 16785346647008134551552260071469, 6968998680035534617128596982413, 3455659998530202578963354075789, 5909455998305735935869760476471, 20679417975385072979487730604099, 20420596874191323024479635306133, 20284723586587341113880187730993, 176524226707777225590476375465, 7219572985808001613683735691295, 1653474421279652916049155972119, 20836181349342231590090437114699, 20196453694376131635225176453765, 9932872335214754300960331956407, 16277471975210781305075685867133, 9942857814893203071643464052173, 19968400178059602727044526558487, 6364640532460306031402653565621, 5269937687154360991660515667217, 3561329712996311864597941269527, 18100245496699940845196998081383],
  [3499137121198421749095886176593, 2205061581514725795705006408773, 17122011771565230477341774092493, 20018647552474762186822455568599, 938052347743330871813609656391, 20114797838200126708050484463801, 20819079543465761528733790734773, 20112511386398718217233447391093, 18630350073386619102917757095369, 9752670110611636391708432751547, 20204555852501922300276339447953, 20047595688507735651937196812579, 16260339637890754194323877255705, 20298439425050600651064184884245, 20836802167929824211938207992785, 3588242158859201470602521514397, 13203829711828561444834142058551, 9864355819399716387629632019759, 863704925848201386543131593253, 2674896185628556683296839963143, 16697300094313429554591543424817, 20811512733323915058349448523749, 5394907319893431791116265019189, 3181463384692316685670988818891, 17870281291543616976557525994689, 6232971086046236437103233426127, 19967285744314856380668791036041, 13923188142843298782008816311745, 11058489205095379348551804191165, 16665364552217680186399636570743, 20343002147782721965054069100495, 7732310729874949453633614886329],
  [12970424762884541802891375690851, 6619401469976965215293579767001, 12547331125406259277133411428583, 6307236127195155551886637334899, 20250154138901956423929259119811, 20154594886126167717795343326737, 20815014651977505132708107062237, 20622806664602660802265476288475, 9706339773650575247606145432019, 20008392659445364414021276170203, 8758721642768990862030212088817, 8403766819874310250026306607753, 11732287798367120691135858883619, 16297235281722209500333601351189, 3556743571001382378344681648827, 15358799164651253625949578643579, 15278798402949477178751121576885, 1756161919545408418537261450727, 20515484379019822359810270688643, 2336420506171107410301711138323, 7042840525898019666875524637703, 20695863214879829673329511310267, 13376077231136386640305133722669, 19948337787210780514073091124639, 1011277476336796141194904353369, 4219614695726244144055917836403, 7184557640950254683673107085643, 20704817549109918966520722055387, 19986710107102412577365935770737, 20813299722409321460067058955609, 20590199080982172956910825044783, 6430198305729785118338546851155],
  [20718919823728637182664610379883, 4968629356182482564003871799325, 10929906451876212469984564138241, 18103674932826837597354390042071, 1771937246806501111741316505549, 8125808956541998006531191646415, 831309663303768471828476512723, 9991614187935906385099790165517, 12645384764934639096949155851771, 20122068064084154920290080440635, 1250616207275423474344582767043, 17521930841015987036565282460323, 20813804746343990941720352109489, 14283399667179139198192602305711, 11721074300933071658653419366731, 834445292338035716842155468399, 14205446302476590465590181918891, 18313873483074605316395685360905, 20448422674974853093182980708827, 20669666102561364707605443533393, 19025065083668654861139944178227, 8997560273078928972340696178171, 20322992290597292513044105738053, 19968128941499205512679596588065, 20799523571067538723689305546141, 13188270970440358311094491894803, 15390226525561023396957201610963, 20822577777154460644663479715353, 7771336744614583210613977582709, 14132263531922481684362103338903, 20808566198266347132343655467997, 11876232189972252625222936443053],
  [5400511318352689101672942542721, 18787959613194688170337775617145, 20820938711755104557058817574489, 20499094791270977835215060729645, 6994813628678972946208118574793, 7995342048697064559894900415439, 20362504649610198728040576537261, 20559756418137574049353976452319, 12064336654146572172088993105253, 20044467453478606957600617778877, 20837100309271243153702628664197, 6311782448599781549088134034725, 7276240448520958887066960634307, 2481580083668418614451996319355, 17204684323109332529776245067129, 12649474280134254862659111030411, 584530323291170853773585434289, 20825034464442276834799508180321, 9027785191895374718359413796225, 7473611267022333887117314689907, 1565749794836172010662450106957, 15744198425440825545852997280447, 11964040347276093201890024845277, 15109996910574309987180595493517, 19948084899276456190764553385141, 20816505735818467782769978665261, 20062966266045640525185334380765, 3881706888893873401136784939897, 6998242840718138571618183987563, 20718546011318558347912958377057, 20402018465528900596984116795167, 7827148611574245315389226322145],
  [20392799690600348595211047314917, 20836056496815656332486074801625, 12666708342457141942345965954365, 14044788246714459255266683681771, 10021856218443552038540054975663, 9034219592069144343627194979629, 10827351931140113158870510081091, 18826828920519455913438662962441, 20817099267576460552320627272537, 10818929685635614677229244751833, 15095010764083929264156723189499, 8088329275278505997441517747917, 1021652123692943127543464231255, 4160143933015788354347346463025, 11888540768706777811932214442557, 4137047417877100913931858236805, 18471791071567112526798049528227, 20166300732842038426706313169295, 20235476316068223880344509461341, 20047894382445101060519849154365, 1734793580579205123310633055789, 864677815550097271127848594195, 19968148406152619352990879564347, 20836609579073712036336954905587, 20461339460065902073407310426397, 9026742039657049577845081183847, 850965098301952686703048084709, 7218754031564478964347880303265, 8916246323931926316009275836739, 19936931917700231522407546259417, 14591368752449501850172892684765, 2669903242430066017010646068003],
  [17174166430981050871393184485171, 15060674673990901080260096651481, 19940996776669269445668337250393, 13640544199441056887799460327369, 20514507874803475844790392258103, 46769112572733270613346169563, 20231468243030969062888914167685, 7494782643498300702004094535135, 20816391468085042243602969576653, 15694455837213110720206525113131, 12206765860173582064564255360907, 7215679400033958597531704156207, 3469615146649025679601297099307, 13636897908657610589445246458765, 20736189470102262389976140846635, 20628626107165096696696011935669, 10845867685564613682990129853931, 18551347151441991080858269114883, 20559675890828105806931429100509, 8205224501428862934517818059909, 20423721698376064257868015490813, 1733974215021578218615996436279, 6311755296960873875060843141871, 20805664892761882878579605436281, 14638870172323676994141981658005, 4120203919338880859140482541835, 20819266418781351310894753026521, 1456404767255679231668316094489, 7192145565527329404147776064461, 9799991825085110165781794902053, 9720032134005441307107772682519, 20734476853214209873213844458315],
  [2956399028308328970477508596077, 6030298761852084048349995778199, 16193536072340398178302027346357, 10415396021258104567784190936575, 3582515528896954557580530510059, 20424070079568677610758487716283, 20743087154257231287102046462181, 20818446464766915392266541450253, 20437462645575132126407737797883, 10219470392596239369209299252359, 20363606873673037582706033172611, 15546791888659253336847801323541, 4101360620387972356950727589969, 8108073322128419312472405233111, 9942751805797494482601325866013, 6295040517729556017188187225923, 12642361174424831042688022817707, 9188365671059382850054141475577, 4470095348221166972932241215103, 20346204319496991713376013545163, 3131373701998927625491703071939, 14695055901422942303161692386851, 20008372742315461985223148653467, 20191156133823757089121496223545, 20521552815377244198088000522889, 15836449149721419283202634261381, 2680384729243842913069217918555, 16415999502133373968679284256639, 20837255164045279002342805125499, 20229358549656415700313667553813, 1760538217549759617343646848499, 10844122803049614357093999768221],
  [2679593210351642350575061584013, 16730951686080606627722905464431, 291437550046123938039749145221, 1989999015958264418455604350017, 17193267304862976999877441476911, 7212693622165876443262769096211, 6184350010319897672738237898989, 8272207705660039301410871799145, 3935195944787149203869706039701, 20155188719056966997462902556255, 19951415192588088415949457290807, 20253787670227715455543900316669, 4061059760367177247208849630255, 20822176490135649277646557316185, 201895400875607707446375329803, 14741485910298006147688855633827, 16273348642339418955964918168703, 15507754989921530516499762280431, 10526127018863724894223264722957, 20177740817328381857293416967263, 20386350495575959888006023768945, 16282649567675635632320306849771, 19950060615992374680744737201231, 20244685042883257458680572078289, 390897013672582731007792259865, 20348164573747743258915838644349, 10086653499664480754102962500659, 4496030985471144024896453534819, 20827399577532682763233508039741, 5837751443748198936333885577097, 5503451472073947646565156012519, 20811858677079306406893234948685],
  [19967532833261635916978535263577, 9018115908262964689070142370937, 5544503200592849827979056739261, 13994414825289448095130319386267, 20560991814099509759333585952527, 20251071512254647313603772655545, 20166308018530411124207927604421, 18235632463049566503965059425821, 6311776679337077274224581330043, 350356692049513402929049121759, 20835853692267017449452742134767, 20798897451087513427841800272809, 13557393423283491844201430328631, 5395334885488713885842137850901, 863683012088119663475552394053, 17758711668004308527800644247427, 7460920226026354314679775307677, 19967267031902921918657687686381, 16288200390907902369928824042839, 12637372000466023006008225752559, 2439620151532252078086549348485, 16481512185696461987996174601449, 19953433154649840043177344996653, 20656637529752167417621812308347, 11549342259564622471098928827347, 20040990620757406599914094467977, 19967965383150397541959758267947, 20835638448297131120000485164029, 2093323579708819275522114638943, 16505762103353118957025011802763, 2666595334703857997059055689583, 16495017079368557512412452213787],
  [615791006683050454917587506085, 20672073322572647486172317490351, 20035208448663636079009696817257, 8120611145988236639261087586115, 11197635851586509542157270593175, 20165002164853850806548423326125, 12113507688951127766904277630961, 20162883358903922692229952860005, 19936119062032587785919073490459, 864659093937480233341408114403, 20814812410467392420142727099225, 2482368410195299453568210836333, 16679093931650047843484118415319, 20828672916068283842842212254649, 5127186199448629658502443679429, 13562490060092722931982685026713, 17317693779592087017456786581665, 20831772894160568829186711943237, 20213316213028023565624268599937, 14813619605588782640380623942609, 18353997958319706166728941096015, 20441707000342412331458637895741, 20520359591826731966046799030235, 403056794644144095549435131285, 20799515822153010839372940278529, 20836654642514235625477196474369, 2680395864346421223989543806601, 16605299234822728300758754641731, 8680007207483388449287801864931, 10850555932176323585410726699645, 9930276215963209919928824110347, 19960714809720403470798223048421],
  [20806091773418689946517868459505, 15371221301122480384152236269925, 2102004658217915493117522095539, 16520312122328433715474799610209, 3272398337036213508530095356635, 8257420491757892863688631051789, 4405273816361633132409728560005, 13685281340850713084214839063773, 8776140397080274826243083566767, 20612946986476212580894340199739, 12113283897476855451141227764573, 2913800112238079343745604797087, 11451408948225341011883729753265, 15311414674946974975448592916667, 841747808549868544666467522595, 20633870065162763593354633925891, 20488275351800769330065598672817, 20809866593772321471292817202437, 20552444535533663541340214590895, 5009221253317766483503964822715, 20324142481771271194305326910167, 17521935058877450762077342456697, 19968933347967298036760595718761, 13572865699132940337538092690119, 8127308015480514471143144391989, 2650211017290674696126427850295, 17190956005954300163748575795539, 11921825559547010120499185622329, 9939295711553800728738997912715, 20667174645100472442393666991523, 7330881708027417572469385166867, 5070971716115953340791196851731],
  [20651631861213181331333744239051, 17758766683801536688419606356633, 1825735311384122679136738328087, 16572765955996799289501526129529, 2996098137255015150849631246403, 16268437040735075791828232911439, 20746504078521675105710110048315, 20119451115619308233180928717233, 20832178408967382165252088991501, 20663995348698471372754362817507, 1219949129748222839166580757103, 20166282945862766221585332384623, 14086937665813304006898725920433, 4930245271241305303222757859245, 9013630232210036620231865149087, 18114000010509151963707361034177, 19024228988112346497099181200323, 7217981996597381272865630282683, 6161293888484651360012188078349, 15359931374922005333692171036139, 20798104130479687125976147118327, 9221488409787070141023153402515, 20829626216801677233082296176873, 20347698185452067950595153311717, 1386416243599246385142809485601, 14822173162348356996460743343331, 20165513845487227383209404607741, 20362770307593535559803449776799, 5975416611636254507961732491501, 20336184984567141199367497185689, 20835908705135798952346056425961, 7219628741814688148629164888161],
  [6176216998828954240212082266959, 7534260704315161459148689786427, 6310323145315145264191529764305, 14470810990635479184147135001991, 12016551558076810981928733996581, 20832856052283661530579047902949, 16280709678875057819928098704493, 18196149692057261901390503113651, 2026013682247346487635993670617, 17007401049708892098020387729207, 15651032948614388942961379954677, 8997105277859185972101904422905, 16009248775288504739509465505337, 10231183008621350861579635102335, 20126779492348466231638251338651, 20454994464960800479392404209793, 20679440678746805242270297814093, 2977291953923065102562513845229, 1772515009804010253645630827423, 8956500595433350618772460663899, 20836570650520944714241493741347, 20081397623688698057845866398177, 4475496824848756871333517851591, 9004428908360016415143895340041, 15389865156228496378509369995481, 6824044740413910918278118036695, 14339074908269577637488651435365, 8687505443321759051103609342917, 15361734559386317443910315270051, 5392770643561032219159740371787, 18589931234694021816793082262557, 17767341125160837606413182205909],
  [14769505360212525474746022260201, 20006732932889631232049396442011, 9904516089411197043355582095959, 20492348956493482237108788269553, 6232940961538365360844917270087, 20807231676643157549378916545633, 13252216589010289498624666408539, 7389509965547072801191949326835, 9017149016635499510205262210559, 1613387396744372240610738324755, 12236822939522099511828309458021, 20241079999914474594349204532443, 20174664300702562037798479019633, 15369651697299874276895186118019, 16038906809603679099742429440875, 20639060282489713841120130913577, 6903333341540016944643642111605, 20691461612118023714863026757001, 11465996329718326077300271419239, 9943129727467831293188354265327, 20826401926777358839524069121253, 8442950637751074691938292461773, 4897661443947057172922170689383, 20810709085394202116114172940993, 17285106457126856002495822811225, 3557337248340868555769765997317, 14875439154505148110316393247345, 11721056900731932062032564461159, 20304382147415695218110508877051, 6903258437963690856281008829741, 11612996560229560411801011270023, 13185545544249392591865922785209],
  [114127883879112290260247037171, 4484767778157506650692750880891, 20211971145266559439791201866587, 20289499712747975981704754166417, 20828743269374497279963702998777, 19984394921769751815210286659571, 13061424430691421285829869607803, 20600476581658342883413414466171, 19967979568385854620916044660477, 13140320522081372904301041204917, 14447909964959872614967301986207, 11757859373080348937713564436165, 9020510091825388792203805702267, 1737621573363658454602683450667, 18787389660641425571724563877917, 10817656162957096891787985127415, 20015750077480757697278481927539, 15131481513458782668048402137555, 20835635862233358154762610305865, 20002379822089221783145587134225, 14137454161136385639305467367173, 19941459709028583516189611458103, 20125747853184661189574754512985, 20442461746056681917740329452783, 18867180205255351883250255600077, 20231514793757762551088760924053, 20836131921281085820472169552125, 1772549006929429778108287774337, 2642616457471300718593165518659, 16415775863823406590081133631279, 2680324494965541677173856312861, 17184911082191403558390067627987],
  [9575840532790704629193334381773, 20829985046729418232179256338149, 7207317537741215624308157272309, 8910053263414924378972914263707, 285231413365723148649521354213, 4732043644994190869686597759559, 3024619884378739526044637078321, 17412067206800009646828458784581, 15302855195629276380217448211117, 7180680427297871045538154445607, 20718920594765031409832386479275, 20798449899422307212525314158533, 20403138473839798162561222085917, 10485472587797294796281819574889, 9943110618831662777196356346451, 9586551936436090290811745474987, 20836998878698981540813550777995, 19989246249238860759201439949337, 10825273411001547418114738796351, 14456599690079320003641064130301, 3586868666394547303270151658425, 2837203874946818378198293989035, 4398383369961079545753220459737, 18946268932878062369761996739977, 14476873897791087987834605634263, 1766177061112046453601669452019, 13707344633495362181058092828561, 4457556655893853066696973233017, 18629302344124596410501319403409, 20421635297815977564018852514243, 18589682381945514872668503286727, 20458047365426935223661751098665],
  [20832705584447042416888075403261, 20799344882775765075703950679553, 10813260248466180659982180072621, 5894697270599774451756265076731, 20638600884783120413361007379845, 20480662328054790592562756633951, 14108278113689224536238050230105, 20543830596285873396708230633393, 20836281028654625619570314814149, 9035321330032212632986008576829, 18275096149167930643786565816015, 3863718118922182479494712851191, 9941972365087080791720790226013, 16266801984787086807422829332291, 15352181099513713450110084082905, 20812729307512897854358880927097, 14455761766984502933616260625441, 14151150892582453400033418632971, 3204464366216856121135889602481, 7692208587670743904045944305387, 18946229021454323923662900966757, 18550131748924517662638927560021, 12068286491330336214609501152225, 12547109693306201349283704981015, 20832780772894167519165096288905, 8089496625846271946761493681199, 1880626976627810149796950631431, 17182373286493937015917617874603, 12469278230850702698142764148035, 7768358676649862981442330010301, 19996142767210626414311998950811, 20552891538835476657722706765901],
  [12644397531014834395442278953119, 663919704390125562714105243539, 20284445379933536584394203635197, 4732247266050501876881208437981, 20538661678400617741304975351901, 17908071988243664648862487328183, 1772533585355899373488170668363, 20835657629202427030115308274513, 14205354233603200934475750969769, 19939744595208773097955143541403, 20815641022146381190908280382109, 7416838919661032637587884007573, 19025023801442911982369014559173, 7046740055823061718731317718469, 20808080381597567171055235848225, 20644669899985275232739671373309, 142203273806329153346786674421, 10252021538081475750760261312235, 20678710750984274383682462129009, 20599151557468612448990470140835, 8474139224034818009145881569741, 20147420419434827223057107636849, 20836503927202480527149871369517, 11758861765092656693146071277841, 19938021950251739581326863621035, 14639645525004496579688809913451, 4495893097292043326957936378993, 9001817434058724838328505807551, 5074052380489180959920624941377, 20808995303149254691067631001553, 18089984760429867965291121738437, 4859899494170900848352657966399],
  [14599122834122563093805035248837, 17521886520902109642481642070735, 13110280249659260817281184624825, 2362961709991910246089880868661, 16467036465828110664232807868165, 7979895735920003530336510705875, 20117094232214657829591733430423, 4692179554574445105252519369953, 12498474010442984158274137491671, 17952699458833341988794249102917, 19968710932250009896455424372547, 1770863742921368585824244127811, 19985938320425323106733277540795, 20610047843244809857887490203385, 20823596247311765227307663812037, 20106242677539043189750406935059, 7851175293152081322606717051927, 20679398589460505269418126338739, 6428928316979142300135363829825, 12548302896198306401334197166293, 1768005220157951491831301808599, 5403686800170938114110484166837, 5392842149798960282037677416131, 18091649121838569263102989863331, 17896043094721731189535364676641, 863047143395238280482762079343, 20006725149347937769884843190991, 6913482716401034620224819860419, 13466584611910271001166835949879, 20363647580371733586009112301063, 20120719974443713162789236128737, 20008421988810174640717228103729],
  [9750960430712502339601958807849, 14482371218659002429425987867051, 5916736131781103707557092941415, 20836259210493856832332412461987, 20573334745690106016950358570613, 19025065891640203177568075718131, 3571074547477440527064809820365, 1771321828080434460981280361561, 11680042295569101765238989784943, 2641857327371117573044468545217, 16568663386371950447141369266181, 9922502088814828736573218268895, 16265011149892376670138144916331, 5036368323774398034960508778817, 6817475360683106017043642675717, 17969862793582950399975258727217, 20307612745351843239213599360559, 3033999895877716791021873426935, 20155974852261047850352863685817, 14679688078244415291687076116827, 20821384497903088655328020434109, 6140989231015125441544516172851, 9620509338797482660548229728391, 5375030976265183524075403193663, 10377006242806067635825936730607, 17544188945340592857310456155325, 20139206657909002412341383052823, 20243609312054929652828309993957, 3569366120637815606404436277203, 5651025496158755944795833296027, 20758509834004902451250034572065, 15586188860283798027696127311477],
  [20082205415171530088416865718845, 4320521058869496580530306501747, 5403933999697576473795510278939, 20821455442395363017221914449341, 17719295138101354628758620661925, 8379735134762049766500732870491, 20835672977561397525864237060029, 15823615270337276684963432647181, 2651210212891343164898485821689, 16740351908906384693891950730033, 9231037667700563090330638830575, 20482051791512984068580310241775, 20649967654701219790018842095669, 20205780289494787642729923727769, 5575552023567443698168679028089, 16298072272069457682120712645175, 3428927829773950991751807805427, 20836768540293629191073545269915, 20741370332172273118336504929569, 5388491696872560835742286801599, 8122276398094508394881573050361, 18113968891586063376414765113905, 13849571465783649334303848972887, 12191375630074675133636386590521, 15898908765918438110741706187889, 5374524421352389784356623289751, 19024489452334585071645157663551, 17381206060390164893696962270841, 6097770219913005566231228219081, 5244387023622472646578095428089, 20798100079374119497306989474555, 17808534562379234862482637527063],
  [20346487718537622759717586328045, 3782175803472804649598637929407, 20076842571111010916293708464071, 4337831835089230689325734886805, 92431744648548377293763601059, 4274277706379034160596585398845, 1850819901888289793719449961715, 17181553105100173102300859208667, 20552372281117269842752964276783, 20378665188130401143826907625597, 20825311863209172192991770305257, 20396274231314178023077216948147, 19968951605256071127899985321867, 20403093412030958433267661307219, 1219800277474966071795729408557, 10179972589665208501681892614441, 5389401512317253948493437719995, 10849620284637246291891535257005, 18093358814406048548694353528483, 10830778670203850983271419869503, 7336344826816175698801673472457, 7199367030418830710474706028475, 20688477270722691492566747914319, 11896751524108534622969869554115, 3142863678230811775837381559115, 20521517872157301329808588550055, 20731073824800802528819104006821, 20087366303753414809440760391049, 3662039400064210595526369161801, 10851012635159817823755107803319, 10258509531728592018241825199171, 20835925061920334344196778704111],
  [20417239037063958246513608695025, 14463523750512835729223350998503, 2661485423197948406444610614873, 17204909152032631154111796391109, 1338292609022574372777134575127, 18274632232426234214848552967405, 3733364609648663314450942369289, 4488029161037949537299378491435, 9014352754849686487378528285607, 9905031015028299957485603284173, 10273537354043740802689172645037, 6524228042806677820397946177221, 20686685769291001312796610970523, 15008141715441147396953118099239, 20384212085224500402406175422445, 3390399760717945793418849702795, 20824679565744752259937747784665, 1686891458170226499849721286751, 10542081672007316066131935775655, 6305830950056993460672519001379, 2126428311970856634932890274059, 16512925278392934520265621094929, 20305244956889029196429961871247, 20425001015714161451053668790041, 7207614765880543367121689315615, 13449283180218441442951828687451, 20086227658272648289988297574925, 3863574799818972900273188751317, 20274424318928527979760523890269, 15592381916436721781430124739891, 8127461547976941534827197634339, 20812735448426300654482000010437],
  [9112997557629816993255569650425, 12414404521094194925573416368263, 20833601167388242057210226605193, 2245984895514814425127541351725, 17180211436123950499230738070025, 11262821415279498332658772965473, 2896612274496267585132264188139, 20798563517518914759544209817487, 11680067752605006829130266187153, 6553720648301396014825987869911, 5279787065755281399030817762733, 15941679660595398825150182087039, 18081390577572127966690886974123, 20589660686851233987985547495803, 20440969130774774232648742872677, 20821879421426189358423431708261, 20295018937675250590662958659003, 10929958865637647628451549432443, 20126796973304683616484495425735, 13100298135957329531028096986585, 2522492601332926516784785924893, 17172375542254423586297069241671, 14482329382001672465357304502501, 9908366068675055733399512744627, 6298696581733121862255201324115, 1252235044499374520589512542309, 19023622252267617561150416345195, 20573999949941411503841028687299, 13003597388996350262291196193811, 20551976629627330504781565462523, 7206646871570783034353519193113, 20712055364649291176330606195441],
  [4855364123828015805249723352355, 19968899123780886686881923792365, 17551064428652055088371724314713, 12903372934747098663296140617023, 20598834194986609216479940963067, 20822626844021192425713115632027, 13624321825854762181293689654693, 20802970923569771337337725970379, 11047327975707365591596601798973, 7338005837886014651495095580917, 18866541108337280075183857162937, 20599220966348781726725817772469, 12632907110223544680899680829677, 20833898982585656585735126401139, 1734572148432495145923783613067, 11758836160341831660916971759407, 328477293369244103987964290801, 2482387876631666062005795987215, 16829441992480392772527189429941, 13541875247513405074162277939267, 20799571106821375519138823092219, 7181873384317519193853396295721, 1654144338286100737201584653909, 2679250681465395632377185678077, 16849962798463333434933027822403, 1406938842885587876719227055925, 843636583530160806202257075635, 20824511225160058376278525915389, 20829790398310257305035421760939, 6370132799161553271789135205757, 2553411976326815235645544309779, 16652231324373622733191252619583],
  [6548541145770890521386439670351, 20708175054937605853361957916923, 19955818915857586113133806437435, 14475490914343857444525607949381, 14471923090479386115991325550907, 942571057564251233245258918171, 20269924542892250752784295188371, 18353301845705957580341721612827, 18196154402337032714665564735419, 20815531919575673289453829351373, 20046699950654589070369848115515, 17467017226809262134413603482985, 7219239490827574374099869468909, 16178048507883231831313130424537, 1747392998086116001212294988571, 1269168891796547475175111331409, 20826257436073285529511527939909, 138023606089623266792211752771, 20382489992410811190820445659229, 20658175288082384691721766639153, 5482879964944297051533478700355, 6737366813750515871101503192467, 7099806262104341641298393402375, 20717801015550648661704423377765, 10832734399022784565265038250369, 19958595749621535937356895055059, 6300098121384501476512631051891, 20837154854608304249635117819651, 1120710651374688217741648349291, 19994668064773896072854640613589, 15451284024858842782863880516515, 20837312529670221121648360890245],
  [4632859878672941295897959826791, 3706607053921862749043079995949, 12663282445435540144016980647293, 7215978388185698228366433160139, 6193154732611708657843698103651, 20458630313019579910924792548187, 10629929580608819821778884952627, 8827608817735648634181861499467, 20818810733402393527922893994405, 20560203221997612962349490187555, 20542147730926075522554329892123, 4544141516931158604002549893621, 14758649157247568903601405875609, 18113961429474139466256589034993, 15547223363653923866579501007095, 4178663520391330038953997873189, 14454417572377898816338527544655, 20807746230445991789772694778565, 20820836458908929496967185978651, 1038036612803765558122802226509, 18432966230001969230700671534055, 7968838043679599051618597971323, 7652579020730483264348121560395, 20381233896430239395095275815303, 12627683395761892653540429274619, 7959258019447551776339998955931, 16203813530018876327313701694389, 20836044291965798540508120873451, 12147907677756866700522268667907, 8202993782809319568293509772603, 20347986449689394253479769364823, 13573733200332797933325051166703],
  [20420279935606333150345920626585, 20608107840107626697758634065133, 14916586697594614288627588228363, 6277410388252269853351469338469, 20560105989461166304231969336841, 1455361037329005153522498310889, 5376451147781036104673234568005, 6056994323108624143517349768017, 18113988326478421088418696976129, 9921139839250479622812460939387, 20243581969905402629167260447383, 11109856805820597834313460011119, 7190413991940400662110721001753, 16153350728717913644744720988749, 20125705728381466022078718435041, 2923569093607156766620241642315, 20244707154748288058714453793449, 15773249842503616801426237581839, 8112015646614934662697741806077, 20306467688874686841746286082031, 13573286552985464446267241280407, 11822338371186727504550455823303, 13096500125803524545612255415965, 20205536907902631334795059753461, 20802032149776197798455689111279, 15802125940258492181979245025005, 8803628898892766313365222650539, 6311250179233688390926131493685, 20599652144069121635720978104753, 1479387221544792313488912589995, 6044035528598242084337436227219, 15372315991409461213136009194027],
  [11757394096971507852136025276201, 20342139338806849961341477416851, 11425330963844573991246098827463, 20178282455609726685147529649085, 7186425992614208521859256874361, 16179690007836320704058629647129, 5646499065274593426138321462137, 18708545563062370414226577870571, 16270630098503382034049160774989, 10829214923383462735347330681327, 10337304390331342308949283203391, 20798169635552234524492625972207, 6610765583285804257238777733383, 13437270248312312544629518541367, 20817307722126589087524664509109, 20481111708615363808211170905251, 20353370589204204626237703216435, 7343192361490883250139231261421, 3746087076146985763270995700277, 4494819144859157686703893721509, 11837429177126511033220904567347, 6071155176840001091988280338257, 9011049174890073033815403136463, 20811871206472649919569663389977, 20814195709442705834702293353047, 11544342741020763198618378597257, 14017284292441912530464404667019, 14955429760873813966814262854563, 1495156757548674848981528184779, 20172252609811328691694310130355, 13552906803905525117962505502359, 15468351496924413149810809637675],
  [19024082999332541784481436163951, 6675078845181080916081165494301, 15236325981045611974668841082565, 9926553814374176485542578387351, 13535874385304492130363077828237, 20510938929844498800650506115507, 20572066540257107187862523149385, 1273149924824439455950680733121, 20447731428600743063125910520797, 2758593493471764595385907323177, 11166751894871295304263269648093, 20737898812439037179103866040735, 6074354688358466833563552425817, 20832155782680961762744801632983, 7185603655812829380012995288525, 20718921476188395934788309709835, 11740581397834769850694589723645, 1377796026465028067213038693289, 20313276128376502322729181617355, 14481653059425966662600626179455, 8371136020385547799291281322987, 15877565516544965589783451166901, 16297634313172165687399071357413, 3338864140699954805372222198641, 2672975248717240704800130659707, 17111712662428420799881928876165, 20821809662571154340191303093901, 11200664174700822185918828927939, 20154257572251271126704478862881, 20356204171376941670687099922773, 9469509804499193853836170375175, 2253044569751408411083578754435],
  [16653051829680572260869436968611, 20166235978758755354725887881569, 6285591714499613003525863193885, 5786616678209200610339713642019, 3579939272072638738953960477911, 20835870961949964203416590788507, 13478599561704336355757622680695, 20267543291330632422009789618241, 9266034298080692563229343238727, 20837295490586941056370825040885, 2014230495027859035807803750563, 16574408334992206353471388335929, 20190335786214284563416375053827, 16047536220511893447627209050085, 16061252527400783365956512467325, 864167994512302608054746442161, 9468931158673084523291066988667, 10953284364710487017834603616365, 11743078028594336353773099544739, 20828108679007541479610940154169, 20810987226478179544786748181483, 5805517524515481079569940428377, 3081955557265666195318239043943, 19967496997596360682611373012715, 785864344860296824518694136003, 20306830283506504982210316477963, 5792833360531514924333255315195, 6298029493721238600520712314301, 13564531701018703824248629334843, 12941572505072062932573749481291, 20424459671484583131032480898891, 15490531783629932926173447898079],
  [19934613290269513149241611970099, 20802434470367072206030510923353, 20205632150017612158608358974495, 11734805037701234354618225781473, 16263434530351496937328671323631, 11205650019272471744585530240963, 20140006031402647041510550089299, 397311742565384552298120667115, 3335913760204994253779393728499, 20804011971632877822737907881921, 20758530868137849619327162334579, 20315615165501962175761089966779, 11280055084292359727003667811709, 10337844100196785244490683983509, 13573898470988737330246486689077, 19967587027139502255065270161991, 13146216836084439980627625936197, 6292737414067470669679995005211, 20802008447555498945325017290333, 20822179502270567847077585508663, 2132944069990433738193661308209, 16438832023542523128194685572559, 4259187677947129099689148779323, 12784672577386137989755968507019, 20588089708295656925650290116043, 9303788245338359537635642958175, 20284035726127892090425579481285, 2007739089375027791088079880755, 17197371144597831719143282704825, 19979176777874620977479661649379, 9942721571687176489946230265291, 10128483960805903170504901325891],
  [19961730231996595065472728908497, 20678052187639943807323033690621, 20811435250609073694248487201867, 13910920812520636159000976131693, 2903465652124240081621030770603, 1771469207912943299521336658313, 20758506221544155446204639538645, 18274359726118807912223675582739, 3701504507743589698860609312995, 2658607008664618395323380355563, 17205579500045851073499912857725, 20799499737173405792707051566051, 6800440223472430039762628231795, 20706906420949537084800168776485, 5395951056505960582973810699681, 509408162630877257658680985809, 17669471568311468809110623727773, 15997543969988476017732764231099, 2654640943672588807102066539353, 17183119801126071149594715884219, 3390815014995371650270119172043, 20387210330745843170171111452619, 2589589304780872584080642538215, 16922787805408002654848409654759, 20832107037847844962507994428169, 20363218267241904667605767677771, 20272711265564797695902261892547, 10173132952738764430019327328885, 7732700297305995730044851194329, 8126090774620276954044877839929, 5757868509139748806106258525107, 11975522804020848365882614976137],
  [12661863267233845999174431264179, 20833676460141391785998948476709, 20819941147215568809806490933435, 7355206283140353480084981649009, 4276380618161146512077053635455, 9744539862079468691896558618271, 12034759591106046817465469350775, 20557299753595693458797512987275, 10841283260096385397196749035083, 2324049956664310623398688110171, 17194313760070735126107814037911, 18393448391065742625735988540349, 19949619803216887797067795924205, 16284842706078911618163496803971, 8199393094218788087126154628337, 20799038989064758192978599529643, 20072815356969731398417480567473, 3928041094809983778672845179457, 20135415599918828464201543913833, 15034628797144744137260363168397, 13692920727679396048370474445617, 20338712672467675113220910837267, 1455732955029088788976995093869, 20809840820818488028956262000775, 19024319689417846866374919531089, 20403132635014055416077905877395, 6289995859111866555064094911865, 272608152071050684779806928133, 20798098262566480271793631798511, 7218956002845372317243317678919, 14346832942396803249660434841259, 20149148046514388664682415578027],
  [2141523032833869487356749008209, 16416521579952540489141786615869, 3588170789200617899240680342921, 12942525206108955959625842744751, 8944496391674633593454556186061, 16290250736834111989388882186291, 20831344664632199127690585534385, 20802481098002754405404758902447, 281211897319751933594701110161, 14703730480478888478891789598763, 2284959865170716108314017460239, 16968228462645114887166912641411, 20512899458109487925669366884779, 2178830904238284165455739204755, 17193940545732548666313740043241, 11751924947186047079449648638995, 19968464983921164789654968636915, 20232597342531691616364679188859, 5752167855289401376696079166359, 9239520240637304167820385327575, 20822148526618664217963602442525, 20284425414083866163353894515011, 19025047918752812379589672153881, 2678749398006396404889463340219, 16612686146773218587188063865971, 20058120418289226432469663393007, 4457885136914304105496170786299, 13759896713641537019374263533567, 20830054443137230506372497809469, 20678396066490684533689609207199, 20458056097125552626433778520851, 18472463063946301982660526847409],
  [2009373587170542197547507115265, 17204758093190287047670056594461, 8601063665184085616877927720215, 2642184988730507650985530350353, 17193119558383679000264453756587, 20830388588149718064129620699381, 20805987958113319917935913591647, 15022990617276118151860810738905, 10291500313087726807913680007067, 13810429859029282776614932597323, 5086787117486421348555081026235, 20256168918056134266143283001527, 17424116299980483911882000263547, 11020582727927989723678032036329, 2679314160159755396091846503801, 17021728737151686318890082820109, 19024994521849831725440382884347, 2963108679579362714760119461273, 20824083872672975078349707827857, 8041815512493318964173289841251, 20799528852774858802830566615329, 20317779362528235205797884754401, 12114104455960295367840342795747, 7453031579863212172606465722451, 13219042964876549633540084429063, 20441322344799886115361702401717, 12643427748139745180689325743769, 8834536914685013585752962461011, 5369380469505289692594867291443, 20836452357948878498877171202555, 17815399962148283384799431493719, 20609061617382124627091720327981],
  [15151775370142790646328548073103, 20837276444243358477070461693221, 9636796501711633335540425660155, 14166599569820278599270048197753, 16763185436430076023363266087387, 10214250943718663406161894624085, 20836820155690436087540256515631, 15692665137235827905137175974211, 19962074111029171229395742099579, 20423162773970103651878285854547, 10850866799640375011976963202415, 20269218305338425767113566873197, 20151237180224891746760836302221, 7377514455836414924539607310483, 4477170397448803645241325741341, 20362395955594203842784056169709, 11876903861415176759581083575689, 9031895792138666091641851714717, 9168948351622018878734722959173, 4495240712608635991657089395577, 6289171990892860403909356601611, 20608682055778304415049360468175, 14928900506832399345245340094643, 840628629834623894664492162917, 3293830780770862308790928375217, 20520846596180415291232701065813, 2574143856165268696843877007115, 11535387050919422109240589518971, 10832098598908041819882545008245, 3563561359782393520432281683899, 5126257262276218625781217185599, 20725873732527165589619039230819],
  [17345171678334564273408201468587, 4056739014746062650888187207331, 20835681879201651179969517828133, 20323822566209268763263666150179, 20058191787942555258048848899055, 4077346515414060996095212276217, 12864063407253752506010498007257, 10850620955499726752762928438977, 2521483673350471599026031223647, 16746397085511674729169523657397, 8093081223913288375859225951207, 20817958582460548081636646209913, 20824044977281172568855957217295, 12225656599936179680839131481381, 9702913913517199476864217617811, 10100802349269197598790544873559, 3943129985172021291706637157491, 20142653398126605470571720739631, 20165692209900796532431992947765, 10584039767408222377737500920367, 5371271311224958629366827204045, 20091118191928564663686445994099, 18114010986993183684891510539003, 11582082479966145939484154325743, 1257740337020108144684521656253, 20599873433292848105457902478777, 20807403617346456106989836613495, 12791986251508258956587362091749, 3764988823481928404705107905107, 11757889015730466529565142328017, 20679028755514004229219949404497, 6671579381318809634293831787991],
  [2537965841391371513164298519483, 17172225435172309081905026450243, 13574483083942886839412145834257, 20589732941267627686536677053331, 4956766601917406093907234853235, 20317277745658331269849416550217, 18079687601066549513590852993709, 10929940492849449171590138714021, 13020272411061865962596258923897, 18906062341538389841533600164593, 10849888494705746964336995120853, 10975042321039505261890281494693, 4484411731065362437476547207763, 5365581666156863591226356788053, 20818023763451436128506208488773, 17568271544191689721525354512899, 19984380827503284806786361168837, 20480438593178198955508537649465, 12824593952750190302296590261639, 3953765153638866705113045020411, 7692315864468150140668505629127, 20126420655855447107109144848221, 13538963197723324774012629435989, 12484777113173528710765211251379, 1768155547480823263426885410827, 20837076050564984153212920433915, 10579116979944249081893136626499, 20380770598665491676210228994501, 14263104964479170284776161693163, 20837293746363051183335480606873, 11502108944846585061711493891695, 6943289990952055992059098458289],
  [18100275354998484654827704808111, 19967739156252789284306895969899, 6310096619329133506741305793639, 5366010041262511486846697955093, 4583861140335179901817093713249, 18100227895091410052607327789227, 17386343596077639184084748355053, 20480424475656487560100568009027, 20677799202799248260637040166705, 8216715688591281819472883710165, 20176596049715778685258372399229, 153394503926876844986811368153, 15587551403411443053841275414261, 20647865443995956915783117577659, 15231839880481548356910516597365, 20828696391581609889128468214935, 848363429429544793933381383929, 20521498613963602808790494369255, 14454271462933060042122001832713, 19968919107288101978861135053829, 20353996714933210401065032707459, 5403788145005072551616870728691, 18432939040129374290087229803659, 20205306806231237839378046667169, 19956191170248282615361032751579, 16291185050864271732887268521549, 20382383236611445140185243630239, 6311261204856217130226153038195, 8468968469983420561058226658427, 6531740195868430925837888717933, 20718098813837082270549205411021, 20819045323541677134836559646407],
  [10030692657308519873156245807745, 14906233622895065366002718178515, 5402544249242366037536182683577, 20204832629334570813546938193701, 17779360691912464133735896907367, 15441717081954343257747817596515, 6310128928787257112197574937923, 864158947139762347527671088333, 20056718943171265619950987458531, 3887899951540212679137937488431, 20109673263327784921633411452989, 2671441545619263730561402848661, 17048067949843644820166142120269, 1274794844219369403765110403809, 12385214066972561409685837242947, 19965376901938166569344343756337, 20837055735616004356370634857275, 1008713112917081464211330038731, 4079038829511348029764049307079, 20625490139170970278342620043211, 8127101054218688246760980180267, 20027257400139298972555444579973, 20535730732438463256454589709981, 11877275780181713637048103579371, 7216202640232036216688922447041, 20718696557212562772630622557317, 7692169792522452967740005766925, 9920816555758938702230046694489, 655752205176749555342961517717, 12666354988076322405506511142793, 860606195131233238736414482171, 20535004132222131791759291467047],
  [10012860085044150052815554829327, 3565874251691061149313402190405, 7920158030888682584611818353229, 20758490376656322023981192545765, 19948804097927786852384884912763, 20231523525859608483190201375723, 19946641317682673382570169313233, 5206531437473255753491293740437, 9942968464319157785678448687685, 17324548788839476244504678562691, 10560670737518942571684882993165, 9941468193853916935717708814443, 20810210353531600113866419374269, 20807853341195530408409777615295, 2779934824539514200462676121173, 8299056341781828260572292683259, 785900088757170079450233015243, 3429482583006507417901857024503, 20081511165649911201342574184751, 4386405251312679798624497148523, 15381664084156142431019832598721, 859135135535023425998038524515, 7731810060508300536786118055811, 20496813969237709763797168338307, 19940222442610188959756077393931, 12263366451951898701287000401215, 20833751714314037234961550402649, 20402913024484159031584012888487, 15017693200816850041324282177403, 5372996929362715887572682174325, 15375570576869206401842698553747, 17798189682409498304060134389835],
  [20177411091402418356957018471555, 8717908536710981222800763161991, 15481195142516596104205364010471, 20807318002251081696816395089797, 20244729281872997216211858817955, 20095947217643080504872810298607, 14782726400368446805140554437277, 14324466962654030007845969024449, 5403006920719490672017481715101, 547835070596521629161949236803, 17612838424643067778896980453945, 19024378081308170791266828772199, 20835677249994872441855743906853, 20827551893179196606436185633223, 8414074424943111293826088032269, 6274018365486684468327649328043, 8323988418766100323800645878471, 19967522285927267003816195787983, 20647683768745126233185741303179, 9915370179403947737262315901831, 5165809847437907784740858938187, 12640615919229602390828858247087, 17715867636095657726986472907173, 2970188128107835624314632320145, 11757182619262748665549424622035, 3487098967083214571301658302649, 20610161385716112347965915789031, 20753384497795080963076453854701, 4660840248131528085753241606097, 20555825459653750354590111874913, 17956125294598268968186416386021, 9548435703967738031503476522821],
  [20322524500465807345991977045103, 8640306307636286127031861708397, 20808140040453291230365534269143, 13547989639278666544001152537469, 20126818469653786327095823763687, 3556383466475338036740046332917, 15232326504834638419983650012081, 20724160819399325765547266153155, 9942273133365185358643422125447, 7806526532751661406227979373931, 4094493768703326614679034111515, 5007576581384593107609845984725, 20836899275730254184286950988219, 17532231995453189255892990283923, 10155956366819894039276130891287, 20125136221075660593622296460187, 9941825797338279381409022344007, 20650236918240151514144795732669, 20383962881439255578215355730385, 9232680094435248191702634080903, 9917397503238585644085014855741, 20679113020654202948578291683257, 2837985717065395604872633674469, 4470311982687732130823995342969, 10746476289082836215294196117269, 3587812716553779920471923668637, 3581717466480132927902667901991, 20734470720196523390131550989899, 2582726156740035539726961473907, 17200805724323567190287046220397, 5004001875400314695811267115509, 20402639500231326979122222263633],
  [17352035630546892508623661461839, 10691446264964470790018738077849, 5402609000161619408761022379725, 11807235017079370642957237223081, 18110585200474286210668741336859, 5582176316187892511891315134125, 20835662281692559269738961642693, 8853709373716592477666721543275, 20610784266190394398087609288205, 20069383349807958029781720760045, 3785600742039239551590762788287, 1465356406714134001958210923691, 15231963159724890376846130281771, 20204984822467401637461483056453, 5379014872739431937910832849133, 15961676588300367886394091496431, 18086539540472570034551080461515, 20836787873072509825173080073647, 6783801046912898041512342808835, 20703476092517627005297182679241, 4781569123150764413209219924203, 20837274009829375083502415134577, 17393223228715049789477072205383, 7653801192626574121154263788653, 20799031561432212624310088249903, 5402295529699979975576461747809, 20308696640675993619250649235713, 17650648906459840218742676053271, 509442323184208738664565557849, 12862369572257879462169020271137, 1298200528384259787878785587899, 20649270158196202892514750153395],
  [20827998279744510889251001520307, 10106203368755581343075990942189, 20816674180263795786590756329739, 6152554658404785413850332211133, 19968928977209205271531705355365, 6962458980818863624370985512301, 20718772562322409343963636148509, 14464119012483938516364510410557, 20823564240280003584414829246879, 10997560474948178788376572456395, 4496051754057200214348639795319, 18392920606349574505298472124049, 4614125908759459225472961127583, 15435339087128681345089488857625, 18089970753061795422518231585015, 20600270102797075621994422779057, 14052987344586837721876998490195, 13552210805949983408019435234677, 20614876127021137899682062163615, 11757892157441544725733506894807, 18788196135712237643092752787235, 8724095277356219197794146886833, 20401933747926631979462816250797, 20803897254370174552518737989679, 11721106442587926561990339782981, 9675410008165907510917482618515, 15389619867218603072077613862689, 20323847127700271778799445192517, 10462269150828176857860530527319, 11417286627851488844705390165603, 13545713625177335880248391921203, 3587627750407317861415222420589],
  [20304312538941946843731419694051, 8016075546212378438718606501347, 20210885332088562371786833292645, 13568138455584736630877212923365, 11916726648634547679107972359765, 3978564292867524061488013453017, 14466271509736273547501384742539, 13850299750061997915791977847243, 7209972179434480398150028130739, 16163199980357489268369781950197, 18550274662952146775924869640309, 19024536627684916441739292129155, 19957453158439232869909610195237, 20346982831089773368840747065407, 20799422058849174262580964045437, 6274026809280235552440801729437, 19994669262934367186186499806297, 7652397710670365416602926391293, 5956496159204009186385902622217, 20463628280068449462735399009887, 11875858357564665683949052395413, 20833899864009037515589379419667, 6294397065731210172318572424665, 20205758438862221652559183235459, 1748823683787702829381290617357, 16100711221255242784591439158933, 20187860497527754454366146279219, 864181209709122209125733905019, 16001144955900172735417263874295, 20590128592757567021105026827695, 14457927596353681575503443220057, 20075319179423656964973900914457],
  [3896107733732944582277505482567, 10929955739913604283548865417101, 18590464145396812735892412831409, 7574269885179147953386789176851, 20141047122219762309723291926699, 20803449248051199921195758777243, 12628952734791825807681493258313, 20833900640062986968242704473267, 10416602524325992826878302443825, 1259362418370774474457017212401, 8656399288806152294996554943281, 20639210644914121278611608206917, 13554855727765550450211495162649, 20816711785624263165521452840351, 10542853790593794645672660908351, 15390189568593987939978900054099, 6433953508187678189493305534357, 4376790209484917490061520363375, 2344625119247125914749629168837, 17178121633875819148116897629735, 20579903163808878213795304461155, 14305637941586645478666055282761, 272597070064474011847429351913, 7218529542850702439686326573801, 11639783232181901950757758097251, 18273947717495018954229448923277, 4486905969244683090938414375067, 20825832599750348938581375207305, 20804346473346362230140458900839, 5366181680760868646540697041217, 19944873523405260907632456905131, 17285060386979076038659750448175],
  [8522027119040009774509548165323, 20480430020577650358859599726971, 4955197569483142448112865491899, 13545327594945627839508371951609, 18083100472331142995639392163147, 14678773229061583837096579457659, 20046204651999184033024473643435, 1579447113785621422000017152915, 10506041254695933465823133249211, 20809062733612676864302466822713, 20125494808846571428861993298619, 18432981847826701219040291575931, 8195293462579786572291733556545, 20836120535384434798955727825403, 10464058934768065544231710127171, 15352434142110211316815276544187, 19976139804107939487783706072235, 15389350603595960590070529699587, 20502626500236775188173950988049, 20453728395075822780440072020433, 1456778598063586289250053982951, 9007837588014445062565312502873, 20086610417303150665976257950405, 3903196178419717101958388979417, 1751954433661355145032485209249, 13859035432884985879958605594081, 15389469364808895315578141864913, 7194508156520068695376755476875, 20697432230682507215646930184535, 18708174005598244813215188607087, 14454935961936687886845252372197, 6773919230124359211419377401413],
  [20717876875875066105460717835525, 8996447943024621269757654179279, 13395553034773250147662933951071, 9019855971818044967315384038785, 8111050511464472359996938490211, 6863522715954756494123868513379, 20683329937492437992482457026099, 12161038639293209428445201584571, 14913162565075359946801086982027, 20826755839457673342294247192277, 20599600354172730199151056870403, 20499243836831695146015447827371, 6086965500780365152179603543509, 5482857467308506767041235269033, 11757420375646662468155698157325, 5126178445967677758273683653991, 13872517345102845240115395229457, 18096815484015551586021396468659, 20803656294884592300719277641593, 20835684956526096878958223737195, 18393520614821495062757995110041, 1111824933508891725141235237647, 15783744617837333351211613971267, 15586847419233545450559518717499, 20799033707612484151618804896135, 8116410575765712863802059592967, 8520730423708694224486630233023, 10829143689780555114552085342295, 12293421460553578663299631365881, 12740882847618625790993204188073, 7188495068012697858764396212667, 15251994242484281763957883835505],
  [20182303265047082643518120001575, 20604749579822078518120476039089, 15972025368539385602890122078785, 20059893529856188911645739566977, 4219267179092890324327812208005, 1535718800385928600197255764253, 19992577285967203649064588373151, 13889579788195575002186672247905, 20813266925868603035902437865887, 11737221274137880854857227145145, 20363628529364237639711955343127, 19024469052448541276091772947221, 6785434840844309894334282088325, 20685120707627880797274185557771, 1771431856312761097966470266615, 6274001631391773187167586244511, 20520471935615418840509671146725, 8929068477208878461992428174715, 19025056112492780592662909581697, 20476106989264037704839764619695, 9034129025169339267978438015599, 9320194174995623367622803591083, 15351642565455041239722798051153, 20442261101304274775930185455833, 20805538371569374191829859504563, 15048730694398357426310812361753, 7744724947620852967647706148171, 3587306580697389836256714536617, 20520248866583529250714973808153, 12560456193295578334622605605867, 13886901775379293795704593508155, 9029918570954895064672486489631],
  [9942112561382685524529795768893, 20222092777726157425831822530531, 18827409628387308252662519615135, 20411711016977549141010851939809, 15363310368455494483408657764257, 14206049401785168599742405634541, 3549561020798244135868481322509, 17168049395007016004410504720061, 9035250029527528705057483877509, 1482061672152241576075793615381, 851845096355667545921054570283, 9580257607016177289561822177137, 20805734915186775918937465548425, 14579923105668389417188423658387, 20276094851637892213813949990589, 20139670706403893998636193781453, 6903855422674731993856302784899, 3442380336235348394449881404515, 19967796629718985909400914186823, 20758486617300231218927400765785, 854259084735257558583098977533, 7530199468913123573447582428283, 14467958523380062546806980285783, 20836023173344446674531799254611, 11828179962957076896615508900247, 20439184821804231324151005161609, 18235409479503401201595000732123, 20837317803071535064909201473893, 19945446683794289533381854941923, 2482994533207089161757821014097, 20416868357478338497819064407531, 8671496353683852614541987250649],
  [3311931150016317039010572306413, 1771694104555398738420269131073, 1693729964518741700631114706243, 19937288771063160789107993742785, 15384308347479566454754822852451, 20816535043182569927386476861293, 20815837209941632739233349293847, 9613667332655607743351195149773, 6797426418472880865538677430683, 7100926399754403223600994037483, 14362874986568837339321371760891, 20021000275870486674131725893507, 7524060486797739493587469843451, 3577904012078163775302512656945, 19023759407847136049584862685971, 12587908210571946567796547284075, 20003803599603428988247779120811, 9108894180829880697951535260383, 826919345654953823194274991243, 20814661838848558620007337810673, 20639295132298657449889615473959, 20480426413328015456875289464123, 9014206684177820688808441639157, 20255539064800366539826697887485, 5624500422552546988200725821679, 6509116860392930632340057268417, 14331687553536438442399507944677, 15231210519293165532677386843163, 20345412122106252473286676277123, 20826133465351829439683478932807, 18709292008914367882291101544361, 20809861567596000068276874355127],
  [13849662167089160629864591318253, 5482847872448110963035590133341, 16259272312869894680686776648021, 20243821041909391477894654853553, 19024541694754896901252216649073, 20820156103953173897724742276307, 2308514288670146983471356125419, 17205953673213500631338913309299, 5366109499936763680798840726593, 1140506386753999850911974186803, 17628311050950869755977500044673, 16290468091138186360362996942311, 5384660395331669482239710704907, 706021132693477835059228702343, 18089929746270751391072394073587, 93462507793651001791834427049, 3744433854297814904955654626349, 4486835272511322620669058730979, 6755891711477584852788288187225, 20709967606814796212138234625539, 20101692278535017583651033056021, 19944924909813577568541608412869, 20669098379728119488900078391133, 19968802712894949791486918331473, 10416782203134443654386179816637, 20389202521409256961640564900803, 4573690457931049513991573641033, 20823545102335363937436859514147, 18095132316232321986835621049133, 20047878627948269106192088906991, 10849374213342114240213792825357, 10061524529242262050331933470169],
  [20056790316164283597090142685179, 4494746446331918910578187345911, 1043182075067765331844129396775, 15772944904961332731819997238759, 382973270180663865547374543101, 20836746879661624809514664292311, 13536126821941260380408753770791, 5743716461847625648295170060799, 20156734046162027958705051057815, 6310364002548016275329164148207, 20447736031147803709672879729697, 20345088180650342995342782151805, 19968950794215335871866743874379, 5386728896608006598740808232965, 20600296135624753057781500292569, 17482465729981044444234370063397, 6298036420619362432745681694701, 15664885407595881705406108610077, 11757431498777535680335502696189, 16268359179296084101985831614967, 20030123340789350396032726817175, 13755945227587095531925587737219, 2647757209488695108061064954553, 17031577946129646472298211857657, 20205709721543836233275558809277, 18550958569494928483183842099403, 20481065111588280403466129641169, 145486730988481286188516046139, 11724483024047850229857264474509, 20665000956904461204909547220183, 5403340160634670816027816395287, 19960318296888304647755520069707],
  [17844529147937018062242207666605, 20047729644235382098424464294685, 20835683304066338126834524407243, 19955221290663665583385507278041, 11216511466882951502850586333819, 14482213561626498491477711726381, 20126206540494419929319930083789, 12770349513259123786492740786087, 674192709985083166220299635283, 19024039662149544131118476955675, 5403258425065290218443955802213, 20012325981820379319661448017811, 17592299615738363422579657331435, 20799553710535710055350714000153, 863061242009015726787000484649, 13337668412136291416196122885645, 19939086033025494556697793188377, 20375680617784226237129595734227, 212565618742083006999952264417, 19968896186664492720923542837521, 16297378110987763240885690677861, 6627394328186719740291151329091, 9815661213686066559601172629809, 10836135630181497105505854755123, 20821523653347805545110303161889, 20825686422852471221567801225623, 19943209324381123430724600570869, 4595582244251962172799885873039, 3114384405723722143860551712283, 17285070995584096243545633090299, 20744785862630843675963393476791, 8283720197511397122127951643963],
  [4490932916619158617307595152477, 6281785045166724607897393867835, 74877448001723700854019017035, 20094474373388187080294124718459, 14970833274687651961584441410459, 1597455382962665796250836194787, 20827822120511480347668074744537, 20520806951810535864820950504331, 20517752938857968408459087774707, 837022648968644766672137145701, 20458000810959172467752609387205, 19945970090546742140666075207603, 1575147252386867983800755895677, 2079568399673101760249761142813, 16771018734928422549604273378751, 20547222431921136189981313035311, 20816284631195955650595647930899, 19956936972488907712831622092585, 20830416520095744635303071857719, 6430049303351944784329079617001, 10732610734581915628062823473165, 13914891315951934797193539982301, 20164933461221401064969061399809, 9023979496053907032797486153201, 20818438643589565841062709540207, 18234813520665746911380052954771, 864698492459368192379980473555, 7266432252175103792375007005501, 14639574153426526440122453895923, 4457017170159218951564803418289, 12657229283834091947822354431271, 7426295123395647232010150454141],
  [863690907967934506999082229873, 13736265827985834854100664515781, 12631681434672442958173196163611, 10688659450274597957526726438953, 20828463536362004695510811548009, 18786892643231905193725828424419, 20578180531975744150516980872441, 20619895392817865615018288820805, 19968949987774420018953559158507, 11721059930637136296515036389563, 11482373146404380902335763695135, 20086728610454944851391532026121, 4481762987681149811607856460461, 2292543459168663503935205175971, 17172973696983647679095302768711, 20837254282621915189169781787003, 4590031586675856161345426240451, 20312130913442524897279143824505, 17594014754625955224963204029583, 20837308120556706418213950395481, 13138723973484815705645919812803, 13021933394465440302994195282729, 17183419920460398022464051285335, 6114354037789990372508992708823, 14459621067716971767667963365383, 9732346793012835342201329691553, 580465470450554074466339698373, 10833499094576327644955262250391, 18748033361949312881343210049261, 20257632464128667789519206595903, 20156533344219391497272840398189, 2937819333469375891297298581737],
  [20799534994107359922970756086957, 16219301057494523198052988739385, 19968936731387624112926416808669, 20081650667910976618137841413599, 4140697489164072353676401922977, 20821878027977891698617026572439, 8113373181805188631979357362661, 20442568456914390853562569461971, 8102181803929848995245113532337, 12193005151318578113257529269185, 20043200565278420096350752915595, 12666483522593977569548040573863, 2242783461920476649763847472731, 20441451055464939212744977276529, 6014291132317269919307303656851, 7209308045291031201585463695009, 20684895286258810423039666041467, 7218510746497900347723842637911, 2544830696697557167193447173691, 16365634295959636586240417321873, 20324123980221130060952259952125, 20826580921947040433174111441531, 9299608738907604983976934037489, 12738757995435551225138635917131, 16297777062962089309431142509953, 20007439302005316197771955658449, 7548609626659296785877309036531, 1067168112091854930364634337251, 3571502531901696306529971418271, 12665926261652642128850860884977, 20755106775822519492417512125331, 1514904205622387507843405115131],
  [20358493462575039493198317445913, 1749493518450255757583609760709, 7022244902128732386680441764937, 11619117144579582706545034820669, 5319972451946748409425986221397, 6310313121713384415969285203585, 17477294976156924270379371900425, 8108880964919087269037618612731, 15901695469944826141135846831477, 20818883517565982317828094075945, 12242293521694472227899140883947, 20202355309303315752588095252537, 20111166535568137021174661785757, 15666549621904502736498436429263, 14302192720825472175050627870251, 16100182426147016194571419107911, 20362609229186089252721638735189, 9927200195416342580872553409613, 18748734325451406231721213349627, 9927418980286073376719474346239, 20836101842470327619707571109787, 5812083772849035795689376689471, 20799548310900268708470958077385, 3087423891053535746287395336791, 20837288787777827927329460762157, 3492287508483422921463135495331, 5956503591106261066444103765705, 20397121621612114444711174220923, 6302307404901477570072582727001, 20490640019428502956030455223085, 14966655936652514067307561020651, 8640558246556133910232058293345],
  [19950882753837553533617902148717, 10534374593472501214653373898075, 20217586935118277031429403494875, 20805092516269282251018555710363, 14744970972216939510999629070725, 20818400099153056591306327016123, 15705125915080935910715298397237, 9627383670207548795170159977009, 9125725239439353767799682662953, 20087038645498071695531444164485, 4480345719240804031934156738765, 20811580998087980639213833185995, 8417133621450063189727067039107, 3588234458784522862401619080383, 3089700231516458108550249597481, 785875315256074014330718354127, 8925581722666395970782422213225, 15384418649834065492412995151183, 7006793293855975840960928434499, 18905615398166592561508147172837, 20836199417469716412883607617387, 18747570478652033876095161394647, 380742551559792365380164274547, 20798320531634859676540135711103, 1771878520425031849123354236527, 20799543180734496878486326566125, 19999096264298236867400610024825, 5956537299242607466146978930831, 14461783929008978193361793683345, 20480631226945719905005719336669, 19967907068821833760746487945169, 7202422192666265181296725916717],
  [18906511963841016350873884951709, 8126350738862895047504837678705, 1757585570397546968480649539083, 20194189778646552485832079450903, 12628207012530352504472731420791, 16294669170924089054851560564537, 13672137163810079949377140351385, 20007868453153359970856864947869, 14103801467582539571566731449591, 20402199656315694584589989076013, 18708024416066808757286108309443, 12639243373130971107064632934361, 20043275048741590501676285307579, 1772327578596733856379589049747, 14444618985570665712075185852339, 10235853296819837322924360408237, 20638863660555608226691079715953, 20815387190648230417226429248391, 18669820242351774577445030253653, 569519691154904721237085227643, 7218380165131674458707977879833, 20718248425108307969847890526533, 2641523181128077791690033333687, 16447412260631522576858109839775, 4485720381070470149890090247835, 9034872060415913690944065351889, 20469686380186935151027022167011, 19961266313674528604597943539135, 19984350744724081527237857906057, 14451361710841636686334896844397, 14837612355151294041365443249905, 7441636994557438784873053920485],
  [20434519383538400212169928154291, 19024021280406180875936282074661, 20799562373239684980451894300649, 18471269880286706546164620862519, 4732911765054297422374887817993, 9904166301356213365623757524285, 17758737127969159363467618937943, 20799254452456053563048892277907, 20835684075102732354002300506635, 9562180730044650258512332060481, 20808122604609484685669992543163, 3232700656897424461315915576349, 1969873641521035643700343607021, 17101416649468407924596691830441, 20679369305812474090389699650705, 3582648537145336993490988164157, 20825277039070834113336604074287, 14396742959285408032939167237643, 2680365316281265018455823489199, 16805045272394147098749976978949, 13929727934215438538960235693587, 18353566657964691565214170239113, 14469335478330497769148221544115, 14810184190414652552672912501419, 11066829514772966173487143346209, 20836390316872768835399553631247, 7787080248691283428552268821887, 6600055555632010301159197104215, 20685045956810447251429700813723, 12665586955354658410117085378963, 20399712724000840604582273811229, 20234732010161348957722071141713],
  [2167266941847134020513391550735, 17183641349743847448277359900733, 20639895158276596965457729517725, 12745204097699445273836479177985, 10838981788280823784494609417905, 8751127813136492864879517355197, 2679044951605783728844289923169, 17170808335379281451239221957931, 20265775181855909474298344317371, 8332967451245727350542966650507, 15378223309058842230137680536237, 1527987449263938031506332966705, 20086445020135575204727036645289, 4148679382102048201310206194803, 4478302981631592836358390945047, 11008600484132486945045847924611, 4463071739965279373706112044651, 19942609285248561620522772883705, 1116561297900066635328627888005, 3555462380653358226622506145727, 15760156416024764530005882600729, 20744790345335693787132348488859, 20382020754223988475772365916949, 13056276353547905346575740598961, 20387673950514484626573458535825, 6429226117920283563343172279213, 13456149757445756957307787956485, 20407147753765556495640362507579, 10376386087489462839551814413781, 20826968947668765619746847770283, 10815348265371891869425772512901, 20600438547102491232610674133343],
  [844484176945075621672476344729, 5482823465054331926190267894221, 20580925071335442400908274816907, 11757443502112674125558361402851, 9184587821134238236019031709435, 20107336841012361015579085510203, 11747819093778312260122267702061, 20646794849086789111878622854689, 1830303744328761451388719654343, 16455992903529390460404444019401, 3634508122844296504447491152049, 6706048589052265923115272373835, 20706534360866347908620296702331, 20829340588237367250770218702695, 13037397638993433078643820118833, 20827010106551483197528302460059, 1218977086316464643947640999225, 12903512175662973938153992028777, 1303273408856573383523892463217, 20007426800537607380964487233233, 5382596839570126053245876598101, 20802950458586116745316472539195, 17856587613975448044265129681715, 7219613726387771678617786644275, 10730967501632122962493673853357, 6981622866958273538053602025979, 11609938877561682792814579437197, 1761094560553814267189573470811, 20363512099244846987885994313629, 7944370645774128113085022119019, 850932247388813801877079576217, 20798246728497182752853999079203],
  [12666037011136237260642912783971, 5874168353765021822153935467119, 7329217452784491998168471106565, 20480622081410051791728783707081, 20813746919749267906843254137227, 12452188329249681395662147851697, 19965525818598322604531400008619, 10850745094674411908425548794613, 20560818102045034729482419302505, 209506521739953002523931608295, 5192793303138503300339414559587, 16278493847250059331208720687775, 18113996686197177190374432150041, 20551906141402724568926619330531, 13691328223633877809603792567859, 20071887024807238454943461372273, 4465870215054951446364949029581, 19968948527827794287803219175197, 18314158969566966891153749097029, 19944898223415841864396305806951, 7402464687911272540883118833201, 20837135352225411638507344786123, 6132035475346822156802662811011, 12218769175449722857864976910167, 20043050569673196060256678139855, 7219405905717807105179248092203, 20701758830340671875406294719325, 20024465553569666679417213743941, 8837964427612070944794666227635, 10840707959530770097053616850137, 20204900590924798925038520745461, 587060803388681952369957530525],
  [16267149112877343948454645588053, 14541780914486296441896791300105, 864133995503637920567676516797, 5394404844452210001230768696711, 20505384966823020847341120719775, 17336592388604911879841802460251, 4487493577577422542805682531205, 19967306990000427228559207064377, 20363249013784122002119104244901, 1151154044024023191476728123511, 9008714325034950484807131780299, 7653658674370707009063938687747, 3556490524244245734094642114487, 14941025875079666382308664251557, 12556975158101233192928528793893, 15385926474594441762071930244995, 5990590372968796419629730977513, 20019518252768511798847068006343, 20497826007537730195336102225797, 10626198242726696622186403342485, 20425390607629058898681951987321, 2086979547674979119576686121861, 16929650425772361218984257974033, 20226301291865950893368062610975, 232710375645534323216391382429, 20825255895371817793448947011863, 16290558930224308499077754442293, 20087353381395294023653116090719, 4486987624950540348573844044069, 9390563988804799439412260688905, 20150461926116726506940999773819, 9035022492360426088494258380639],
  [19944915349973639339596981553371, 19964480396662485462865628652209, 8127205511278351658653554353897, 18630159010994511710743297551641, 11735277224417759712649917224235, 12454386453321557660030808017369, 20833303724535018325795656437429, 14444420828661448465290755335811, 20528385969974051593036944717177, 20024538200727669017604240236741, 14285042053895227298803127296871, 18669788149985650633997610427771, 9428986222772027776726832089119, 20559801557075696165699151634437, 19024765402415722746186684848873, 13536791603043917337904491199571, 837749244697210820189691949055, 20836299324790393164687347908923, 3549817304684988173964768565463, 20447723400605946095015962600773, 8040099668361619603133318732979, 20837283463896785519548229040517, 14120740730874766275400437138067, 12429846667183142977873402669613, 20334265943804105248644831345731, 8108225600601333156631618969285, 20104484547779789028391039157209, 10628363219813146918252959538403, 12508764426396611368531072172141, 5557053168542109916944069244481, 4219542379983744867156195940859, 20382840597753173307349718666519],
  [20814641876511805760832068861615, 5189417415990536705135802248661, 20813248405986963959311833532627, 17364049536466669361209460250873, 4219773401554628985757097848869, 10217825763776605053921074364637, 20402706066017959531377199943053, 16267577338097531017350573336597, 20813287042080279106353850469591, 4674048575033972626998347353919, 8127424537890146383232964541487, 17940637730396648098682381699729, 10415543543446324925521244132075, 11915047885438791995059785939169, 4491321509176961127593020997879, 13238164167389109850139975360107, 3046216834677228079412476247481, 20836320715077458427429792927695, 7123672403906276604945529648755, 13421826879454113989979252150371, 20238965938725962148283307256479, 863734390671256859986121515691, 20195426707771386400503444805337, 20565502353367846853711912556773, 15903379131744106324618604705727, 8118881003193118631061890136473, 20007856481178367870316835340457, 11520764223098536323126190644245, 12651223304415615840682396682729, 19964927146074822733343171876369, 9035053637877159265565928971213, 11726096547983568634486559944075],
  [20340497764984734476589755154795, 9731485256430995582758078689283, 1741630071504083073115240344137, 14844184586184408888377531562701, 20560230594503264472346549461957, 5495712058804279366485176950787, 19024507898199996928499350020027, 3509442731087990638639487896007, 8110801514237930728460029757055, 10767031500772233097485692585429, 8996240586692279111380965944245, 12660207695993943050383202131391, 386797382032893370387599312617, 20423454000087896438401602660647, 20450518660428504682121513475665, 14973219841256714762610713911061, 20631338360663916403206417701357, 5560925790654143041025616724265, 4180293916105758593488882428761, 20532146157924673661418707230751, 19968578471762962529351409140353, 20820118004934255048918322361927, 9918994146282736912303699648537, 20245223543995665458469183342935, 9929141612258677825469721025329, 13850824493004167734599798938377, 20377065871763657342513357994787, 16297050362223536513771451276395, 2773056998280831690527428147819, 20678684792533353804752254857125, 2743073708049062942858126971291, 10830385395235408007757303528405],
  [20727582345156550895396240214075, 15388904886638776133214052450499, 6740774298541126441854903009407, 726526837086192483931430044721, 20520378206130860646013291829237, 20809195940196129946344921585771, 1367538494364152996224707235373, 5553216726640505081467995323131, 4495319538776761043653567781837, 20243831977600744674432282535469, 4554066932032959073166513821511, 19951735753945518102983846447675, 18089938448942421151726250568107, 7219464811883882865798440407689, 20717279975957616374807454402531, 9296775475617956025199632512699, 20373934639695530040897454119437, 16287499617479404542921062308697, 1062049609912919077632606135833, 8219600603493254559890586709649, 20706608751215961585539977924387, 3580260445177876962383701773481, 20574718366861749841652866473685, 9854078361651812711322349076407, 3035611184111082099463955105993, 188205850954392036833835905225, 11680011255518488813319387894291, 19981970039264533091134966801607, 20831581481178860281187663213079, 3184946657664943738367543434989, 20804683841463893429001480414779, 2601601609822703952264010914473],
  [16811237933280110941078569736361, 19963732268585951736440636456381, 20323700561091602447109194442101, 1760389365438416645427682876601, 20830433867407938801012390573971, 13165363734232707080776465757347, 9943149792962658005589841283375, 2106200338571745251287944148349, 16534638316162879189404151958219, 9119341315712635953982052912445, 7193410270243403341039840217711, 20639638873167279904405921061465, 12977034791949073327893085747699, 1746788177622556399527815600201, 20534284672767818475452280697775, 3587498035576671305506369852427, 3159168080717994347762109380987, 14382977910513290766335911335545, 20758497832898989901810851950809, 20831133876050530052257208193783, 6977652455682473491142726823401, 18906660944597679102825879849803, 9034195480516277719376955893909, 20441406552306441933023235772241, 11353028642969942749298260222231, 9905372676824798333266087362975, 8095957193646408618943801950923, 15389905355645449241476250484581, 19974499181955476202051390295011, 12284826604656285411019412315543, 20518126967509102608734557680521, 3560561106486798967589451172153],
  [9430002904612695959679715033125, 9842036159133518588168029704837, 10157673643141264144296450194279, 13357736918174736658265142636177, 20835963564671440785995604950279, 1874549344975364868209747013303, 16910774873506660258472927017275, 20052970816531913523983971725155, 4495641374453192019689958469859, 20351651333638415318110515945529, 20080128759720273281845827256237, 4259259858771234064692306013091, 840675685522690667374307433785, 20284294406356242264323307165465, 5640095107459709445803573802065, 11734811464930988987046893801501, 2236172560830308297667110149641, 17205356798214219011869055781173, 8110243238967506700224216656095, 20370042241133097237712693251359, 19955670092565976365467456424839, 12659798325584435781510611612921, 10215895554442033567413105411113, 20323913720726695713270522513001, 15730420563986739262086980707899, 20744791462745484954623595013915, 13560004977562114010089754343905, 20042727280578784100495130970301, 7464070285915110418341311930475, 14600772980400736126347431156141, 15473023143843464273488774770201, 12271083200253974391105024893459],
  [20517604603764229039302314161907, 20809641958662704142393966298203, 612429931391100500655102330425, 20814961262416128904145563060283, 666673847787309761254409998961, 272576059449359387240183094485, 11275894301702505300026914506585, 20560312529378764092400621082065, 9933990348532191072235734701753, 20828714961134372876748890553839, 19936046215674603532284190917163, 6311738124644649037261832028535, 19943037691014850757037810682477, 19967488486321928049253204601207, 3061190069114275510788024480689, 9017976627065142043218876578339, 3968508552531708150887702980133, 13573656508842951903622336812221, 539956863228762012677790397097, 13546071364872836139721557261691, 8221173881835653587514696601989, 20802023656844149624126214136441, 19959548917988719523131191944939, 20210884191168488056813316374973, 20372099265915609840317895251057, 15153416064191871219183927681767, 19955173495751334316512685172491, 626932911081982278232527383315, 20521349764530257968338804248513, 11730730463060764318889678373641, 10047815760568472307533667828207, 11749626031517652725488269674787],
  [20835943351282823739132853366803, 8410045238320601737445982436247, 20029007372024585737159041370257, 19935521551690799612474101908239, 20837279951441762037937952829497, 320534624336466965235392231199, 14640232714175053553646067698885, 6273975790804367241305502978779, 17930360186699631229822961487185, 20835890558999143517913777338079, 3152414605269033407586779825879, 5031495626297885171714047783319, 20729305719696424318790416225571, 18114010174355661224863986631355, 20121673757607413114162642386201, 20204139636904686104651835408473, 10693129961956774563458866511763, 16268862023110353518609243893749, 20441253876354288206077333369049, 1969387016288919893015468880113, 17187073803589100965156505297901, 5230534593849383457827061680565, 14481901797997912399556011470509, 18101964839148384591019135829371, 20079441002512436743964138382735, 4020790080198948212491869235823, 19025062854718808667801323269033, 9361011667453939873282786611365, 20165086506795143353349069206409, 4669122155564243885225268345531, 20758479559053752572301264850545, 17609458866600478770915425905139],
  [15385083696998287379065126400221, 20085674954428604303731901307707, 4495195306918385814482597766335, 519754545704546836259820709487, 5889180961458624256694704581089, 20126143637786721709298405524881, 20811880404521829837939789853635, 8868856304128661694757973978601, 2071152740564906258823241664843, 17205132253779675376509987521389, 20403065339243568129241613129797, 19937613188445716497418857463159, 14746643828751461797629979889875, 9936107109756467580109230682379, 16297170404597490556017963254293, 20507513180051838268637079889811, 10270432712553131236870726959743, 20140508739879123385493489840241, 9018532481690725656465676942497, 2798802340988919498199818342161, 4792129214027906773528897821441, 11757168684319154567447361270743, 17403482346493150505331054813767, 2650610044029026213125608144891, 17046426406694661933551055596465, 5568616715822229013456149725153, 1742905610218788799017498174515, 7956133884634785408379805601617, 20119185093144709309286010431431, 20305765136643867071295549965773, 12488228938779215806976142697709, 20281296349462842178420691434481],
  [12903313595606219167809866544589, 6588063369480427780208001154097, 20695641067084182285933169163951, 16099617943713686245350043814345, 20802989878322889864056965966123, 5393116400142026673842785131093, 20560973514659786640700798229975, 18098565675307749163179419763497, 5167089772297777127459871806613, 20006729821027610341953149124115, 18114009366526234788104035247195, 4901086277157473538855044869511, 20623724901876149401393422496867, 18088268642929432556033461786673, 20421999106346507302256303363717, 3310301579711538480062533439219, 10377318784196879379463276326165, 7111601479719970469623415909221, 9823419896657074395215477745455, 20120541546593974579225694093807, 20818149785636059799006278633023, 6143600867552602398166293586141, 20811561465865645134026818877855, 9547034989732258402043380203989, 2838254980544183283846925662137, 3649689482944594891894286324669, 20758529450194480466171282843881, 8101360044853158834592475855969, 20832136230417885547642995998603, 2931404272676922558678374385019, 12666672906402450294898336671731, 16215875307748134945470991192537],
  [9548216671276301529074061644795, 1332664431411285122951235911069, 5381300436968379661571302367855, 9341341666913379263893028787269, 18113981268424732169261600003945, 2314539570093991985922138529205, 17204312209493975321905096812843, 19943137112896377184309620232337, 20807658689618315768024310377465, 2747178913841914529686227875411, 20119937735733443313066838877741, 20744802286014057805210296866501, 5246051308175616707431066607511, 8477520755586402501266707700971, 17442983699926332320575365009095, 20047056029948706460885429498461, 14480759531992981660800574815025, 1346911172242544937875449153331, 15360002745989857868627845838499, 20836529408065620644313943464451, 18313682078746691824619378920567, 20500953516730913035847402995289, 678166788989142451385380273599, 20837271248770103712254166912129, 7181202340893236603954351064599, 5285532050384377118667797134689, 7214935702600171512899708072495, 12548077658783903574255782446703, 13570010001626828132263694962203, 1828940692058008158482209143149, 16997328948551988879476583673361, 2658015428776487981818968243431],
  [16973823664589945523792387014885, 20548940893349758801884089875307, 20001109564919436423175328849633, 7839160639320453767315189903089, 20593589273771994484696013334617, 1218679134714285662754808789669, 11995664047364687227222311990209, 20280550547488554625114098694815, 11087621007564183213032272750577, 20816691899839784428641212643999, 1749643966593440168996694453977, 20639942690128012344852162616355, 7186276896427333137270898901797, 8009069982436680662222092890845, 20539270168806563903726788771475, 8126207353378479503635794777887, 12143237368459312262950672250711, 20717652729624897042437369660149, 12627832408885979394854625458699, 14478975034287536810165048869465, 20195226011963862961608532931543, 10849971113292830930082855730019, 15920482389193379245005586263875, 18826352032308145037534477057237, 20007893636136128086285452199889, 20817253564692563376620512248651, 2388650357053147052348489996781, 17168198244602438522496506039035, 8127403452912742740249923410985, 20086874593225866557922568166873, 4009150147719030504868349177451, 12304596662144062703073932270051],
  [1768751156910573699549649933739, 14482150867845502663056227058869, 20259919577591060543441880253331, 5617411976974660095240600187067, 20619350234409447065530876776589, 19023647791161046800107868916521, 7693281134280999189211439016065, 6924931346824500696267712271437, 20660981540172502824587315030491, 12644100094389896379226254563893, 20636542115284794364617712477057, 88778708095464897225344246255, 3864488718211778991805008967385, 3288958515651201833592176229337, 16100328415509216799910626648583, 20749937293807090419377852932319, 20812776584036435984250120052263, 7846027285066744317168934490577, 20821838948352267092842010486303, 19967681571038486862863645887297, 12232475780583715569141920837069, 5005646528703646750073506497965, 20363391511582555719165792176069, 18100279572664382922080272150493, 20814998956189687132190640247343, 7928477016036227924684716842691, 10850973559744277337422744802443, 5491848980853226789693676543345, 12389041689102349831420562124995, 7412143290291366331362389576405, 9924024051793368706494225001367, 3211091278097163072145681619329],
  [12666523922040405524639658000105, 5321716538074828346258230569153, 7205625034151518647661988668955, 17990457953538469969491325231421, 20813881044573161783937325558085, 1573551410376769001544316797803, 20037571944102822191726387997869, 20412688456958649862689224721857, 2404095568628594037912569031903, 16474869133333575497961150714387, 13653425238562550854057394035847, 20678960630389203542614167802409, 7206571318123372491592601607137, 739434647948539935818226015611, 19023891515903084683958936873495, 20836647957565198932226956685651, 9379076355848411397097219462067, 20157699607271412021645578061425, 1734495634924460871336314336511, 20837300083655582850465785546453, 7272082715403590904960796950547, 19968909425951090021114618557549, 15359285786181119092656203564091, 14797676151681303309978979992683, 5390980004576942736036418635623, 11435275227605773014588031705769, 17770740903174657146881556499097, 14454329722734513660204278967515, 9388893025115609730188340936741, 20132628812649466157495564694119, 20215777794826188725337755314461, 18432991739027192667875945219909],
  [20101086809352269150629312001405, 8520995959988419175779900280617, 3430348772205154296526143277537, 20798712537042159660228227088479, 13495760341711563762024467024285, 20806414291304588101183621178531, 15384129919630879739372928806941, 20482033603845745281017759766455, 9000104380805882099267689438349, 8719539542046614781052751068409, 20414321700534682708810610859931, 2679576935083303434696478217663, 16938231209517393104472344509935, 9793872032775045395519761134779, 15078474625115390088095547688901, 20836978757677274720581401803851, 19957757814260450031692012728175, 9601608866616936719365107058943, 20572860308555810602048613131979, 3587945680548689985855276152195, 19994656645462676450507176290117, 20732790199470250572612089994857, 11166787350523874312038507491219, 3583057299415254477922210565889, 20047259834304429581494280289341, 5325143204923123251752710217601, 8094816454559544729821413344953, 17714104982559739460116375448285, 1771266709675930931941406620889, 12665038871557281746165406029131, 20320023946956443430677137327707, 440590653079479759588660898035],
  [9014671691060030765207828711453, 12841072923792691505074358135837, 20639128411963964860742483551501, 7052193464166089115376628411723, 5845874143247574331593680422957, 15389402370094059857473510424761, 12752765933763015370409647600625, 15358442309581907123180465020115, 15056293942116930797273278010393, 20808923952637854133951331330465, 10500024441145867407055061778927, 20494036882609192413109337291245, 20176979484411583536760979079609, 272631072443146075464777157923, 16042332700446378242067535936079, 4811176464523568175939205459079, 20244676867763774156957564816049, 18105427903306241164067512496649, 10993438020689057340692053012475, 4494410141559997614256405142599, 20836726491773662582125806892187, 19939403958880556748041730322883, 20331015092421354101799442082549, 8300659200568729802318187338431, 20837315505260992429155454716737, 8862887093599612339823876858275, 8522182498282209401362502340677, 20292610163306540133662633053019, 15359655621203083369199224614597, 20197149580069879403647160356637, 12846009551725197872358091641587, 15982302887613383931385898916761],
  [1586224160279461989606459393221, 19968403289845025967804676871135, 20170665794944161332208128351519, 20821732093100259249580436281563, 15685427335822849455813691612477, 20823584246371818054648720490011, 5166582875248886352816693693093, 6745919099381218982453404375265, 17980158961198237603620439447565, 20046758032764043329837170023601, 11757220083549144301836300605945, 20826989522845732432593459243479, 5808352973488526819906317111683, 5403914378656889537824100431691, 8290756540169940362997703708465, 17285098044029619189155661885191, 688820650437971952869826216689, 6310085857164902819315574580271, 20087294930906303489407646548041, 3726804357515742270694163586811, 4484074511125299578345777192185, 20238011996035194357322014297455, 2680024684497287254871921334707, 16431965095421732823798477913223, 3919390945608656326096901102457, 20165858777733630573612731687209, 20824938535275306786875656438523, 4962884697541467918686980161669, 14024135902344812651995669587627, 18113978325384016743010360330181, 20283663240367185780229100735633, 8362664414462863096971453521447],
  [18590866970121525034822321481147, 10821013436037530482971015196703, 10849763175463665330495662387585, 20094545743036168737561045181331, 15351149456543820020690138069531, 20660514314754508896615124708541, 10831240674024092550561355394229, 2364566062643262053623272497305, 16821907945581108903422202015857, 13729013721690732411950134782695, 4111415112212235091979753941793, 20836278758123247825699929685115, 9209996856143905626845553010443, 18827678891687584538662193645219, 20655109646262981066117710479391, 14481206206656049248030864234695, 20535249964042357893334942531817, 20798526402206969342088790082345, 3154055224219594768734322853807, 19025028316887200520828147597453, 20758525842053943139750322136005, 14125963390777784978985651715661, 2675217355662222827127757571321, 17167152869780173827958633814825, 10850944305690084139746992309421, 19024557914242918944134765546031, 20429248050421104110122751891431, 5040634438962801705160006142787, 8108544489088002577209207712217, 18076212624659335610966842632589, 20283439601837083128722546234745, 11994048176546137361254900879739],
  [13714717331308601459188000925217, 4495458904907056488189881492245, 19952458560850047597724838679013, 6278758026290245860541941500715, 18393348938523574928161264874309, 20811876184337775453225626466281, 15809512931972659567434342107631, 20307021344336537944873772027105, 20799047488073971381838442969297, 8601133266973303759209991720775, 12769666267673572794157773947971, 5679397619835985544817721776043, 20481088441299919713379341580745, 16265786569240676966040141380133, 14882252016239320838728450607507, 10833283130544584317392020357363, 20836371444288392584266574631171, 532143814742203598783269772351, 20572983291923626123033640265869, 5660688842391256278838716797391, 20837302129385958942444702345505, 15814437587049835233148068747767, 11166775398910946414604609424589, 20066617142162322109004696570259, 4460573677572484976104087682349, 20231520332417787329457718038677, 7181501448486220490703736593431, 2561990350166541363011863953461, 16943976882859743164752359695453, 8245819236274048227719842774787, 20471326227957955981480376088683, 20824491521905969921840917724459],
  [11317809318596713392996709987517, 20806396722377041022354623087891, 14560747493308926002432226334205, 8482672044920855191170545134889, 160174976464825643889063924241, 20520676068827436359210085769245, 10822885298043447698921364822485, 20806377200282239024073283671739, 14867193515181101232481470845179, 14482352784146624255215416163007, 1160669987876442577472038691789, 13257711810295303651033085548427, 19940725175610833761991699653525, 19024050424313790064440066414227, 2426366991724468683206755474739, 17167599686789945221341385412045, 20837253396180961103682959492731, 11331089719614054454155411809467, 11115264785843891933661500551111, 20474579566778856726739683094163, 16297498062731171793005188887131, 20291575159809792153149945856537, 20251595050899196148968088585157, 13811382412870931230763439391571, 13559075379148384195342373263133, 20323131338600762831493640363145, 9429068721007040532455385457221, 19025034666039065501553185091413, 13066265880243677900523490640105, 13573341651558238362290571327553, 14455668422521996419199712442455, 20798568580155902489844434498955],
  [3316046966357791737099617990203, 6277422710040603642488945762477, 18946247546255859589659801574849, 20480658109824372929348623192625, 11515690794269429831608970466371, 2672618390451284182525866884339, 16889210313613903225292589392267, 1745021538561011230841401143327, 7540077374910663663024181590353, 1996579399862966330124636045793, 17197818878554401986944239343127, 12053969118113138645240836994453, 20596623450248693599516657607451, 20272485041333826743468862173569, 6541746793795419606971324756497, 20696609575141632205673402084029, 11560384644158886911902555178513, 4851295473057896938989677480981, 20155362431385536588351372048707, 17837708130572147677712057819361, 20804702930508949525336634011223, 9033679756220708590133610739921, 20008413520419653067440416657679, 2650402420072144274543347519057, 16692822136821297924630589004061, 20095875844657338183008965061615, 15389798155805019264112391449127, 13404607529828102881887999628267, 2418320522362548859719190668317, 17205207166047276194752644574193, 10813187261737103897183024935341, 9922069288480850314985535864467],
  [11311287355140943703924153121733, 20830124547532651734739766273941, 6844910759106946369067534549459, 20693179173716848300004790783881, 20250997234332370197728164495609, 2917226743486642864244383219903, 10090721200113485874091739535407, 4417237929275687621303458690595, 20322849761864020554750163675397, 2674876715876650737469050509861, 16358170665865562701100378875859, 13550457500098197193521998902295, 20836858361297115738467949017903, 14074702562269999925381126804267, 20080469397640252874841899553365, 4026533214398670090525165073087, 20837323340029914387362950051465, 18472090442595700478798047968931, 1101527998184210745569171031149]]

def A1N : List (List ℕ) := [
  [2864, 1426, 1996, 3723, 557, 107, 3244, 2733, 1541, 869, 3162, 1396, 2119, 243, 2902, 74, 3580, 1480, 1350, 65, 181, 1390, 2731, 3784, 851, 2433, 3516, 350, 268, 3474, 1997, 1702],
  [1352, 3576, 430, 3660, 312, 2120, 166, 3350, 1434, 545, 272, 135, 1252, 2248, 2795, 1081, 3215, 2895, 1615, 176, 3359, 3653, 1633, 1490, 2978, 522, 2694, 289, 2695, 212, 3281, 376],
  [936, 19, 89, 838, 3053, 2611, 621, 2594, 3631, 1569, 15, 3198, 3216, 989, 1076, 2518, 1212, 2257, 266, 3063, 235, 1832, 629, 1534, 249, 66, 493, 3375, 3439, 1334, 2847, 2665],
  [1362, 153, 2416, 2848, 1403, 547, 3737, 1695, 2970, 220, 3569, 5, 2269, 928, 453, 111, 296, 677, 2593, 3324, 1058, 2180, 3240, 1224, 130, 2922, 2940, 1311, 938, 3070, 683, 2901],
  [128, 3661, 120, 2131, 537, 637, 134, 43, 516, 3490, 3692, 1518, 2732, 2780, 1661, 291, 2577, 3492, 598, 984, 2702, 1603, 3338, 197, 2258, 97, 2706, 1342, 982, 226, 204, 884],
  [2846, 2197, 1265, 3652, 2481, 902, 38, 2830, 1859, 1150, 1444, 3277, 1258, 3269, 174, 3270, 51, 2522, 445, 1488, 341, 20, 1597, 2432, 1783, 529, 3376, 1745, 580, 222, 2715, 3055],
  [713, 1283, 3668, 1143, 3062, 151, 3339, 304, 2361, 1273, 1097, 203, 158, 746, 1995, 2381, 920, 3491, 2412, 1178, 61, 3635, 2250, 391, 662, 1828, 890, 2349, 105, 2971, 189, 2982],
  [1066, 1281, 157, 273, 424, 1857, 1921, 644, 2249, 3148, 787, 84, 2232, 3377, 460, 455, 2127, 1051, 3154, 13, 2511, 327, 3741, 974, 660, 88, 250, 1505, 2938, 3531, 1472, 3261],
  [2964, 948, 314, 2163, 2181, 1288, 1536, 3346, 1511, 3729, 82, 3730, 28, 2913, 652, 384, 42, 227, 1206, 3651, 3117, 966, 2939, 3033, 764, 337, 1979, 2595, 1012, 386, 2909, 752],
  [3568, 59, 2350, 143, 3166, 1089, 1442, 318, 112, 1137, 3260, 3600, 368, 3054, 3424, 1109, 199, 1841, 2434, 805, 1099, 2265, 844, 1820, 36, 3155, 258, 3074, 859, 867, 295, 319],
  [1689, 2179, 2105, 437, 1858, 3309, 1454, 245, 3037, 3262, 690, 639, 2357, 499, 2510, 335, 1821, 281, 3672, 1526, 1074, 180, 342, 1045, 3214, 2696, 3703, 1771, 3085, 2957, 27, 1110],
  [1650, 1691, 825, 471, 1368, 1343, 1986, 2033, 1778, 1931, 3153, 2400, 491, 2967, 3050, 1286, 300, 3634, 2673, 1210, 2360, 2236, 2896, 3336, 63, 1231, 2050, 3558, 3122, 2772, 1050, 2646],
  [271, 2872, 285, 1198, 519, 919, 1103, 215, 1634, 3705, 2750, 1154, 996, 2314, 603, 2053, 3744, 2748, 585, 2804, 2963, 2905, 2851, 1949, 1617, 2718, 2260, 952, 3597, 3078, 1939, 2148],
  [548, 3038, 3573, 1684, 3097, 2092, 801, 3790, 228, 2302, 1618, 986, 1475, 543, 34, 1925, 2959, 3706, 3469, 757, 2564, 323, 2231, 2328, 750, 2521, 2167, 3517, 3658, 178, 587, 2740],
  [3006, 2869, 3715, 498, 2945, 110, 1929, 239, 830, 1508, 1241, 459, 238, 461, 2946, 1761, 993, 1709, 2544, 1546, 2283, 3583, 2550, 355, 3701, 2480, 3273, 2943, 2639, 1571, 1844, 3341],
  [1228, 2792, 2273, 2491, 2277, 985, 2831, 2975, 511, 3764, 2001, 364, 3606, 90, 1956, 905, 641, 1268, 451, 333, 2615, 2476, 3614, 2227, 504, 3185, 2744, 2737, 1353, 2578, 2906, 488],
  [2821, 2498, 962, 2870, 136, 2500, 583, 388, 854, 1440, 57, 3535, 3718, 3131, 3561, 1217, 2679, 185, 2714, 3455, 888, 3073, 1983, 2965, 2508, 132, 1622, 2625, 2454, 3605, 2473, 429],
  [3704, 41, 2113, 101, 416, 680, 1195, 551, 3662, 2760, 3519, 2027, 3417, 4, 1662, 1328, 1139, 1170, 1322, 1115, 630, 1848, 1895, 2606, 3334, 3659, 1733, 744, 3151, 3372, 1447, 2259],
  [3289, 2852, 2211, 3624, 188, 1179, 1006, 518, 1308, 402, 793, 446, 3205, 3091, 2376, 3610, 3061, 3619, 1204, 2116, 2935, 1102, 146, 1013, 3291, 2552, 1706, 398, 2742, 1408, 1808, 3169],
  [2288, 769, 3333, 3147, 2974, 3656, 2004, 1364, 3040, 2122, 1619, 3689, 2365, 70, 3243, 3179, 1141, 2912, 1845, 3425, 3727, 86, 564, 1935, 3466, 2800, 2887, 1257, 2462, 133, 3332, 331],
  [738, 496, 1379, 666, 231, 1978, 2811, 1256, 2981, 2420, 2413, 3566, 270, 1369, 1751, 2569, 1788, 2956, 843, 3129, 248, 2205, 216, 1589, 1255, 1471, 643, 1755, 2047, 870, 2164, 2262],
  [833, 3189, 1762, 1675, 3445, 113, 2638, 1457, 549, 1429, 1095, 126, 2868, 3235, 2648, 2572, 1700, 3461, 330, 806, 3406, 1885, 1292, 812, 1877, 1707, 2154, 3353, 2058, 1183, 2206, 3630],
  [3664, 2184, 2294, 950, 2419, 2697, 791, 3321, 3676, 192, 1404, 3130, 2635, 717, 1295, 2083, 994, 1969, 2709, 1883, 792, 2114, 1744, 2261, 1862, 2142, 789, 3638, 2973, 1665, 2378, 2710],
  [2054, 1748, 640, 3245, 3734, 1040, 3465, 1977, 571, 2801, 205, 2071, 1664, 1101, 440, 1348, 287, 3696, 3419, 2947, 3009, 435, 3001, 2972, 1725, 3680, 2993, 2773, 280, 1225, 1305, 840],
  [1653, 609, 1460, 1090, 2584, 3390, 2859, 2874, 3728, 3136, 1250, 3266, 1992, 1355, 3731, 2461, 3427, 2671, 3141, 234, 1363, 730, 1599, 710, 724, 586, 975, 3251, 2447, 3779, 2805, 2693],
  [3228, 422, 3565, 2728, 1079, 307, 691, 2394, 1815, 1315, 1157, 2627, 695, 2016, 3675, 1974, 1620, 3448, 3032, 1824, 3219, 1957, 1226, 1982, 3157, 354, 3114, 2986, 2085, 2484, 456, 3199],
  [3343, 672, 2039, 2139, 1192, 3698, 67, 2532, 767, 940, 1337, 658, 310, 3121, 3028, 3292, 2342, 1056, 2035, 24, 2415, 2213, 520, 2705, 3248, 2666, 2968, 316, 1461, 1875, 2822, 1926],
  [2404, 1211, 3405, 317, 3447, 9, 669, 1692, 1126, 1448, 2316, 2622, 1077, 2716, 2699, 879, 3005, 2636, 1376, 2111, 159, 1795, 1112, 1354, 532, 980, 218, 3443, 2775, 2464, 3400, 1263],
  [3392, 3064, 2645, 1909, 3752, 3302, 165, 903, 1420, 495, 1331, 1414, 1621, 1274, 2929, 2815, 3434, 3127, 2348, 2653, 1595, 2346, 1854, 389, 208, 2576, 2029, 1693, 3740, 3202, 2781, 2899],
  [109, 955, 1966, 2339, 3536, 3301, 1510, 1726, 64, 2619, 124, 1129, 841, 1632, 1080, 2512, 3496, 3105, 2556, 3233, 257, 949, 707, 1392, 411, 1023, 954, 929, 2837, 3551, 2192, 2115],
  [2256, 3711, 514, 2691, 2843, 1493, 277, 3473, 2558, 1601, 3165, 3478, 3241, 2692, 247, 794, 2487, 3765, 3789, 3025, 889, 3612, 156, 3125, 147, 485, 427, 1586, 1494, 77, 1289, 2647],
  [1945, 464, 720, 2153, 396, 2628, 2916, 2633, 1229, 1792, 2411, 3572, 3265, 2754, 582, 2166, 3272, 1182, 3781, 2526, 284, 599, 2762, 2060, 1016, 1410, 2282, 1293, 1878, 2525, 2495, 953],
  [1930, 2894, 2514, 3058, 1765, 1456, 3362, 1823, 1573, 1780, 3170, 2629, 1932, 1491, 1980, 3274, 741, 2683, 2291, 1629, 2617, 343, 2063, 1572, 1446, 1521, 382, 241, 2201, 3626, 2878, 2457],
  [849, 2449, 116, 1840, 3547, 1509, 2130, 3363, 3310, 1818, 224, 1185, 1805, 2040, 2616, 3416, 1602, 3290, 340, 3700, 78, 876, 1600, 804, 942, 47, 2829, 2995, 1394, 3280, 3639, 2482],
  [3060, 293, 771, 2312, 2684, 3444, 2657, 682, 2876, 202, 3792, 308, 1681, 749, 597, 390, 1822, 2875, 2599, 2441, 3026, 303, 351, 1558, 886, 1561, 1299, 563, 1527, 3366, 2562, 3319],
  [2391, 3567, 3297, 1135, 2507, 2245, 872, 1879, 2539, 939, 1842, 2354, 1247, 2568, 1863, 1123, 3537, 297, 2753, 560, 1492, 624, 1279, 195, 2109, 1740, 3407, 1905, 1148, 3760, 169, 1542],
  [2463, 2161, 395, 1318, 2015, 810, 2545, 3284, 2089, 1574, 2620, 3515, 3733, 3495, 2064, 1663, 2833, 3663, 561, 3528, 1836, 3156, 2392, 2185, 3453, 2888, 211, 581, 1719, 1208, 1009, 701],
  [1667, 1067, 2170, 2999, 2100, 3449, 3268, 3504, 836, 2254, 3257, 550, 2546, 1802, 387, 2417, 3067, 1201, 3396, 2061, 594, 3330, 274, 1764, 1181, 1538, 371, 865, 80, 3328, 3143, 1728],
  [2825, 527, 3093, 3271, 3128, 3312, 3177, 2658, 119, 765, 822, 1254, 480, 1000, 1230, 377, 2722, 3183, 3526, 3702, 3337, 2768, 1388, 1817, 2590, 458, 1970, 1872, 1537, 3360, 3665, 1132],
  [3557, 2530, 778, 3123, 44, 2293, 1227, 664, 647, 635, 172, 2385, 3304, 3499, 3101, 895, 2817, 162, 3036, 1891, 497, 3671, 2834, 3724, 3267, 201, 909, 2280, 2224, 2386, 3232, 1142],
  [3014, 225, 2803, 193, 1497, 1393, 367, 1356, 261, 990, 3613, 2290, 694, 1019, 2052, 718, 2490, 3077, 2021, 1114, 2873, 3308, 2123, 2000, 2072, 766, 3247, 3065, 584, 3436, 2917, 123],
  [1312, 3498, 2497, 809, 1548, 1937, 1155, 2084, 2985, 1813, 562, 3126, 2664, 3066, 2736, 1866, 559, 2580, 2352, 906, 2608, 3285, 93, 3358, 3386, 842, 3579, 2926, 3034, 3152, 155, 357],
  [2013, 3190, 3697, 3508, 751, 3497, 18, 1791, 32, 508, 887, 781, 1287, 3570, 3404, 3588, 3384, 3509, 96, 788, 615, 1507, 1423, 1552, 356, 653, 2239, 2677, 3595, 2621, 2509, 3412],
  [882, 2898, 3648, 642, 2284, 2010, 1445, 2923, 1825, 1385, 2453, 2300, 1238, 2203, 21, 1865, 951, 1285, 1084, 1532, 11, 1787, 2890, 2395, 3768, 1516, 1897, 100, 714, 3222, 2091, 1637],
  [605, 1968, 1017, 1938, 2134, 1759, 907, 3540, 3239, 3158, 3380, 2501, 904, 2925, 2513, 1366, 2861, 3745, 1, 2162, 2443, 681, 2268, 2581, 3632, 2255, 40, 1668, 2081, 3098, 2202, 3623],
  [521, 2393, 294, 3539, 170, 1382, 1048, 574, 873, 2351, 2944, 3772, 3545, 2405, 326, 1570, 1029, 679, 1722, 1713, 770, 860, 2423, 3459, 1916, 3794, 2900, 2469, 1503, 3726, 3211, 665],
  [254, 2921, 3754, 428, 1831, 2719, 3149, 2347, 17, 1576, 2542, 1902, 2110, 1737, 1694, 3221, 179, 2389, 55, 1037, 1140, 965, 988, 2017, 2078, 1284, 2233, 3159, 1592, 2223, 2751, 1468],
  [1789, 251, 1948, 1365, 457, 1061, 934, 264, 3604, 3511, 3223, 2043, 1401, 2334, 139, 3197, 3087, 1049, 3349, 3041, 1746, 2117, 339, 1116, 2151, 3397, 3329, 3140, 1395, 2761, 87, 3608],
  [262, 1244, 1209, 1678, 1540, 8, 1151, 2877, 2322, 1545, 467, 1753, 1316, 2315, 2272, 2159, 1367, 3609, 3423, 2698, 2253, 2303, 1111, 3477, 3571, 1113, 2194, 3354, 2903, 3220, 2783, 1889],
  [1738, 73, 1455, 477, 1047, 1032, 1161, 1575, 1481, 3642, 3758, 2790, 1793, 1819, 2952, 1687, 3059, 2429, 987, 2155, 2309, 663, 3475, 2515, 1500, 2338, 1946, 916, 2387, 182, 2003, 790],
  [1078, 969, 1072, 149, 2799, 2407, 2763, 2687, 1608, 3553, 3340, 3611, 2369, 2326, 2474, 50, 1616, 408, 426, 618, 816, 908, 538, 3044, 2217, 3687, 3541, 2118, 2883, 1043, 3657, 3487],
  [941, 54, 392, 3015, 2023, 1407, 1640, 2489, 1638, 2743, 2364, 2320, 1666, 2390, 3722, 3342, 2598, 1796, 352, 2235, 3732, 768, 1918, 2135, 2121, 3013, 2093, 2809, 3716, 142, 558, 1167],
  [748, 733, 1644, 1184, 1435, 3481, 2332, 3112, 2207, 2969, 3021, 675, 3335, 2176, 1539, 1809, 1963, 1100, 3636, 2124, 419, 1901, 1816, 1583, 1927, 320, 2141, 353, 871, 923, 1486, 103],
  [3788, 2660, 3016, 3193, 688, 2219, 31, 1703, 1727, 1976, 602, 697, 1807, 465, 1754, 1835, 1943, 1459, 3793, 2779, 2353, 2437, 2533, 1180, 3201, 2904, 1458, 2102, 3584, 760, 935, 1704],
  [1215, 2585, 1730, 2613, 2951, 570, 1847, 3174, 3714, 1485, 1568, 3180, 1145, 2712, 1989, 1756, 726, 187, 1524, 2672, 737, 1917, 2987, 654, 2313, 1547, 1710, 667, 1743, 3011, 3493, 1413],
  [2345, 463, 674, 1893, 1207, 1028, 3118, 2641, 2642, 3253, 1887, 347, 3168, 2036, 1774, 2038, 3432, 2976, 360, 2485, 1033, 3115, 1981, 184, 2295, 2881, 1786, 1397, 656, 1504, 2618, 1351],
  [1001, 1580, 3388, 885, 1649, 2382, 2305, 2297, 3207, 2991, 1197, 3435, 3746, 1068, 2281, 1708, 606, 1679, 2893, 2574, 2941, 1321, 2828, 808, 1686, 1239, 1065, 1581, 311, 336, 1104, 1031],
  [819, 1384, 3318, 2688, 217, 2914, 2589, 1476, 85, 2703, 3520, 1711, 1172, 2049, 3144, 2989, 1059, 305, 1130, 1920, 478, 626, 2729, 1734, 565, 3293, 2307, 3720, 3485, 2520, 918, 3249],
  [2455, 229, 324, 168, 2020, 3379, 728, 1134, 3089, 1391, 1327, 1922, 2066, 1960, 3644, 3750, 1243, 3527, 3171, 861, 2543, 696, 1020, 1127, 3422, 3563, 2251, 723, 2690, 693, 3299, 1770],
  [1888, 1567, 3242, 1267, 3717, 1763, 1894, 566, 2218, 1402, 3107, 2566, 3776, 1685, 1483, 2845, 2824, 1147, 2701, 2746, 2160, 899, 2708, 2818, 3775, 3096, 2098, 3735, 1464, 1749, 1654, 2195],
  [1843, 230, 1867, 3410, 3120, 431, 863, 1688, 1928, 454, 1024, 361, 1036, 3113, 2918, 631, 2051, 1317, 1411, 414, 3721, 2689, 3056, 1712, 3472, 992, 1594, 2813, 1506, 407, 2106, 1951],
  [1952, 2241, 3543, 2560, 494, 821, 3785, 2074, 1869, 2172, 2439, 1680, 2607, 3355, 930, 2014, 1409, 721, 1242, 2479, 2827, 2596, 815, 2460, 1705, 743, 645, 282, 1038, 1782, 823, 534],
  [3258, 3413, 358, 2396, 2008, 1742, 2933, 2980, 780, 2421, 2570, 206, 2, 30, 2494, 3655, 1303, 490, 2997, 1598, 614, 3601, 2144, 2075, 1988, 3175, 1381, 2101, 3677, 1344, 1967, 1156],
  [813, 1495, 3238, 2459, 1860, 1298, 3012, 1636, 3138, 2759, 2210, 555, 3426, 922, 2659, 2070, 3458, 359, 2333, 850, 1773, 3003, 1775, 834, 1069, 2592, 3008, 1515, 3736, 2157, 2059, 668],
  [3688, 1837, 378, 1936, 1294, 399, 736, 2778, 3770, 2435, 700, 2046, 1015, 1203, 2330, 1046, 1166, 2612, 1868, 2145, 3483, 3451, 2031, 747, 1304, 2865, 1959, 2007, 2425, 2669, 1496, 2193],
  [2366, 1436, 2488, 719, 1319, 828, 3146, 2344, 2734, 1160, 2575, 1406, 421, 1658, 2133, 3554, 2372, 2820, 1914, 3666, 1188, 2011, 1723, 3437, 3039, 322, 1950, 3617, 3327, 1144, 1484, 883],
  [3124, 546, 725, 959, 595, 1525, 1627, 12, 37, 1656, 617, 1302, 1683, 3111, 2573, 240, 2707, 2175, 1062, 131, 3071, 2094, 1412, 1655, 2150, 2408, 2138, 835, 2675, 1690, 729, 2796],
  [2006, 2067, 2931, 3382, 415, 3780, 2136, 1528, 2152, 995, 698, 1587, 2962, 2045, 3654, 1551, 1908, 1153, 1427, 259, 670, 3691, 1007, 442, 3488, 2953, 1186, 3500, 1961, 2478, 2174, 2129],
  [1677, 3640, 2225, 321, 117, 260, 2287, 2942, 705, 1175, 2363, 3186, 3683, 3763, 3777, 3275, 958, 2079, 1562, 1919, 3246, 161, 2755, 2651, 2200, 1052, 1438, 1389, 3699, 661, 702, 1672],
  [3506, 2299, 2026, 578, 2667, 853, 3510, 2301, 2216, 1624, 1896, 1701, 3590, 2221, 2787, 1501, 1276, 2178, 2226, 503, 3069, 2318, 2496, 438, 236, 1498, 3599, 1651, 373, 2591, 2470, 1370],
  [3615, 1953, 3628, 2427, 2267, 1125, 3479, 3766, 45, 232, 214, 1882, 2252, 1556, 1193, 1433, 960, 81, 152, 575, 410, 727, 671, 3686, 2343, 309, 2523, 2244, 1430, 108, 2358, 3313],
  [1550, 482, 2541, 3305, 2368, 484, 2860, 2527, 1275, 1806, 1018, 468, 1380, 3629, 3195, 2182, 608, 3771, 1291, 1042, 3457, 1253, 706, 1784, 2296, 1799, 3368, 2209, 1387, 2215, 425, 1557],
  [3325, 1798, 2306, 1850, 3083, 1588, 3320, 2711, 1091, 1752, 397, 1549, 874, 3514, 2229, 3378, 1643, 3564, 1544, 2655, 2644, 2555, 1613, 3311, 439, 3142, 2062, 2814, 1670, 2034, 1517, 3521],
  [2451, 3431, 1593, 931, 3650, 2341, 848, 2264, 2087, 1760, 917, 1479, 914, 219, 290, 1449, 1330, 1716, 1131, 3778, 3769, 332, 2270, 2428, 372, 200, 3278, 2186, 1642, 620, 2080, 2661],
  [2276, 1612, 3582, 2450, 2096, 2682, 2604, 3344, 590, 2623, 734, 2379, 2717, 207, 1797, 3709, 2384, 1259, 1277, 1596, 3607, 1489, 1645, 1120, 1174, 1441, 807, 1399, 1987, 2397, 3441, 2399],
  [363, 3043, 3542, 2403, 864, 1453, 3755, 1605, 2137, 3047, 2492, 1002, 210, 650, 2442, 852, 98, 1199, 2610, 708, 649, 1993, 2884, 1462, 2649, 2076, 3030, 2243, 2359, 1585, 3364, 3467],
  [183, 25, 306, 2057, 3494, 1717, 3621, 1962, 2808, 1107, 2414, 1428, 3234, 2637, 3550, 796, 3460, 1057, 2371, 2336, 2856, 1386, 540, 1856, 2456, 1055, 3161, 2019, 1975, 783, 636, 1152],
  [893, 3482, 2466, 3786, 3411, 1467, 2238, 3749, 3622, 542, 1614, 3548, 501, 2988, 2173, 1971, 473, 164, 1087, 3546, 829, 1779, 3286, 976, 2082, 1639, 1296, 483, 2410, 3103, 1998, 1022],
  [2230, 1314, 513, 3181, 517, 1419, 3693, 2503, 2536, 2586, 2807, 1124, 536, 1374, 334, 244, 943, 1422, 1026, 1591, 3525, 3562, 79, 3167, 1853, 441, 177, 2266, 3773, 1021, 1011, 2279],
  [2776, 3357, 1249, 3756, 839, 1718, 3440, 2756, 2504, 2724, 2554, 1128, 3596, 2274, 1482, 1876, 466, 1158, 1196, 2663, 3402, 2849, 470, 3196, 601, 2770, 2538, 2325, 946, 3633, 968, 3027],
  [1955, 3090, 1118, 2563, 436, 2601, 1899, 3684, 1133, 655, 1994, 3767, 687, 2126, 1811, 2090, 921, 144, 509, 3438, 1329, 1431, 2844, 3712, 772, 1729, 2505, 3513, 3255, 1830, 1240, 2237],
  [2041, 114, 71, 283, 1973, 3057, 1648, 1106, 3352, 2565, 3522, 3556, 2374, 3160, 567, 1964, 1332, 2609, 2418, 69, 2065, 1731, 2867, 500, 1070, 1044, 1790, 937, 1162, 1373, 875, 2377],
  [3079, 539, 2626, 811, 997, 1035, 3031, 3471, 3263, 999, 3104, 716, 881, 2445, 678, 476, 3532, 1767, 1768, 2839, 2324, 898, 383, 991, 686, 2424, 2650, 2199, 3296, 915, 2836, 2323],
  [3300, 1094, 1223, 2030, 1697, 2367, 3369, 2547, 1324, 95, 857, 2212, 3713, 2077, 3452, 785, 1747, 370, 3303, 2140, 2676, 1371, 2678, 528, 3429, 3095, 2373, 1041, 1092, 3374, 3560, 1607],
  [1827, 1941, 1884, 963, 973, 799, 58, 60, 345, 709, 1555, 878, 2858, 1906, 148, 1833, 3049, 855, 154, 2128, 1910, 722, 735, 2311, 1741, 2920, 530, 190, 877, 2380, 409, 1477],
  [2936, 3620, 1232, 3408, 2537, 2892, 3646, 3072, 803, 1846, 3559, 22, 140, 7, 2088, 2735, 1326, 507, 2791, 3585, 447, 2741, 604, 1641, 506, 3307, 1907, 3217, 401, 3403, 394, 1502],
  [3549, 1138, 1005, 2198, 2535, 2757, 3046, 2025, 553, 1533, 1014, 1606, 3206, 2765, 3602, 3135, 1237, 3250, 2553, 2886, 381, 763, 3088, 892, 2528, 2840, 2055, 1715, 141, 926, 2810, 1566],
  [3743, 3002, 3591, 2222, 3110, 2907, 1579, 2738, 481, 3782, 3637, 46, 2143, 3134, 3603, 1604, 633, 745, 2871, 1282, 403, 798, 2885, 2506, 2440, 1659, 2782, 646, 3418, 1947, 2331, 911],
  [3759, 1264, 1911, 3762, 2097, 512, 862, 3489, 1904, 1216, 3345, 1972, 1814, 1082, 167, 486, 3783, 1168, 1270, 3212, 2654, 956, 3224, 2643, 2777, 2841, 3739, 964, 2582, 1903, 160, 94],
  [99, 2549, 3264, 406, 577, 3674, 3462, 3108, 2452, 2857, 2700, 774, 2278, 1424, 2862, 2924, 0, 2073, 3019, 2614, 684, 449, 515, 2802, 385, 1300, 775, 1105, 1096, 1543, 1054, 3045],
  [2880, 1785, 2882, 1628, 2422, 2806, 2771, 634, 1177, 3456, 1398, 3172, 2725, 1810, 1025, 49, 374, 3753, 1377, 927, 1466, 127, 14, 1564, 1721, 405, 510, 2789, 3401, 286, 3581, 3256],
  [625, 269, 1829, 3106, 998, 1310, 1934, 3029, 2713, 1473, 121, 1383, 2863, 1421, 1339, 3373, 3298, 910, 3017, 2146, 3237, 1990, 3279, 596, 2720, 3398, 252, 278, 122, 1812, 2183, 475],
  [1450, 452, 462, 755, 3252, 2949, 3533, 1732, 1582, 2169, 3381, 3415, 657, 349, 3387, 432, 3747, 3484, 2156, 404, 256, 535, 3178, 365, 858, 1673, 104, 221, 759, 732, 612, 487],
  [1777, 3194, 56, 3075, 1991, 648, 223, 3577, 3589, 1320, 827, 1750, 2477, 1839, 3230, 1801, 2992, 762, 3035, 1083, 3625, 2002, 3757, 1187, 3552, 758, 2785, 2037, 3592, 880, 448, 3259],
  [2042, 756, 3667, 1757, 2022, 1657, 1280, 1635, 1698, 2930, 3018, 2866, 3227, 1674, 3204, 3082, 3024, 979, 1108, 2559, 846, 2919, 2426, 2630, 818, 279, 1340, 2994, 1266, 328, 417, 2104],
  [616, 1523, 3051, 2401, 1623, 2879, 2758, 2409, 3209, 2704, 366, 3042, 3099, 68, 301, 191, 1942, 2597, 1027, 1584, 1088, 592, 196, 83, 897, 1307, 1325, 1200, 3594, 2228, 125, 2132],
  [2727, 533, 315, 2979, 3428, 1297, 413, 2624, 3627, 3081, 3023, 2308, 3383, 348, 3518, 1520, 2774, 1864, 2561, 589, 3184, 1218, 3682, 2681, 1913, 420, 1437, 3052, 3468, 1262, 3575, 2493],
  [2634, 945, 2915, 1898, 2855, 3188, 2788, 2125, 1671, 1933, 826, 1781, 3361, 276, 1766, 3226, 1924, 845, 380, 1251, 2112, 983, 1323, 913, 1220, 659, 715, 525, 3367, 3133, 2797, 2767],
  [777, 3365, 2024, 3139, 1531, 786, 2329, 1214, 1838, 3645, 2086, 611, 233, 1478, 3385, 572, 1341, 362, 242, 313, 1173, 824, 1417, 1499, 2605, 2458, 10, 3673, 3210, 970, 292, 2519],
  [1772, 607, 1034, 1874, 2891, 3288, 1735, 2009, 3544, 1222, 2966, 623, 1739, 2499, 3389, 1233, 3092, 505, 2187, 3187, 3109, 673, 1345, 3213, 3399, 1699, 2977, 2286, 2551, 1519, 75, 831],
  [3530, 1720, 925, 3649, 3022, 588, 2764, 1800, 3306, 3048, 3164, 1470, 2835, 3191, 344, 48, 76, 2747, 3218, 820, 1565, 1487, 1405, 1514, 2838, 3225, 3119, 3020, 800, 3480, 2990, 3507],
  [1278, 947, 2444, 685, 3678, 2932, 2018, 1416, 118, 972, 1890, 622, 6, 739, 2196, 1306, 856, 1855, 2769, 795, 2948, 1769, 3421, 2588, 2911, 1194, 1984, 3007, 298, 255, 329, 2632],
  [2850, 1004, 779, 1272, 1190, 173, 175, 1219, 1008, 474, 1039, 2191, 3470, 171, 2362, 2934, 1085, 62, 3347, 3681, 1159, 1333, 2486, 3512, 3173, 576, 1073, 600, 847, 1849, 3294, 3694],
  [2652, 1122, 2928, 1886, 2656, 933, 901, 2674, 1260, 2275, 3208, 2745, 1301, 325, 1064, 2327, 1221, 2271, 3761, 3315, 3395, 3317, 1826, 1119, 2310, 711, 3529, 3476, 115, 2304, 3502, 2108],
  [1213, 1530, 1205, 3791, 638, 610, 568, 1676, 375, 1236, 150, 198, 1610, 479, 1647, 832, 2375, 2826, 263, 3282, 3371, 1522, 39, 3669, 2600, 699, 1563, 1965, 3420, 2529, 1335, 52],
  [1245, 3116, 1030, 1063, 2430, 3137, 1117, 3132, 2298, 2662, 3370, 3348, 573, 2927, 2685, 91, 186, 237, 2319, 1861, 1418, 2954, 2147, 3084, 1360, 3150, 1336, 2958, 1794, 3182, 773, 3391],
  [896, 3774, 3394, 3316, 1202, 1529, 2937, 3192, 894, 2908, 2548, 2749, 1358, 866, 692, 1146, 2723, 3409, 1923, 2468, 1375, 1985, 3450, 2955, 1071, 556, 2812, 754, 3356, 3254, 1880, 1554],
  [302, 627, 2028, 784, 3076, 2680, 3430, 2337, 1776, 3574, 912, 1803, 1309, 2103, 2579, 92, 2534, 2398, 3695, 891, 1093, 676, 3446, 868, 817, 1189, 3414, 2069, 2670, 1176, 3725, 531],
  [2889, 2292, 2032, 1463, 2448, 689, 2854, 3555, 3523, 742, 632, 2431, 3100, 434, 3276, 2631, 1944, 967, 29, 1590, 3323, 1559, 971, 2246, 3229, 1669, 2465, 2068, 2961, 1852, 3578, 1631],
  [2168, 2823, 137, 209, 145, 1758, 2436, 1165, 944, 1349, 1313, 1261, 2171, 3501, 3326, 3503, 1191, 3641, 2208, 3231, 1347, 1361, 2214, 1513, 3287, 2587, 2317, 1163, 26, 443, 3086, 554],
  [1834, 2335, 2602, 3464, 3685, 2516, 1234, 1873, 1171, 3322, 3200, 253, 2640, 2950, 3787, 523, 932, 1136, 3538, 1443, 1415, 1626, 2402, 1954, 3176, 1452, 2483, 1060, 2475, 2752, 2446, 957],
  [3000, 1609, 2095, 3463, 2603, 1248, 379, 2730, 2686, 526, 2517, 1881, 2321, 802, 651, 1121, 288, 106, 1357, 1560, 1003, 418, 3433, 3102, 33, 2983, 3486, 1338, 16, 2910, 2370, 469],
  [1724, 2739, 3719, 3587, 1359, 2984, 2220, 2786, 3004, 3593, 3068, 1372, 2540, 412, 3690, 2234, 299, 2005, 2766, 2798, 1512, 541, 492, 2388, 1535, 1553, 591, 1611, 981, 1290, 502, 2240],
  [3616, 2107, 3710, 593, 2721, 2438, 2472, 1439, 579, 2996, 1053, 3080, 2242, 2285, 703, 72, 1432, 2557, 369, 213, 1682, 2794, 731, 1086, 2177, 3505, 1577, 3707, 1870, 3145, 2726, 3670],
  [1378, 3203, 2340, 275, 163, 53, 2158, 1999, 613, 1630, 444, 569, 35, 129, 552, 1169, 704, 1246, 2099, 3010, 194, 3351, 3647, 1269, 338, 3163, 2853, 814, 712, 2012, 3236, 3748],
  [761, 3283, 3094, 2188, 2567, 3524, 2263, 1625, 2048, 619, 3598, 2165, 138, 2502, 3295, 3442, 753, 1346, 837, 2204, 1075, 472, 1235, 346, 544, 393, 433, 3643, 3708, 2383, 3618, 961],
  [2583, 2668, 1736, 450, 1660, 1892, 524, 3586, 1851, 1940, 1646, 3, 1271, 3454, 1469, 628, 776, 265, 267, 782, 1652, 1164, 740, 1915, 2044, 102, 3742, 2842, 924, 246, 3738, 2784],
  [400, 1425, 1804, 2960, 3679, 2471, 1871, 3751, 900, 2897, 1474, 2406, 2531, 2998, 1578, 2816, 1149, 3314, 2819, 2189, 489, 977, 2247, 2571, 1400, 2356, 2056, 2289, 1451, 2524, 3393, 1912],
  [1900, 2190, 2355, 797, 2149, 1010, 2793, 2832, 23, 1958, 2467, 3534, 1696, 978, 423, 3331, 1098, 1714, 1465]]

def sv : List ℕ := [19, 50, 61, 96, 112, 137, 157]

def K1s : List ℕ := [14850380359425064339000947622681, 15958787851461476723067844273895, 16710179359223466169565908878339, 11551613021332517215682629106759, 14454381116168543564648474611111, 19936902316155777735349816587723, 2817239737909388584495545711099]

def K3s : List ℕ := [1592387373754304308596948629877, 1484023465436905600542392790821, 1675594884854845589171168989445, 1728955979686356890619707908703, 1076610926562244011845699547557, 1319399888806039057482937728817, 1392944856767296075278604565249]

def words : List (List ℕ) := [[1, 0, 2, 2, 2, 2, 2, 0, 1, 1, 0, 2, 2, 0, 1, 1, 1, 1, 1, 0, 2], [2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 2, 2, 2, 0, 2, 2, 2, 0, 2, 0, 1, 0, 2], [1, 0, 1, 1, 0, 1, 0, 2, 2, 2, 2, 0, 1, 1, 1, 1, 0, 2, 0, 2, 2, 0, 2], [1, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1, 1, 0, 2, 2, 2, 0, 1, 0, 1, 0, 2, 0, 2, 2], [1, 0, 2, 2, 2, 2, 2, 0, 2, 0, 2, 2, 0, 2, 2, 2, 0, 1], [1, 1, 0, 1, 0, 2, 0, 2, 2, 0, 1, 1, 0, 1, 0, 2, 0, 2, 2], [1, 1, 1, 1, 1, 0, 2, 2, 2, 2, 2]]

def mx2 : List ℕ := [0, 1, 7, 14, 17, 6, 21, 15, 5, 3, 2, 22, 20, 11, 19, 4, 13, 18, 9, 10, 12, 16, 8]

def mx3 : List ℕ := [0, 22, 21, 20, 6, 12, 16, 13, 11, 19, 18, 17, 3, 5, 2, 10, 9, 14, 15, 4, 8, 7, 1]
/-- The `i`-th base-23 digit. -/
def dg (p i : ℕ) : ℕ := Nat.mod (Nat.div p (Nat.pow 23 i)) 23

theorem dg_def (p i : ℕ) : dg p i = p / 23 ^ i % 23 := rfl

theorem dg_lt (p i : ℕ) : dg p i < 23 := Nat.mod_lt _ (by norm_num)

/-- Pack `f j, f (j+1), …, f (j+k-1)` as base-23 digits. -/
def packR (f : ℕ → ℕ) (j : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => f j + 23 * packR f (j + 1) k

theorem dg_packR (f : ℕ → ℕ) (hf : ∀ i, f i < 23) :
    ∀ (k j i : ℕ), i < k → dg (packR f j k) i = f (j + i) := by
  intro k
  induction k with
  | zero => intro j i hi; omega
  | succ k ih =>
    intro j i hi
    cases i with
    | zero =>
      simp only [dg_def, packR, pow_zero, Nat.div_one, add_zero]
      have := hf j
      omega
    | succ i =>
      have h := ih (j + 1) i (by omega)
      simp only [dg_def, packR] at h ⊢
      have e : (f j + 23 * packR f (j + 1) k) / 23 ^ (i + 1) = packR f (j + 1) k / 23 ^ i := by
        rw [pow_succ', ← Nat.div_div_eq_div_mul]
        have := hf j
        congr 1
        omega
      rw [e, h]
      congr 1
      omega

theorem packR_congr (f f' : ℕ → ℕ) :
    ∀ (k j : ℕ), (∀ i, i < k → f (j + i) = f' (j + i)) → packR f j k = packR f' j k := by
  intro k
  induction k with
  | zero => intro j _; rfl
  | succ k ih =>
    intro j h
    simp only [packR]
    have h0 := h 0 (by omega)
    rw [Nat.add_zero] at h0
    rw [h0, ih (j + 1)]
    · intro i hi
      have := h (i + 1) (by omega)
      rwa [show j + (i + 1) = j + 1 + i by omega] at this
    
/-- Composition on packed tables. -/
def pmul (a b : ℕ) : ℕ := packR (fun i => dg a (dg b i)) 0 23

def ppow (g : ℕ) : ℕ → ℕ
  | 0 => IDP
  | m + 1 => pmul g (ppow g m)

/-- The packed table of a permutation. -/
def pkP (p : Equiv.Perm (Fin 23)) : ℕ :=
  packR (fun i => if h : i < 23 then ((p ⟨i, h⟩ : Fin 23) : ℕ) else 0) 0 23

theorem dg_pkP (p : Equiv.Perm (Fin 23)) (i : Fin 23) : dg (pkP p) i = p i := by
  have hf : ∀ i, (fun i => if h : i < 23 then ((p ⟨i, h⟩ : Fin 23) : ℕ) else 0) i < 23 := by
    intro i
    simp only
    split_ifs
    · exact (p _).2
    · norm_num
  have := dg_packR _ hf 23 0 i i.2
  rw [pkP, this]
  simp

theorem pkP_mul (x y : Equiv.Perm (Fin 23)) : pkP (x * y) = pmul (pkP x) (pkP y) := by
  show packR _ 0 23 = packR (fun i => dg (pkP x) (dg (pkP y) i)) 0 23
  apply packR_congr
  intro i hi
  simp only [zero_add, hi, dif_pos]
  have e1 := dg_pkP y ⟨i, hi⟩
  rw [Fin.val_mk] at e1
  rw [e1, dg_pkP x]
  rfl

theorem tab_getElem (p : Equiv.Perm (Fin 23)) (n : ℕ) (h1 : n < (tab p).length) (hn : n < 23) :
    (tab p)[n]'h1 = (p ⟨n, hn⟩ : ℕ) := by
  have := tget_tab p ⟨n, hn⟩
  unfold tget at this
  rw [List.getD_eq_getElem _ _ h1] at this
  exact this

theorem pkP_inj {x y : Equiv.Perm (Fin 23)} (h : pkP x = pkP y) : x = y := by
  ext i
  have := congrArg (fun n => dg n i) h
  simp only [dg_pkP] at this
  exact this

theorem pkP_conj (g x : Equiv.Perm (Fin 23)) :
    pkP (g * x * g⁻¹) = pmul (pmul (pkP g) (pkP x)) (pkP g⁻¹) := by
  rw [pkP_mul, pkP_mul]

theorem pkP_one : pkP (1 : Equiv.Perm (Fin 23)) = IDP := by decide +kernel

theorem pkP_pow (g : Equiv.Perm (Fin 23)) (m : ℕ) : pkP (g ^ m) = ppow (pkP g) m := by
  induction m with
  | zero => rw [pow_zero]; exact pkP_one
  | succ m ih => rw [pow_succ', pkP_mul, ih]; rfl

theorem perm_pow_iter (h : Equiv.Perm (Fin 23)) (m : ℕ) (y : Fin 23) :
    (((h ^ m) y : Fin 23) : ℕ) = (dg (pkP h))^[m] (y : ℕ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ← ih, pow_succ', Equiv.Perm.coe_mul, Function.comp_apply,
      ← dg_pkP]

theorem conj_pow_apply {l c h : Equiv.Perm (Fin 23)} (hl : l * c = h * l) (m : ℕ) (y : Fin 23) :
    l ((c ^ m) y) = (h ^ m) (l y) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Equiv.Perm.coe_mul, Function.comp_apply, pow_succ', Equiv.Perm.coe_mul,
      Function.comp_apply, ← ih]
    have := congrArg (fun f : Equiv.Perm (Fin 23) => f ((c ^ m) y)) hl
    simpa using this

/-- The table (as a list) of a packed table. -/
def dec (n : ℕ) : Tab := (List.range 23).map (dg n)

theorem tab_eq_dec (p : Equiv.Perm (Fin 23)) : tab p = dec (pkP p) := by
  apply List.ext_getElem
  · simp [tab, dec]
  · intro n h1 h2
    have hn : n < 23 := by simpa [tab] using h1
    simp only [dec, List.getElem_map, List.getElem_range]
    rw [tab_getElem p n h1 hn]
    exact (dg_pkP p ⟨n, hn⟩).symm

/-- Candidate table of a conjugator `l` with `l c = h l`, determined by `l 0`. -/
def phi (M : ℕ) (mx : List ℕ) (a : ℕ) : Tab := mx.map (fun m => (dg M)^[m] a)

theorem tab_eq_phi {l c h : Equiv.Perm (Fin 23)} (hl : l * c = h * l) (mx : List ℕ)
    (hlen : mx.length = 23) (hmx : ∀ x : Fin 23, (c ^ mx.getD x 0) 0 = x) :
    tab l = phi (pkP h) mx (l 0) := by
  apply List.ext_getElem
  · simp [tab, phi, hlen]
  · intro n h1 h2
    have hn : n < 23 := by simpa [tab] using h1
    have hL : (tab l)[n]'h1 = (l ⟨n, hn⟩ : ℕ) := tab_getElem l n h1 hn
    simp only [phi, List.getElem_map]
    refine hL.trans ?_
    have hx := hmx ⟨n, hn⟩
    have e1 := conj_pow_apply hl (mx.getD n 0) 0
    rw [hx] at e1
    rw [e1, perm_pow_iter, List.getD_eq_getElem _ _ (by omega)]

/-! ## Permutations from packed tables -/

theorem packR_dg (n : ℕ) : ∀ k j : ℕ, packR (dg n) j k = n / 23 ^ j % 23 ^ k := by
  intro k
  induction k with
  | zero => intro j; simp [packR, Nat.mod_one]
  | succ k ih =>
    intro j
    simp only [packR, ih]
    have e : n / 23 ^ (j + 1) = n / 23 ^ j / 23 := by
      rw [pow_succ, Nat.div_div_eq_div_mul]
    rw [e, pow_succ' 23 k, Nat.mod_mul]
    rfl

/-- Validity of a packed table: canonical and surjective. -/
def chkPk (n : ℕ) : Bool :=
  decide (n < 23 ^ 23) && (List.range 23).all (fun y => (List.range 23).any (fun i => dg n i == y))

theorem pk_surj {n : ℕ} (h : chkPk n = true) (y : Fin 23) : ∃ i : Fin 23, dg n i = y := by
  simp only [chkPk, Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 y (List.mem_range.2 y.2)
  simp only [List.any_eq_true, beq_iff_eq, List.mem_range] at this
  obtain ⟨i, hi, hiy⟩ := this
  exact ⟨⟨i, hi⟩, hiy⟩

def ofPkFun (n : ℕ) : Fin 23 → Fin 23 := fun i => ⟨dg n i, dg_lt n i⟩

theorem ofPkFun_bij {n : ℕ} (h : chkPk n = true) : Function.Bijective (ofPkFun n) := by
  have hs : Function.Surjective (ofPkFun n) := by
    intro y
    obtain ⟨i, hi⟩ := pk_surj h y
    exact ⟨i, Fin.ext hi⟩
  exact ⟨Finite.injective_iff_surjective.2 hs, hs⟩

noncomputable def ofPk (n : ℕ) : Equiv.Perm (Fin 23) :=
  if h : chkPk n = true then Equiv.ofBijective _ (ofPkFun_bij h) else 1

theorem pkP_ofPk {n : ℕ} (h : chkPk n = true) : pkP (ofPk n) = n := by
  have hlt : n < 23 ^ 23 := by
    simp only [chkPk, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1
  unfold ofPk
  rw [dif_pos h]
  have : pkP (Equiv.ofBijective _ (ofPkFun_bij h)) = packR (dg n) 0 23 := by
    unfold pkP
    apply packR_congr
    intro i hi
    simp only [zero_add, hi, dif_pos]
    rfl
  rw [this, packR_dg]
  simp only [pow_zero, Nat.div_one]
  exact Nat.mod_eq_of_lt hlt

theorem dg_ofPk {n : ℕ} (h : chkPk n = true) (i : Fin 23) : dg n i = ofPk n i := by
  rw [← dg_pkP, pkP_ofPk h]

/-! ## Kernel checks -/

/-- Chunked access (chunks of 32). -/
def chunk (c : List (List ℕ)) (k : ℕ) : ℕ := nthD 0 (nthD [] c (k / 32)) (k % 32)

def Ev (n : ℕ) : ℕ := chunk EN n
def rot (n : ℕ) : ℕ := 23 * (n / 23) + (n % 23 + 1) % 23
def pre (n : ℕ) : ℕ := 23 * (n / 23) + (n % 23 + 22) % 23

def conjP (g gi x : ℕ) : ℕ := pmul (pmul g x) gi


theorem conjP_eq (g gi x : ℕ) : conjP g gi x = packR (fun i => dg g (dg x (dg gi i))) 0 23 := by
  unfold conjP pmul
  apply packR_congr
  intro i hi
  rw [zero_add, dg_packR _ (fun i => dg_lt _ _) 23 0 (dg gi i) (dg_lt _ _), zero_add]

/-- Conjugation by `G1` on packed tables (unrolled for speed). -/
def cj1 (x : ℕ) : ℕ := dg G1 (dg x 10) + 23 * (dg G1 (dg x 22) + 23 * (dg G1 (dg x 7) + 23 * (dg G1 (dg x 15) + 23 * (dg G1 (dg x 20) + 23 * (dg G1 (dg x 5) + 23 * (dg G1 (dg x 19) + 23 * (dg G1 (dg x 2) + 23 * (dg G1 (dg x 8) + 23 * (dg G1 (dg x 9) + 23 * (dg G1 (dg x 0) + 23 * (dg G1 (dg x 11) + 23 * (dg G1 (dg x 12) + 23 * (dg G1 (dg x 13) + 23 * (dg G1 (dg x 18) + 23 * (dg G1 (dg x 3) + 23 * (dg G1 (dg x 16) + 23 * (dg G1 (dg x 21) + 23 * (dg G1 (dg x 14) + 23 * (dg G1 (dg x 6) + 23 * (dg G1 (dg x 4) + 23 * (dg G1 (dg x 17) + 23 * (dg G1 (dg x 1)))))))))))))))))))))))

/-- Conjugation by `G2` on packed tables (unrolled for speed). -/
def cj2 (x : ℕ) : ℕ := dg G2 (dg x 11) + 23 * (dg G2 (dg x 0) + 23 * (dg G2 (dg x 5) + 23 * (dg G2 (dg x 16) + 23 * (dg G2 (dg x 21) + 23 * (dg G2 (dg x 8) + 23 * (dg G2 (dg x 12) + 23 * (dg G2 (dg x 3) + 23 * (dg G2 (dg x 15) + 23 * (dg G2 (dg x 10) + 23 * (dg G2 (dg x 1) + 23 * (dg G2 (dg x 6) + 23 * (dg G2 (dg x 14) + 23 * (dg G2 (dg x 19) + 23 * (dg G2 (dg x 17) + 23 * (dg G2 (dg x 9) + 23 * (dg G2 (dg x 20) + 23 * (dg G2 (dg x 4) + 23 * (dg G2 (dg x 22) + 23 * (dg G2 (dg x 18) + 23 * (dg G2 (dg x 13) + 23 * (dg G2 (dg x 7) + 23 * (dg G2 (dg x 2)))))))))))))))))))))))

/-- Conjugation by `G2I` on packed tables (unrolled for speed). -/
def cj2i (x : ℕ) : ℕ := dg G2I (dg x 1) + 23 * (dg G2I (dg x 10) + 23 * (dg G2I (dg x 22) + 23 * (dg G2I (dg x 7) + 23 * (dg G2I (dg x 17) + 23 * (dg G2I (dg x 2) + 23 * (dg G2I (dg x 11) + 23 * (dg G2I (dg x 21) + 23 * (dg G2I (dg x 5) + 23 * (dg G2I (dg x 15) + 23 * (dg G2I (dg x 9) + 23 * (dg G2I (dg x 0) + 23 * (dg G2I (dg x 6) + 23 * (dg G2I (dg x 20) + 23 * (dg G2I (dg x 12) + 23 * (dg G2I (dg x 8) + 23 * (dg G2I (dg x 3) + 23 * (dg G2I (dg x 14) + 23 * (dg G2I (dg x 19) + 23 * (dg G2I (dg x 13) + 23 * (dg G2I (dg x 16) + 23 * (dg G2I (dg x 4) + 23 * (dg G2I (dg x 18)))))))))))))))))))))))

theorem cj1_eq (x : ℕ) : cj1 x = conjP G1 G1 x := by rw [conjP_eq]; rfl
theorem cj2_eq (x : ℕ) : cj2 x = conjP G2 G2I x := by rw [conjP_eq]; rfl
theorem cj2i_eq (x : ℕ) : cj2i x = conjP G2I G2 x := by rw [conjP_eq]; rfl


theorem pkP_g1 : pkP g₁ = G1 := by decide +kernel
theorem pkP_g2 : pkP g₂ = G2 := by decide +kernel
theorem pkP_g2i : pkP g₂⁻¹ = G2I := by decide +kernel
theorem pkP_g3i : pkP g₃⁻¹ = G3I := by decide +kernel

def clsChk : Bool := (List.range 3795).all fun n =>
  decide (chunk A1N n < 3795) && (cj1 (Ev n) == Ev (chunk A1N n)) &&
  (cj2 (Ev n) == Ev (rot n)) && (cj2i (Ev n) == Ev (pre n))

theorem clsChk_true : clsChk = true := by decide +kernel

theorem Ev_n0 : Ev n0 = G1 := by decide +kernel

/-- Candidate refutation of the representative `i`: no conjugator candidate lies in `M₂₃`. -/
def badB (i : ℕ) : Bool :=
  !(sift (Tget fullTabs) fullLvls (phi (pmul (Ev (23 * i)) G2) mx3 0))

def allBad : Bool := (List.range 165).all fun i => sv.contains i || badB i

theorem allBad_true : allBad = true := by decide +kernel

def wordP (a b c : ℕ) : List ℕ → ℕ
  | [] => IDP
  | l :: w => pmul (if l = 0 then a else if l = 1 then b else c) (wordP a b c w)

def svOne (m : ℕ) : Bool :=
  chkPk (Ev (23 * sv.getD m 0)) && chkPk (K1s.getD m 0) &&
  sift (Tget fullTabs) fullLvls (dec (K1s.getD m 0)) &&
  (pmul (Ev (23 * sv.getD m 0)) (K1s.getD m 0) == pmul (K1s.getD m 0) G1) &&
  chkPk (K3s.getD m 0) && sift (Tget fullTabs) fullLvls (dec (K3s.getD m 0)) &&
  (pmul (pmul (Ev (23 * sv.getD m 0)) G2) (K3s.getD m 0) == pmul (K3s.getD m 0) G3I) &&
  (wordP (Ev (23 * sv.getD m 0)) G2 G2I (words.getD m []) == G1)

theorem svOne_true : ∀ m, m < 7 → svOne m = true := by
  have : (List.range 7).all svOne = true := by decide +kernel
  intro m hm
  simp only [List.all_eq_true, List.mem_range] at this
  exact this m hm

def distChk : Bool := (List.range 7).all fun a => (List.range 7).all fun b =>
  a == b || (List.range 23).all fun t =>
    pmul (ppow G2 t) (Ev (23 * sv.getD a 0)) != pmul (Ev (23 * sv.getD b 0)) (ppow G2 t)

theorem distChk_true : distChk = true := by decide +kernel

theorem hmx3 : (List.range 23).all (fun x => (dg G3I)^[mx3.getD x 0] 0 == x) = true := by
  decide +kernel
theorem hmx2 : (List.range 23).all (fun x => (dg G2)^[mx2.getD x 0] 0 == x) = true := by
  decide +kernel
theorem hlt2 : (List.range 23).all (fun x => decide (mx2.getD x 0 < 23)) = true := by
  decide +kernel
theorem len_mx3 : mx3.length = 23 := by decide +kernel

/-! ## Group-theoretic glue -/

def orb (x : Equiv.Perm (Fin 23) × Equiv.Perm (Fin 23) × Equiv.Perm (Fin 23)) :
    Set (Equiv.Perm (Fin 23) × Equiv.Perm (Fin 23) × Equiv.Perm (Fin 23)) :=
  {y | ∃ k ∈ M23, y = conjTriple k x}

theorem conjTriple_mul (k l : Equiv.Perm (Fin 23))
    (x : Equiv.Perm (Fin 23) × Equiv.Perm (Fin 23) × Equiv.Perm (Fin 23)) :
    conjTriple (k * l) x = conjTriple k (conjTriple l x) := by
  simp [conjTriple, mul_assoc]

theorem conjTriple_one (x : Equiv.Perm (Fin 23) × Equiv.Perm (Fin 23) × Equiv.Perm (Fin 23)) :
    conjTriple 1 x = x := by
  simp [conjTriple]

theorem mem_orb_self (x : Equiv.Perm (Fin 23) × Equiv.Perm (Fin 23) × Equiv.Perm (Fin 23)) :
    x ∈ orb x := ⟨1, M23.one_mem, (conjTriple_one x).symm⟩

theorem orb_conj {k : Equiv.Perm (Fin 23)} (hk : k ∈ M23)
    (x : Equiv.Perm (Fin 23) × Equiv.Perm (Fin 23) × Equiv.Perm (Fin 23)) :
    orb (conjTriple k x) = orb x := by
  ext y
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l * k, M23.mul_mem hl hk, by rw [conjTriple_mul]⟩
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l * k⁻¹, M23.mul_mem hl (M23.inv_mem hk), ?_⟩
    rw [conjTriple_mul, ← conjTriple_mul k⁻¹ k, inv_mul_cancel, conjTriple_one]

theorem classIn_conj {g h k : Equiv.Perm (Fin 23)} (hh : h ∈ classIn g) (hk : k ∈ M23) :
    k * h * k⁻¹ ∈ classIn g := by
  obtain ⟨l, hl, rfl⟩ := hh
  exact ⟨k * l, M23.mul_mem hk hl, by group⟩

theorem classIn_mem {g h : Equiv.Perm (Fin 23)} (hg : g ∈ M23) (hh : h ∈ classIn g) :
    h ∈ M23 := by
  obtain ⟨l, hl, rfl⟩ := hh
  exact M23.mul_mem (M23.mul_mem hl hg) (M23.inv_mem hl)

theorem classIn_of_conj {c h k : Equiv.Perm (Fin 23)} (hk : k ∈ M23) (e : h * k = k * c) :
    h ∈ classIn c := by
  refine ⟨k, hk, ?_⟩
  rw [← e]; group

theorem classIn_inv_of_conj {c h k : Equiv.Perm (Fin 23)} (hk : k ∈ M23) (e : h * k = k * c⁻¹) :
    h⁻¹ ∈ classIn c := by
  refine ⟨k, hk, ?_⟩
  have : h = k * c⁻¹ * k⁻¹ := by rw [← e]; group
  rw [this]; group

theorem g1_inv : g₁⁻¹ = g₁ := by decide +kernel

theorem g1_mem : g₁ ∈ M23 := Subgroup.subset_closure (by simp)
theorem g2_mem : g₂ ∈ M23 := Subgroup.subset_closure (by simp)

theorem prod_eq_one : g₁ * g₂ * g₃ = 1 := by decide +kernel

theorem g3_mem : g₃ ∈ M23 := by
  have : g₃ = (g₁ * g₂)⁻¹ := eq_inv_of_mul_eq_one_right prod_eq_one
  rw [this]
  exact M23.inv_mem (M23.mul_mem g1_mem g2_mem)

/-! ## The class of `g₁` is contained in the listed orbits -/

def Sx (x : Equiv.Perm (Fin 23)) : Prop := ∃ n < 3795, pkP x = Ev n

theorem clsFacts : ∀ n, n < 3795 → chunk A1N n < 3795 ∧ cj1 (Ev n) = Ev (chunk A1N n) ∧
    cj2 (Ev n) = Ev (rot n) ∧ cj2i (Ev n) = Ev (pre n) := by
  have h := clsChk_true
  simp only [clsChk, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  intro n hn
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h n hn
  exact ⟨h1, h2, h3, h4⟩

theorem Sx_conj {g : Equiv.Perm (Fin 23)} {G Gi : ℕ} (hG : pkP g = G) (hGi : pkP g⁻¹ = Gi)
    (f : ℕ → ℕ) (hf : ∀ n, n < 3795 → f n < 3795 ∧ conjP G Gi (Ev n) = Ev (f n))
    {x : Equiv.Perm (Fin 23)} (hx : Sx x) : Sx (g * x * g⁻¹) := by
  obtain ⟨n, hn, hxn⟩ := hx
  refine ⟨f n, (hf n hn).1, ?_⟩
  rw [pkP_conj, hxn, hG, hGi]
  exact (hf n hn).2

theorem rot_lt (n : ℕ) (hn : n < 3795) : rot n < 3795 := by unfold rot; omega
theorem pre_lt (n : ℕ) (hn : n < 3795) : pre n < 3795 := by unfold pre; omega

theorem Sx_g1 : Sx g₁ := ⟨n0, by norm_num [n0], by rw [pkP_g1]; exact Ev_n0.symm⟩

theorem cls_sub {k : Equiv.Perm (Fin 23)} (hk : k ∈ M23) :
    ∀ x, Sx x → Sx (k * x * k⁻¹) := by
  unfold M23 at hk
  refine Subgroup.closure_induction'' (p := fun k _ => ∀ x, Sx x → Sx (k * x * k⁻¹)) ?_ ?_ ?_ ?_ hk
  · intro g hg x hx
    rcases hg with rfl | rfl
    · refine Sx_conj (G := G1) (Gi := G1) pkP_g1 (by rw [g1_inv]; exact pkP_g1) (fun n => chunk A1N n) ?_ hx
      intro n hn
      obtain ⟨a, b, _, _⟩ := clsFacts n hn
      exact ⟨a, by rw [← cj1_eq]; exact b⟩
    · refine Sx_conj (G := G2) (Gi := G2I) pkP_g2 pkP_g2i rot ?_ hx
      intro n hn
      obtain ⟨_, _, b, _⟩ := clsFacts n hn
      exact ⟨rot_lt n hn, by rw [← cj2_eq]; exact b⟩
  · intro g hg x hx
    rcases hg with rfl | rfl
    · rw [g1_inv]
      refine Sx_conj (G := G1) (Gi := G1) pkP_g1 (by rw [g1_inv]; exact pkP_g1) (fun n => chunk A1N n) ?_ hx
      intro n hn
      obtain ⟨a, b, _, _⟩ := clsFacts n hn
      exact ⟨a, by rw [← cj1_eq]; exact b⟩
    · refine Sx_conj (G := G2I) (Gi := G2) pkP_g2i (by rw [inv_inv]; exact pkP_g2) pre ?_ hx
      intro n hn
      obtain ⟨_, _, _, b⟩ := clsFacts n hn
      exact ⟨pre_lt n hn, by rw [← cj2i_eq]; exact b⟩
  · intro x hx
    simpa using hx
  · intro x y _ _ hx hy z hz
    have := hx _ (hy z hz)
    have e : x * (y * z * y⁻¹) * x⁻¹ = x * y * z * (x * y)⁻¹ := by group
    rw [e] at this
    exact this

theorem rotate_down : ∀ j i : ℕ, j < 23 → i < 165 → ∀ h : Equiv.Perm (Fin 23),
    pkP h = Ev (23 * i + j) →
    ∃ u ∈ M23, u * g₂ = g₂ * u ∧ pkP (u * h * u⁻¹) = Ev (23 * i) := by
  intro j
  induction j with
  | zero =>
    intro i _ _ h hh
    exact ⟨1, M23.one_mem, by simp, by simpa using hh⟩
  | succ j ih =>
    intro i hj hi h hh
    have hn : 23 * i + (j + 1) < 3795 := by omega
    obtain ⟨_, _, _, b⟩ := clsFacts _ hn
    have hh' : pkP (g₂⁻¹ * h * g₂⁻¹⁻¹) = Ev (23 * i + j) := by
      rw [pkP_conj, hh, pkP_g2i, inv_inv, pkP_g2]
      have : pmul (pmul G2I (Ev (23 * i + (j + 1)))) G2 = Ev (pre (23 * i + (j + 1))) := by
        rw [show pmul (pmul G2I (Ev (23 * i + (j + 1)))) G2 = conjP G2I G2 _ from rfl, ← cj2i_eq]
        exact b
      have hp : pre (23 * i + (j + 1)) = 23 * i + j := by unfold pre; omega
      rw [this, hp]
    obtain ⟨u1, hu1, hc, ht⟩ := ih i (by omega) hi _ hh'
    refine ⟨u1 * g₂⁻¹, M23.mul_mem hu1 (M23.inv_mem g2_mem), ?_, ?_⟩
    · have e : g₂ * (u1 * g₂⁻¹) = u1 := by
        rw [← mul_assoc, ← hc, mul_assoc, mul_inv_cancel, mul_one]
      rw [e, mul_assoc, inv_mul_cancel, mul_one]
    · have e : u1 * g₂⁻¹ * h * (u1 * g₂⁻¹)⁻¹ = u1 * (g₂⁻¹ * h * g₂⁻¹⁻¹) * u1⁻¹ := by group
      rw [e]; exact ht

/-! ## Non-conjugacy to `g₃` for the bad representatives -/

theorem hmx3' : ∀ x : Fin 23, (g₃⁻¹ ^ mx3.getD x 0) 0 = x := by
  have h := hmx3
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  intro x
  apply Fin.ext
  rw [perm_pow_iter, pkP_g3i]
  simpa using h x x.2

theorem hmx2' : ∀ x : Fin 23, (g₂ ^ mx2.getD x 0) 0 = x := by
  have h := hmx2
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  intro x
  apply Fin.ext
  rw [perm_pow_iter, pkP_g2]
  simpa using h x x.2

theorem hlt2' : ∀ x : Fin 23, mx2.getD x 0 < 23 := by
  have h := hlt2
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  intro x
  exact h x x.2

theorem bad_sound {l h : Equiv.Perm (Fin 23)} (hl : l ∈ M23) (e : l * g₃⁻¹ = h * l) :
    ∃ l' ∈ M23, l' * g₃⁻¹ = h * l' ∧ l' 0 = 0 := by
  set t := mx3.getD (l⁻¹ 0) 0 with ht
  have h0 : (g₃⁻¹ ^ t) 0 = l⁻¹ 0 := hmx3' _
  refine ⟨l * g₃⁻¹ ^ t, M23.mul_mem hl (M23.pow_mem (M23.inv_mem g3_mem) t), ?_, ?_⟩
  · calc l * g₃⁻¹ ^ t * g₃⁻¹ = l * (g₃⁻¹ ^ t * g₃⁻¹) := mul_assoc _ _ _
      _ = l * (g₃⁻¹ * g₃⁻¹ ^ t) := by rw [← pow_succ, pow_succ']
      _ = (l * g₃⁻¹) * g₃⁻¹ ^ t := (mul_assoc _ _ _).symm
      _ = h * (l * g₃⁻¹ ^ t) := by rw [e, mul_assoc]
  · rw [Equiv.Perm.coe_mul, Function.comp_apply, h0]
    simp

theorem bad_contra {i : ℕ} (_hi : i < 165) (hb : badB i = true) {h1 h3 : Equiv.Perm (Fin 23)}
    (hp : pkP h1 = Ev (23 * i)) (h3c : h3 ∈ classIn g₃) (hprod : h1 * g₂ * h3 = 1) : False := by
  obtain ⟨l, hl, hl3⟩ := h3c
  have e0 : h1 * g₂ = h3⁻¹ := eq_inv_of_mul_eq_one_left hprod
  have e : l * g₃⁻¹ = (h1 * g₂) * l := by
    rw [e0, hl3]; group
  obtain ⟨l', hl', e', h0⟩ := bad_sound hl e
  have ht := tab_eq_phi e' mx3 len_mx3 hmx3'
  rw [h0, pkP_mul, hp, pkP_g2] at ht
  have hs := (M23Cert.mem_M23_iff_sift_full l').1 hl'
  rw [ht] at hs
  have h00 : ((0 : Fin 23) : ℕ) = 0 := rfl
  rw [h00] at hs
  unfold badB at hb
  rw [Bool.not_eq_true'] at hb
  rw [hb] at hs
  exact Bool.noConfusion hs

/-! ## The seven representatives -/

noncomputable def Rm (m : Fin 7) : Equiv.Perm (Fin 23) := ofPk (Ev (23 * sv.getD m 0))

noncomputable def F (m : Fin 7) :
    Equiv.Perm (Fin 23) × Equiv.Perm (Fin 23) × Equiv.Perm (Fin 23) :=
  (Rm m, g₂, (Rm m * g₂)⁻¹)

theorem svFacts (m : Fin 7) :
    chkPk (Ev (23 * sv.getD m 0)) = true ∧ chkPk (K1s.getD m 0) = true ∧
    sift (Tget fullTabs) fullLvls (dec (K1s.getD m 0)) = true ∧
    pmul (Ev (23 * sv.getD m 0)) (K1s.getD m 0) = pmul (K1s.getD m 0) G1 ∧
    chkPk (K3s.getD m 0) = true ∧ sift (Tget fullTabs) fullLvls (dec (K3s.getD m 0)) = true ∧
    pmul (pmul (Ev (23 * sv.getD m 0)) G2) (K3s.getD m 0) = pmul (K3s.getD m 0) G3I ∧
    wordP (Ev (23 * sv.getD m 0)) G2 G2I (words.getD m []) = G1 := by
  have h := svOne_true m m.2
  simp only [svOne, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, i⟩ := h
  exact ⟨a, b, c, d, e, f, g, i⟩

theorem ofPk_mem {n : ℕ} (hc : chkPk n = true)
    (hs : sift (Tget fullTabs) fullLvls (dec n) = true) : ofPk n ∈ M23 := by
  apply M23Cert.mem_M23_of_sift_full
  rw [tab_eq_dec, pkP_ofPk hc]
  exact hs

theorem pkP_Rm (m : Fin 7) : pkP (Rm m) = Ev (23 * sv.getD m 0) :=
  pkP_ofPk (svFacts m).1

theorem Rm_cls (m : Fin 7) : Rm m ∈ classIn g₁ := by
  obtain ⟨_, b, c, d, _⟩ := svFacts m
  refine classIn_of_conj (k := ofPk (K1s.getD m 0)) (ofPk_mem b c) ?_
  apply pkP_inj
  rw [pkP_mul, pkP_mul, pkP_Rm, pkP_ofPk b, pkP_g1]
  exact d

theorem h3_cls (m : Fin 7) : (Rm m * g₂)⁻¹ ∈ classIn g₃ := by
  obtain ⟨_, _, _, _, e, f, g, _⟩ := svFacts m
  refine classIn_inv_of_conj (k := ofPk (K3s.getD m 0)) (ofPk_mem e f) ?_
  apply pkP_inj
  rw [pkP_mul, pkP_mul, pkP_mul, pkP_Rm, pkP_ofPk e, pkP_g2, pkP_g3i]
  exact g

def wordPerm (a b c : Equiv.Perm (Fin 23)) : List ℕ → Equiv.Perm (Fin 23)
  | [] => 1
  | l :: w => (if l = 0 then a else if l = 1 then b else c) * wordPerm a b c w

theorem pkP_wordPerm (a b c : Equiv.Perm (Fin 23)) (w : List ℕ) :
    pkP (wordPerm a b c w) = wordP (pkP a) (pkP b) (pkP c) w := by
  induction w with
  | nil => simp only [wordPerm, wordP]; exact pkP_one
  | cons l w ih =>
    have e : pkP (if l = 0 then a else if l = 1 then b else c) =
        (if l = 0 then pkP a else if l = 1 then pkP b else pkP c) := by
      split_ifs <;> rfl
    rw [wordPerm, wordP, pkP_mul, ih, e]

theorem wordPerm_mem (H : Subgroup (Equiv.Perm (Fin 23))) {a b c : Equiv.Perm (Fin 23)}
    (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) (w : List ℕ) : wordPerm a b c w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons l w ih =>
    simp only [wordPerm]
    refine H.mul_mem ?_ ih
    split_ifs <;> assumption

theorem gen_eq (m : Fin 7) : Subgroup.closure {Rm m, g₂, (Rm m * g₂)⁻¹} = M23 := by
  have hR : Rm m ∈ M23 := classIn_mem g1_mem (Rm_cls m)
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hR
    · exact g2_mem
    · exact M23.inv_mem (M23.mul_mem hR g2_mem)
  · unfold M23
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    have hS : ∀ y ∈ ({Rm m, g₂, (Rm m * g₂)⁻¹} : Set (Equiv.Perm (Fin 23))),
        y ∈ Subgroup.closure {Rm m, g₂, (Rm m * g₂)⁻¹} := fun y hy => Subgroup.subset_closure hy
    rcases hx with rfl | rfl
    · have hw : g₁ = wordPerm (Rm m) g₂ g₂⁻¹ (words.getD m []) := by
        apply pkP_inj
        rw [pkP_wordPerm, pkP_Rm, pkP_g2, pkP_g2i, pkP_g1]
        exact (svFacts m).2.2.2.2.2.2.2.symm
      rw [SetLike.mem_coe, hw]
      exact wordPerm_mem _ (hS _ (by simp)) (hS _ (by simp)) (Subgroup.inv_mem _ (hS _ (by simp))) _
    · exact hS _ (by simp)

theorem F_mem (m : Fin 7) : F m ∈ sigmaC := by
  refine ⟨Rm_cls m, ?_, h3_cls m, ?_, gen_eq m⟩
  · show g₂ ∈ classIn g₂
    exact ⟨1, M23.one_mem, by simp⟩
  · show Rm m * g₂ * (Rm m * g₂)⁻¹ = 1
    exact mul_inv_cancel _

/-! ## The seven orbits are pairwise distinct -/

theorem dist_facts (a b : Fin 7) (hab : a ≠ b) (t : ℕ) (ht : t < 23) :
    pmul (ppow G2 t) (Ev (23 * sv.getD a 0)) ≠ pmul (Ev (23 * sv.getD b 0)) (ppow G2 t) := by
  have h := distChk_true
  simp only [distChk, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq] at h
  rcases h a a.2 b b.2 with hab' | h2
  · exact absurd (Fin.ext hab') hab
  · exact h2 t ht

theorem eq_pow_of_comm {k : Equiv.Perm (Fin 23)} (hk : k * g₂ = g₂ * k) :
    k = g₂ ^ (mx2.getD (k 0) 0) := by
  apply Equiv.ext
  intro x
  have e1 := conj_pow_apply hk (mx2.getD x 0) 0
  have e3 : (g₂ ^ (mx2.getD x 0)) 0 = x := hmx2' x
  have e2 : (g₂ ^ (mx2.getD (k 0) 0)) 0 = k 0 := hmx2' (k 0)
  generalize mx2.getD x 0 = m at e1 e3
  generalize mx2.getD (k 0) 0 = t at e2 ⊢
  rw [e3] at e1
  calc k x = (g₂ ^ m) (k 0) := e1
    _ = (g₂ ^ m) ((g₂ ^ t) 0) := by rw [e2]
    _ = (g₂ ^ t) ((g₂ ^ m) 0) := by
      rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← pow_add, ← pow_add, add_comm]
    _ = (g₂ ^ t) x := by rw [e3]

theorem orb_F_inj : Function.Injective (fun m : Fin 7 => orb (F m)) := by
  intro a b hab
  by_contra hne
  have h1 : F b ∈ orb (F a) := by
    have : F b ∈ orb (F b) := mem_orb_self _
    simp only at hab
    rw [← hab] at this
    exact this
  obtain ⟨k, hk, hkF⟩ := h1
  have c1 : Rm b = k * Rm a * k⁻¹ := congrArg (fun x => x.1) hkF
  have c2 : g₂ = k * g₂ * k⁻¹ := congrArg (fun x => x.2.1) hkF
  have hc : k * g₂ = g₂ * k := by
    calc k * g₂ = (k * g₂ * k⁻¹) * k := by group
      _ = g₂ * k := by rw [← c2]
  have hr : k * Rm a = Rm b * k := by
    calc k * Rm a = (k * Rm a * k⁻¹) * k := by group
      _ = Rm b * k := by rw [← c1]
  have hk' := eq_pow_of_comm hc
  rw [hk'] at hr
  have ht : mx2.getD (k 0) 0 < 23 := hlt2' _
  have := congrArg pkP hr
  rw [pkP_mul, pkP_mul, pkP_pow, pkP_g2, pkP_Rm, pkP_Rm] at this
  exact dist_facts a b hne _ ht this

/-! ## Every orbit is one of the seven -/

theorem main2 {h1 h3 : Equiv.Perm (Fin 23)} (h1c : h1 ∈ classIn g₁) (h3c : h3 ∈ classIn g₃)
    (hprod : h1 * g₂ * h3 = 1) : ∃ m : Fin 7, orb (h1, g₂, h3) = orb (F m) := by
  have hS : Sx h1 := by
    obtain ⟨k, hk, rfl⟩ := h1c
    exact cls_sub hk g₁ Sx_g1
  obtain ⟨n, hn, hpn⟩ := hS
  have hi : n / 23 < 165 := by omega
  have hn' : n = 23 * (n / 23) + n % 23 := by omega
  obtain ⟨u, hu, huc, hpu⟩ := rotate_down (n % 23) (n / 23) (by omega) hi h1 (by rw [← hn']; exact hpn)
  set i := n / 23 with hidef
  have hug : u * g₂ * u⁻¹ = g₂ := by rw [huc]; group
  have horb : orb (h1, g₂, h3) = orb (u * h1 * u⁻¹, g₂, u * h3 * u⁻¹) := by
    have : conjTriple u (h1, g₂, h3) = (u * h1 * u⁻¹, g₂, u * h3 * u⁻¹) := by
      simp only [conjTriple, hug]
    rw [← this, orb_conj hu]
  have h3c' := classIn_conj h3c hu
  have hprod' : (u * h1 * u⁻¹) * g₂ * (u * h3 * u⁻¹) = 1 := by
    calc (u * h1 * u⁻¹) * g₂ * (u * h3 * u⁻¹)
        = u * h1 * u⁻¹ * (u * g₂ * u⁻¹) * (u * h3 * u⁻¹) := by rw [hug]
      _ = u * (h1 * g₂ * h3) * u⁻¹ := by group
      _ = 1 := by rw [hprod]; group
  have hab := allBad_true
  simp only [allBad, List.all_eq_true, List.mem_range, Bool.or_eq_true] at hab
  rcases hab i hi with hs | hb
  · have hmem : i ∈ sv := List.contains_iff_mem.1 hs
    obtain ⟨j, hj, hji⟩ := List.mem_iff_getElem.1 hmem
    have hlen : sv.length = 7 := by decide +kernel
    refine ⟨⟨j, by omega⟩, ?_⟩
    rw [horb]
    have hm : sv.getD j 0 = i := by rw [List.getD_eq_getElem _ _ hj]; exact hji
    have e1 : u * h1 * u⁻¹ = Rm ⟨j, by omega⟩ := by
      apply pkP_inj
      rw [hpu, pkP_Rm]
      show _ = Ev (23 * sv.getD j 0)
      rw [hm]
    have e3 : u * h3 * u⁻¹ = (Rm ⟨j, by omega⟩ * g₂)⁻¹ := by
      rw [← e1]
      exact eq_inv_of_mul_eq_one_right hprod'
    show orb (u * h1 * u⁻¹, g₂, u * h3 * u⁻¹) = orb (Rm ⟨j, _⟩, g₂, (Rm ⟨j, _⟩ * g₂)⁻¹)
    rw [e1, e3]
  · exact (bad_contra hi hb hpu h3c' hprod').elim

theorem nielsen_eq : nielsenClass = Set.range (fun m : Fin 7 => orb (F m)) := by
  ext s
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, ⟨h1c, h2c, h3c, hprod, -⟩, rfl⟩
    change h1 ∈ classIn g₁ at h1c
    change h2 ∈ classIn g₂ at h2c
    change h3 ∈ classIn g₃ at h3c
    change h1 * h2 * h3 = 1 at hprod
    obtain ⟨k, hk, rfl⟩ := h2c
    have hk' : k⁻¹ ∈ M23 := M23.inv_mem hk
    obtain ⟨m, hm⟩ := main2 (classIn_conj h1c hk') (classIn_conj h3c hk')
      (by
        calc k⁻¹ * h1 * k⁻¹⁻¹ * g₂ * (k⁻¹ * h3 * k⁻¹⁻¹)
            = k⁻¹ * (h1 * (k * g₂ * k⁻¹) * h3) * k := by group
          _ = 1 := by rw [hprod]; group)
    refine ⟨m, ?_⟩
    show orb (F m) = orb (h1, k * g₂ * k⁻¹, h3)
    rw [← hm]
    have : conjTriple k⁻¹ (h1, k * g₂ * k⁻¹, h3) = (k⁻¹ * h1 * k⁻¹⁻¹, g₂, k⁻¹ * h3 * k⁻¹⁻¹) := by
      simp only [conjTriple]
      refine Prod.ext rfl (Prod.ext ?_ rfl)
      group
    rw [← this, orb_conj hk']
  · rintro ⟨m, rfl⟩
    exact ⟨F m, F_mem m, rfl⟩

end NCls

open NCls in
theorem solution : nielsenClass.ncard = 7 := by
  rw [nielsen_eq, Set.ncard_range_of_injective orb_F_inj]
  simp

