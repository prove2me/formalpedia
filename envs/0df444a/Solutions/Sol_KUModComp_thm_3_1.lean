-- Prove2me | solution 1 for KUModComp.thm_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T09:23:43.302737+00:00
-- url     : https://prove2.me/submissions/17966650-accd-4bc2-b55b-4e6c7a6c4e53

import Mathlib
import Definitions.Def_KUModComp_mmeSpec
import Definitions.Def_KUModComp_modCompSpec
import Definitions.Def_KUModComp_SLP

/-! S1b: a code-generation monad with Hoare triples for KUModComp SLPs (67f1a882). -/

set_option autoImplicit false
set_option linter.all false

namespace KUModComp
namespace KUDecomp

/-- A program generator: given the next free register index, produce a result, code, and the
next free index. -/
def Gen (α : Type) : Type := ℕ → α × List Instr × ℕ

def Gen.pure {α : Type} (a : α) : Gen α := fun n => (a, [], n)

def Gen.bind {α β : Type} (g : Gen α) (f : α → Gen β) : Gen β := fun n =>
  ((f (g n).1 (g n).2.2).1, (g n).2.1 ++ (f (g n).1 (g n).2.2).2.1, (f (g n).1 (g n).2.2).2.2)

/-- Emit one single-result instruction; returns the index of its result register. -/
def Gen.emit (i : Instr) : Gen ℕ := fun n => (n, [i], n + 1)

/-- Values held by registers are stable under appending: `r` holds `v` in `regs`. -/
def Holds {R : Type*} [CommRing R] (regs : List R) (r : ℕ) (v : R) : Prop :=
  r < regs.length ∧ regs.getD r 0 = v

/-- A predicate on register files that survives appending registers. -/
def Stable {R : Type*} (P : List R → Prop) : Prop := ∀ regs new, P regs → P (regs ++ new)

/-- Hoare triple: from any register file satisfying `P`, running the generated code appends
registers up to the announced next index and establishes `Q`. -/
def Triple {R : Type*} [CommRing R] (ι : R → R) {α : Type} (g : Gen α) (P : List R → Prop)
    (Q : α → List R → Prop) : Prop :=
  ∀ regs : List R, P regs → ∃ new : List R,
    (g regs.length).2.1.foldl (step ι) regs = regs ++ new ∧
    (regs ++ new).length = (g regs.length).2.2 ∧ Q (g regs.length).1 (regs ++ new)

theorem holds_append {R : Type*} [CommRing R] (regs new : List R) (r : ℕ) (v : R) (h : Holds regs r v) :
    Holds (regs ++ new) r v := by
  have h1 := h.1
  refine ⟨by simp; omega, ?_⟩
  rw [List.getD_append _ _ _ _ h.1]; exact h.2

theorem holds_reg {R : Type*} [CommRing R] (regs : List R) (r : ℕ) (v : R) (h : Holds regs r v) :
    reg regs r = v := h.2

theorem triple_pure {R : Type*} [CommRing R] (ι : R → R) {α : Type} (a : α)
    (P : List R → Prop) (Q : α → List R → Prop) (h : ∀ regs, P regs → Q a regs) :
    Triple ι (Gen.pure a) P Q := by
  intro regs hP
  exact ⟨[], by simp [Gen.pure], by simp [Gen.pure], by simpa [Gen.pure] using h regs hP⟩

theorem triple_bind {R : Type*} [CommRing R] (ι : R → R) {α β : Type} (g : Gen α)
    (f : α → Gen β) (P : List R → Prop) (Q : α → List R → Prop) (S : β → List R → Prop)
    (hg : Triple ι g P Q) (hf : ∀ a, Triple ι (f a) (Q a) S) :
    Triple ι (Gen.bind g f) P S := by
  intro regs hP
  obtain ⟨n₁, c₁, l₁, q₁⟩ := hg regs hP
  obtain ⟨n₂, c₂, l₂, q₂⟩ := hf (g regs.length).1 (regs ++ n₁) q₁
  rw [l₁] at c₂ l₂ q₂
  refine ⟨n₁ ++ n₂, ?_, ?_, ?_⟩
  · simp only [Gen.bind]
    rw [List.foldl_append, c₁, c₂, List.append_assoc]
  · simpa [Gen.bind, List.append_assoc] using l₂
  · simpa [Gen.bind, List.append_assoc] using q₂

theorem triple_emit_add {R : Type*} [CommRing R] (ι : R → R) (i j : ℕ) (a b : R)
    (P : List R → Prop) (hP : Stable P) (hi : ∀ regs, P regs → Holds regs i a)
    (hj : ∀ regs, P regs → Holds regs j b) :
    Triple ι (Gen.emit (.add i j)) P (fun r regs => P regs ∧ Holds regs r (a + b)) := by
  intro regs h
  refine ⟨[reg regs i + reg regs j], rfl, by simp [Gen.emit], hP _ _ h, ?_⟩
  refine ⟨by simp [Gen.emit], ?_⟩
  simp only [Gen.emit]
  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
  simp [holds_reg _ _ _ (hi regs h), holds_reg _ _ _ (hj regs h)]

theorem triple_emit_mul {R : Type*} [CommRing R] (ι : R → R) (i j : ℕ) (a b : R)
    (P : List R → Prop) (hP : Stable P) (hi : ∀ regs, P regs → Holds regs i a)
    (hj : ∀ regs, P regs → Holds regs j b) :
    Triple ι (Gen.emit (.mul i j)) P (fun r regs => P regs ∧ Holds regs r (a * b)) := by
  intro regs h
  refine ⟨[reg regs i * reg regs j], rfl, by simp [Gen.emit], hP _ _ h, ?_⟩
  refine ⟨by simp [Gen.emit], ?_⟩
  simp only [Gen.emit]
  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
  simp [holds_reg _ _ _ (hi regs h), holds_reg _ _ _ (hj regs h)]


/-! ## Vectors of registers -/

def HoldsVec {R : Type*} [CommRing R] (regs : List R) (rs : List ℕ) (vs : List R) : Prop :=
  List.Forall₂ (Holds regs) rs vs

theorem holdsVec_append {R : Type*} [CommRing R] (regs new : List R) (rs : List ℕ) (vs : List R)
    (h : HoldsVec regs rs vs) : HoldsVec (regs ++ new) rs vs :=
  List.Forall₂.imp (fun r v hv => holds_append regs new r v hv) h

theorem stable_and {R : Type*} [CommRing R] (P Q : List R → Prop) (hP : Stable P)
    (hQ : Stable Q) : Stable (fun regs => P regs ∧ Q regs) :=
  fun regs new h => ⟨hP regs new h.1, hQ regs new h.2⟩

theorem stable_holds {R : Type*} [CommRing R] (r : ℕ) (v : R) :
    Stable (fun regs : List R => Holds regs r v) :=
  fun regs new h => holds_append regs new r v h

theorem stable_holdsVec {R : Type*} [CommRing R] (rs : List ℕ) (vs : List R) :
    Stable (fun regs : List R => HoldsVec regs rs vs) :=
  fun regs new h => holdsVec_append regs new rs vs h

theorem triple_of_false {R : Type*} [CommRing R] (ι : R → R) {α : Type} (g : Gen α)
    (P : List R → Prop) (Q : α → List R → Prop) (h : ∀ regs, P regs → False) :
    Triple ι g P Q := fun regs hP => (h regs hP).elim

/-- Elementwise sum of two register vectors. -/
def vecAdd : List ℕ → List ℕ → Gen (List ℕ)
  | i :: is, j :: js =>
      Gen.bind (Gen.emit (.add i j)) fun r => Gen.bind (vecAdd is js) fun rs => Gen.pure (r :: rs)
  | _, _ => Gen.pure []

theorem triple_vecAdd {R : Type*} [CommRing R] (ι : R → R) :
    ∀ (is js : List ℕ) (as bs : List R) (P : List R → Prop), Stable P →
      (∀ regs, P regs → HoldsVec regs is as) → (∀ regs, P regs → HoldsVec regs js bs) →
      Triple ι (vecAdd is js) P
        (fun out regs => P regs ∧ HoldsVec regs out (List.zipWith (· + ·) as bs))
  | i :: is, j :: js, a :: as, b :: bs, P, hP, hx, hy => by
    have hxi : ∀ regs, P regs → Holds regs i a := fun regs h => (List.forall₂_cons.1 (hx regs h)).1
    have hyj : ∀ regs, P regs → Holds regs j b := fun regs h => (List.forall₂_cons.1 (hy regs h)).1
    refine triple_bind ι _ _ P _ _ (triple_emit_add ι i j a b P hP hxi hyj) fun r => ?_
    have hP' : Stable (fun regs => P regs ∧ Holds regs r (a + b)) :=
      stable_and _ _ hP (stable_holds r (a + b))
    refine triple_bind ι _ _ _ _ _ (triple_vecAdd ι is js as bs _ hP'
      (fun regs h => (List.forall₂_cons.1 (hx regs h.1)).2)
      (fun regs h => (List.forall₂_cons.1 (hy regs h.1)).2)) fun rs => ?_
    refine triple_pure ι _ _ _ fun regs h => ⟨h.1.1, ?_⟩
    exact List.Forall₂.cons h.1.2 h.2
  | [], _, as, bs, P, _, hx, _ => by
    cases hx' : as with
    | nil =>
      exact triple_pure ι _ _ _ fun regs h => ⟨h, by simp [HoldsVec]⟩
    | cons a as' =>
      exact triple_pure ι _ _ _ fun regs h => absurd (hx regs h) (by rw [hx']; simp [HoldsVec])
  | _ :: _, [], as, bs, P, _, _, hy => by
    cases hy' : bs with
    | nil =>
      exact triple_pure ι _ _ _ fun regs h => ⟨h, by simp [HoldsVec]⟩
    | cons b bs' =>
      exact triple_pure ι _ _ _ fun regs h => absurd (hy regs h) (by rw [hy']; simp [HoldsVec])
  | _ :: _, _ :: _, [], bs, P, _, hx, _ => by
    exact triple_of_false ι _ _ _ fun regs h => absurd (hx regs h) (by simp [HoldsVec])
  | _ :: _, _ :: _, _ :: _, [], P, _, _, hy => by
    exact triple_of_false ι _ _ _ fun regs h => absurd (hy regs h) (by simp [HoldsVec])

/-- Ring-operation count of generated code. -/
def Gen.ops {α : Type} (g : Gen α) (n : ℕ) : ℕ := ringOps ⟨(g n).2.1, []⟩

theorem ops_bind {α β : Type} (g : Gen α) (f : α → Gen β) (n : ℕ) :
    (Gen.bind g f).ops n = g.ops n + (f (g n).1).ops (g n).2.2 := by
  simp only [Gen.ops, Gen.bind]
  exact ringOps_append' _ _
where
  ringOps_append' (c₁ c₂ : List Instr) :
      ringOps ⟨c₁ ++ c₂, []⟩ = ringOps ⟨c₁, []⟩ + ringOps ⟨c₂, []⟩ := by
    simp [ringOps, List.filter_append]

/-! ## S1c: remaining emit triples, ops lemmas, run extraction -/

theorem triple_emit_val {R : Type*} [CommRing R] (ι : R → R) (i : Instr) (f : List R → R)
    (hstep : ∀ regs, step ι regs i = regs ++ [f regs]) (v : R)
    (P : List R → Prop) (hP : Stable P) (hv : ∀ regs, P regs → f regs = v) :
    Triple ι (Gen.emit i) P (fun r regs => P regs ∧ Holds regs r v) := by
  intro regs h
  refine ⟨[f regs], by simp [Gen.emit, hstep], by simp [Gen.emit], hP _ _ h, ?_⟩
  refine ⟨by simp [Gen.emit], ?_⟩
  simp only [Gen.emit]
  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
  simp [hv regs h]

theorem triple_emit_zero {R : Type*} [CommRing R] (ι : R → R) (P : List R → Prop)
    (hP : Stable P) : Triple ι (Gen.emit .zero) P (fun r regs => P regs ∧ Holds regs r 0) :=
  triple_emit_val ι .zero (fun _ => 0) (fun _ => rfl) 0 P hP (fun _ _ => rfl)

theorem triple_emit_one {R : Type*} [CommRing R] (ι : R → R) (P : List R → Prop)
    (hP : Stable P) : Triple ι (Gen.emit .one) P (fun r regs => P regs ∧ Holds regs r 1) :=
  triple_emit_val ι .one (fun _ => 1) (fun _ => rfl) 1 P hP (fun _ _ => rfl)

theorem triple_emit_neg {R : Type*} [CommRing R] (ι : R → R) (i : ℕ) (a : R)
    (P : List R → Prop) (hP : Stable P) (hi : ∀ regs, P regs → Holds regs i a) :
    Triple ι (Gen.emit (.neg i)) P (fun r regs => P regs ∧ Holds regs r (-a)) :=
  triple_emit_val ι (.neg i) (fun regs => -reg regs i) (fun _ => rfl) (-a) P hP
    (fun regs h => by rw [holds_reg _ _ _ (hi regs h)])

theorem triple_emit_inv {R : Type*} [CommRing R] (ι : R → R) (i : ℕ) (a : R)
    (P : List R → Prop) (hP : Stable P) (hi : ∀ regs, P regs → Holds regs i a) :
    Triple ι (Gen.emit (.inv i)) P (fun r regs => P regs ∧ Holds regs r (ι a)) :=
  triple_emit_val ι (.inv i) (fun regs => ι (reg regs i)) (fun _ => rfl) (ι a) P hP
    (fun regs h => by rw [holds_reg _ _ _ (hi regs h)])

theorem holdsVec_range' {R : Type*} [CommRing R] :
    ∀ (xs regs : List R), HoldsVec (regs ++ xs) (List.range' regs.length xs.length) xs
  | [], regs => by simp [HoldsVec]
  | x :: xs, regs => by
    rw [List.length_cons, List.range'_succ]
    refine List.Forall₂.cons ⟨by simp, ?_⟩ ?_
    · rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]; simp
    · have := holdsVec_range' xs (regs ++ [x])
      simpa [List.append_assoc, HoldsVec] using this

/-- Emit one oracle call; returns the `N'` result registers. -/
def Gen.emitMME (d₀ m' N' : ℕ) (cs ps : List ℕ) : Gen (List ℕ) :=
  fun n => (List.range' n N', [.mme d₀ m' N' cs ps], n + N')

theorem triple_emitMME {R : Type*} [CommRing R] (ι : R → R) (d₀ m' N' : ℕ) (cs ps : List ℕ)
    (cf : (Fin m' → Fin d₀) → R) (pf : Fin N' → Fin m' → R)
    (P : List R → Prop) (hP : Stable P)
    (hc : ∀ regs, P regs → ∀ e, regAt regs cs (finFunctionFinEquiv e) = cf e)
    (hp : ∀ regs, P regs → ∀ (k : Fin N') (i : Fin m'), regAt regs ps ((k : ℕ) * m' + i) = pf k i) :
    Triple ι (Gen.emitMME d₀ m' N' cs ps) P
      (fun out regs => P regs ∧ HoldsVec regs out (List.ofFn (mmeSpec cf pf))) := by
  intro regs h
  have e1 : (fun e => regAt regs cs (finFunctionFinEquiv e)) = cf := funext (hc regs h)
  have e2 : (fun (k : Fin N') (i : Fin m') => regAt regs ps ((k : ℕ) * m' + i)) = pf :=
    funext fun k => funext fun i => hp regs h k i
  refine ⟨List.ofFn (mmeSpec cf pf), ?_, by simp [Gen.emitMME], hP _ _ h, ?_⟩
  · simp only [Gen.emitMME, List.foldl_cons, List.foldl_nil, step]
    rw [e1, e2]
  · have := holdsVec_range' (List.ofFn (mmeSpec (d := d₀) cf pf)) regs
    simpa [Gen.emitMME] using this

theorem ops_pure {α : Type} (a : α) (n : ℕ) : (Gen.pure a).ops n = 0 := rfl

theorem ops_emit (i : Instr) (n : ℕ) : (Gen.emit i).ops n = if i.isRingOp then 1 else 0 := by
  cases i <;> rfl

theorem ops_emitMME (d₀ m' N' : ℕ) (cs ps : List ℕ) (n : ℕ) :
    (Gen.emitMME d₀ m' N' cs ps).ops n = 0 := rfl

theorem ops_vecAdd : ∀ (is js : List ℕ) (n : ℕ), (vecAdd is js).ops n = min is.length js.length
  | i :: is, j :: js, n => by
    simp only [vecAdd, ops_bind, ops_emit, ops_pure, ops_vecAdd is js, List.length_cons]
    simp [Instr.isRingOp]; omega
  | [], _, n => by simp [vecAdd, ops_pure]
  | _ :: _, [], n => by simp [vecAdd, ops_pure]

/-- Holding registers determine the output of `map reg`. -/
theorem map_reg_of_holdsVec {R : Type*} [CommRing R] (regs : List R) :
    ∀ (rs : List ℕ) (vs : List R), HoldsVec regs rs vs → rs.map (reg regs) = vs
  | [], [], _ => rfl
  | r :: rs, v :: vs, h => by
    rw [List.map_cons, holds_reg _ _ _ (List.forall₂_cons.1 h).1,
      map_reg_of_holdsVec regs rs vs (List.forall₂_cons.1 h).2]
  | [], _ :: _, h => by simp [HoldsVec] at h
  | _ :: _, [], h => by simp [HoldsVec] at h

/-- **Run extraction.** A triple from a precondition holding on the input yields the run's
output. -/
theorem run_of_triple {R : Type*} [CommRing R] (ι : R → R) (g : Gen (List ℕ))
    (P : List R → Prop) (Q : List ℕ → List R → Prop) (T : List R → Prop)
    (h : Triple ι g P Q) (hQ : ∀ out regs, Q out regs → ∃ vs, HoldsVec regs out vs ∧ T vs)
    (inp : List R) (hP : P inp) :
    T (run ι ⟨(g inp.length).2.1, (g inp.length).1⟩ inp) := by
  obtain ⟨new, h1, _, h3⟩ := h inp hP
  obtain ⟨vs, hv, hT⟩ := hQ _ _ h3
  unfold run
  simp only
  rw [h1, map_reg_of_holdsVec _ _ _ hv]
  exact hT

theorem ringOps_gen {α : Type} (g : Gen α) (n : ℕ) (o : List ℕ) :
    ringOps ⟨(g n).2.1, o⟩ = g.ops n := rfl

theorem oracleCalls_gen_nil (c : List Instr) (o : List ℕ)
    (h : ∀ i ∈ c, i.isRingOp = true) : oracleCalls ⟨c, o⟩ = [] := by
  unfold oracleCalls
  rw [List.filterMap_eq_nil_iff]
  intro i hi
  have := h i hi
  clear hi
  revert this
  cases i <;> simp [Instr.isRingOp, Instr.oracleParams]

/-! ## Coefficient lists as polynomials -/

open Polynomial in
/-- The polynomial with coefficient list `vs` (low degree first). -/
noncomputable def toPoly {R : Type*} [CommRing R] : List R → R[X]
  | [] => 0
  | a :: as => C a + X * toPoly as

/-- Padded elementwise sum of coefficient lists. -/
def listAddPad {R : Type*} [CommRing R] : List R → List R → List R
  | a :: as, b :: bs => (a + b) :: listAddPad as bs
  | [], bs => bs
  | as, [] => as

open Polynomial in
theorem toPoly_listAddPad {R : Type*} [CommRing R] :
    ∀ as bs : List R, toPoly (listAddPad as bs) = toPoly as + toPoly bs
  | a :: as, b :: bs => by
    simp only [listAddPad, toPoly, toPoly_listAddPad as bs, C_add]; ring
  | [], bs => by simp [listAddPad, toPoly]
  | _ :: _, [] => by simp [listAddPad, toPoly]

open Polynomial in
theorem toPoly_map_mul {R : Type*} [CommRing R] (a : R) :
    ∀ bs : List R, toPoly (bs.map (a * ·)) = C a * toPoly bs
  | [] => by simp [toPoly]
  | b :: bs => by simp only [List.map_cons, toPoly, toPoly_map_mul a bs, C_mul]; ring

/-- Padded vector sum: missing entries are copied (no instruction). -/
def vecAddPad : List ℕ → List ℕ → Gen (List ℕ)
  | i :: is, j :: js =>
      Gen.bind (Gen.emit (.add i j)) fun r => Gen.bind (vecAddPad is js) fun rs => Gen.pure (r :: rs)
  | [], js => Gen.pure js
  | is, [] => Gen.pure is

theorem triple_vecAddPad {R : Type*} [CommRing R] (ι : R → R) :
    ∀ (is js : List ℕ) (as bs : List R) (P : List R → Prop), Stable P →
      (∀ regs, P regs → HoldsVec regs is as) → (∀ regs, P regs → HoldsVec regs js bs) →
      Triple ι (vecAddPad is js) P
        (fun out regs => P regs ∧ HoldsVec regs out (listAddPad as bs))
  | i :: is, j :: js, a :: as, b :: bs, P, hP, hx, hy => by
    have hxi : ∀ regs, P regs → Holds regs i a := fun regs h => (List.forall₂_cons.1 (hx regs h)).1
    have hyj : ∀ regs, P regs → Holds regs j b := fun regs h => (List.forall₂_cons.1 (hy regs h)).1
    refine triple_bind ι _ _ P _ _ (triple_emit_add ι i j a b P hP hxi hyj) fun r => ?_
    have hP' : Stable (fun regs => P regs ∧ Holds regs r (a + b)) :=
      stable_and _ _ hP (stable_holds r (a + b))
    refine triple_bind ι _ _ _ _ _ (triple_vecAddPad ι is js as bs _ hP'
      (fun regs h => (List.forall₂_cons.1 (hx regs h.1)).2)
      (fun regs h => (List.forall₂_cons.1 (hy regs h.1)).2)) fun rs => ?_
    refine triple_pure ι _ _ _ fun regs h => ⟨h.1.1, ?_⟩
    exact List.Forall₂.cons h.1.2 h.2
  | [], js, as, bs, P, _, hx, hy => by
    cases hx' : as with
    | nil => exact triple_pure ι _ _ _ fun regs h => ⟨h, by simpa [listAddPad] using hy regs h⟩
    | cons a as' =>
      exact triple_pure ι _ _ _ fun regs h => absurd (hx regs h) (by rw [hx']; simp [HoldsVec])
  | i :: is, [], as, bs, P, _, hx, hy => by
    cases hy' : bs with
    | nil =>
      refine triple_pure ι _ _ _ fun regs h => ⟨h, ?_⟩
      cases as with
      | nil => simpa [vecAddPad, listAddPad] using hx regs h
      | cons a as' => simpa [vecAddPad, listAddPad] using hx regs h
    | cons b bs' =>
      exact triple_pure ι _ _ _ fun regs h => absurd (hy regs h) (by rw [hy']; simp [HoldsVec])
  | _ :: _, _ :: _, [], bs, P, _, hx, _ => by
    exact triple_of_false ι _ _ _ fun regs h => absurd (hx regs h) (by simp [HoldsVec])
  | _ :: _, _ :: _, _ :: _, [], P, _, _, hy => by
    exact triple_of_false ι _ _ _ fun regs h => absurd (hy regs h) (by simp [HoldsVec])

theorem ops_vecAddPad : ∀ (is js : List ℕ) (n : ℕ),
    (vecAddPad is js).ops n = min is.length js.length
  | i :: is, j :: js, n => by
    simp only [vecAddPad, ops_bind, ops_emit, ops_pure, ops_vecAddPad is js, List.length_cons]
    simp [Instr.isRingOp]; omega
  | [], _, n => by simp [vecAddPad, ops_pure]
  | _ :: _, [], n => by simp [vecAddPad, ops_pure]

/-- Scalar times vector. -/
def vecSmul (s : ℕ) : List ℕ → Gen (List ℕ)
  | [] => Gen.pure []
  | j :: js => Gen.bind (Gen.emit (.mul s j)) fun r => Gen.bind (vecSmul s js) fun rs =>
      Gen.pure (r :: rs)

theorem vecSmul_length (s : ℕ) : ∀ (js : List ℕ) (n : ℕ), ((vecSmul s js) n).1.length = js.length
  | [], n => rfl
  | j :: js, n => by
    simp only [vecSmul, Gen.bind, Gen.pure, Gen.emit, List.length_cons]
    rw [vecSmul_length s js]

theorem ops_vecSmul (s : ℕ) : ∀ (js : List ℕ) (n : ℕ), (vecSmul s js).ops n = js.length
  | [], n => rfl
  | j :: js, n => by
    simp only [vecSmul, ops_bind, ops_emit, ops_pure, ops_vecSmul s js, List.length_cons]
    simp [Instr.isRingOp]; omega

theorem triple_vecSmul {R : Type*} [CommRing R] (ι : R → R) (s : ℕ) (a : R) :
    ∀ (js : List ℕ) (bs : List R) (P : List R → Prop), Stable P →
      (∀ regs, P regs → Holds regs s a) → (∀ regs, P regs → HoldsVec regs js bs) →
      Triple ι (vecSmul s js) P
        (fun out regs => P regs ∧ HoldsVec regs out (bs.map (a * ·)))
  | j :: js, b :: bs, P, hP, hs, hy => by
    have hyj : ∀ regs, P regs → Holds regs j b := fun regs h => (List.forall₂_cons.1 (hy regs h)).1
    refine triple_bind ι _ _ P _ _ (triple_emit_mul ι s j a b P hP hs hyj) fun r => ?_
    have hP' : Stable (fun regs => P regs ∧ Holds regs r (a * b)) :=
      stable_and _ _ hP (stable_holds r (a * b))
    refine triple_bind ι _ _ _ _ _ (triple_vecSmul ι s a js bs _ hP'
      (fun regs h => hs regs h.1)
      (fun regs h => (List.forall₂_cons.1 (hy regs h.1)).2)) fun rs => ?_
    refine triple_pure ι _ _ _ fun regs h => ⟨h.1.1, ?_⟩
    exact List.Forall₂.cons h.1.2 h.2
  | [], bs, P, _, _, hy => by
    cases hy' : bs with
    | nil => exact triple_pure ι _ _ _ fun regs h => ⟨h, by simp [HoldsVec]⟩
    | cons b bs' =>
      exact triple_pure ι _ _ _ fun regs h => absurd (hy regs h) (by rw [hy']; simp [HoldsVec])
  | _ :: _, [], P, _, _, hy => by
    exact triple_of_false ι _ _ _ fun regs h => absurd (hy regs h) (by simp [HoldsVec])

/-- Schoolbook polynomial multiplication of coefficient-register lists. -/
def schoolMul : List ℕ → List ℕ → Gen (List ℕ)
  | [], _ => Gen.pure []
  | i :: is, js => Gen.bind (vecSmul i js) fun p => Gen.bind (schoolMul is js) fun q =>
      match p with
      | [] => Gen.pure q
      | p₀ :: p' => Gen.bind (vecAddPad p' q) fun t => Gen.pure (p₀ :: t)

theorem ops_schoolMul : ∀ (is js : List ℕ) (n : ℕ),
    (schoolMul is js).ops n ≤ 2 * is.length * js.length
  | [], js, n => by simp [schoolMul, ops_pure]
  | i :: is, js, n => by
    simp only [schoolMul, ops_bind, ops_vecSmul]
    have hl := vecSmul_length i js n
    have ih := ops_schoolMul is js ((vecSmul i js) n).2.2
    generalize ((vecSmul i js) n).1 = p at hl ⊢
    rcases p with _ | ⟨p₀, p'⟩
    · simp only [ops_pure, List.length_cons] at *
      nlinarith
    · simp only [ops_bind, ops_pure, ops_vecAddPad, List.length_cons] at *
      have := Nat.min_le_left p'.length
        ((schoolMul is js) ((vecSmul i js) n).2.2).1.length
      nlinarith

open Polynomial in
theorem triple_schoolMul {R : Type*} [CommRing R] (ι : R → R) :
    ∀ (is js : List ℕ) (as bs : List R) (P : List R → Prop), Stable P →
      (∀ regs, P regs → HoldsVec regs is as) → (∀ regs, P regs → HoldsVec regs js bs) →
      Triple ι (schoolMul is js) P
        (fun out regs => P regs ∧ ∃ vs, HoldsVec regs out vs ∧ toPoly vs = toPoly as * toPoly bs)
  | [], js, as, bs, P, _, hx, _ => by
    cases hx' : as with
    | nil => exact triple_pure ι _ _ _ fun regs h => ⟨h, [], by simp [HoldsVec], by simp [toPoly]⟩
    | cons a as' =>
      exact triple_pure ι _ _ _ fun regs h => absurd (hx regs h) (by rw [hx']; simp [HoldsVec])
  | i :: is, js, [], bs, P, _, hx, _ => by
    exact triple_of_false ι _ _ _ fun regs h => absurd (hx regs h) (by simp [HoldsVec])
  | i :: is, js, a :: as, bs, P, hP, hx, hy => by
    have hxi : ∀ regs, P regs → Holds regs i a := fun regs h => (List.forall₂_cons.1 (hx regs h)).1
    have hxs : ∀ regs, P regs → HoldsVec regs is as :=
      fun regs h => (List.forall₂_cons.1 (hx regs h)).2
    refine triple_bind ι _ _ P _ _ (triple_vecSmul ι i a js bs P hP hxi hy) fun p => ?_
    have hP1 : Stable (fun regs => P regs ∧ HoldsVec regs p (bs.map (a * ·))) :=
      stable_and _ _ hP (stable_holdsVec p _)
    refine triple_bind ι _ _ _ _ _ (triple_schoolMul ι is js as bs _ hP1
      (fun regs h => hxs regs h.1) (fun regs h => hy regs h.1)) fun q => ?_
    rcases p with _ | ⟨p₀, p'⟩
    · cases bs with
      | nil =>
        refine triple_pure ι _ _ _ fun regs h => ⟨h.1.1, ?_⟩
        obtain ⟨vs, hv, hvp⟩ := h.2
        exact ⟨vs, hv, by rw [hvp]; simp [toPoly]⟩
      | cons b bs' =>
        exact triple_of_false ι _ _ _ fun regs h => absurd h.1.2 (by simp [HoldsVec])
    · cases bs with
      | nil =>
        exact triple_of_false ι _ _ _ fun regs h => absurd h.1.2 (by simp [HoldsVec])
      | cons b bs' =>
        -- precondition: (P ∧ HoldsVec (p₀ :: p') ..) ∧ ∃ vs, HoldsVec q vs ∧ ...
        intro regs h
        obtain ⟨vs, hv, hvp⟩ := h.2
        have hp := List.forall₂_cons.1 h.1.2
        let P2 : List R → Prop := fun regs' => (P regs' ∧ Holds regs' p₀ (a * b)) ∧
          HoldsVec regs' p' (bs'.map (a * ·)) ∧ HoldsVec regs' q vs
        have hP2 : Stable P2 := fun r n h' =>
          ⟨⟨hP _ _ h'.1.1, holds_append _ _ _ _ h'.1.2⟩, holdsVec_append _ _ _ _ h'.2.1,
            holdsVec_append _ _ _ _ h'.2.2⟩
        have T := triple_bind ι _ _ P2 _ _ (triple_vecAddPad ι p' q (bs'.map (a * ·)) vs P2 hP2
          (fun _ h' => h'.2.1) (fun _ h' => h'.2.2)) fun t =>
          triple_pure ι (p₀ :: t) _
            (fun out regs' => P regs' ∧ ∃ vs, HoldsVec regs' out vs ∧
              toPoly vs = toPoly (a :: as) * toPoly (b :: bs')) fun regs' h' =>
            ⟨h'.1.1.1, (a * b) :: listAddPad (bs'.map (a * ·)) vs,
              List.Forall₂.cons h'.1.1.2 h'.2, by
                simp only [toPoly, toPoly_listAddPad, toPoly_map_mul, hvp, C_mul]; ring⟩
        exact T regs ⟨⟨h.1.1, hp.1⟩, hp.2, hv⟩

/-! ## S2-G1/G2: blocks over `R[X]/(cyc p e)` and their operations -/

open Polynomial in
theorem toPoly_coeff {R : Type*} [CommRing R] :
    ∀ (vs : List R) (q : ℕ), (toPoly vs).coeff q = vs.getD q 0
  | [], q => by simp [toPoly]
  | a :: as, 0 => by simp [toPoly]
  | a :: as, q + 1 => by simp [toPoly, coeff_X_mul, toPoly_coeff as q, coeff_C]

open Polynomial in
/-- `cyc p e = Φ_p(X^e) = ∑_{i<p} X^{i e}` (for `p` prime and `e` a power of `p`, a cyclotomic
polynomial). -/
noncomputable def cyc (R : Type*) [CommRing R] (p e : ℕ) : R[X] :=
  ∑ i ∈ Finset.range p, X ^ (i * e)

open Polynomial in
theorem cyc_coeff {R : Type*} [CommRing R] (p e q : ℕ) (he : 0 < e) :
    (cyc R p e).coeff q = if q % e = 0 ∧ q / e < p then 1 else 0 := by
  unfold cyc
  rw [finsetSum_coeff]
  simp only [coeff_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single (q / e)]
    · rw [if_pos]; exact (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h.1)).symm
    · intro b _ hb; rw [if_neg]; intro hq; apply hb; rw [hq, Nat.mul_div_cancel _ he]
    · intro hn; exact absurd (Finset.mem_range.2 h.2) hn
  · apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg]
    intro hq
    apply h
    subst hq
    refine ⟨Nat.mul_mod_left _ _, ?_⟩
    rw [Nat.mul_div_cancel _ he]
    exact Finset.mem_range.1 hi

theorem succ_mod_eq (q e : ℕ) (he : 0 < e) :
    (q + 1) % e = if q % e + 1 = e then 0 else q % e + 1 := by
  have h1 := Nat.mod_add_div q e
  have h2 := Nat.mod_lt q he
  have h3 : (q + 1) % e = (q % e + 1) % e := by
    conv_lhs => rw [← h1]
    rw [show q % e + e * (q / e) + 1 = (q % e + 1) + e * (q / e) by ring, Nat.add_mul_mod_self_left]
  rw [h3]
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

/-- Copy a register list, adding `nt` at the positions where the countdown hits `0`
(countdown restarts at `e - 1`). -/
def shiftAdd (e nt : ℕ) : ℕ → List ℕ → Gen (List ℕ)
  | _, [] => Gen.pure []
  | 0, r :: rs => Gen.bind (Gen.emit (.add r nt)) fun r' =>
      Gen.bind (shiftAdd e nt (e - 1) rs) fun t => Gen.pure (r' :: t)
  | k + 1, r :: rs => Gen.bind (shiftAdd e nt k rs) fun t => Gen.pure (r :: t)

def shiftAddVal {R : Type*} [CommRing R] (e : ℕ) (c : R) : ℕ → List R → List R
  | _, [] => []
  | 0, a :: as => (a + c) :: shiftAddVal e c (e - 1) as
  | k + 1, a :: as => a :: shiftAddVal e c k as

theorem shiftAddVal_length {R : Type*} [CommRing R] (e : ℕ) (c : R) :
    ∀ (k : ℕ) (as : List R), (shiftAddVal e c k as).length = as.length
  | _, [] => by simp [shiftAddVal]
  | 0, a :: as => by simp [shiftAddVal, shiftAddVal_length e c (e - 1) as]
  | k + 1, a :: as => by simp [shiftAddVal, shiftAddVal_length e c k as]

theorem shiftAddVal_getD {R : Type*} [CommRing R] (e : ℕ) (he : 0 < e) (c : R) :
    ∀ (k : ℕ) (as : List R) (q : ℕ), k < e →
      (shiftAddVal e c k as).getD q 0 = as.getD q 0 + if q < as.length ∧ q % e = k then c else 0
  | _, [], q, _ => by simp [shiftAddVal]
  | 0, a :: as, 0, _ => by simp [shiftAddVal]
  | 0, a :: as, q + 1, hk => by
    simp only [shiftAddVal, List.getD_cons_succ, List.length_cons]
    rw [shiftAddVal_getD e he c (e - 1) as q (by omega), succ_mod_eq q e he]
    congr 1
    have hm := Nat.mod_lt q he
    have key : (q < as.length ∧ q % e = e - 1) ↔
        (q + 1 < as.length + 1 ∧ (if q % e + 1 = e then 0 else q % e + 1) = 0) := by
      by_cases hc : q % e + 1 = e
      · rw [if_pos hc]; constructor <;> intro h1 <;> omega
      · rw [if_neg hc]; constructor <;> intro h1 <;> omega
    by_cases h1 : q < as.length ∧ q % e = e - 1
    · rw [if_pos h1, if_pos (key.1 h1)]
    · rw [if_neg h1, if_neg (mt key.2 h1)]
  | k + 1, a :: as, 0, hk => by
    simp only [shiftAddVal, List.getD_cons_zero, Nat.zero_mod]
    simp
  | k + 1, a :: as, q + 1, hk => by
    simp only [shiftAddVal, List.getD_cons_succ, List.length_cons]
    rw [shiftAddVal_getD e he c k as q (by omega), succ_mod_eq q e he]
    congr 1
    have hm := Nat.mod_lt q he
    have key : (q < as.length ∧ q % e = k) ↔
        (q + 1 < as.length + 1 ∧ (if q % e + 1 = e then 0 else q % e + 1) = k + 1) := by
      by_cases hc : q % e + 1 = e
      · rw [if_pos hc]; constructor <;> intro h1 <;> omega
      · rw [if_neg hc]; constructor <;> intro h1 <;> omega
    by_cases h1 : q < as.length ∧ q % e = k
    · rw [if_pos h1, if_pos (key.1 h1)]
    · rw [if_neg h1, if_neg (mt key.2 h1)]

theorem triple_shiftAdd {R : Type*} [CommRing R] (ι : R → R) (e nt : ℕ) (c : R) :
    ∀ (k : ℕ) (rs : List ℕ) (as : List R) (P : List R → Prop), Stable P →
      (∀ regs, P regs → Holds regs nt c) → (∀ regs, P regs → HoldsVec regs rs as) →
      Triple ι (shiftAdd e nt k rs) P
        (fun out regs => P regs ∧ HoldsVec regs out (shiftAddVal e c k as))
  | k, [], as, P, _, _, hy => by
    cases hy' : as with
    | nil =>
      refine triple_pure ι _ _ _ fun regs h => ⟨h, ?_⟩
      cases k <;> simp [shiftAddVal, HoldsVec]
    | cons b bs' =>
      exact triple_pure ι _ _ _ fun regs h => absurd (hy regs h) (by rw [hy']; simp [HoldsVec])
  | _, _ :: _, [], P, _, _, hy => by
    exact triple_of_false ι _ _ _ fun regs h => absurd (hy regs h) (by simp [HoldsVec])
  | 0, r :: rs, a :: as, P, hP, hc, hy => by
    have hyr : ∀ regs, P regs → Holds regs r a := fun regs h => (List.forall₂_cons.1 (hy regs h)).1
    refine triple_bind ι _ _ P _ _ (triple_emit_add ι r nt a c P hP hyr hc) fun r' => ?_
    have hP' : Stable (fun regs => P regs ∧ Holds regs r' (a + c)) :=
      stable_and _ _ hP (stable_holds r' (a + c))
    refine triple_bind ι _ _ _ _ _ (triple_shiftAdd ι e nt c (e - 1) rs as _ hP'
      (fun regs h => hc regs h.1)
      (fun regs h => (List.forall₂_cons.1 (hy regs h.1)).2)) fun t => ?_
    refine triple_pure ι _ _ _ fun regs h => ⟨h.1.1, ?_⟩
    exact List.Forall₂.cons h.1.2 h.2
  | k + 1, r :: rs, a :: as, P, hP, hc, hy => by
    have hyr : ∀ regs, P regs → Holds regs r a := fun regs h => (List.forall₂_cons.1 (hy regs h)).1
    refine triple_bind ι _ _ _ _ _ (triple_shiftAdd ι e nt c k rs as P hP hc
      (fun regs h => (List.forall₂_cons.1 (hy regs h)).2)) fun t => ?_
    refine triple_pure ι _ _ _ fun regs h => ⟨h.1, ?_⟩
    exact List.Forall₂.cons (hyr regs h.1) h.2

theorem ops_shiftAdd (e nt : ℕ) (he : 0 < e) :
    ∀ (k : ℕ) (rs : List ℕ) (n : ℕ), k < e →
      (shiftAdd e nt k rs).ops n * e ≤ rs.length + (e - 1 - k)
  | k, [], n, _ => by cases k <;> simp [shiftAdd, ops_pure]
  | 0, r :: rs, n, _ => by
    simp only [shiftAdd, ops_bind, ops_emit, ops_pure, List.length_cons]
    have ih := ops_shiftAdd e nt he (e - 1) rs (n + 1) (by omega)
    simp only [Instr.isRingOp, if_true]
    simp only [Gen.emit] at ih ⊢
    have h1 : e - 1 - (e - 1) = 0 := by omega
    have h2 : e - 1 - 0 = e - 1 := by omega
    rw [h1] at ih
    rw [h2, Nat.add_zero, Nat.add_mul, Nat.one_mul]
    omega
  | k + 1, r :: rs, n, hk => by
    simp only [shiftAdd, ops_bind, ops_pure, List.length_cons, Nat.add_zero]
    have ih := ops_shiftAdd e nt he k rs n (by omega)
    omega

open Polynomial in
theorem toPoly_map_neg {R : Type*} [CommRing R] :
    ∀ bs : List R, toPoly (bs.map Neg.neg) = -toPoly bs
  | [] => by simp [toPoly]
  | b :: bs => by simp only [List.map_cons, toPoly, toPoly_map_neg bs, C_neg]; ring

theorem holdsVec_getD {R : Type*} [CommRing R] (regs : List R) :
    ∀ (rs : List ℕ) (vs : List R), HoldsVec regs rs vs → ∀ i, i < rs.length →
      Holds regs (rs.getD i 0) (vs.getD i 0)
  | [], [], _, i, hi => by simp at hi
  | r :: rs, v :: vs, h, 0, _ => by simpa using (List.forall₂_cons.1 h).1
  | r :: rs, v :: vs, h, i + 1, hi => by
    simpa using holdsVec_getD regs rs vs (List.forall₂_cons.1 h).2 i (by simpa using hi)
  | [], _ :: _, h, _, _ => by simp [HoldsVec] at h
  | _ :: _, [], h, _, _ => by simp [HoldsVec] at h

theorem holdsVec_length {R : Type*} [CommRing R] (regs : List R) (rs : List ℕ) (vs : List R)
    (h : HoldsVec regs rs vs) : rs.length = vs.length := List.Forall₂.length_eq h

/-- Multiply a block (length `D = (p-1) e`) by `X` modulo `cyc p e`: `O(p)` instructions. -/
def mulXGen (e D : ℕ) (blk : List ℕ) : Gen (List ℕ) :=
  Gen.bind (Gen.emit (.neg (blk.getD (D - 1) 0))) fun nt =>
    Gen.bind (shiftAdd e nt (e - 1) (blk.take (D - 1))) fun t => Gen.pure (nt :: t)

open Polynomial in
theorem mulX_poly {R : Type*} [CommRing R] (p e : ℕ) (hp : 2 ≤ p) (he : 0 < e) (vs : List R)
    (hl : vs.length = (p - 1) * e) :
    toPoly ((-vs.getD ((p - 1) * e - 1) 0) ::
        shiftAddVal e (-vs.getD ((p - 1) * e - 1) 0) (e - 1) (vs.take ((p - 1) * e - 1))) =
      X * toPoly vs - C (vs.getD ((p - 1) * e - 1) 0) * cyc R p e := by
  set D := (p - 1) * e with hD
  have hD1 : 1 ≤ D := by rw [hD]; exact Nat.mul_pos (by omega) he
  set t := vs.getD (D - 1) 0
  ext q
  rw [coeff_sub, coeff_C_mul, cyc_coeff p e q he, toPoly_coeff]
  rcases q with _ | q
  · simp
    omega
  · rw [List.getD_cons_succ, shiftAddVal_getD e he _ _ _ q (by omega), coeff_X_mul, toPoly_coeff,
      succ_mod_eq q e he]
    have hmod := Nat.mod_lt q he
    have hq := Nat.mod_add_div q e
    rw [List.length_take, hl]
    rcases Nat.lt_or_ge q (D - 1) with h | h
    · have e1 : (vs.take (D - 1)).getD q 0 = vs.getD q 0 := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]
      rw [e1]
      have hlt : q < D - 1 ⊓ D := by omega
      by_cases hc : q % e + 1 = e
      · have hdiv : (q + 1) / e < p := by
          rw [Nat.div_lt_iff_lt_mul he]
          have : (p - 1) * e < p * e := Nat.mul_lt_mul_of_pos_right (by omega) he
          omega
        simp only [hc, if_true, true_and, hdiv, hlt]
        rw [if_pos (by omega)]
        ring
      · simp only [hc, if_false]
        rw [if_neg (by omega), if_neg (by omega)]
        ring
    · rcases Nat.lt_or_ge q D with h' | h'
      · have hq' : q = D - 1 := by omega
        have e1 : (vs.take (D - 1)).getD q 0 = 0 := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_take, hq']
        rw [e1, if_neg (by omega)]
        have hqe : q + 1 = (p - 1) * e := by omega
        have hc : q % e + 1 = e := by
          have := succ_mod_eq q e he
          rw [hqe, Nat.mul_mod_left] at this
          split_ifs at this with hh <;> omega
        have hdiv : (q + 1) / e < p := by rw [hqe, Nat.mul_div_cancel _ he]; omega
        simp only [hc, if_true, true_and, hdiv]
        rw [hq']
        ring
      · have e1 : (vs.take (D - 1)).getD q 0 = 0 := by
          rw [List.getD_eq_default _ _ (by rw [List.length_take]; omega)]
        have e2 : vs.getD q 0 = 0 := by
          rw [List.getD_eq_default _ _ (by omega)]
        rw [e1, e2, if_neg (by omega)]
        by_cases hc : q % e + 1 = e
        · have hdiv : ¬ (q + 1) / e < p := by
            intro hlt
            have h3 : (q + 1) % e = 0 := by rw [succ_mod_eq q e he, if_pos hc]
            have h4 := Nat.mod_add_div (q + 1) e
            rw [h3, Nat.zero_add] at h4
            have h5 : (q + 1) / e ≤ p - 1 := by omega
            have h6 : e * ((q + 1) / e) ≤ e * (p - 1) := Nat.mul_le_mul_left e h5
            rw [mul_comm e (p - 1)] at h6
            omega
          simp [hc, hdiv]
        · simp [hc]

/-- A block: `(p-1) e` registers whose coefficient polynomial represents `v` modulo `cyc p e`. -/
def HoldsB {R : Type*} [CommRing R] (p e : ℕ) (regs : List R) (blk : List ℕ)
    (v : AdjoinRoot (cyc R p e)) : Prop :=
  ∃ vs : List R, HoldsVec regs blk vs ∧ vs.length = (p - 1) * e ∧
    AdjoinRoot.mk (cyc R p e) (toPoly vs) = v

theorem stable_holdsB {R : Type*} [CommRing R] (p e : ℕ) (blk : List ℕ)
    (v : AdjoinRoot (cyc R p e)) : Stable (fun regs : List R => HoldsB p e regs blk v) :=
  fun regs new ⟨vs, h1, h2, h3⟩ => ⟨vs, holdsVec_append _ _ _ _ h1, h2, h3⟩

theorem triple_mulX {R : Type*} [CommRing R] (ι : R → R) (p e : ℕ) (hp : 2 ≤ p) (he : 0 < e)
    (blk : List ℕ) (v : AdjoinRoot (cyc R p e)) (P : List R → Prop) (hP : Stable P)
    (hb : ∀ regs, P regs → HoldsB p e regs blk v) :
    Triple ι (mulXGen e ((p - 1) * e) blk) P
      (fun out regs => P regs ∧ HoldsB p e regs out (AdjoinRoot.root (cyc R p e) * v)) := by
  intro regs h
  obtain ⟨vs, hv, hl, hval⟩ := hb regs h
  set D := (p - 1) * e with hD
  have hD1 : 1 ≤ D := by rw [hD]; exact Nat.mul_pos (by omega) he
  have hlen := holdsVec_length _ _ _ hv
  set t := vs.getD (D - 1) 0
  let P1 : List R → Prop := fun r => P r ∧ HoldsVec r blk vs
  have hP1 : Stable P1 := stable_and _ _ hP (stable_holdsVec blk vs)
  have hlast : ∀ r, P1 r → Holds r (blk.getD (D - 1) 0) t :=
    fun r h' => holdsVec_getD r blk vs h'.2 (D - 1) (by omega)
  have T := triple_bind ι _ _ P1 _ _ (triple_emit_neg ι _ t P1 hP1 hlast) fun nt => by
    have hP2 : Stable (fun r => P1 r ∧ Holds r nt (-t)) := stable_and _ _ hP1 (stable_holds nt _)
    exact triple_bind ι _ _ _ _ _ (triple_shiftAdd ι e nt (-t) (e - 1) (blk.take (D - 1))
      (vs.take (D - 1)) _ hP2 (fun r h' => h'.2)
      (fun r h' => List.forall₂_take (D - 1) h'.1.2)) fun tl =>
      triple_pure ι (nt :: tl) _
        (fun out r => P r ∧ HoldsB p e r out (AdjoinRoot.root (cyc R p e) * v)) fun r h' =>
        ⟨h'.1.1.1, (-t) :: shiftAddVal e (-t) (e - 1) (vs.take (D - 1)),
          List.Forall₂.cons h'.1.2 h'.2, by
            simp only [List.length_cons]
            have : (shiftAddVal e (-t) (e - 1) (vs.take (D - 1))).length = D - 1 := by
              rw [shiftAddVal_length]; simp; omega
            omega, by
            rw [mulX_poly p e hp he vs hl, map_sub, map_mul, map_mul, AdjoinRoot.mk_self,
              mul_zero, sub_zero, AdjoinRoot.mk_X, hval]⟩
  exact T regs ⟨h, hv⟩

theorem triple_post {R : Type*} [CommRing R] (ι : R → R) {α : Type} (g : Gen α)
    (P : List R → Prop) (Q Q' : α → List R → Prop) (h : Triple ι g P Q)
    (hQ : ∀ a regs, Q a regs → Q' a regs) : Triple ι g P Q' := by
  intro regs hP
  obtain ⟨new, h1, h2, h3⟩ := h regs hP
  exact ⟨new, h1, h2, hQ _ _ h3⟩

theorem ops_mulX (p e : ℕ) (hp : 2 ≤ p) (he : 0 < e) (blk : List ℕ) (n : ℕ) :
    (mulXGen e ((p - 1) * e) blk).ops n ≤ p - 1 := by
  have key : ∀ nt m, (shiftAdd e nt (e - 1) (blk.take ((p - 1) * e - 1))).ops m ≤ p - 2 := by
    intro nt m
    have h := ops_shiftAdd e nt he (e - 1) (blk.take ((p - 1) * e - 1)) m (by omega)
    have hl : (blk.take ((p - 1) * e - 1)).length ≤ (p - 1) * e - 1 := by simp
    rw [Nat.sub_self, Nat.add_zero] at h
    have hpos : 0 < (p - 1) * e := Nat.mul_pos (by omega) he
    have h2 : (shiftAdd e nt (e - 1) (blk.take ((p - 1) * e - 1))).ops m * e < (p - 1) * e := by
      omega
    have := Nat.lt_of_mul_lt_mul_right h2
    omega
  unfold mulXGen
  rw [ops_bind, ops_bind, ops_pure]
  rw [show (Gen.emit (Instr.neg (blk.getD ((p - 1) * e - 1) 0))).ops n = 1 from rfl]
  have := key ((Gen.emit (Instr.neg (blk.getD ((p - 1) * e - 1) 0))) n).1
    ((Gen.emit (Instr.neg (blk.getD ((p - 1) * e - 1) 0))) n).2.2
  omega

/-- Multiply a block by `X ^ j` (`j` single shifts). -/
def mulXPow (e D : ℕ) : ℕ → List ℕ → Gen (List ℕ)
  | 0, blk => Gen.pure blk
  | j + 1, blk => Gen.bind (mulXGen e D blk) fun b => mulXPow e D j b

theorem triple_mulXPow {R : Type*} [CommRing R] (ι : R → R) (p e : ℕ) (hp : 2 ≤ p) (he : 0 < e) :
    ∀ (j : ℕ) (blk : List ℕ) (v : AdjoinRoot (cyc R p e)) (P : List R → Prop), Stable P →
      (∀ regs, P regs → HoldsB p e regs blk v) →
      Triple ι (mulXPow e ((p - 1) * e) j blk) P
        (fun out regs => P regs ∧ HoldsB p e regs out (AdjoinRoot.root (cyc R p e) ^ j * v))
  | 0, blk, v, P, _, hb => triple_pure ι _ _ _ fun regs h => ⟨h, by simpa using hb regs h⟩
  | j + 1, blk, v, P, hP, hb => by
    refine triple_bind ι _ _ P _ _ (triple_mulX ι p e hp he blk v P hP hb) fun b => ?_
    have hP' : Stable (fun regs => P regs ∧ HoldsB p e regs b (AdjoinRoot.root (cyc R p e) * v)) :=
      stable_and _ _ hP (stable_holdsB p e b _)
    refine triple_post ι _ _ _ _ (triple_mulXPow ι p e hp he j b _ _ hP' (fun regs h => h.2))
      fun out regs h => ⟨h.1.1, ?_⟩
    have e1 : AdjoinRoot.root (cyc R p e) ^ (j + 1) * v =
        AdjoinRoot.root (cyc R p e) ^ j * (AdjoinRoot.root (cyc R p e) * v) := by ring
    rw [e1]; exact h.2

theorem ops_mulXPow (p e : ℕ) (hp : 2 ≤ p) (he : 0 < e) :
    ∀ (j : ℕ) (blk : List ℕ) (n : ℕ), (mulXPow e ((p - 1) * e) j blk).ops n ≤ j * (p - 1)
  | 0, blk, n => by simp [mulXPow, ops_pure]
  | j + 1, blk, n => by
    simp only [mulXPow, ops_bind]
    have h1 := ops_mulX p e hp he blk n
    have h2 := ops_mulXPow p e hp he j ((mulXGen e ((p - 1) * e) blk) n).1
      ((mulXGen e ((p - 1) * e) blk) n).2.2
    rw [Nat.add_mul, Nat.one_mul]
    omega

theorem listAddPad_length {R : Type*} [CommRing R] :
    ∀ as bs : List R, (listAddPad as bs).length = max as.length bs.length
  | a :: as, b :: bs => by simp [listAddPad, listAddPad_length as bs, Nat.succ_max_succ]
  | [], bs => by simp [listAddPad]
  | _ :: _, [] => by simp [listAddPad]

theorem triple_blkAdd {R : Type*} [CommRing R] (ι : R → R) (p e : ℕ) (b₁ b₂ : List ℕ)
    (v₁ v₂ : AdjoinRoot (cyc R p e)) (P : List R → Prop) (hP : Stable P)
    (h₁ : ∀ regs, P regs → HoldsB p e regs b₁ v₁) (h₂ : ∀ regs, P regs → HoldsB p e regs b₂ v₂) :
    Triple ι (vecAddPad b₁ b₂) P (fun out regs => P regs ∧ HoldsB p e regs out (v₁ + v₂)) := by
  intro regs h
  obtain ⟨vs₁, hv₁, hl₁, hx₁⟩ := h₁ regs h
  obtain ⟨vs₂, hv₂, hl₂, hx₂⟩ := h₂ regs h
  have T := triple_vecAddPad ι b₁ b₂ vs₁ vs₂
    (fun r => P r ∧ HoldsVec r b₁ vs₁ ∧ HoldsVec r b₂ vs₂)
    (stable_and _ _ hP (stable_and _ _ (stable_holdsVec _ _) (stable_holdsVec _ _)))
    (fun _ h' => h'.2.1) (fun _ h' => h'.2.2)
  obtain ⟨new, c1, c2, c3⟩ := T regs ⟨h, hv₁, hv₂⟩
  refine ⟨new, c1, c2, c3.1.1, listAddPad vs₁ vs₂, c3.2, ?_, ?_⟩
  · rw [listAddPad_length, hl₁, hl₂, max_self]
  · rw [toPoly_listAddPad, map_add, hx₁, hx₂]

/-- Negate a vector. -/
def vecNeg : List ℕ → Gen (List ℕ)
  | [] => Gen.pure []
  | j :: js => Gen.bind (Gen.emit (.neg j)) fun r => Gen.bind (vecNeg js) fun rs =>
      Gen.pure (r :: rs)

theorem ops_vecNeg : ∀ (js : List ℕ) (n : ℕ), (vecNeg js).ops n = js.length
  | [], n => rfl
  | j :: js, n => by
    simp only [vecNeg, ops_bind, ops_emit, ops_pure, ops_vecNeg js, List.length_cons]
    simp [Instr.isRingOp]; omega

theorem triple_vecNeg {R : Type*} [CommRing R] (ι : R → R) :
    ∀ (js : List ℕ) (bs : List R) (P : List R → Prop), Stable P →
      (∀ regs, P regs → HoldsVec regs js bs) →
      Triple ι (vecNeg js) P (fun out regs => P regs ∧ HoldsVec regs out (bs.map Neg.neg))
  | j :: js, b :: bs, P, hP, hy => by
    have hyj : ∀ regs, P regs → Holds regs j b := fun regs h => (List.forall₂_cons.1 (hy regs h)).1
    refine triple_bind ι _ _ P _ _ (triple_emit_neg ι j b P hP hyj) fun r => ?_
    have hP' : Stable (fun regs => P regs ∧ Holds regs r (-b)) :=
      stable_and _ _ hP (stable_holds r (-b))
    refine triple_bind ι _ _ _ _ _ (triple_vecNeg ι js bs _ hP'
      (fun regs h => (List.forall₂_cons.1 (hy regs h.1)).2)) fun rs => ?_
    refine triple_pure ι _ _ _ fun regs h => ⟨h.1.1, ?_⟩
    exact List.Forall₂.cons h.1.2 h.2
  | [], bs, P, _, hy => by
    cases hy' : bs with
    | nil => exact triple_pure ι _ _ _ fun regs h => ⟨h, by simp [HoldsVec]⟩
    | cons b bs' =>
      exact triple_pure ι _ _ _ fun regs h => absurd (hy regs h) (by rw [hy']; simp [HoldsVec])
  | _ :: _, [], P, _, hy => by
    exact triple_of_false ι _ _ _ fun regs h => absurd (hy regs h) (by simp [HoldsVec])

theorem triple_blkNeg {R : Type*} [CommRing R] (ι : R → R) (p e : ℕ) (b : List ℕ)
    (v : AdjoinRoot (cyc R p e)) (P : List R → Prop) (hP : Stable P)
    (hb : ∀ regs, P regs → HoldsB p e regs b v) :
    Triple ι (vecNeg b) P (fun out regs => P regs ∧ HoldsB p e regs out (-v)) := by
  intro regs h
  obtain ⟨vs, hv, hl, hx⟩ := hb regs h
  have T := triple_vecNeg ι b vs (fun r => P r ∧ HoldsVec r b vs)
    (stable_and _ _ hP (stable_holdsVec _ _)) (fun _ h' => h'.2)
  obtain ⟨new, c1, c2, c3⟩ := T regs ⟨h, hv⟩
  refine ⟨new, c1, c2, c3.1.1, vs.map Neg.neg, c3.2, by simp [hl], ?_⟩
  rw [toPoly_map_neg, map_neg, hx]

/-- Block subtraction `b₁ - b₂`. -/
def blkSub (b₁ b₂ : List ℕ) : Gen (List ℕ) := Gen.bind (vecNeg b₂) fun nb => vecAddPad b₁ nb

theorem triple_blkSub {R : Type*} [CommRing R] (ι : R → R) (p e : ℕ) (b₁ b₂ : List ℕ)
    (v₁ v₂ : AdjoinRoot (cyc R p e)) (P : List R → Prop) (hP : Stable P)
    (h₁ : ∀ regs, P regs → HoldsB p e regs b₁ v₁) (h₂ : ∀ regs, P regs → HoldsB p e regs b₂ v₂) :
    Triple ι (blkSub b₁ b₂) P (fun out regs => P regs ∧ HoldsB p e regs out (v₁ - v₂)) := by
  refine triple_bind ι _ _ P _ _ (triple_blkNeg ι p e b₂ v₂ P hP h₂) fun nb => ?_
  refine triple_post ι _ _ _ _ (triple_blkAdd ι p e b₁ nb v₁ (-v₂) _
    (stable_and _ _ hP (stable_holdsB p e nb _)) (fun regs h => h₁ regs h.1) (fun regs h => h.2))
    fun out regs h => ⟨h.1.1, by rw [sub_eq_add_neg]; exact h.2⟩

theorem ops_blkSub (b₁ b₂ : List ℕ) (n : ℕ) : (blkSub b₁ b₂).ops n ≤ b₁.length + b₂.length := by
  unfold blkSub
  rw [ops_bind, ops_vecNeg, ops_vecAddPad]
  have := Nat.min_le_left b₁.length ((vecNeg b₂) n).1.length
  omega

open Polynomial in
/-- In `R[X]/(cyc p e)`, the root `X` satisfies `X ^ (p e) = 1`. -/
theorem root_pow_pe {R : Type*} [CommRing R] (p e : ℕ) :
    AdjoinRoot.root (cyc R p e) ^ (p * e) = 1 := by
  have h : (X : R[X]) ^ (p * e) - 1 = cyc R p e * (X ^ e - 1) := by
    unfold cyc
    rw [show (X : R[X]) ^ (p * e) = (X ^ e) ^ p by rw [← pow_mul, mul_comm]]
    rw [← geom_sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← pow_mul, mul_comm]
  have h2 := congrArg (AdjoinRoot.mk (cyc R p e)) h
  rw [map_sub, map_mul, AdjoinRoot.mk_self, zero_mul, map_pow, AdjoinRoot.mk_X, map_one] at h2
  exact sub_eq_zero.1 h2

open Polynomial in
/-- `∑_{i<p} (X^e)^i = 0` in `R[X]/(cyc p e)`. -/
theorem root_cyc_sum {R : Type*} [CommRing R] (p e : ℕ) :
    ∑ i ∈ Finset.range p, (AdjoinRoot.root (cyc R p e) ^ e) ^ i = 0 := by
  have h : AdjoinRoot.mk (cyc R p e) (∑ i ∈ Finset.range p, (X : R[X]) ^ (i * e)) = 0 :=
    AdjoinRoot.mk_self
  rw [map_sum] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, AdjoinRoot.mk_X, ← pow_mul, mul_comm]

/-! ## S2-G4: principal roots of unity (pure algebra) -/

theorem sum_range_mul_pow {A : Type*} [CommRing A] (x : A) (n : ℕ) :
    ∀ m : ℕ, ∑ j ∈ Finset.range (n * m), x ^ j =
      (∑ j ∈ Finset.range n, x ^ j) * ∑ r ∈ Finset.range m, (x ^ n) ^ r
  | 0 => by simp
  | m + 1 => by
    rw [Nat.mul_succ, Finset.sum_range_add, sum_range_mul_pow x n m, Finset.sum_range_succ _ m,
      mul_add]
    congr 1
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add, ← pow_mul]; ring

theorem sum_pow_coprime {A : Type*} [CommRing A] (p : ℕ) (hp : 1 < p) (η : A) (hη1 : η ^ p = 1)
    (hη : ∑ r ∈ Finset.range p, η ^ r = 0) (u : ℕ) (hu : Nat.Coprime u p) :
    ∑ r ∈ Finset.range p, (η ^ u) ^ r = 0 := by
  obtain ⟨u', -, hu'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hu hp
  have hmod : ∀ k, η ^ k = η ^ (k % p) := by
    intro k
    conv_lhs => rw [← Nat.mod_add_div k p, pow_add, pow_mul, hη1, one_pow, mul_one]
  rw [← hη]
  refine Finset.sum_nbij' (fun r => (u * r) % p) (fun r => (u' * r) % p) ?_ ?_ ?_ ?_ ?_
  · intro r _; rw [Finset.mem_range]; exact Nat.mod_lt _ (by omega)
  · intro r _; rw [Finset.mem_range]; exact Nat.mod_lt _ (by omega)
  · intro r hr
    rw [Finset.mem_range] at hr
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← mul_assoc, mul_comm u' u, Nat.mul_mod, hu',
      one_mul, Nat.mod_mod, Nat.mod_eq_of_lt hr]
  · intro r hr
    rw [Finset.mem_range] at hr
    rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← mul_assoc, Nat.mul_mod, hu', one_mul,
      Nat.mod_mod, Nat.mod_eq_of_lt hr]
  · intro r _
    rw [← pow_mul, hmod (u * r)]

/-- **Principal root.** If `η = ω ^ (p^λ)` satisfies `η^p = 1` and `∑_{r<p} η^r = 0`, then
`∑_{j < p^(λ+1)} (ω^i)^j = 0` whenever `p^(λ+1) ∤ i`. -/
theorem principal_sum {A : Type*} [CommRing A] (p l : ℕ) (hp : p.Prime) (ω : A)
    (hη1 : (ω ^ (p ^ l)) ^ p = 1) (hη : ∑ r ∈ Finset.range p, (ω ^ (p ^ l)) ^ r = 0)
    (i : ℕ) (hi : ¬ p ^ (l + 1) ∣ i) :
    ∑ j ∈ Finset.range (p ^ (l + 1)), (ω ^ i) ^ j = 0 := by
  have hi0 : i ≠ 0 := by rintro rfl; exact hi (dvd_zero _)
  obtain ⟨s, u, hpu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hi0 p hp.ne_one
  have hs : s ≤ l := by
    by_contra h
    exact hi (Dvd.dvd.mul_right (pow_dvd_pow p (by omega)) u)
  have hsplit : p ^ (l + 1) = p ^ (l - s) * (p * p ^ s) := by
    rw [← pow_succ', ← pow_add]; congr 1; omega
  rw [hsplit, sum_range_mul_pow, sum_range_mul_pow]
  have hz : (ω ^ (p ^ s * u)) ^ p ^ (l - s) = (ω ^ (p ^ l)) ^ u := by
    rw [← pow_mul, ← pow_mul]; congr 1
    rw [mul_comm (p ^ s) u, mul_assoc, ← pow_add, Nat.add_sub_cancel' hs, mul_comm]
  rw [hz, sum_pow_coprime p hp.one_lt _ hη1 hη u
    ((Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpu))]
  simp

/-! ## S2-G3/G4 algebra: the DFT, its radix-p splitting, and its inverse -/

theorem sum_range_mul_split {M : Type*} [AddCommMonoid M] (f : ℕ → M) (p : ℕ) :
    ∀ m : ℕ, ∑ j ∈ Finset.range (p * m), f j =
      ∑ r ∈ Finset.range p, ∑ u ∈ Finset.range m, f (p * u + r)
  | 0 => by simp
  | m + 1 => by
    rw [Nat.mul_succ, Finset.sum_range_add, sum_range_mul_split f p m, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_range_succ]

/-- The discrete Fourier transform of length `L` with root `ω`. -/
def dft {A : Type*} [CommRing A] (ω : A) (L : ℕ) (a : ℕ → A) (k : ℕ) : A :=
  ∑ j ∈ Finset.range L, ω ^ (j * k) * a j

theorem dft_one {A : Type*} [CommRing A] (ω : A) (a : ℕ → A) (k : ℕ) : dft ω 1 a k = a 0 := by
  simp [dft]

/-- **Radix-p decimation in time.** -/
theorem dft_split {A : Type*} [CommRing A] (ω : A) (p M : ℕ) (hM : (ω ^ p) ^ M = 1)
    (a : ℕ → A) (k : ℕ) :
    dft ω (p * M) a k =
      ∑ r ∈ Finset.range p, ω ^ (r * k) * dft (ω ^ p) M (fun u => a (p * u + r)) (k % M) := by
  unfold dft
  rw [sum_range_mul_split]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hk : (ω ^ p) ^ (u * k) = (ω ^ p) ^ (u * (k % M)) := by
    conv_lhs => rw [← Nat.mod_add_div k M]
    rw [mul_add, pow_add, show u * (M * (k / M)) = M * (u * (k / M)) by ring,
      pow_mul (ω ^ p) M (u * (k / M)), hM, one_pow, mul_one]
  have h2 : ω ^ ((p * u + r) * k) = ω ^ (r * k) * (ω ^ p) ^ (u * k) := by
    rw [← pow_mul, ← pow_add]; ring_nf
  rw [h2, hk]; ring

/-- **Inverse DFT** for a principal `L`-th root of unity. -/
theorem dft_inv {A : Type*} [CommRing A] (ω : A) (L : ℕ) (hL : ω ^ L = 1)
    (hprin : ∀ i, ¬ L ∣ i → ∑ j ∈ Finset.range L, (ω ^ i) ^ j = 0) (a : ℕ → A) (j' : ℕ)
    (hj' : j' < L) : dft (ω ^ (L - 1)) L (dft ω L a) j' = (L : A) * a j' := by
  unfold dft
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_eq_single j']
  · have : ∀ k ∈ Finset.range L, (ω ^ (L - 1)) ^ (k * j') * (ω ^ (j' * k) * a j') = a j' := by
      intro k _
      rw [← mul_assoc, ← pow_mul, ← pow_add,
        show (L - 1) * (k * j') + j' * k = L * (k * j') by
          rcases Nat.eq_zero_or_pos L with h | h
          · omega
          · obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
            simp only [Nat.add_sub_cancel]; ring,
        pow_mul, hL, one_pow, one_mul]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · intro j hj hne
    rw [Finset.mem_range] at hj
    have hnd : ¬ L ∣ j + (L - 1) * j' := by
      rintro ⟨c, hc⟩
      have hz : ((L : ℤ)) ∣ (j : ℤ) - j' := by
        refine ⟨(c : ℤ) - j', ?_⟩
        have h1 : ((j + (L - 1) * j' : ℕ) : ℤ) = ((L * c : ℕ) : ℤ) := by rw [hc]
        push_cast [Nat.cast_sub (show 1 ≤ L by omega)] at h1
        linarith
      have := Int.eq_zero_of_abs_lt_dvd hz (abs_sub_lt_iff.2 ⟨by omega, by omega⟩)
      omega
    have h0 := hprin _ hnd
    have : ∀ k ∈ Finset.range L, (ω ^ (L - 1)) ^ (k * j') * (ω ^ (j * k) * a j) =
        (ω ^ (j + (L - 1) * j')) ^ k * a j := by
      intro k _
      rw [← mul_assoc, ← pow_mul, ← pow_mul, ← pow_add]; ring_nf
    rw [Finset.sum_congr rfl this, ← Finset.sum_mul, h0, zero_mul]
  · intro h; exact absurd (Finset.mem_range.2 hj') h

/-! ## S2-G3 framework: mapping a generator over a list; block vectors -/

def mapGen {α β : Type} (f : α → Gen β) : List α → Gen (List β)
  | [] => Gen.pure []
  | a :: as => Gen.bind (f a) fun b => Gen.bind (mapGen f as) fun bs => Gen.pure (b :: bs)

theorem triple_mapGen {R : Type*} [CommRing R] (ι : R → R) {α β : Type} (f : α → Gen β)
    (S : α → β → List R → Prop) (hS : ∀ a b, Stable (S a b)) :
    ∀ (as : List α) (P : List R → Prop), Stable P →
      (∀ a ∈ as, ∀ P' : List R → Prop, Stable P' → (∀ r, P' r → P r) →
        Triple ι (f a) P' (fun b r => P' r ∧ S a b r)) →
      Triple ι (mapGen f as) P (fun bs r => P r ∧ List.Forall₂ (fun a b => S a b r) as bs)
  | [], P, _, _ => triple_pure ι _ _ _ fun _ h => ⟨h, List.Forall₂.nil⟩
  | a :: as, P, hP, hf => by
    refine triple_bind ι _ _ P _ _ (hf a (by simp) P hP (fun _ h => h)) fun b => ?_
    have hP' : Stable (fun r => P r ∧ S a b r) := stable_and _ _ hP (hS a b)
    refine triple_bind ι _ _ _ _ _ (triple_mapGen ι f S hS as _ hP'
      (fun a' ha' P'' hP'' hPP => hf a' (by simp [ha']) P'' hP'' (fun r h => (hPP r h).1)))
      fun bs => ?_
    exact triple_pure ι _ _ _ fun _ h => ⟨h.1.1, List.Forall₂.cons h.1.2 h.2⟩

theorem ops_mapGen {α β : Type} (f : α → Gen β) (B : ℕ) (hB : ∀ a m, (f a).ops m ≤ B) :
    ∀ (as : List α) (n : ℕ), (mapGen f as).ops n ≤ as.length * B
  | [], n => by simp [mapGen, ops_pure]
  | a :: as, n => by
    simp only [mapGen, ops_bind, ops_pure, List.length_cons, Nat.add_zero]
    have h1 := hB a n
    have h2 := ops_mapGen f B hB as ((f a) n).2.2
    rw [Nat.succ_mul]
    omega

theorem forall₂_range_getD {β : Type} {S : ℕ → β → Prop} (d : β) :
    ∀ (L s : ℕ) (bs : List β), List.Forall₂ S (List.range' s L) bs →
      bs.length = L ∧ ∀ i < L, S (s + i) (bs.getD i d)
  | 0, s, bs, h => by
    rw [List.range'_zero] at h
    cases h; simp
  | L + 1, s, bs, h => by
    rw [List.range'_succ] at h
    cases h with
    | cons h1 h2 =>
      obtain ⟨hl, hi⟩ := forall₂_range_getD d L (s + 1) _ h2
      refine ⟨by simp [hl], fun i hi' => ?_⟩
      rcases i with _ | i
      · simpa using h1
      · have := hi i (by omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this

/-- A vector of `L` blocks holding the values `a 0, …, a (L-1)`. -/
def HoldsBF {R : Type*} [CommRing R] (p e : ℕ) (regs : List R) (blks : List (List ℕ)) (L : ℕ)
    (a : ℕ → AdjoinRoot (cyc R p e)) : Prop :=
  blks.length = L ∧ ∀ i < L, HoldsB p e regs (blks.getD i []) (a i)

theorem stable_holdsBF {R : Type*} [CommRing R] (p e : ℕ) (blks : List (List ℕ)) (L : ℕ)
    (a : ℕ → AdjoinRoot (cyc R p e)) : Stable (fun regs : List R => HoldsBF p e regs blks L a) :=
  fun regs new h => ⟨h.1, fun i hi => stable_holdsB p e _ _ regs new (h.2 i hi)⟩

/-- Stride extraction: blocks `p*u + r` for `u < M` (no instructions). -/
def stride (blks : List (List ℕ)) (p r M : ℕ) : List (List ℕ) :=
  (List.range M).map fun u => blks.getD (p * u + r) []

theorem holdsBF_stride {R : Type*} [CommRing R] (p e : ℕ) (regs : List R)
    (blks : List (List ℕ)) (M r : ℕ) (hr : r < p) (a : ℕ → AdjoinRoot (cyc R p e))
    (h : HoldsBF p e regs blks (p * M) a) :
    HoldsBF p e regs (stride blks p r M) M (fun u => a (p * u + r)) := by
  refine ⟨by simp [stride], fun u hu => ?_⟩
  have : (stride blks p r M).getD u [] = blks.getD (p * u + r) [] := by
    simp [stride, List.getD_eq_getElem?_getD, hu]
  rw [this]
  exact h.2 _ (by nlinarith)

/-- Sum of a nonempty list of blocks. -/
def sumBlocks : List (List ℕ) → Gen (List ℕ)
  | [] => Gen.pure []
  | [b] => Gen.pure b
  | b :: b' :: bs => Gen.bind (sumBlocks (b' :: bs)) fun t => vecAddPad b t

theorem triple_sumBlocks {R : Type*} [CommRing R] (ι : R → R) (p e : ℕ) :
    ∀ (bs : List (List ℕ)) (vs : List (AdjoinRoot (cyc R p e))) (P : List R → Prop), Stable P →
      (∀ regs, P regs → List.Forall₂ (HoldsB p e regs) bs vs) → vs ≠ [] →
      Triple ι (sumBlocks bs) P (fun out regs => P regs ∧ HoldsB p e regs out vs.sum)
  | [], vs, P, _, h, hne => triple_of_false ι _ _ _ fun regs hr => by
      have := h regs hr; cases this; exact hne rfl
  | [b], vs, P, _, h, _ => triple_pure ι _ _ _ fun regs hr => by
      have := h regs hr
      cases this with
      | cons h1 h2 => cases h2; exact ⟨hr, by simpa using h1⟩
  | b :: b' :: bs, [], P, _, _, hne => absurd rfl hne
  | b :: b' :: bs, [v], P, _, h, _ => triple_of_false ι _ _ _ fun regs hr => by
      have := h regs hr
      cases this with
      | cons _ h2 => cases h2
  | b :: b' :: bs, v :: v' :: vs, P, hP, h, _ => by
    refine triple_bind ι _ _ P _ _ (triple_sumBlocks ι p e (b' :: bs) (v' :: vs) P hP
      (fun regs hr => (List.forall₂_cons.1 (h regs hr)).2) (by simp)) fun t => ?_
    refine triple_post ι _ _ _ _ (triple_blkAdd ι p e b t v _ _
      (stable_and _ _ hP (stable_holdsB p e t _))
      (fun regs hr => (List.forall₂_cons.1 (h regs hr.1)).1) (fun regs hr => hr.2))
      fun out regs hr => ⟨hr.1.1, by rw [List.sum_cons]; exact hr.2⟩

theorem ops_sumBlocks (D : ℕ) :
    ∀ (bs : List (List ℕ)) (n : ℕ), (∀ b ∈ bs, b.length ≤ D) → (sumBlocks bs).ops n ≤ bs.length * D
  | [], n, _ => by simp [sumBlocks, ops_pure]
  | [b], n, _ => by simp [sumBlocks, ops_pure]
  | b :: b' :: bs, n, hb => by
    simp only [sumBlocks, ops_bind, ops_vecAddPad]
    have h1 := ops_sumBlocks D (b' :: bs) n (fun x hx => hb x (by simp at hx ⊢; tauto))
    have h2 := hb b (by simp)
    have h3 := Nat.min_le_left b.length ((sumBlocks (b' :: bs)) n).1.length
    simp only [List.length_cons] at h1 ⊢
    rw [Nat.succ_mul]
    omega

theorem forall₂_swap_map {α β γ : Type*} (Q : β → γ → Prop) (g : α → γ) :
    ∀ (rs : List α) (bs : List β), List.Forall₂ (fun r b => Q b (g r)) rs bs →
      List.Forall₂ Q bs (rs.map g)
  | [], [], _ => List.Forall₂.nil
  | r :: rs, b :: bs, h => by
    rw [List.map_cons]
    exact List.Forall₂.cons (List.forall₂_cons.1 h).1
      (forall₂_swap_map Q g rs bs (List.forall₂_cons.1 h).2)
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

theorem list_sum_range_map {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∀ p : ℕ, ((List.range p).map g).sum = ∑ r ∈ Finset.range p, g r
  | 0 => by simp
  | p + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_range_map g p,
      Finset.sum_range_succ]
    simp

theorem root_pow_mod {R : Type*} [CommRing R] (p e x : ℕ) :
    AdjoinRoot.root (cyc R p e) ^ (x % (p * e)) = AdjoinRoot.root (cyc R p e) ^ x := by
  conv_rhs => rw [← Nat.mod_add_div x (p * e), pow_add, pow_mul, root_pow_pe, one_pow, mul_one]

/-- One output of a radix-p butterfly: `∑_{r<p} X^(s r k) · A_r[k mod M]`. -/
def twGen (p e s k M : ℕ) (subs : List (List (List ℕ))) : Gen (List ℕ) :=
  Gen.bind (mapGen (fun r => mulXPow e ((p - 1) * e) ((s * r * k) % (p * e))
    ((subs.getD r []).getD (k % M) [])) (List.range p)) sumBlocks

theorem triple_twGen {R : Type*} [CommRing R] (ι : R → R) (p e s k M : ℕ) (hp : 2 ≤ p)
    (he : 0 < e) (hM : 0 < M) (subs : List (List (List ℕ)))
    (A : ℕ → ℕ → AdjoinRoot (cyc R p e)) (P : List R → Prop) (hP : Stable P)
    (hA : ∀ regs, P regs → ∀ r < p, HoldsBF p e regs (subs.getD r []) M (A r)) :
    Triple ι (twGen p e s k M subs) P (fun out regs => P regs ∧ HoldsB p e regs out
      (∑ r ∈ Finset.range p, (AdjoinRoot.root (cyc R p e) ^ s) ^ (r * k) * A r (k % M))) := by
  set g : ℕ → AdjoinRoot (cyc R p e) :=
    fun r => (AdjoinRoot.root (cyc R p e) ^ s) ^ (r * k) * A r (k % M) with hg
  refine triple_bind ι _ _ P _ _ (triple_mapGen ι _ (fun r b regs => HoldsB p e regs b (g r))
    (fun r b => stable_holdsB p e b _) (List.range p) P hP ?_) fun ts => ?_
  · intro r hr P' hP' hPP
    rw [List.mem_range] at hr
    refine triple_post ι _ _ _ _ (triple_mulXPow ι p e hp he _ _ (A r (k % M)) P' hP'
      (fun regs h' => (hA regs (hPP regs h') r hr).2 _ (Nat.mod_lt _ hM))) fun out regs h' =>
      ⟨h'.1, ?_⟩
    have : AdjoinRoot.root (cyc R p e) ^ (s * r * k % (p * e)) * A r (k % M) = g r := by
      rw [root_pow_mod, hg]; simp only; rw [← pow_mul, mul_assoc]
    rw [← this]; exact h'.2
  · refine triple_post ι _ _ _ _ (triple_sumBlocks ι p e ts ((List.range p).map g) _
      (stable_and _ _ hP (fun regs new h => List.Forall₂.imp
        (fun r b hb => stable_holdsB p e b (g r) regs new hb) h))
      (fun regs h => forall₂_swap_map _ g _ _ h.2) (by simp; omega)) fun out regs h =>
      ⟨h.1.1, by rw [← list_sum_range_map]; exact h.2⟩

/-- **Radix-p FFT** of `p^l` blocks with root `X^s` (decimation in time). -/
def fftGen (p e : ℕ) : ℕ → ℕ → List (List ℕ) → Gen (List (List ℕ))
  | 0, _, blks => Gen.pure blks
  | l + 1, s, blks =>
      Gen.bind (mapGen (fun r => fftGen p e l (s * p) (stride blks p r (p ^ l))) (List.range p))
        fun subs => mapGen (fun k => twGen p e s k (p ^ l) subs) (List.range (p * p ^ l))

theorem holdsBF_of_forall₂ {R : Type*} [CommRing R] (p e : ℕ) (regs : List R) (L : ℕ)
    (bs : List (List ℕ)) (a : ℕ → AdjoinRoot (cyc R p e))
    (h : List.Forall₂ (fun k b => HoldsB p e regs b (a k)) (List.range L) bs) :
    HoldsBF p e regs bs L a := by
  rw [List.range_eq_range'] at h
  obtain ⟨hl, hi⟩ := forall₂_range_getD (S := fun k b => HoldsB p e regs b (a k)) [] L 0 bs h
  exact ⟨hl, fun i hi' => by simpa using hi i hi'⟩

theorem triple_fftGen {R : Type*} [CommRing R] (ι : R → R) (p e : ℕ) (hp : 2 ≤ p) (he : 0 < e) :
    ∀ (l s : ℕ) (blks : List (List ℕ)) (a : ℕ → AdjoinRoot (cyc R p e)) (P : List R → Prop),
      Stable P → (∀ regs, P regs → HoldsBF p e regs blks (p ^ l) a) →
      (AdjoinRoot.root (cyc R p e) ^ s) ^ (p ^ l) = 1 →
      Triple ι (fftGen p e l s blks) P (fun out regs => P regs ∧
        HoldsBF p e regs out (p ^ l) (dft (AdjoinRoot.root (cyc R p e) ^ s) (p ^ l) a))
  | 0, s, blks, a, P, _, hb, _ => triple_pure ι _ _ _ fun regs h => ⟨h, by
      refine ⟨(hb regs h).1, fun i hi => ?_⟩
      have hi0 : i = 0 := by simpa using hi
      subst hi0
      rw [pow_zero, dft_one]
      exact (hb regs h).2 0 (by simp)⟩
  | l + 1, s, blks, a, P, hP, hb, hroot => by
    set ω := AdjoinRoot.root (cyc R p e) ^ s with hω
    set M := p ^ l
    have hpow : p ^ (l + 1) = p * M := pow_succ' p l
    have hM : 0 < M := pow_pos (by omega) l
    have hroot' : (ω ^ p) ^ M = 1 := by rw [← pow_mul, ← hpow]; exact hroot
    set A : ℕ → ℕ → AdjoinRoot (cyc R p e) := fun r => dft (ω ^ p) M (fun u => a (p * u + r))
      with hA
    refine triple_bind ι _ _ P _ _ (triple_mapGen ι _
      (fun r sub regs => HoldsBF p e regs sub M (A r))
      (fun r sub => stable_holdsBF p e sub M _) (List.range p) P hP ?_) fun subs => ?_
    · intro r hr P' hP' hPP
      rw [List.mem_range] at hr
      have hroot2 : (AdjoinRoot.root (cyc R p e) ^ (s * p)) ^ p ^ l = 1 := by
        rw [pow_mul]; exact hroot'
      refine triple_post ι _ _ _ _ (triple_fftGen ι p e hp he l (s * p) (stride blks p r M)
        (fun u => a (p * u + r)) P' hP' (fun regs h' => holdsBF_stride p e regs blks M r hr a
          (by rw [← hpow]; exact hb regs (hPP regs h'))) hroot2) fun out regs h' => ⟨h'.1, ?_⟩
      have e1 : AdjoinRoot.root (cyc R p e) ^ (s * p) = ω ^ p := by rw [hω, pow_mul]
      rw [e1] at h'
      exact h'.2
    · have hsub : ∀ regs, (P regs ∧ List.Forall₂ (fun r sub => HoldsBF p e regs sub M (A r))
          (List.range p) subs) → ∀ r < p, HoldsBF p e regs (subs.getD r []) M (A r) := by
        intro regs h r hr
        have h2 := h.2
        rw [List.range_eq_range'] at h2
        have := (forall₂_range_getD (S := fun r sub => HoldsBF p e regs sub M (A r)) [] p 0 subs
          h2).2 r hr
        simpa using this
      refine triple_post ι _ _ _ _ (triple_mapGen ι _
        (fun k b regs => HoldsB p e regs b (dft ω (p * M) a k))
        (fun k b => stable_holdsB p e b _) (List.range (p * M)) _
        (stable_and _ _ hP (fun regs new h => List.Forall₂.imp
          (fun r sub hs => stable_holdsBF p e sub M (A r) regs new hs) h)) ?_) fun out regs h =>
        ⟨h.1.1, by rw [hpow]; exact holdsBF_of_forall₂ p e regs _ out _ h.2⟩
      intro k _ P'' hP'' hPP
      refine triple_post ι _ _ _ _ (triple_twGen ι p e s k M hp he hM subs A P'' hP''
        (fun regs h' => hsub regs (hPP regs h'))) fun out regs h' => ⟨h'.1, ?_⟩
      rw [dft_split ω p M hroot' a k]
      exact h'.2


/-! ## S2-G3 lengths and operation count of the FFT -/

theorem mapGen_length {α β : Type} (f : α → Gen β) :
    ∀ (as : List α) (n : ℕ), ((mapGen f as) n).1.length = as.length
  | [], n => rfl
  | a :: as, n => by
    simp only [mapGen, Gen.bind, Gen.pure, List.length_cons]
    rw [mapGen_length f as]

theorem mapGen_mem {α β : Type} (f : α → Gen β) :
    ∀ (as : List α) (n : ℕ), ∀ b ∈ ((mapGen f as) n).1, ∃ a ∈ as, ∃ m, b = ((f a) m).1
  | [], n, b, hb => by simp [mapGen, Gen.pure] at hb
  | a :: as, n, b, hb => by
    simp only [mapGen, Gen.bind, Gen.pure, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨a, by simp, n, rfl⟩
    · obtain ⟨a', ha', m, rfl⟩ := mapGen_mem f as _ b hb
      exact ⟨a', by simp [ha'], m, rfl⟩

theorem getD_forall {β : Type} (P : β → Prop) (l : List β) (d : β) (h : ∀ x ∈ l, P x)
    (hd : P d) (i : ℕ) : P (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => simpa using hd
  | some b => simpa using h b (List.mem_of_getElem? hi)

theorem getD_length_le (D : ℕ) (bs : List (List ℕ)) (h : ∀ b ∈ bs, b.length ≤ D) (i : ℕ) :
    (bs.getD i []).length ≤ D :=
  getD_forall (fun b : List ℕ => b.length ≤ D) bs [] h (by simp) i

theorem shiftAdd_length (e nt : ℕ) :
    ∀ (k : ℕ) (rs : List ℕ) (n : ℕ), ((shiftAdd e nt k rs) n).1.length = rs.length
  | k, [], n => by cases k <;> simp [shiftAdd, Gen.pure]
  | 0, r :: rs, n => by
    simp only [shiftAdd, Gen.bind, Gen.emit, Gen.pure, List.length_cons]
    rw [shiftAdd_length e nt (e - 1) rs]
  | k + 1, r :: rs, n => by
    simp only [shiftAdd, Gen.bind, Gen.pure, List.length_cons]
    rw [shiftAdd_length e nt k rs]

theorem mulXGen_length (e D : ℕ) (hD : 1 ≤ D) (blk : List ℕ) (n : ℕ) :
    ((mulXGen e D blk) n).1.length ≤ D := by
  simp only [mulXGen, Gen.bind, Gen.emit, Gen.pure, List.length_cons, shiftAdd_length,
    List.length_take]
  omega

theorem mulXPow_length (e D : ℕ) (hD : 1 ≤ D) :
    ∀ (j : ℕ) (blk : List ℕ) (n : ℕ), blk.length ≤ D → ((mulXPow e D j blk) n).1.length ≤ D
  | 0, blk, n, h => by simpa [mulXPow, Gen.pure] using h
  | j + 1, blk, n, _ => by
    simp only [mulXPow, Gen.bind]
    exact mulXPow_length e D hD j _ _ (mulXGen_length e D hD blk n)

theorem vecAddPad_length : ∀ (is js : List ℕ) (n : ℕ),
    ((vecAddPad is js) n).1.length = max is.length js.length
  | i :: is, j :: js, n => by
    simp only [vecAddPad, Gen.bind, Gen.emit, Gen.pure, List.length_cons, vecAddPad_length is js]
    omega
  | [], js, n => by simp [vecAddPad, Gen.pure]
  | _ :: _, [], n => by simp [vecAddPad, Gen.pure]

theorem sumBlocks_length (D : ℕ) :
    ∀ (bs : List (List ℕ)) (n : ℕ), (∀ b ∈ bs, b.length ≤ D) → ((sumBlocks bs) n).1.length ≤ D
  | [], n, _ => by simp [sumBlocks, Gen.pure]
  | [b], n, h => by simpa [sumBlocks, Gen.pure] using h b (by simp)
  | b :: b' :: bs, n, h => by
    simp only [sumBlocks, Gen.bind]
    rw [vecAddPad_length]
    have h1 := sumBlocks_length D (b' :: bs) n (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have h2 := h b (by simp)
    omega

theorem stride_length (D : ℕ) (blks : List (List ℕ)) (p r M : ℕ)
    (h : ∀ b ∈ blks, b.length ≤ D) : ∀ b ∈ stride blks p r M, b.length ≤ D := by
  intro b hb
  simp only [stride, List.mem_map] at hb
  obtain ⟨u, -, rfl⟩ := hb
  exact getD_length_le D blks h _

theorem twGen_mem_length (p e s k M : ℕ) (hp : 2 ≤ p) (he : 0 < e)
    (subs : List (List (List ℕ))) (hs : ∀ sub ∈ subs, ∀ b ∈ sub, b.length ≤ (p - 1) * e) (m : ℕ) :
    ∀ b ∈ ((mapGen (fun r => mulXPow e ((p - 1) * e) ((s * r * k) % (p * e))
      ((subs.getD r []).getD (k % M) [])) (List.range p)) m).1, b.length ≤ (p - 1) * e := by
  have hD : 1 ≤ (p - 1) * e := Nat.mul_pos (by omega) he
  intro b hb
  obtain ⟨r, -, m', rfl⟩ := mapGen_mem _ _ m b hb
  exact mulXPow_length e _ hD _ _ m' (getD_length_le _ _
    (getD_forall (fun sub : List (List ℕ) => ∀ b ∈ sub, b.length ≤ (p - 1) * e) subs [] hs
      (by simp) r) _)

theorem twGen_length (p e s k M : ℕ) (hp : 2 ≤ p) (he : 0 < e) (subs : List (List (List ℕ)))
    (hs : ∀ sub ∈ subs, ∀ b ∈ sub, b.length ≤ (p - 1) * e) (n : ℕ) :
    ((twGen p e s k M subs) n).1.length ≤ (p - 1) * e := by
  unfold twGen
  simp only [Gen.bind]
  exact sumBlocks_length _ _ _ (twGen_mem_length p e s k M hp he subs hs n)

theorem ops_twGen (p e s k M : ℕ) (hp : 2 ≤ p) (he : 0 < e) (subs : List (List (List ℕ)))
    (hs : ∀ sub ∈ subs, ∀ b ∈ sub, b.length ≤ (p - 1) * e) (n : ℕ) :
    (twGen p e s k M subs).ops n ≤ p * (p * e * (p - 1)) + p * ((p - 1) * e) := by
  unfold twGen
  rw [ops_bind]
  have hpe : 0 < p * e := Nat.mul_pos (by omega) he
  have h1 := ops_mapGen (fun r => mulXPow e ((p - 1) * e) ((s * r * k) % (p * e))
    ((subs.getD r []).getD (k % M) [])) (p * e * (p - 1))
    (fun r m => le_trans (ops_mulXPow p e hp he _ _ m)
      (Nat.mul_le_mul_right _ (Nat.mod_lt _ hpe).le)) (List.range p) n
  rw [List.length_range] at h1
  refine Nat.add_le_add h1 ?_
  refine le_trans (ops_sumBlocks ((p - 1) * e) _ _ (twGen_mem_length p e s k M hp he subs hs n)) ?_
  rw [mapGen_length, List.length_range]

theorem fftGen_length (p e : ℕ) (hp : 2 ≤ p) (he : 0 < e) :
    ∀ (l s : ℕ) (blks : List (List ℕ)) (n : ℕ), (∀ b ∈ blks, b.length ≤ (p - 1) * e) →
      ∀ b ∈ ((fftGen p e l s blks) n).1, b.length ≤ (p - 1) * e
  | 0, s, blks, n, h => by simpa [fftGen, Gen.pure] using h
  | l + 1, s, blks, n, h => by
    intro b hb
    simp only [fftGen, Gen.bind] at hb
    obtain ⟨k, -, m, rfl⟩ := mapGen_mem _ _ _ b hb
    refine twGen_length p e s k _ hp he _ ?_ m
    intro sub hsub
    obtain ⟨r, -, m', rfl⟩ := mapGen_mem _ _ _ sub hsub
    exact fftGen_length p e hp he l (s * p) _ m' (stride_length _ blks p r _ h)

theorem ops_fftGen (p e : ℕ) (hp : 2 ≤ p) (he : 0 < e) :
    ∀ (l s : ℕ) (blks : List (List ℕ)) (n : ℕ), (∀ b ∈ blks, b.length ≤ (p - 1) * e) →
      (fftGen p e l s blks).ops n ≤ l * p ^ l * (p * (p * e * (p - 1)) + p * ((p - 1) * e))
  | 0, s, blks, n, _ => by simp [fftGen, ops_pure]
  | l + 1, s, blks, n, h => by
    simp only [fftGen]
    rw [ops_bind]
    have h1 := ops_mapGen (fun r => fftGen p e l (s * p) (stride blks p r (p ^ l)))
      (l * p ^ l * (p * (p * e * (p - 1)) + p * ((p - 1) * e)))
      (fun r m => ops_fftGen p e hp he l (s * p) _ m (stride_length _ blks p r _ h))
      (List.range p) n
    have h2 := ops_mapGen (fun k => twGen p e s k (p ^ l)
      ((mapGen (fun r => fftGen p e l (s * p) (stride blks p r (p ^ l))) (List.range p)) n).1)
      (p * (p * e * (p - 1)) + p * ((p - 1) * e))
      (fun k m => ops_twGen p e s k _ hp he _ (fun sub hsub => by
        obtain ⟨r, -, m', rfl⟩ := mapGen_mem _ _ _ sub hsub
        exact fftGen_length p e hp he l (s * p) _ m' (stride_length _ blks p r _ h)) m)
      (List.range (p * p ^ l))
      ((mapGen (fun r => fftGen p e l (s * p) (stride blks p r (p ^ l))) (List.range p)) n).2.2
    rw [List.length_range] at h1 h2
    refine le_trans (Nat.add_le_add h1 h2) (le_of_eq ?_)
    ring

/-! ## S2-G4 principal roots in `R[X]/(cyc p e)` -/

theorem root_principal {R : Type*} [CommRing R] (p e l : ℕ) (hp : p.Prime) (hdvd : p ^ l ∣ e) :
    (AdjoinRoot.root (cyc R p e) ^ (e / p ^ l)) ^ (p ^ (l + 1)) = 1 ∧
    ∀ i, ¬ p ^ (l + 1) ∣ i →
      ∑ j ∈ Finset.range (p ^ (l + 1)),
        ((AdjoinRoot.root (cyc R p e) ^ (e / p ^ l)) ^ i) ^ j = 0 := by
  have hη : (AdjoinRoot.root (cyc R p e) ^ (e / p ^ l)) ^ (p ^ l) =
      AdjoinRoot.root (cyc R p e) ^ e := by
    rw [← pow_mul, Nat.div_mul_cancel hdvd]
  have hη1 : (AdjoinRoot.root (cyc R p e) ^ e) ^ p = 1 := by
    rw [← pow_mul, mul_comm]; exact root_pow_pe p e
  refine ⟨?_, fun i hi => principal_sum p l hp _ (by rw [hη]; exact hη1)
    (by rw [hη]; exact root_cyc_sum p e) i hi⟩
  rw [pow_succ, pow_mul, hη, hη1]

/-! ## S2-G5 cyclic convolution over blocks -/

/-- Cyclic convolution of length `N`. -/
def cconv {A : Type*} [CommRing A] (N : ℕ) (a b : ℕ → A) (k : ℕ) : A :=
  ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, if (i + j) % N = k then a i * b j else 0

theorem pow_mod_of_pow_eq_one {A : Type*} [CommRing A] (ω : A) (N : ℕ) (hN : ω ^ N = 1)
    (x : ℕ) : ω ^ (x % N) = ω ^ x := by
  conv_rhs => rw [← Nat.mod_add_div x N, pow_add, pow_mul, hN, one_pow, mul_one]

theorem dft_cconv {A : Type*} [CommRing A] (ω : A) (N : ℕ) (hN : ω ^ N = 1) (a b : ℕ → A)
    (k : ℕ) : dft ω N (cconv N a b) k = dft ω N a k * dft ω N b k := by
  unfold dft cconv
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  have hN0 : 0 < N := by
    rw [Finset.mem_range] at hi; omega
  rw [if_pos (Finset.mem_range.2 (Nat.mod_lt _ hN0)), pow_mul, pow_mod_of_pow_eq_one ω N hN,
    ← pow_mul, add_mul, pow_add]
  ring

theorem dft_smul {A : Type*} [CommRing A] (ω : A) (L : ℕ) (c : A) (f : ℕ → A) (k : ℕ) :
    dft ω L (fun j => c * f j) k = c * dft ω L f k := by
  unfold dft; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring

/-- Correctness of a block multiplier (up to the scale factor `sc`). -/
def MulOK {R : Type*} [CommRing R] (ι : R → R) (p e sc : ℕ)
    (mulB : List ℕ → List ℕ → Gen (List ℕ)) : Prop :=
  ∀ (b₁ b₂ : List ℕ) (v₁ v₂ : AdjoinRoot (cyc R p e)) (P : List R → Prop), Stable P →
    (∀ regs, P regs → HoldsB p e regs b₁ v₁) → (∀ regs, P regs → HoldsB p e regs b₂ v₂) →
    Triple ι (mulB b₁ b₂) P (fun out regs => P regs ∧
      HoldsB p e regs out (((sc : ℕ) : AdjoinRoot (cyc R p e)) * (v₁ * v₂)))

/-- Cyclic convolution of two vectors of `p^l` blocks: forward FFTs, pointwise products,
inverse FFT. The output is `p^l` times the convolution. -/
def convGen (p e l s : ℕ) (mulB : List ℕ → List ℕ → Gen (List ℕ)) (as bs : List (List ℕ)) :
    Gen (List (List ℕ)) :=
  Gen.bind (fftGen p e l s as) fun A =>
  Gen.bind (fftGen p e l s bs) fun B =>
  Gen.bind (mapGen (fun k => mulB (A.getD k []) (B.getD k [])) (List.range (p ^ l))) fun C =>
  fftGen p e l (s * (p ^ l - 1)) C

theorem triple_convGen {R : Type*} [CommRing R] (ι : R → R) (p e : ℕ) (hp : 2 ≤ p) (he : 0 < e)
    (l s sc : ℕ) (mulB : List ℕ → List ℕ → Gen (List ℕ)) (hmul : MulOK ι p e sc mulB)
    (as bs : List (List ℕ)) (a b : ℕ → AdjoinRoot (cyc R p e)) (P : List R → Prop)
    (hP : Stable P) (ha : ∀ regs, P regs → HoldsBF p e regs as (p ^ l) a)
    (hb : ∀ regs, P regs → HoldsBF p e regs bs (p ^ l) b)
    (hroot : (AdjoinRoot.root (cyc R p e) ^ s) ^ (p ^ l) = 1)
    (hprin : ∀ i, ¬ p ^ l ∣ i →
      ∑ j ∈ Finset.range (p ^ l), ((AdjoinRoot.root (cyc R p e) ^ s) ^ i) ^ j = 0) :
    Triple ι (convGen p e l s mulB as bs) P (fun out regs => P regs ∧
      HoldsBF p e regs out (p ^ l)
        (fun k => ((p ^ l : ℕ) : AdjoinRoot (cyc R p e)) *
          (((sc : ℕ) : AdjoinRoot (cyc R p e)) * cconv (p ^ l) a b k))) := by
  unfold convGen
  refine triple_bind ι _ _ P _ _ (triple_fftGen ι p e hp he l s as a P hP ha hroot) fun A => ?_
  have hP1 : Stable (fun regs => P regs ∧ HoldsBF p e regs A (p ^ l)
      (dft (AdjoinRoot.root (cyc R p e) ^ s) (p ^ l) a)) :=
    stable_and _ _ hP (stable_holdsBF p e A _ _)
  refine triple_bind ι _ _ _ _ _ (triple_fftGen ι p e hp he l s bs b _ hP1
    (fun regs h => hb regs h.1) hroot) fun B => ?_
  have hP2 : Stable (fun regs => (P regs ∧ HoldsBF p e regs A (p ^ l)
      (dft (AdjoinRoot.root (cyc R p e) ^ s) (p ^ l) a)) ∧ HoldsBF p e regs B (p ^ l)
      (dft (AdjoinRoot.root (cyc R p e) ^ s) (p ^ l) b)) :=
    stable_and _ _ hP1 (stable_holdsBF p e B _ _)
  refine triple_bind ι _ _ _ _ _ (triple_mapGen ι _
    (fun k blk regs => HoldsB p e regs blk (((sc : ℕ) : AdjoinRoot (cyc R p e)) *
      (dft (AdjoinRoot.root (cyc R p e) ^ s) (p ^ l) a k *
        dft (AdjoinRoot.root (cyc R p e) ^ s) (p ^ l) b k)))
    (fun k blk => stable_holdsB p e blk _) (List.range (p ^ l)) _ hP2 ?_) fun C => ?_
  · intro k hk P' hP' hPP
    rw [List.mem_range] at hk
    exact hmul _ _ _ _ P' hP' (fun regs h => ((hPP regs h).1.2).2 k hk)
      (fun regs h => ((hPP regs h).2).2 k hk)
  · have hroot' : (AdjoinRoot.root (cyc R p e) ^ (s * (p ^ l - 1))) ^ (p ^ l) = 1 := by
      rw [pow_mul, ← pow_mul, mul_comm (p ^ l - 1) (p ^ l), pow_mul, hroot, one_pow]
    refine triple_post ι _ _ _ _ (triple_fftGen ι p e hp he l (s * (p ^ l - 1)) C
      (fun k => ((sc : ℕ) : AdjoinRoot (cyc R p e)) *
        (dft (AdjoinRoot.root (cyc R p e) ^ s) (p ^ l) a k *
        dft (AdjoinRoot.root (cyc R p e) ^ s) (p ^ l) b k)) _
      (stable_and _ _ hP2 (fun regs new h => List.Forall₂.imp
        (fun k blk hb => stable_holdsB p e blk _ regs new hb) h))
      (fun regs h => holdsBF_of_forall₂ p e regs _ C _ h.2) hroot') fun out regs h =>
        ⟨h.1.1.1.1, ?_⟩
    refine ⟨h.2.1, fun j hj => ?_⟩
    have hcc : (fun k => ((sc : ℕ) : AdjoinRoot (cyc R p e)) *
        (dft (AdjoinRoot.root (cyc R p e) ^ s) (p ^ l) a k *
        dft (AdjoinRoot.root (cyc R p e) ^ s) (p ^ l) b k)) =
        dft (AdjoinRoot.root (cyc R p e) ^ s) (p ^ l)
          (fun j => ((sc : ℕ) : AdjoinRoot (cyc R p e)) * cconv (p ^ l) a b j) :=
      funext fun k => by rw [dft_smul, dft_cconv _ _ hroot a b k]
    have h3 := h.2.2 j hj
    rw [hcc, show AdjoinRoot.root (cyc R p e) ^ (s * (p ^ l - 1)) =
      (AdjoinRoot.root (cyc R p e) ^ s) ^ (p ^ l - 1) by rw [pow_mul],
      dft_inv _ _ hroot hprin _ j hj] at h3
    exact h3

theorem ops_convGen (p e : ℕ) (hp : 2 ≤ p) (he : 0 < e) (l s : ℕ)
    (mulB : List ℕ → List ℕ → Gen (List ℕ)) (Bm : ℕ)
    (hmo : ∀ b₁ b₂ n, b₁.length ≤ (p - 1) * e → b₂.length ≤ (p - 1) * e →
      (mulB b₁ b₂).ops n ≤ Bm)
    (hml : ∀ b₁ b₂ n, b₁.length ≤ (p - 1) * e → b₂.length ≤ (p - 1) * e →
      ((mulB b₁ b₂) n).1.length ≤ (p - 1) * e)
    (as bs : List (List ℕ)) (ha : ∀ b ∈ as, b.length ≤ (p - 1) * e)
    (hb : ∀ b ∈ bs, b.length ≤ (p - 1) * e) (n : ℕ) :
    (convGen p e l s mulB as bs).ops n ≤
      3 * (l * p ^ l * (p * (p * e * (p - 1)) + p * ((p - 1) * e))) + p ^ l * Bm := by
  unfold convGen
  simp only [ops_bind]
  have hA := fftGen_length p e hp he l s as n ha
  have hB := fftGen_length p e hp he l s bs ((fftGen p e l s as) n).2.2 hb
  have h1 := ops_fftGen p e hp he l s as n ha
  have h2 := ops_fftGen p e hp he l s bs ((fftGen p e l s as) n).2.2 hb
  have h3 := ops_mapGen (fun k => mulB (((fftGen p e l s as) n).1.getD k [])
    (((fftGen p e l s bs) ((fftGen p e l s as) n).2.2).1.getD k [])) Bm
    (fun k m => hmo _ _ m (getD_length_le _ _ hA k) (getD_length_le _ _ hB k))
    (List.range (p ^ l)) ((fftGen p e l s bs) ((fftGen p e l s as) n).2.2).2.2
  rw [List.length_range] at h3
  have h4 := ops_fftGen p e hp he l (s * (p ^ l - 1))
    ((mapGen (fun k => mulB (((fftGen p e l s as) n).1.getD k [])
      (((fftGen p e l s bs) ((fftGen p e l s as) n).2.2).1.getD k [])) (List.range (p ^ l)))
        ((fftGen p e l s bs) ((fftGen p e l s as) n).2.2).2.2).1
    ((mapGen (fun k => mulB (((fftGen p e l s as) n).1.getD k [])
      (((fftGen p e l s bs) ((fftGen p e l s as) n).2.2).1.getD k [])) (List.range (p ^ l)))
        ((fftGen p e l s bs) ((fftGen p e l s as) n).2.2).2.2).2.2
    (fun b hb' => by
      obtain ⟨k, -, m, rfl⟩ := mapGen_mem _ _ _ b hb'
      exact hml _ _ m (getD_length_le _ _ hA k) (getD_length_le _ _ hB k))
  omega


/-! ## S2-G6a list plumbing, the final reduction modulo `cyc p n`, overlap-add -/

open Polynomial in
theorem toPoly_append {R : Type*} [CommRing R] :
    ∀ as bs : List R, toPoly (as ++ bs) = toPoly as + X ^ as.length * toPoly bs
  | [], bs => by simp [toPoly]
  | a :: as, bs => by
    simp only [List.cons_append, toPoly, toPoly_append as bs, List.length_cons, pow_succ]; ring

open Polynomial in
theorem toPoly_take_drop {R : Type*} [CommRing R] (vs : List R) (n : ℕ) (h : n ≤ vs.length) :
    toPoly vs = toPoly (vs.take n) + X ^ n * toPoly (vs.drop n) := by
  conv_lhs => rw [← List.take_append_drop n vs]
  rw [toPoly_append, List.length_take, min_eq_left h]

/-- The `q`-th chunk of length `n`. -/
def chunk {α : Type*} (vs : List α) (n q : ℕ) : List α := (vs.drop (q * n)).take n

theorem chunk_length_le {α : Type*} (vs : List α) (n q : ℕ) : (chunk vs n q).length ≤ n := by
  simp [chunk]

theorem chunk_length {α : Type*} (vs : List α) (n q : ℕ) (h : q * n + n ≤ vs.length) :
    (chunk vs n q).length = n := by
  simp only [chunk, List.length_take, List.length_drop]; omega

open Polynomial in
theorem toPoly_chunks {R : Type*} [CommRing R] (n : ℕ) :
    ∀ (c : ℕ) (vs : List R), vs.length = c * n →
      toPoly vs = ∑ q ∈ Finset.range c, X ^ (q * n) * toPoly (chunk vs n q)
  | 0, vs, h => by
    have : vs = [] := by simpa using h
    subst this; simp [toPoly]
  | c + 1, vs, h => by
    have hle : n ≤ vs.length := by rw [h, Nat.add_mul, one_mul]; omega
    have hl' : (vs.drop n).length = c * n := by
      rw [List.length_drop, h, Nat.add_mul, one_mul, Nat.add_sub_cancel]
    have hc : ∀ q, chunk (vs.drop n) n q = chunk vs n (q + 1) := by
      intro q; simp only [chunk, List.drop_drop]; congr 2; ring
    rw [Finset.sum_range_succ', toPoly_take_drop vs n hle, toPoly_chunks n c (vs.drop n) hl',
      Finset.mul_sum]
    simp only [hc]
    rw [add_comm]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr rfl fun q _ => ?_; ring
    · simp [chunk]

open Polynomial in
theorem toPoly_flatten {R : Type*} [CommRing R] (n : ℕ) :
    ∀ (ws : List (List R)), (∀ w ∈ ws, w.length = n) →
      toPoly ws.flatten = ∑ q ∈ Finset.range ws.length, X ^ (q * n) * toPoly (ws.getD q [])
  | [], _ => by simp [toPoly]
  | w :: ws, h => by
    rw [List.flatten_cons, toPoly_append, toPoly_flatten n ws
      (fun x hx => h x (List.mem_cons_of_mem _ hx)), List.length_cons, Finset.sum_range_succ',
      h w (by simp), Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [add_comm]; refine congrArg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr rfl fun q _ => ?_; ring
    · simp

theorem length_flatten_const {β : Type*} (n : ℕ) :
    ∀ (ws : List (List β)), (∀ w ∈ ws, w.length = n) → ws.flatten.length = ws.length * n
  | [], _ => by simp
  | w :: ws, h => by
    rw [List.flatten_cons, List.length_append, length_flatten_const n ws
      (fun x hx => h x (List.mem_cons_of_mem _ hx)), h w (by simp), List.length_cons]
    ring

theorem holdsVec_flatten {R : Type*} [CommRing R] (regs : List R) :
    ∀ (bs : List (List ℕ)) (ws : List (List R)), List.Forall₂ (HoldsVec regs) bs ws →
      HoldsVec regs bs.flatten ws.flatten
  | [], [], _ => List.Forall₂.nil
  | b :: bs, w :: ws, h => by
    rw [List.flatten_cons, List.flatten_cons]
    exact List.rel_append (List.forall₂_cons.1 h).1
      (holdsVec_flatten regs bs ws (List.forall₂_cons.1 h).2)
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

theorem holdsVec_chunk {R : Type*} [CommRing R] (regs : List R) (H : List ℕ) (hv : List R)
    (h : HoldsVec regs H hv) (n q : ℕ) : HoldsVec regs (chunk H n q) (chunk hv n q) :=
  List.forall₂_take _ (List.forall₂_drop _ h)

/-- Reduce `(p+1) n` coefficients modulo `cyc p n` (using `X^(p n) = 1`). -/
def reduceGen (p n : ℕ) (H : List ℕ) : Gen (List ℕ) :=
  Gen.bind (vecNeg (chunk H n (p - 1))) fun t =>
  Gen.bind (mapGen (fun q => if q = 0 then
      Gen.bind (vecAddPad (chunk H n 0) t) fun s => vecAddPad s (chunk H n p)
    else vecAddPad (chunk H n q) t) (List.range (p - 1))) fun S =>
  Gen.pure S.flatten

/-- Value of the `q`-th output chunk of the reduction. -/
def redVal {R : Type*} [CommRing R] (p n : ℕ) (hv : List R) (q : ℕ) : List R :=
  if q = 0 then listAddPad (listAddPad (chunk hv n 0) ((chunk hv n (p - 1)).map Neg.neg))
    (chunk hv n p)
  else listAddPad (chunk hv n q) ((chunk hv n (p - 1)).map Neg.neg)

open Polynomial in
theorem triple_reduceGen {R : Type*} [CommRing R] (ι : R → R) (p n : ℕ) (hp : 2 ≤ p)
    (H : List ℕ) (hv : List R) (hlen : hv.length = (p + 1) * n) (P : List R → Prop)
    (hP : Stable P) (hH : ∀ regs, P regs → HoldsVec regs H hv) :
    Triple ι (reduceGen p n H) P (fun out regs => P regs ∧
      HoldsB p n regs out (AdjoinRoot.mk (cyc R p n) (toPoly hv))) := by
  have hcl : ∀ q, q ≤ p → (chunk hv n q).length = n := fun q hq =>
    chunk_length hv n q (by rw [hlen]; nlinarith)
  have hwl : ∀ q, q < p - 1 → (redVal p n hv q).length = n := by
    intro q hq
    unfold redVal
    split_ifs <;> simp only [listAddPad_length, List.length_map, hcl 0 (by omega),
      hcl (p - 1) (by omega), hcl p le_rfl, hcl q (by omega), max_self]
  unfold reduceGen
  refine triple_bind ι _ _ P _ _ (triple_vecNeg ι _ _ P hP
    (fun regs h => holdsVec_chunk regs H hv (hH regs h) n (p - 1))) fun tb => ?_
  have hP1 : Stable (fun regs => P regs ∧
      HoldsVec regs tb ((chunk hv n (p - 1)).map Neg.neg)) :=
    stable_and _ _ hP (stable_holdsVec _ _)
  refine triple_bind ι _ _ _ _ _ (triple_mapGen ι _
    (fun q b regs => HoldsVec regs b (redVal p n hv q))
    (fun q b => stable_holdsVec _ _) (List.range (p - 1)) _ hP1 ?_) fun S => ?_
  · intro q _ P' hP' hPP
    beta_reduce
    by_cases hq0 : q = 0
    · subst hq0
      rw [if_pos rfl]
      refine triple_bind ι _ _ P' _ _ (triple_vecAddPad ι _ _ _ _ P' hP'
        (fun regs h => holdsVec_chunk regs H hv (hH regs (hPP regs h).1) n 0)
        (fun regs h => (hPP regs h).2)) fun s => ?_
      refine triple_post ι _ _ _ _ (triple_vecAddPad ι _ _ _ _ _
        (stable_and _ _ hP' (stable_holdsVec _ _)) (fun regs h => h.2)
        (fun regs h => holdsVec_chunk regs H hv (hH regs (hPP regs h.1).1) n p))
        fun out regs h => ⟨h.1.1, by rw [redVal, if_pos rfl]; exact h.2⟩
    · rw [if_neg hq0]
      refine triple_post ι _ _ _ _ (triple_vecAddPad ι _ _ _ _ P' hP'
        (fun regs h => holdsVec_chunk regs H hv (hH regs (hPP regs h).1) n q)
        (fun regs h => (hPP regs h).2)) fun out regs h =>
          ⟨h.1, by rw [redVal, if_neg hq0]; exact h.2⟩
  · have hwl' : ∀ w ∈ (List.range (p - 1)).map (redVal p n hv), w.length = n := fun w hw => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hw
      exact hwl q (List.mem_range.1 hq)
    refine triple_pure ι _ _ _ fun regs h => ⟨h.1.1,
      ((List.range (p - 1)).map (redVal p n hv)).flatten,
      holdsVec_flatten regs S _ (forall₂_swap_map (HoldsVec regs) (redVal p n hv) _ _ h.2),
      ?_, ?_⟩
    · rw [length_flatten_const n _ hwl', List.length_map, List.length_range]
    · rw [toPoly_flatten n _ hwl', toPoly_chunks n (p + 1) hv hlen, map_sum, map_sum]
      simp only [List.length_map, List.length_range, map_mul, map_pow, AdjoinRoot.mk_X]
      have hw : ∀ q ∈ Finset.range (p - 1), AdjoinRoot.root (cyc R p n) ^ (q * n) *
          AdjoinRoot.mk (cyc R p n)
            (toPoly (((List.range (p - 1)).map (redVal p n hv)).getD q [])) =
          AdjoinRoot.root (cyc R p n) ^ (q * n) *
            AdjoinRoot.mk (cyc R p n) (toPoly (chunk hv n q)) -
          AdjoinRoot.root (cyc R p n) ^ (q * n) *
            AdjoinRoot.mk (cyc R p n) (toPoly (chunk hv n (p - 1))) +
          if q = 0 then AdjoinRoot.mk (cyc R p n) (toPoly (chunk hv n p)) else 0 := by
        intro q hq
        rw [Finset.mem_range] at hq
        have e1 : ((List.range (p - 1)).map (redVal p n hv)).getD q [] = redVal p n hv q := by
          simp [List.getD_eq_getElem?_getD, hq]
        rw [e1, redVal]
        split_ifs with h0
        · subst h0
          simp only [toPoly_listAddPad, toPoly_map_neg, map_add, map_neg, zero_mul, pow_zero]
          ring
        · simp only [toPoly_listAddPad, toPoly_map_neg, map_add, map_neg]
          ring
      rw [Finset.sum_congr rfl hw, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_ite_eq', if_pos (Finset.mem_range.2 (by omega)), ← Finset.sum_mul,
        show p + 1 = p - 1 + 1 + 1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
        show p - 1 + 1 = p by omega]
      have hcyc : ∑ q ∈ Finset.range (p - 1), AdjoinRoot.root (cyc R p n) ^ (q * n) +
          AdjoinRoot.root (cyc R p n) ^ ((p - 1) * n) = 0 := by
        have h := root_cyc_sum (R := R) p n
        rw [show Finset.range p = Finset.range (p - 1 + 1) by congr 1; omega,
          Finset.sum_range_succ] at h
        simpa only [← pow_mul'] using h
      linear_combination (-AdjoinRoot.mk (cyc R p n) (toPoly (chunk hv n (p - 1)))) * hcyc -
        AdjoinRoot.mk (cyc R p n) (toPoly (chunk hv n p)) * root_pow_pe (R := R) p n

theorem ops_reduceGen (p n : ℕ) (H : List ℕ) (m : ℕ) :
    (reduceGen p n H).ops m ≤ n + (p - 1) * (2 * n) := by
  have hc : ∀ q, (chunk H n q).length ≤ n := fun q => chunk_length_le H n q
  unfold reduceGen
  rw [ops_bind, ops_bind, ops_pure, Nat.add_zero, ops_vecNeg]
  refine Nat.add_le_add (hc _) (le_trans (ops_mapGen _ (2 * n) (fun q k => ?_) _ _) (by simp))
  beta_reduce
  split_ifs
  · rw [ops_bind, ops_vecAddPad, ops_vecAddPad]
    have := hc 0; have := hc p
    omega
  · rw [ops_vecAddPad]; have := hc q; omega

theorem length_flatten_le {β : Type*} (n : ℕ) :
    ∀ (ws : List (List β)), (∀ w ∈ ws, w.length ≤ n) → ws.flatten.length ≤ ws.length * n
  | [], _ => by simp
  | w :: ws, h => by
    rw [List.flatten_cons, List.length_append, List.length_cons, Nat.succ_mul]
    have h1 := length_flatten_le n ws (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have h2 := h w (by simp)
    omega

theorem vecNeg_length : ∀ (js : List ℕ) (n : ℕ), ((vecNeg js) n).1.length = js.length
  | [], n => rfl
  | j :: js, n => by
    simp only [vecNeg, Gen.bind, Gen.emit, Gen.pure, List.length_cons]
    rw [vecNeg_length js]

theorem reduceGen_length (p n : ℕ) (H : List ℕ) (m : ℕ) :
    ((reduceGen p n H) m).1.length ≤ (p - 1) * n := by
  have hc : ∀ q, (chunk H n q).length ≤ n := fun q => chunk_length_le H n q
  have h3 : ((vecNeg (chunk H n (p - 1))) m).1.length ≤ n := by
    rw [vecNeg_length]; exact hc _
  unfold reduceGen
  simp only [Gen.bind, Gen.pure]
  refine le_trans (length_flatten_le n _ ?_) (by rw [mapGen_length, List.length_range])
  intro b hb
  obtain ⟨q, -, k, rfl⟩ := mapGen_mem _ _ _ b hb
  beta_reduce
  split_ifs
  · simp only [Gen.bind, vecAddPad_length]
    have := hc 0; have := hc p
    omega
  · rw [vecAddPad_length]
    have := hc q
    omega

/-- Add the block `Q` into the accumulator at offset `o`. -/
def addAt (o : ℕ) (acc Q : List ℕ) : Gen (List ℕ) :=
  Gen.bind (vecAddPad (acc.drop o) Q) fun t => Gen.pure (acc.take o ++ t)

def addAtVal {R : Type*} [CommRing R] (o : ℕ) (av qv : List R) : List R :=
  av.take o ++ listAddPad (av.drop o) qv

open Polynomial in
theorem toPoly_addAtVal {R : Type*} [CommRing R] (o : ℕ) (av qv : List R) (h : o ≤ av.length) :
    toPoly (addAtVal o av qv) = toPoly av + X ^ o * toPoly qv := by
  rw [addAtVal, toPoly_append, toPoly_listAddPad, List.length_take, min_eq_left h,
    toPoly_take_drop av o h]
  ring

theorem addAtVal_length {R : Type*} [CommRing R] (o : ℕ) (av qv : List R)
    (h : o + qv.length ≤ av.length) : (addAtVal o av qv).length = av.length := by
  rw [addAtVal, List.length_append, listAddPad_length, List.length_take, List.length_drop]
  omega

theorem triple_addAt {R : Type*} [CommRing R] (ι : R → R) (o : ℕ) (acc Q : List ℕ)
    (av qv : List R) (P : List R → Prop) (hP : Stable P)
    (ha : ∀ regs, P regs → HoldsVec regs acc av) (hq : ∀ regs, P regs → HoldsVec regs Q qv) :
    Triple ι (addAt o acc Q) P (fun out regs => P regs ∧ HoldsVec regs out (addAtVal o av qv)) := by
  unfold addAt
  refine triple_bind ι _ _ P _ _ (triple_vecAddPad ι _ _ (av.drop o) qv P hP
    (fun regs h => List.forall₂_drop o (ha regs h)) hq) fun t => ?_
  exact triple_pure ι _ _ _ fun regs h =>
    ⟨h.1, List.rel_append (List.forall₂_take o (ha regs h.1)) h.2⟩

theorem ops_addAt (o : ℕ) (acc Q : List ℕ) (n : ℕ) : (addAt o acc Q).ops n ≤ Q.length := by
  unfold addAt
  rw [ops_bind, ops_pure, ops_vecAddPad]
  omega

theorem addAt_length (o : ℕ) (acc Q : List ℕ) (n : ℕ) (h : o + Q.length ≤ acc.length) :
    ((addAt o acc Q) n).1.length = acc.length := by
  simp only [addAt, Gen.bind, Gen.pure, List.length_append, vecAddPad_length, List.length_take,
    List.length_drop]
  omega

/-- Overlap-add: add block `i` of `bs` at offset `m * (k + i)`. -/
def overlapGen (m : ℕ) : ℕ → List ℕ → List (List ℕ) → Gen (List ℕ)
  | _, acc, [] => Gen.pure acc
  | k, acc, b :: bs => Gen.bind (addAt (m * k) acc b) fun acc' => overlapGen m (k + 1) acc' bs

def overlapVal {R : Type*} [CommRing R] (m : ℕ) : ℕ → List R → List (List R) → List R
  | _, av, [] => av
  | k, av, w :: ws => overlapVal m (k + 1) (addAtVal (m * k) av w) ws

theorem triple_overlapGen {R : Type*} [CommRing R] (ι : R → R) (m : ℕ) :
    ∀ (bs : List (List ℕ)) (ws : List (List R)) (k : ℕ) (acc : List ℕ) (av : List R)
      (P : List R → Prop), Stable P → (∀ regs, P regs → HoldsVec regs acc av) →
      (∀ regs, P regs → List.Forall₂ (HoldsVec regs) bs ws) →
      Triple ι (overlapGen m k acc bs) P
        (fun out regs => P regs ∧ HoldsVec regs out (overlapVal m k av ws))
  | [], [], k, acc, av, P, _, ha, _ => triple_pure ι _ _ _ fun regs h => ⟨h, ha regs h⟩
  | b :: bs, w :: ws, k, acc, av, P, hP, ha, hb => by
    refine triple_bind ι _ _ P _ _ (triple_addAt ι (m * k) acc b av w P hP ha
      (fun regs h => (List.forall₂_cons.1 (hb regs h)).1)) fun acc' => ?_
    exact triple_post ι _ _ _ _ (triple_overlapGen ι m bs ws (k + 1) acc' _ _
      (stable_and _ _ hP (stable_holdsVec _ _)) (fun regs h => h.2)
      (fun regs h => (List.forall₂_cons.1 (hb regs h.1)).2)) fun out regs h => ⟨h.1.1, h.2⟩
  | [], _ :: _, k, acc, av, P, _, _, hb => triple_of_false ι _ _ _ fun regs h => by
      have := hb regs h; cases this
  | _ :: _, [], k, acc, av, P, _, _, hb => triple_of_false ι _ _ _ fun regs h => by
      have := hb regs h; cases this

open Polynomial in
theorem overlapVal_spec {R : Type*} [CommRing R] (m T : ℕ) :
    ∀ (ws : List (List R)) (k : ℕ) (av : List R), av.length = T →
      (∀ i < ws.length, m * (k + i) + (ws.getD i []).length ≤ T) →
      (overlapVal m k av ws).length = T ∧
      toPoly (overlapVal m k av ws) = toPoly av +
        ∑ i ∈ Finset.range ws.length, X ^ (m * (k + i)) * toPoly (ws.getD i [])
  | [], k, av, h, _ => ⟨h, by simp [overlapVal]⟩
  | w :: ws, k, av, h, hw => by
    have h0 := hw 0 (by simp)
    simp only [Nat.add_zero, List.getD_cons_zero] at h0
    have hl : (addAtVal (m * k) av w).length = T := by rw [addAtVal_length _ _ _ (by omega), h]
    obtain ⟨ih1, ih2⟩ := overlapVal_spec m T ws (k + 1) _ hl (fun i hi => by
      have := hw (i + 1) (by simp; omega)
      have e : k + 1 + i = k + (i + 1) := by omega
      rw [e]; simpa using this)
    refine ⟨ih1, ?_⟩
    rw [show overlapVal m k av (w :: ws) = overlapVal m (k + 1) (addAtVal (m * k) av w) ws from rfl,
      ih2, toPoly_addAtVal _ _ _ (by omega), List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_zero]
    have e : ∀ i, m * (k + 1 + i) = m * (k + (i + 1)) := fun i => by ring
    simp only [e]
    ring

theorem ops_overlapGen (m D : ℕ) :
    ∀ (bs : List (List ℕ)) (k : ℕ) (acc : List ℕ) (n : ℕ), (∀ b ∈ bs, b.length ≤ D) →
      (overlapGen m k acc bs).ops n ≤ bs.length * D
  | [], k, acc, n, _ => by simp [overlapGen, ops_pure]
  | b :: bs, k, acc, n, h => by
    simp only [overlapGen]
    rw [ops_bind, List.length_cons, Nat.succ_mul]
    have h1 := ops_addAt (m * k) acc b n
    have h2 := ops_overlapGen m D bs (k + 1) ((addAt (m * k) acc b) n).1
      ((addAt (m * k) acc b) n).2.2 (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have h3 := h b (by simp)
    omega


/-! ## S2-G6b the Schoenhage step: `R[X]/(cyc p n)` via convolution over `R[X]/(cyc p m')` -/

open Polynomial in
theorem toPoly_natDegree_le {R : Type*} [CommRing R] (vs : List R) :
    (toPoly vs).natDegree ≤ vs.length - 1 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro t ht
  rw [toPoly_coeff]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show vs.length ≤ t by omega)]

open Polynomial in
theorem toPoly_degree_lt {R : Type*} [CommRing R] (vs : List R) (D : ℕ) (h : vs.length ≤ D) :
    (toPoly vs).degree < D := by
  rw [degree_lt_iff_coeff_zero]
  intro t ht
  rw [toPoly_coeff]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show vs.length ≤ t by omega)]

open Polynomial in
theorem toPoly_replicate_zero {R : Type*} [CommRing R] :
    ∀ k : ℕ, toPoly (List.replicate k (0 : R)) = 0
  | 0 => rfl
  | k + 1 => by
    rw [List.replicate_succ, toPoly, toPoly_replicate_zero k]; simp

theorem holdsVec_replicate {R : Type*} [CommRing R] (regs : List R) (z : ℕ) (v : R)
    (h : Holds regs z v) : ∀ k, HoldsVec regs (List.replicate k z) (List.replicate k v)
  | 0 => List.Forall₂.nil
  | k + 1 => List.Forall₂.cons h (holdsVec_replicate regs z v h k)

open Polynomial in
theorem cyc_monic_deg {R : Type*} [CommRing R] [Nontrivial R] (p e : ℕ) (hp : 2 ≤ p)
    (he : 0 < e) : (cyc R p e).Monic ∧ (cyc R p e).degree = ((p - 1) * e : ℕ) := by
  have hsplit : cyc R p e = X ^ ((p - 1) * e) + ∑ i ∈ Finset.range (p - 1), X ^ (i * e) := by
    unfold cyc
    rw [show Finset.range p = Finset.range (p - 1 + 1) by congr 1; omega,
      Finset.sum_range_succ, add_comm]
  have hlow : (∑ i ∈ Finset.range (p - 1), (X : R[X]) ^ (i * e)).degree <
      ((p - 1) * e : ℕ) := by
    rw [← mem_degreeLT]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [mem_degreeLT, degree_X_pow]
    rw [Finset.mem_range] at hi
    have : i * e < (p - 1) * e := by nlinarith
    exact_mod_cast this
  rw [hsplit]
  refine ⟨monic_X_pow_add hlow, ?_⟩
  rw [degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]

open Polynomial in
/-- **No wrap-around**: two polynomials of degree `< (p-1) e` equal modulo `cyc p e` are equal. -/
theorem no_wrap {R : Type*} [CommRing R] (p e : ℕ) (hp : 2 ≤ p) (he : 0 < e) (P Q : R[X])
    (hP : P.degree < ((p - 1) * e : ℕ)) (hQ : Q.degree < ((p - 1) * e : ℕ))
    (h : AdjoinRoot.mk (cyc R p e) P = AdjoinRoot.mk (cyc R p e) Q) : P = Q := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  obtain ⟨hmon, hdeg⟩ := cyc_monic_deg (R := R) p e hp he
  rw [AdjoinRoot.mk_eq_mk] at h
  have hlt : (P - Q).degree < (cyc R p e).degree := by
    rw [hdeg]; exact lt_of_le_of_lt (degree_sub_le P Q) (max_lt hP hQ)
  have h1 := (modByMonic_eq_zero_iff_dvd hmon).2 h
  rw [(modByMonic_eq_self_iff hmon).2 hlt] at h1
  exact sub_eq_zero.1 h1

theorem map_cconv {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (N : ℕ) (a b : ℕ → A)
    (k : ℕ) : φ (cconv N a b k) = cconv N (fun j => φ (a j)) (fun j => φ (b j)) k := by
  unfold cconv
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

open Polynomial in
theorem cconv_mem_degreeLT {R : Type*} [CommRing R] (N m D : ℕ) (F G : ℕ → R[X])
    (hF : ∀ j, (F j).natDegree ≤ m - 1) (hG : ∀ j, (G j).natDegree ≤ m - 1) (hm : 0 < m)
    (hD : 2 * m ≤ D + 1) (k : ℕ) : cconv N F G k ∈ degreeLT R D := by
  unfold cconv
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  split_ifs
  · rw [mem_degreeLT, degree_lt_iff_coeff_zero]
    intro t ht
    apply coeff_eq_zero_of_natDegree_lt
    have := natDegree_mul_le (p := F i) (q := G j)
    have := hF i
    have := hG j
    omega
  · exact Submodule.zero_mem _

open Polynomial in
theorem toPoly_chunks_ext {R : Type*} [CommRing R] (n c0 c : ℕ) (vs : List R)
    (h : vs.length = c0 * n) (hc : c0 ≤ c) :
    toPoly vs = ∑ q ∈ Finset.range c, X ^ (q * n) * toPoly (chunk vs n q) := by
  rw [toPoly_chunks n c0 vs h]
  refine Finset.sum_subset (Finset.range_subset_range.2 hc) fun q _ hq => ?_
  rw [Finset.mem_range, not_lt] at hq
  have : chunk vs n q = [] := by
    simp only [chunk]
    rw [List.drop_eq_nil_of_le (by rw [h]; exact Nat.mul_le_mul_right _ hq), List.take_nil]
  rw [this]; simp [toPoly]

theorem forall₂_of_getD {α β : Type*} {S : α → β → Prop} (d : α) :
    ∀ (C : List α) (W : ℕ → β), (∀ k < C.length, S (C.getD k d) (W k)) →
      List.Forall₂ S C ((List.range C.length).map W)
  | [], W, _ => by simp
  | c :: cs, W, h => by
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    exact List.Forall₂.cons (by simpa using h 0 (by simp))
      (forall₂_of_getD d cs (W ∘ Nat.succ) (fun k hk => by simpa using h (k + 1) (by simp; omega)))

/-- Pad a chunk with copies of the zero register `z` up to length `D`. -/
def padBlk (z D : ℕ) (c : List ℕ) : List ℕ := c ++ List.replicate (D - c.length) z

theorem padBlk_length (z D : ℕ) (c : List ℕ) (h : c.length ≤ D) : (padBlk z D c).length = D := by
  simp [padBlk]; omega

theorem holdsB_padBlk {R : Type*} [CommRing R] (p e : ℕ) (regs : List R) (z : ℕ)
    (hz : Holds regs z 0) (c : List ℕ) (cv : List R) (hc : HoldsVec regs c cv)
    (hl : cv.length ≤ (p - 1) * e) :
    HoldsB p e regs (padBlk z ((p - 1) * e) c) (AdjoinRoot.mk (cyc R p e) (toPoly cv)) := by
  have hcl := holdsVec_length _ _ _ hc
  refine ⟨cv ++ List.replicate ((p - 1) * e - cv.length) 0, ?_, ?_, ?_⟩
  · unfold padBlk; rw [hcl]; exact List.rel_append hc (holdsVec_replicate regs z 0 hz _)
  · simp; omega
  · rw [toPoly_append, toPoly_replicate_zero, mul_zero, add_zero]

open Polynomial in
/-- The algebra of the Schoenhage step in `R[X]/(cyc p n)`. -/
theorem step_value {R : Type*} [CommRing R] (p n m L N sc : ℕ) (hn : n = L * m) (hN : N = p * L)
    (fvs gvs : List R) (hfl : fvs.length = ((p - 1) * L) * m)
    (hgl : gvs.length = ((p - 1) * L) * m) :
    AdjoinRoot.mk (cyc R p n) (∑ i ∈ Finset.range N, X ^ (m * i) *
      (N • (sc • cconv N (fun j => toPoly (chunk fvs m j)) (fun j => toPoly (chunk gvs m j)) i))) =
    ((N * sc : ℕ) : AdjoinRoot (cyc R p n)) *
      (AdjoinRoot.mk (cyc R p n) (toPoly fvs) * AdjoinRoot.mk (cyc R p n) (toPoly gvs)) := by
  have hωN : (AdjoinRoot.root (cyc R p n) ^ m) ^ N = 1 := by
    rw [← pow_mul, hN, show m * (p * L) = p * n by rw [hn]; ring]; exact root_pow_pe p n
  have hle : (p - 1) * L ≤ N := by rw [hN]; exact Nat.mul_le_mul_right _ (Nat.sub_le p 1)
  have hX : ∀ (vs : List R), vs.length = ((p - 1) * L) * m →
      AdjoinRoot.mk (cyc R p n) (toPoly vs) = dft (AdjoinRoot.root (cyc R p n) ^ m) N
        (fun j => AdjoinRoot.mk (cyc R p n) (toPoly (chunk vs m j))) 1 := by
    intro vs hl
    rw [toPoly_chunks_ext m _ N vs hl hle, map_sum]
    unfold dft
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, AdjoinRoot.mk_X, mul_one, ← pow_mul, mul_comm m j]
  rw [hX fvs hfl, hX gvs hgl, ← dft_cconv _ N hωN, map_sum]
  unfold dft
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, AdjoinRoot.mk_X, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul,
    mul_one, ← pow_mul]
  simp only [map_cconv]
  push_cast
  ring

/-- **One Schoenhage step** for `R[X]/(cyc p n)`, `n = p^λ m`: split into `(p-1) p^λ` chunks of
length `m`, pad them into blocks of `R[X]/(cyc p m')`, cyclic convolution of length `p^(λ+1)`,
overlap-add, reduce. -/
def stepGen (p n m m' lam : ℕ) (mulB : List ℕ → List ℕ → Gen (List ℕ)) (fb gb : List ℕ) :
    Gen (List ℕ) :=
  Gen.bind (Gen.emit .zero) fun z =>
  Gen.bind (convGen p m' (lam + 1) (m' / p ^ lam) mulB
    ((List.range (p ^ (lam + 1))).map fun j => padBlk z ((p - 1) * m') (chunk fb m j))
    ((List.range (p ^ (lam + 1))).map fun j => padBlk z ((p - 1) * m') (chunk gb m j))) fun C =>
  Gen.bind (overlapGen m 0 (List.replicate ((p + 1) * n) z) C) fun H =>
  reduceGen p n H

theorem triple_stepGen {R : Type*} [CommRing R] (ι : R → R) (p n m m' lam sc : ℕ)
    (hp : p.Prime) (hn : n = p ^ lam * m) (hm : 0 < m) (hm' : 2 * m ≤ (p - 1) * m' + 1)
    (hfit : (p - 1) * m' ≤ n + m) (hdiv : p ^ lam ∣ m')
    (mulB : List ℕ → List ℕ → Gen (List ℕ)) (hmul : MulOK ι p m' sc mulB)
    (fb gb : List ℕ) (f g : AdjoinRoot (cyc R p n)) (P : List R → Prop) (hP : Stable P)
    (hf : ∀ regs, P regs → HoldsB p n regs fb f) (hg : ∀ regs, P regs → HoldsB p n regs gb g) :
    Triple ι (stepGen p n m m' lam mulB fb gb) P (fun out regs => P regs ∧
      HoldsB p n regs out (((p ^ (lam + 1) * sc : ℕ) : AdjoinRoot (cyc R p n)) * (f * g))) := by
  have hp2 : 2 ≤ p := hp.two_le
  have hm'0 : 0 < m' := by
    rcases Nat.eq_zero_or_pos m' with h0 | h0
    · subst h0; omega
    · exact h0
  have hmD : m ≤ (p - 1) * m' := by omega
  intro regs h
  obtain ⟨fvs, hfv, hfl, hfx⟩ := hf regs h
  obtain ⟨gvs, hgv, hgl, hgx⟩ := hg regs h
  let P1 : List R → Prop := fun r => P r ∧ HoldsVec r fb fvs ∧ HoldsVec r gb gvs
  have hP1 : Stable P1 :=
    stable_and _ _ hP (stable_and _ _ (stable_holdsVec _ _) (stable_holdsVec _ _))
  suffices T : Triple ι (stepGen p n m m' lam mulB fb gb) P1 (fun out regs => P regs ∧
      HoldsB p n regs out (((p ^ (lam + 1) * sc : ℕ) : AdjoinRoot (cyc R p n)) * (f * g))) from
    T regs ⟨h, hfv, hgv⟩
  unfold stepGen
  refine triple_bind ι _ _ P1 _ _ (triple_emit_zero ι P1 hP1) fun z => ?_
  have hP2 : Stable (fun r => P1 r ∧ Holds r z 0) := stable_and _ _ hP1 (stable_holds z 0)
  have hblk : ∀ (cb : List ℕ) (cvs : List R), (∀ r, (P1 r ∧ Holds r z 0) → HoldsVec r cb cvs) →
      ∀ r, (P1 r ∧ Holds r z 0) → HoldsBF p m' r
        ((List.range (p ^ (lam + 1))).map fun j => padBlk z ((p - 1) * m') (chunk cb m j))
        (p ^ (lam + 1)) (fun j => AdjoinRoot.mk (cyc R p m') (toPoly (chunk cvs m j))) := by
    intro cb cvs hc r hr
    refine ⟨by simp, fun i hi => ?_⟩
    have e : ((List.range (p ^ (lam + 1))).map fun j =>
        padBlk z ((p - 1) * m') (chunk cb m j)).getD i [] =
        padBlk z ((p - 1) * m') (chunk cb m i) := by
      simp [List.getD_eq_getElem?_getD, hi]
    rw [e]
    exact holdsB_padBlk p m' r z hr.2 _ _ (holdsVec_chunk r cb cvs (hc r hr) m i)
      (le_trans (chunk_length_le _ _ _) hmD)
  obtain ⟨hroot, hprin⟩ := root_principal (R := R) p m' lam hp hdiv
  refine triple_bind ι _ _ _ _ _ (triple_convGen ι p m' hp2 hm'0 (lam + 1) (m' / p ^ lam) sc
    mulB hmul _ _ _ _ _ hP2 (hblk fb fvs fun r hr => hr.1.2.1)
    (hblk gb gvs fun r hr => hr.1.2.2) hroot hprin) fun C => ?_
  intro r hr
  have hC := hr.2
  have hCl : C.length = p ^ (lam + 1) := hC.1
  let W : ℕ → List R := fun k =>
    if hk : k < p ^ (lam + 1) then (hC.2 k hk).choose else []
  have hWe : ∀ k (hk : k < p ^ (lam + 1)), W k = (hC.2 k hk).choose := fun k hk => dif_pos hk
  have hFd : ∀ (vs : List R) j, (toPoly (chunk vs m j)).natDegree ≤ m - 1 := fun vs j =>
    le_trans (toPoly_natDegree_le _) (Nat.sub_le_sub_right (chunk_length_le _ _ _) 1)
  have hWp : ∀ k < p ^ (lam + 1), toPoly (W k) = (p ^ (lam + 1)) • (sc • cconv (p ^ (lam + 1))
      (fun j => toPoly (chunk fvs m j)) (fun j => toPoly (chunk gvs m j)) k) := by
    intro k hk
    obtain ⟨_, hl, hx⟩ := (hC.2 k hk).choose_spec
    rw [hWe k hk]
    refine no_wrap p m' hp2 hm'0 _ _ (toPoly_degree_lt _ _ (le_of_eq hl)) ?_ ?_
    · rw [← Polynomial.mem_degreeLT]
      exact nsmul_mem (nsmul_mem (cconv_mem_degreeLT _ m _ _ _ (hFd fvs) (hFd gvs) hm hm' k) _) _
    · rw [hx, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul]
      simp only [map_cconv]
  have hfa : List.Forall₂ (HoldsVec r) C ((List.range (p ^ (lam + 1))).map W) := by
    have := forall₂_of_getD (S := HoldsVec r) [] C W (fun k hk => by
      rw [hWe k (by omega)]
      exact ((hC.2 k (by omega)).choose_spec).1)
    rwa [hCl] at this
  have hWl : ∀ k < p ^ (lam + 1), (W k).length = (p - 1) * m' := fun k hk => by
    rw [hWe k hk]; exact ((hC.2 k hk).choose_spec).2.1
  have hmN : m * p ^ (lam + 1) = p * n := by rw [hn, pow_succ]; ring
  have hHv := overlapVal_spec m ((p + 1) * n) ((List.range (p ^ (lam + 1))).map W) 0
    (List.replicate ((p + 1) * n) 0) (by simp) (fun i hi => by
      rw [List.length_map, List.length_range] at hi
      have e : ((List.range (p ^ (lam + 1))).map W).getD i [] = W i := by
        simp [List.getD_eq_getElem?_getD, hi]
      rw [e, hWl i hi, Nat.zero_add]
      have h1 : m * i + m ≤ m * p ^ (lam + 1) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hi
      have h2 : (p + 1) * n = p * n + n := by ring
      omega)
  let P4 : List R → Prop := fun r' => ((P1 r' ∧ Holds r' z 0) ∧ HoldsBF p m' r' C (p ^ (lam + 1))
    (fun k => ((p ^ (lam + 1) : ℕ) : AdjoinRoot (cyc R p m')) * (((sc : ℕ) : AdjoinRoot (cyc R p m')) *
      cconv (p ^ (lam + 1)) (fun j => AdjoinRoot.mk (cyc R p m') (toPoly (chunk fvs m j)))
        (fun j => AdjoinRoot.mk (cyc R p m') (toPoly (chunk gvs m j))) k))) ∧
    List.Forall₂ (HoldsVec r') C ((List.range (p ^ (lam + 1))).map W)
  have hP4 : Stable P4 := stable_and _ _ (stable_and _ _ hP2 (stable_holdsBF _ _ _ _ _))
    (fun regs new h => List.Forall₂.imp (fun b w hb => stable_holdsVec b w regs new hb) h)
  have T4 : Triple ι (Gen.bind (overlapGen m 0 (List.replicate ((p + 1) * n) z) C) fun H =>
      reduceGen p n H) P4 (fun out r' => P r' ∧ HoldsB p n r' out (AdjoinRoot.mk (cyc R p n)
        (toPoly (overlapVal m 0 (List.replicate ((p + 1) * n) 0)
          ((List.range (p ^ (lam + 1))).map W))))) := by
    refine triple_bind ι _ _ P4 _ _ (triple_overlapGen ι m C _ 0 _ _ P4 hP4
      (fun r' h' => holdsVec_replicate r' z 0 h'.1.1.2 _) (fun r' h' => h'.2)) fun H => ?_
    exact triple_post ι _ _ _ _ (triple_reduceGen ι p n hp2 H _ hHv.1 _
      (stable_and _ _ hP4 (stable_holdsVec _ _)) (fun r' h' => h'.2)) fun out r' h' =>
        ⟨h'.1.1.1.1.1.1, h'.2⟩
  obtain ⟨new, h1, h2, h3⟩ := T4 r ⟨hr, hfa⟩
  refine ⟨new, h1, h2, h3.1, ?_⟩
  have hval : AdjoinRoot.mk (cyc R p n) (toPoly (overlapVal m 0 (List.replicate ((p + 1) * n) 0)
      ((List.range (p ^ (lam + 1))).map W))) =
      ((p ^ (lam + 1) * sc : ℕ) : AdjoinRoot (cyc R p n)) * (f * g) := by
    rw [hHv.2, toPoly_replicate_zero, zero_add, List.length_map, List.length_range]
    have hs : ∀ i ∈ Finset.range (p ^ (lam + 1)), (Polynomial.X : Polynomial R) ^ (m * (0 + i)) *
        toPoly (((List.range (p ^ (lam + 1))).map W).getD i []) =
        Polynomial.X ^ (m * i) * ((p ^ (lam + 1)) • (sc • cconv (p ^ (lam + 1))
          (fun j => toPoly (chunk fvs m j)) (fun j => toPoly (chunk gvs m j)) i)) := by
      intro i hi
      rw [Finset.mem_range] at hi
      have e : ((List.range (p ^ (lam + 1))).map W).getD i [] = W i := by
        simp [List.getD_eq_getElem?_getD, hi]
      rw [e, hWp i hi, Nat.zero_add]
    rw [Finset.sum_congr rfl hs, step_value p n m (p ^ lam) (p ^ (lam + 1)) sc
      (by rw [hn, mul_comm]) (pow_succ' p lam) fvs gvs (by rw [hfl, hn]; ring)
      (by rw [hgl, hn]; ring), hfx, hgx]
  rw [← hval]
  exact h3.2


/-! ## S2-G6c base multiplier and the recursive multiplier for `R[X]/(cyc p (p^k))`, p = 2, 3 -/

theorem triple_conj_struct {R : Type*} [CommRing R] (ι : R → R) {α : Type} (g : Gen α)
    (P : List R → Prop) (Q : α → List R → Prop) (S : α → Prop) (h : Triple ι g P Q)
    (hS : ∀ n, S (g n).1) : Triple ι g P (fun a regs => Q a regs ∧ S a) := by
  intro regs hP
  obtain ⟨new, h1, h2, h3⟩ := h regs hP
  exact ⟨new, h1, h2, h3, hS _⟩

theorem schoolMul_length : ∀ (is js : List ℕ) (n : ℕ),
    ((schoolMul is js) n).1.length ≤ is.length + js.length
  | [], js, n => by simp [schoolMul, Gen.pure]
  | i :: is, js, n => by
    simp only [schoolMul, Gen.bind]
    have hl := vecSmul_length i js n
    have ih := schoolMul_length is js ((vecSmul i js) n).2.2
    generalize ((vecSmul i js) n).1 = p at hl ⊢
    rcases p with _ | ⟨p₀, p'⟩
    · simp only [Gen.pure, List.length_cons] at *; omega
    · simp only [Gen.bind, Gen.pure, List.length_cons, vecAddPad_length] at *; omega

/-- Base multiplier: schoolbook product, pad to `(p+1) n`, reduce. -/
def baseMul (p n : ℕ) (fb gb : List ℕ) : Gen (List ℕ) :=
  Gen.bind (schoolMul fb gb) fun H0 =>
  Gen.bind (Gen.emit .zero) fun z =>
  reduceGen p n (H0 ++ List.replicate ((p + 1) * n - H0.length) z)

theorem triple_baseMul {R : Type*} [CommRing R] (ι : R → R) (p n : ℕ) (hp : 2 ≤ p)
    (hp3 : p ≤ 3) : MulOK ι p n 1 (baseMul p n) := by
  intro b₁ b₂ v₁ v₂ P hP h₁ h₂ regs h
  obtain ⟨vs₁, hv₁, hl₁, hx₁⟩ := h₁ regs h
  obtain ⟨vs₂, hv₂, hl₂, hx₂⟩ := h₂ regs h
  have hb1 : b₁.length = (p - 1) * n := (holdsVec_length _ _ _ hv₁).trans hl₁
  have hb2 : b₂.length = (p - 1) * n := (holdsVec_length _ _ _ hv₂).trans hl₂
  let P1 : List R → Prop := fun r => P r ∧ HoldsVec r b₁ vs₁ ∧ HoldsVec r b₂ vs₂
  have hP1 : Stable P1 :=
    stable_and _ _ hP (stable_and _ _ (stable_holdsVec _ _) (stable_holdsVec _ _))
  suffices T : Triple ι (baseMul p n b₁ b₂) P1 (fun out regs => P regs ∧
      HoldsB p n regs out (((1 : ℕ) : AdjoinRoot (cyc R p n)) * (v₁ * v₂))) from
    T regs ⟨h, hv₁, hv₂⟩
  unfold baseMul
  refine triple_bind ι _ _ P1 _ _ (triple_conj_struct ι _ _ _
    (fun out : List ℕ => out.length ≤ b₁.length + b₂.length)
    (triple_schoolMul ι b₁ b₂ vs₁ vs₂ P1 hP1 (fun r hr => hr.2.1) (fun r hr => hr.2.2))
    (fun m => schoolMul_length b₁ b₂ m)) fun H0 => ?_
  intro r hr
  obtain ⟨⟨hr1, vs, hvs, hval⟩, hHl⟩ := hr
  have hvl : vs.length = H0.length := (holdsVec_length _ _ _ hvs).symm
  have hle : H0.length ≤ (p + 1) * n := by
    rw [hb1, hb2] at hHl
    interval_cases p <;> omega
  let P2 : List R → Prop := fun r' => P1 r' ∧ HoldsVec r' H0 vs
  have hP2 : Stable P2 := stable_and _ _ hP1 (stable_holdsVec _ _)
  have T2 : Triple ι (Gen.bind (Gen.emit .zero) fun z =>
      reduceGen p n (H0 ++ List.replicate ((p + 1) * n - H0.length) z)) P2
      (fun out r' => P r' ∧ HoldsB p n r' out (AdjoinRoot.mk (cyc R p n)
        (toPoly (vs ++ List.replicate ((p + 1) * n - H0.length) 0)))) := by
    refine triple_bind ι _ _ P2 _ _ (triple_emit_zero ι P2 hP2) fun z => ?_
    exact triple_post ι _ _ _ _ (triple_reduceGen ι p n hp _ _ (by simp; omega) _
      (stable_and _ _ hP2 (stable_holds z 0))
      (fun r' h' => List.rel_append h'.1.2 (holdsVec_replicate r' z 0 h'.2 _)))
      fun out r' h' => ⟨h'.1.1.1.1, h'.2⟩
  obtain ⟨new, c1, c2, c3⟩ := T2 r ⟨hr1, hvs⟩
  refine ⟨new, c1, c2, c3.1, ?_⟩
  have e : AdjoinRoot.mk (cyc R p n) (toPoly (vs ++ List.replicate ((p + 1) * n - H0.length) 0)) =
      ((1 : ℕ) : AdjoinRoot (cyc R p n)) * (v₁ * v₂) := by
    rw [toPoly_append, toPoly_replicate_zero, mul_zero, add_zero, hval, map_mul, hx₁, hx₂,
      Nat.cast_one, one_mul]
  rw [← e]
  exact c3.2

/-- Number of FFT levels exponent `λ` and the inner exponent `μ'` (p = 2 or 3). -/
def lamP (p k : ℕ) : ℕ := if p = 2 then k - k / 2 else k / 2

def muP' (p k : ℕ) : ℕ := if p = 2 then k / 2 + 1 else k - k / 2

theorem muP'_lt (p k : ℕ) (hk : ¬ k ≤ 2) : muP' p k < k := by
  unfold muP'; split_ifs <;> omega

/-- The recursive multiplier for `R[X]/(cyc p (p^k))`. -/
def mulRec (p : ℕ) (k : ℕ) : List ℕ → List ℕ → Gen (List ℕ) :=
  if h : k ≤ 2 then baseMul p (p ^ k) else
    stepGen p (p ^ k) (p ^ (k - lamP p k)) (p ^ muP' p k) (lamP p k) (mulRec p (muP' p k))
termination_by k
decreasing_by exact muP'_lt p k h

/-- Its scale factor. -/
def scl (p : ℕ) (k : ℕ) : ℕ :=
  if h : k ≤ 2 then 1 else p ^ (lamP p k + 1) * scl p (muP' p k)
termination_by k
decreasing_by exact muP'_lt p k h

theorem params_ok (p k : ℕ) (hp : p = 2 ∨ p = 3) (hk : ¬ k ≤ 2) :
    p ^ k = p ^ lamP p k * p ^ (k - lamP p k) ∧
    2 * p ^ (k - lamP p k) ≤ (p - 1) * p ^ muP' p k + 1 ∧
    (p - 1) * p ^ muP' p k ≤ p ^ k + p ^ (k - lamP p k) ∧ p ^ lamP p k ∣ p ^ muP' p k := by
  rcases hp with rfl | rfl
  · rw [show lamP 2 k = k - k / 2 from if_pos rfl, show muP' 2 k = k / 2 + 1 from if_pos rfl,
      show k - (k - k / 2) = k / 2 by omega]
    have e1 : 2 ^ (k / 2 + 1) = 2 ^ (k / 2) * 2 := pow_succ 2 (k / 2)
    have e2 : 2 ^ (k / 2) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self k 2)
    refine ⟨by rw [← pow_add]; congr 1; omega, by omega, by omega, pow_dvd_pow 2 (by omega)⟩
  · rw [show lamP 3 k = k / 2 from if_neg (by norm_num),
      show muP' 3 k = k - k / 2 from if_neg (by norm_num)]
    have e2 : 3 ^ (k - k / 2) ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le k _)
    refine ⟨by rw [← pow_add]; congr 1; omega, by omega, by omega, pow_dvd_pow 3 (by omega)⟩

/-- **Correctness of the recursive multiplier** (Schoenhage–Cantor–Kaltofen, radix p = 2, 3). -/
theorem mulRec_ok {R : Type*} [CommRing R] (ι : R → R) (p : ℕ) (hp : p = 2 ∨ p = 3) :
    ∀ k, MulOK ι p (p ^ k) (scl p k) (mulRec p k) := by
  have hp2 : 2 ≤ p := by omega
  have hp3 : p ≤ 3 := by omega
  have hpr : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k ≤ 2
    · rw [mulRec, dif_pos hk, scl, dif_pos hk]
      exact triple_baseMul ι p (p ^ k) hp2 hp3
    · obtain ⟨h1, h2, h3, h4⟩ := params_ok p k hp hk
      rw [mulRec, dif_neg hk, scl, dif_neg hk]
      intro b₁ b₂ v₁ v₂ P hP hb₁ hb₂
      exact triple_stepGen ι p (p ^ k) (p ^ (k - lamP p k)) (p ^ muP' p k) (lamP p k)
        (scl p (muP' p k)) hpr h1 (pow_pos (by omega) _) h2 h3 h4 (mulRec p (muP' p k))
        (ih _ (muP'_lt p k hk)) b₁ b₂ v₁ v₂ P hP hb₁ hb₂


/-! ## S2-G7 cost of the recursive multiplier -/

theorem ops_emit_le (i : Instr) (n : ℕ) : (Gen.emit i).ops n ≤ 1 := by
  rw [ops_emit]; split <;> omega

theorem fftGen_len_succ (p e l s : ℕ) (blks : List (List ℕ)) (n : ℕ) :
    ((fftGen p e (l + 1) s blks) n).1.length = p * p ^ l := by
  simp only [fftGen, Gen.bind]
  rw [mapGen_length, List.length_range]

theorem convGen_out (p e : ℕ) (hp : 2 ≤ p) (he : 0 < e) (l s : ℕ)
    (mulB : List ℕ → List ℕ → Gen (List ℕ))
    (hml : ∀ b₁ b₂ n, ((mulB b₁ b₂) n).1.length ≤ (p - 1) * e)
    (as bs : List (List ℕ)) (n : ℕ) :
    ((convGen p e (l + 1) s mulB as bs) n).1.length = p * p ^ l ∧
    ∀ b ∈ ((convGen p e (l + 1) s mulB as bs) n).1, b.length ≤ (p - 1) * e := by
  unfold convGen
  simp only [Gen.bind]
  refine ⟨fftGen_len_succ _ _ _ _ _ _, fftGen_length p e hp he _ _ _ _ ?_⟩
  intro b hb
  obtain ⟨k, -, m, rfl⟩ := mapGen_mem _ _ _ b hb
  exact hml _ _ m

theorem mulRec_length (p : ℕ) :
    ∀ (k : ℕ) (b₁ b₂ : List ℕ) (n : ℕ), ((mulRec p k b₁ b₂) n).1.length ≤ (p - 1) * p ^ k := by
  intro k b₁ b₂ n
  rw [mulRec]
  split_ifs with hk
  · simp only [baseMul, Gen.bind]; exact reduceGen_length _ _ _ _
  · simp only [stepGen, Gen.bind]; exact reduceGen_length _ _ _ _

theorem ops_stepGen (p n m m' lam : ℕ) (hp : 2 ≤ p) (hm' : 0 < m') (hmm : m ≤ (p - 1) * m')
    (mulB : List ℕ → List ℕ → Gen (List ℕ)) (Bm : ℕ)
    (hmo : ∀ b₁ b₂ n, b₁.length ≤ (p - 1) * m' → b₂.length ≤ (p - 1) * m' →
      (mulB b₁ b₂).ops n ≤ Bm)
    (hml : ∀ b₁ b₂ n, ((mulB b₁ b₂) n).1.length ≤ (p - 1) * m')
    (fb gb : List ℕ) (k : ℕ) :
    (stepGen p n m m' lam mulB fb gb).ops k ≤
      1 + ((3 * ((lam + 1) * p ^ (lam + 1) * (p * (p * m' * (p - 1)) + p * ((p - 1) * m'))) +
        p ^ (lam + 1) * Bm) + (p * p ^ lam * ((p - 1) * m') + (n + (p - 1) * (2 * n)))) := by
  have hpad : ∀ (z : ℕ) (xb : List ℕ), ∀ b ∈ (List.range (p ^ (lam + 1))).map
      (fun j => padBlk z ((p - 1) * m') (chunk xb m j)), b.length ≤ (p - 1) * m' := by
    intro z xb b hb
    simp only [List.mem_map] at hb
    obtain ⟨j, -, rfl⟩ := hb
    rw [padBlk_length _ _ _ (le_trans (chunk_length_le _ _ _) hmm)]
  unfold stepGen
  simp only [ops_bind]
  refine Nat.add_le_add (ops_emit_le _ _) (Nat.add_le_add ?_ (Nat.add_le_add ?_ ?_))
  · exact ops_convGen p m' hp hm' (lam + 1) _ mulB Bm hmo (fun b₁ b₂ n _ _ => hml b₁ b₂ n)
      _ _ (hpad _ _) (hpad _ _) _
  · refine le_trans (ops_overlapGen m ((p - 1) * m') _ 0 _ _
      (convGen_out p m' hp hm' lam _ mulB hml _ _ _).2) ?_
    rw [(convGen_out p m' hp hm' lam _ mulB hml _ _ _).1]
  · exact ops_reduceGen _ _ _ _

theorem lamP_le (p k : ℕ) : lamP p k ≤ k := by unfold lamP; split_ifs <;> omega

theorem muP'_five (p k : ℕ) (hk : ¬ k ≤ 2) : 5 * (muP' p k + 1) ≤ 4 * (k + 1) := by
  unfold muP'; split_ifs <;> omega

theorem pow10_ratio (a b : ℕ) (h : 5 * (a + 1) ≤ 4 * (b + 1)) : 8 * (a + 1) ^ 10 ≤ (b + 1) ^ 10 := by
  have h1 : (5 * (a + 1)) ^ 10 ≤ (4 * (b + 1)) ^ 10 := Nat.pow_le_pow_left h 10
  rw [mul_pow, mul_pow] at h1
  norm_num at h1
  omega

theorem pow_lam_mu (p k : ℕ) (hp : p = 2 ∨ p = 3) (hk : ¬ k ≤ 2) :
    p ^ (lamP p k + 1) * p ^ muP' p k ≤ 4 * p ^ k := by
  rw [← pow_add]
  rcases hp with rfl | rfl
  · rw [show lamP 2 k = k - k / 2 from if_pos rfl, show muP' 2 k = k / 2 + 1 from if_pos rfl,
      show k - k / 2 + 1 + (k / 2 + 1) = k + 2 by omega, pow_add]
    norm_num; omega
  · rw [show lamP 3 k = k / 2 from if_neg (by norm_num),
      show muP' 3 k = k - k / 2 from if_neg (by norm_num),
      show k / 2 + 1 + (k - k / 2) = k + 1 by omega, pow_add]
    norm_num; omega

/-- **Cost of the recursive multiplier**: `O(n (log n)^10)` with `n = p^k`. -/
theorem ops_mulRec (p : ℕ) (hp : p = 2 ∨ p = 3) :
    ∀ (k : ℕ) (b₁ b₂ : List ℕ) (n : ℕ), b₁.length ≤ (p - 1) * p ^ k →
      b₂.length ≤ (p - 1) * p ^ k → (mulRec p k b₁ b₂).ops n ≤ 1000 * p ^ k * (k + 1) ^ 10 := by
  have hp2 : 2 ≤ p := by omega
  have hp3 : p ≤ 3 := by omega
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro b₁ b₂ n hl₁ hl₂
    have hQ : 1 ≤ (k + 1) ^ 10 := Nat.one_le_pow _ _ (by omega)
    have hN : 1 ≤ p ^ k := Nat.one_le_pow _ _ (by omega)
    have hd : p - 1 ≤ 2 := by omega
    by_cases hk : k ≤ 2
    · rw [mulRec, dif_pos hk]
      unfold baseMul
      simp only [ops_bind]
      have hpk : p ^ k ≤ 9 := le_trans (Nat.pow_le_pow_left hp3 k)
        (le_trans (Nat.pow_le_pow_right (by norm_num) hk) (by norm_num))
      have hL : (p - 1) * p ^ k ≤ 18 := le_trans (Nat.mul_le_mul hd hpk) (by norm_num)
      have hs := ops_schoolMul b₁ b₂ n
      have hm : 2 * b₁.length * b₂.length ≤ 2 * 18 * 18 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (le_trans hl₁ hL)) (le_trans hl₂ hL)
      refine le_trans (Nat.add_le_add hs (Nat.add_le_add (ops_emit_le _ _)
        (ops_reduceGen _ _ _ _))) ?_
      have h2 : (p - 1) * (2 * p ^ k) ≤ 36 := by
        rw [← Nat.mul_assoc, Nat.mul_comm (p - 1) 2, Nat.mul_assoc]
        exact le_trans (Nat.mul_le_mul_left 2 hL) (by norm_num)
      have h3 : 1000 ≤ 1000 * p ^ k * (k + 1) ^ 10 := by
        rw [Nat.mul_assoc]; exact Nat.le_mul_of_pos_right _ (Nat.mul_pos hN hQ)
      omega
    · obtain ⟨_, h2, _, _⟩ := params_ok p k hp hk
      have hlt := muP'_lt p k hk
      have hm' : 0 < p ^ muP' p k := pow_pos (by omega : 0 < p) _
      have hmpos : 0 < p ^ (k - lamP p k) := pow_pos (by omega : 0 < p) _
      have hmm : p ^ (k - lamP p k) ≤ (p - 1) * p ^ muP' p k := by omega
      rw [mulRec, dif_neg hk]
      refine le_trans (ops_stepGen p (p ^ k) (p ^ (k - lamP p k)) (p ^ muP' p k) (lamP p k) hp2
        hm' hmm (mulRec p (muP' p k)) (1000 * p ^ muP' p k * (muP' p k + 1) ^ 10)
        (fun b₁ b₂ n h1 h2 => ih _ hlt b₁ b₂ n h1 h2) (fun b₁ b₂ n => mulRec_length p _ b₁ b₂ n)
        b₁ b₂ n) ?_
      have hX := pow_lam_mu p k hp hk
      have hR := pow10_ratio _ _ (muP'_five p k hk)
      have hlam := lamP_le p k
      have hc : p * p * (p - 1) + p * (p - 1) ≤ 24 := by
        rcases hp with rfl | rfl <;> norm_num
      have e1 : (lamP p k + 1) * p ^ (lamP p k + 1) *
          (p * (p * p ^ muP' p k * (p - 1)) + p * ((p - 1) * p ^ muP' p k)) =
          (lamP p k + 1) * (p ^ (lamP p k + 1) * p ^ muP' p k) * (p * p * (p - 1) + p * (p - 1)) := by
        ring
      have e2 : p ^ (lamP p k + 1) * (1000 * p ^ muP' p k * (muP' p k + 1) ^ 10) =
          1000 * (p ^ (lamP p k + 1) * p ^ muP' p k) * (muP' p k + 1) ^ 10 := by ring
      have e3 : p * p ^ lamP p k * ((p - 1) * p ^ muP' p k) =
          (p ^ (lamP p k + 1) * p ^ muP' p k) * (p - 1) := by ring
      rw [e1, e2, e3]
      have hk1 : k + 1 ≤ (k + 1) ^ 10 := by
        calc k + 1 = (k + 1) ^ 1 := (pow_one _).symm
          _ ≤ (k + 1) ^ 10 := Nat.pow_le_pow_right (by omega) (by norm_num)
      generalize p ^ (lamP p k + 1) * p ^ muP' p k = X at hX ⊢
      generalize p * p * (p - 1) + p * (p - 1) = c at hc ⊢
      generalize (muP' p k + 1) ^ 10 = Q' at hR ⊢
      generalize (k + 1) ^ 10 = Q at hR hQ hk1 ⊢
      generalize p ^ k = N at hX hN ⊢
      generalize p - 1 = d at hd ⊢
      have b1 : (lamP p k + 1) * X * c ≤ (k + 1) * (4 * N) * 24 :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) hX) hc
      have b2 : 1000 * X * Q' ≤ 1000 * (4 * N) * Q' :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hX) le_rfl
      have b3 : X * d ≤ 4 * N * 2 := Nat.mul_le_mul hX hd
      have b4 : d * (2 * N) ≤ 2 * (2 * N) := Nat.mul_le_mul hd le_rfl
      have b5 : N * (8 * Q') ≤ N * Q := Nat.mul_le_mul_left _ hR
      have b6 : (k + 1) * N ≤ Q * N := Nat.mul_le_mul_right _ hk1
      have b7 : N ≤ N * Q := Nat.le_mul_of_pos_right _ (by omega)
      linarith only [b1, b2, b3, b4, b5, b6, b7, hN, hQ]

/-! ## S2-G8 the full polynomial product: radix-2 and radix-3 products combined by Bezout -/

def natConst : ℕ → Gen ℕ
  | 0 => Gen.emit .zero
  | c + 1 => Gen.bind (natConst ((c + 1) / 2)) fun r => Gen.bind (Gen.emit (.add r r)) fun s =>
      if (c + 1) % 2 = 0 then Gen.pure s else
        Gen.bind (Gen.emit .one) fun o => Gen.emit (.add s o)
termination_by c => c
decreasing_by all_goals omega

theorem triple_natConst {R : Type*} [CommRing R] (ι : R → R) (P : List R → Prop) (hP : Stable P)
    (c : ℕ) : Triple ι (natConst c) P (fun r regs => P regs ∧ Holds regs r (c : R)) := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rcases c with _ | c
    · rw [natConst]
      exact triple_post ι _ _ _ _ (triple_emit_zero ι P hP) fun r regs h => ⟨h.1, by simpa using h.2⟩
    · rw [natConst]
      refine triple_bind ι _ _ P _ _ (ih ((c + 1) / 2) (by omega)) fun r => ?_
      have hS1 : Stable (fun regs : List R => P regs ∧ Holds regs r ((((c + 1) / 2 : ℕ)) : R)) :=
        stable_and _ _ hP (stable_holds _ _)
      refine triple_bind ι _ _ _ _ _ (triple_emit_add ι r r _ _ _ hS1 (fun _ h => h.2)
        (fun _ h => h.2)) fun s => ?_
      have hv : (((c + 1) / 2 : ℕ) : R) + (((c + 1) / 2 : ℕ) : R) + (((c + 1) % 2 : ℕ) : R) =
          ((c + 1 : ℕ) : R) := by
        rw [← Nat.cast_add, ← Nat.cast_add]; congr 1; omega
      split_ifs with hpar
      · refine triple_pure ι _ _ _ fun regs h => ⟨h.1.1, ?_⟩
        rw [← hv, hpar, Nat.cast_zero, add_zero]; exact h.2
      · have hS2 : Stable (fun regs : List R => (P regs ∧ Holds regs r ((((c + 1) / 2 : ℕ)) : R)) ∧
            Holds regs s ((((c + 1) / 2 : ℕ) : R) + (((c + 1) / 2 : ℕ) : R))) :=
          stable_and _ _ hS1 (stable_holds _ _)
        refine triple_bind ι _ _ _ _ _ (triple_emit_one ι _ hS2) fun o => ?_
        refine triple_post ι _ _ _ _ (triple_emit_add ι s o _ _ _ (stable_and _ _ hS2
          (stable_holds _ _)) (fun _ h => h.1.2) (fun _ h => h.2)) ?_
        intro a regs h
        refine ⟨h.1.1.1.1, ?_⟩
        have h1 : (c + 1) % 2 = 1 := by omega
        rw [← hv, h1, Nat.cast_one]; exact h.2

theorem ops_natConst (c : ℕ) : ∀ n, (natConst c).ops n ≤ 4 * Nat.log 2 c + 4 := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro n
    rcases c with _ | c
    · rw [natConst]; exact le_trans (ops_emit_le _ _) (by omega)
    · rw [natConst]
      simp only [ops_bind]
      have hrest : ∀ m s, (if (c + 1) % 2 = 0 then Gen.pure s else
          Gen.bind (Gen.emit .one) fun o => Gen.emit (.add s o)).ops m ≤ 2 := by
        intro m s; split_ifs
        · rw [ops_pure]; omega
        · rw [ops_bind]; exact Nat.add_le_add (ops_emit_le _ _) (ops_emit_le _ _)
      refine le_trans (Nat.add_le_add_left (Nat.add_le_add (ops_emit_le _ _) (hrest _ _)) _) ?_
      rcases Nat.eq_zero_or_pos c with rfl | hc
      · have h0 : (natConst ((0 + 1) / 2)).ops n ≤ 1 := by
          rw [show (0 + 1) / 2 = 0 from rfl, natConst]; exact ops_emit_le _ _
        omega
      · have h1 := ih ((c + 1) / 2) (by omega) n
        have h2 : Nat.log 2 ((c + 1) / 2) = Nat.log 2 (c + 1) - 1 := Nat.log_div_base 2 (c + 1)
        have h3 : 0 < Nat.log 2 (c + 1) := Nat.log_pos (by norm_num) (by omega)
        omega

theorem scl_pow (p : ℕ) : ∀ k, ∃ E, E ≤ 4 * k ∧ scl p k = p ^ E := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k ≤ 2
    · exact ⟨0, by omega, by rw [scl, dif_pos hk, pow_zero]⟩
    · by_cases hk' : muP' p k ≤ 2
      · refine ⟨lamP p k + 1, ?_, by rw [scl, dif_neg hk, scl, dif_pos hk', mul_one]⟩
        have := lamP_le p k
        omega
      · obtain ⟨E, hE, hs⟩ := ih _ (muP'_lt p k hk)
        refine ⟨lamP p k + 1 + E, ?_, by rw [scl, dif_neg hk, hs, ← pow_add]⟩
        have h1 : lamP p k + 1 + 4 * muP' p k ≤ 4 * k := by
          unfold lamP muP' at hk' ⊢; split_ifs at hk' ⊢ <;> omega
        omega

theorem bezout_nat (a b : ℕ) (h : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b) :
    ∃ u w : ℕ, u * a = 1 + w * b ∧ u ≤ b ∧ w ≤ a := by
  rcases Nat.lt_or_ge 1 b with hb1 | hb1
  · obtain ⟨m, hmb, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime h hb1
    refine ⟨m, a * m / b, ?_, hmb.le, ?_⟩
    · have h2 := Nat.div_add_mod (a * m) b
      rw [hm] at h2
      rw [Nat.mul_comm m a]; linarith
    · have h3 : a * m < b * a := by
        rw [Nat.mul_comm b a]; exact Nat.mul_lt_mul_of_pos_left hmb ha
      exact le_of_lt (Nat.div_lt_of_lt_mul h3)
  · refine ⟨1, a - 1, ?_, by omega, by omega⟩
    have : b = 1 := by omega
    subst this; omega

def k2P (n : ℕ) : ℕ := Nat.log 2 (2 * n) + 1

def k3P (n : ℕ) : ℕ := Nat.log 3 n + 1

theorem scl_pos (p k : ℕ) (hp : 0 < p) : 0 < scl p k := by
  obtain ⟨E, -, h⟩ := scl_pow p k; rw [h]; exact pow_pos hp _

theorem bez_exists (n : ℕ) : ∃ uw : ℕ × ℕ, uw.1 * scl 2 (k2P n) = 1 + uw.2 * scl 3 (k3P n) ∧
    uw.1 ≤ scl 3 (k3P n) ∧ uw.2 ≤ scl 2 (k2P n) := by
  have hc : Nat.Coprime (scl 2 (k2P n)) (scl 3 (k3P n)) := by
    obtain ⟨E2, -, h2⟩ := scl_pow 2 (k2P n)
    obtain ⟨E3, -, h3⟩ := scl_pow 3 (k3P n)
    rw [h2, h3]; exact Nat.Coprime.pow _ _ (by norm_num)
  obtain ⟨u, w, h1, h2, h3⟩ := bezout_nat _ _ hc (scl_pos 2 _ (by norm_num)) (scl_pos 3 _ (by norm_num))
  exact ⟨(u, w), h1, h2, h3⟩

noncomputable def bzUW (n : ℕ) : ℕ × ℕ := Classical.choose (bez_exists n)

theorem bzUW_spec (n : ℕ) : (bzUW n).1 * scl 2 (k2P n) = 1 + (bzUW n).2 * scl 3 (k3P n) ∧
    (bzUW n).1 ≤ scl 3 (k3P n) ∧ (bzUW n).2 ≤ scl 2 (k2P n) :=
  Classical.choose_spec (bez_exists n)

/-- Product of two coefficient vectors padded into one block of `R[X]/(cyc p (p^k))`. -/
def polyMulP (p k : ℕ) (as bs : List ℕ) : Gen (List ℕ) :=
  Gen.bind (Gen.emit .zero) fun z =>
  mulRec p k (padBlk z ((p - 1) * p ^ k) as) (padBlk z ((p - 1) * p ^ k) bs)

open Polynomial in
theorem triple_polyMulP {R : Type*} [CommRing R] (ι : R → R) (p k : ℕ) (hp : p = 2 ∨ p = 3)
    (as bs : List ℕ) (av bv : List R) (P : List R → Prop) (hP : Stable P)
    (ha : ∀ regs, P regs → HoldsVec regs as av) (hb : ∀ regs, P regs → HoldsVec regs bs bv)
    (hl : av.length + bv.length ≤ (p - 1) * p ^ k) :
    Triple ι (polyMulP p k as bs) P (fun out regs => P regs ∧ ∃ ws : List R,
      HoldsVec regs out ws ∧ ws.length = (p - 1) * p ^ k ∧
      toPoly ws = ((scl p k : ℕ) : R[X]) * (toPoly av * toPoly bv)) := by
  have hp2 : 2 ≤ p := by omega
  have hD : 0 < (p - 1) * p ^ k := Nat.mul_pos (by omega) (pow_pos (by omega) _)
  unfold polyMulP
  refine triple_bind ι _ _ P _ _ (triple_emit_zero ι P hP) fun z => ?_
  have hP' : Stable (fun regs : List R => P regs ∧ Holds regs z 0) :=
    stable_and _ _ hP (stable_holds z 0)
  refine triple_post ι _ _ _ _ (mulRec_ok ι p hp k _ _ _ _ _ hP'
    (fun regs h => holdsB_padBlk p (p ^ k) regs z h.2 as av (ha regs h.1) (by omega))
    (fun regs h => holdsB_padBlk p (p ^ k) regs z h.2 bs bv (hb regs h.1) (by omega))) ?_
  rintro out regs ⟨h1, ws, hws, hwl, hwv⟩
  refine ⟨h1.1, ws, hws, hwl, ?_⟩
  apply no_wrap p (p ^ k) hp2 (pow_pos (by omega) _) _ _ (toPoly_degree_lt ws _ hwl.le)
  · have h1 := toPoly_natDegree_le av
    have h2 := toPoly_natDegree_le bv
    have h3 : (((scl p k : ℕ) : R[X]) * (toPoly av * toPoly bv)).natDegree ≤
        (p - 1) * p ^ k - 1 := by
      refine le_trans natDegree_mul_le ?_
      rw [natDegree_natCast, zero_add]
      refine le_trans natDegree_mul_le ?_
      omega
    have hlt : (p - 1) * p ^ k - 1 < (p - 1) * p ^ k := by omega
    exact lt_of_le_of_lt (degree_le_of_natDegree_le h3) (by exact_mod_cast hlt)
  · rw [hwv, map_mul, map_mul, map_natCast]

theorem ops_polyMulP (p k : ℕ) (hp : p = 2 ∨ p = 3) (as bs : List ℕ)
    (ha : as.length ≤ (p - 1) * p ^ k) (hb : bs.length ≤ (p - 1) * p ^ k) (n : ℕ) :
    (polyMulP p k as bs).ops n ≤ 1 + 1000 * p ^ k * (k + 1) ^ 10 := by
  unfold polyMulP
  rw [ops_bind]
  exact Nat.add_le_add (ops_emit_le _ _) (ops_mulRec p hp k _ _ _
    (by rw [padBlk_length _ _ _ ha]) (by rw [padBlk_length _ _ _ hb]))

theorem polyMulP_length (p k : ℕ) (as bs : List ℕ) (n : ℕ) :
    ((polyMulP p k as bs) n).1.length ≤ (p - 1) * p ^ k := by
  unfold polyMulP; simp only [Gen.bind]; exact mulRec_length _ _ _ _ _

/-- Bezout combination `u * c₂ - w * c₃`, truncated to `2n` coefficients. -/
noncomputable def combGen (n : ℕ) (c₂ c₃ : List ℕ) : Gen (List ℕ) :=
  Gen.bind (natConst (bzUW n).1) fun ru =>
  Gen.bind (natConst (bzUW n).2) fun rw =>
  Gen.bind (vecSmul ru c₂) fun x =>
  Gen.bind (vecSmul rw c₃) fun y =>
  Gen.bind (vecNeg y) fun ny =>
  Gen.bind (vecAddPad x ny) fun zs =>
  Gen.pure (zs.take (2 * n))

theorem triple_combGen {R : Type*} [CommRing R] (ι : R → R) (n : ℕ) (c₂ c₃ : List ℕ)
    (w₂ w₃ : List R) (P : List R → Prop) (hP : Stable P)
    (h₂ : ∀ regs, P regs → HoldsVec regs c₂ w₂) (h₃ : ∀ regs, P regs → HoldsVec regs c₃ w₃) :
    Triple ι (combGen n c₂ c₃) P (fun out regs => P regs ∧ HoldsVec regs out
      ((listAddPad (w₂.map ((((bzUW n).1 : ℕ) : R) * ·))
        ((w₃.map ((((bzUW n).2 : ℕ) : R) * ·)).map Neg.neg)).take (2 * n))) := by
  unfold combGen
  refine triple_bind ι _ _ P _ _ (triple_natConst ι P hP _) fun ru => ?_
  have S1 := stable_and _ _ hP (stable_holds ru ((((bzUW n).1 : ℕ) : R)))
  refine triple_bind ι _ _ _ _ _ (triple_natConst ι _ S1 _) fun rw => ?_
  have S2 := stable_and _ _ S1 (stable_holds rw ((((bzUW n).2 : ℕ) : R)))
  refine triple_bind ι _ _ _ _ _ (triple_vecSmul ι ru _ c₂ w₂ _ S2 (fun _ h => h.1.2)
    (fun _ h => h₂ _ h.1.1)) fun x => ?_
  have S3 := stable_and _ _ S2 (stable_holdsVec x (w₂.map ((((bzUW n).1 : ℕ) : R) * ·)))
  refine triple_bind ι _ _ _ _ _ (triple_vecSmul ι rw _ c₃ w₃ _ S3 (fun _ h => h.1.2)
    (fun _ h => h₃ _ h.1.1.1)) fun y => ?_
  have S4 := stable_and _ _ S3 (stable_holdsVec y (w₃.map ((((bzUW n).2 : ℕ) : R) * ·)))
  refine triple_bind ι _ _ _ _ _ (triple_vecNeg ι y _ _ S4 (fun _ h => h.2)) fun ny => ?_
  have S5 := stable_and _ _ S4
    (stable_holdsVec ny ((w₃.map ((((bzUW n).2 : ℕ) : R) * ·)).map Neg.neg))
  refine triple_bind ι _ _ _ _ _ (triple_vecAddPad ι x ny _ _ _ S5 (fun _ h => h.1.1.2)
    (fun _ h => h.2)) fun zs => ?_
  exact triple_pure ι _ _ _ fun regs h => ⟨h.1.1.1.1.1.1, List.forall₂_take _ h.2⟩

theorem ops_combGen (n : ℕ) (c₂ c₃ : List ℕ) (m : ℕ) :
    (combGen n c₂ c₃).ops m ≤ (4 * Nat.log 2 (bzUW n).1 + 4) + (4 * Nat.log 2 (bzUW n).2 + 4) +
      2 * c₂.length + 2 * c₃.length := by
  unfold combGen
  simp only [ops_bind, ops_pure, ops_vecSmul, ops_vecNeg, vecSmul_length, ops_vecAddPad]
  have h1 := ops_natConst (bzUW n).1 m
  have h2 := ops_natConst (bzUW n).2 ((natConst (bzUW n).1) m).2.2
  have h3 := Nat.min_le_left c₂.length c₃.length
  omega

/-- Product of two coefficient vectors of length at most `n`: `2n` coefficients. -/
noncomputable def polyMulG (n : ℕ) (as bs : List ℕ) : Gen (List ℕ) :=
  Gen.bind (polyMulP 2 (k2P n) as bs) fun c₂ =>
  Gen.bind (polyMulP 3 (k3P n) as bs) fun c₃ =>
  combGen n c₂ c₃

noncomputable def polyMulGen (n : ℕ) : Gen (List ℕ) := polyMulG n (List.range' 0 n) (List.range' n n)

theorem k2P_ok (n : ℕ) : 2 * n < 2 ^ k2P n := Nat.lt_pow_succ_log_self (by norm_num) _

theorem k3P_ok (n : ℕ) : n < 3 ^ k3P n := Nat.lt_pow_succ_log_self (by norm_num) _

open Polynomial in
theorem triple_polyMulG {R : Type*} [CommRing R] (ι : R → R) (n : ℕ) (as bs : List ℕ) (av bv : List R)
    (hla : av.length ≤ n) (hlb : bv.length ≤ n) (P : List R → Prop) (hP : Stable P)
    (ha : ∀ regs, P regs → HoldsVec regs as av)
    (hb : ∀ regs, P regs → HoldsVec regs bs bv) :
    Triple ι (polyMulG n as bs) P (fun out regs => P regs ∧ ∃ zs : List R, HoldsVec regs out zs ∧
      zs = List.ofFn (fun j : Fin (2 * n) => (toPoly av * toPoly bv).coeff (j : ℕ))) := by
  obtain ⟨hbz, -, -⟩ := bzUW_spec n
  have hl2 : av.length + bv.length ≤ (2 - 1) * 2 ^ k2P n := by
    have := k2P_ok n; omega
  have hl3 : av.length + bv.length ≤ (3 - 1) * 3 ^ k3P n := by
    have := k3P_ok n; omega
  unfold polyMulG
  refine triple_bind ι _ _ P _ _ (triple_polyMulP ι 2 (k2P n) (Or.inl rfl) _ _ av bv P hP ha hb
    hl2) fun c₂ => ?_
  intro regs hr
  obtain ⟨hr0, w₂, hw₂, hw₂l, hw₂v⟩ := hr
  let P1 : List R → Prop := fun r => P r ∧ HoldsVec r c₂ w₂
  have hP1 : Stable P1 := stable_and _ _ hP (stable_holdsVec _ _)
  suffices T : Triple ι (Gen.bind (polyMulP 3 (k3P n) as bs)
      fun c₃ => combGen n c₂ c₃) P1 (fun out regs => P regs ∧ ∃ zs : List R, HoldsVec regs out zs ∧
      zs = List.ofFn (fun j : Fin (2 * n) => (toPoly av * toPoly bv).coeff (j : ℕ))) from
    T regs ⟨hr0, hw₂⟩
  refine triple_bind ι _ _ P1 _ _ (triple_polyMulP ι 3 (k3P n) (Or.inr rfl) _ _ av bv P1 hP1
    (fun r h => ha r h.1) (fun r h => hb r h.1) hl3) fun c₃ => ?_
  intro regs' hr'
  obtain ⟨hr1, w₃, hw₃, hw₃l, hw₃v⟩ := hr'
  let P2 : List R → Prop := fun r => P1 r ∧ HoldsVec r c₃ w₃
  have hP2 : Stable P2 := stable_and _ _ hP1 (stable_holdsVec _ _)
  obtain ⟨new, e1, e2, e3⟩ := triple_combGen ι n c₂ c₃ w₂ w₃ P2 hP2 (fun r h => h.1.2)
    (fun r h => h.2) regs' ⟨hr1, hw₃⟩
  refine ⟨new, e1, e2, e3.1.1.1, _, e3.2, ?_⟩
  -- the value
  set F := toPoly av * toPoly bv
  have hval : toPoly (listAddPad (w₂.map ((((bzUW n).1 : ℕ) : R) * ·))
      ((w₃.map ((((bzUW n).2 : ℕ) : R) * ·)).map Neg.neg)) = F := by
    rw [toPoly_listAddPad, toPoly_map_neg, toPoly_map_mul, toPoly_map_mul, hw₂v, hw₃v,
      map_natCast, map_natCast]
    have hc := congrArg (Nat.cast : ℕ → R[X]) hbz
    push_cast at hc
    linear_combination F * hc
  have hlen : 2 * n ≤ (listAddPad (w₂.map ((((bzUW n).1 : ℕ) : R) * ·))
      ((w₃.map ((((bzUW n).2 : ℕ) : R) * ·)).map Neg.neg)).length := by
    rw [listAddPad_length, List.length_map, hw₂l]
    have := k2P_ok n
    omega
  set L := listAddPad (w₂.map ((((bzUW n).1 : ℕ) : R) * ·))
      ((w₃.map ((((bzUW n).2 : ℕ) : R) * ·)).map Neg.neg) with hLdef
  apply List.ext_getElem
  · rw [List.length_take, List.length_ofFn]; omega
  · intro j hj1 hj2
    have hjL : j < L.length := by rw [List.length_take] at hj1; omega
    simp only [List.getElem_take, List.getElem_ofFn, Fin.val_mk]
    rw [← hval, toPoly_coeff]
    simp [hjL]

open Polynomial in
theorem triple_polyMulGen {R : Type*} [CommRing R] (ι : R → R) (n : ℕ) (av bv : List R)
    (hla : av.length = n) (hlb : bv.length = n) (P : List R → Prop) (hP : Stable P)
    (ha : ∀ regs, P regs → HoldsVec regs (List.range' 0 n) av)
    (hb : ∀ regs, P regs → HoldsVec regs (List.range' n n) bv) :
    Triple ι (polyMulGen n) P (fun out regs => P regs ∧ ∃ zs : List R, HoldsVec regs out zs ∧
      zs = List.ofFn (fun j : Fin (2 * n) => (toPoly av * toPoly bv).coeff (j : ℕ))) :=
  triple_polyMulG ι n _ _ av bv hla.le hlb.le P hP ha hb

open Polynomial in
theorem densePoly_eq_toPoly {R : Type*} [CommRing R] :
    ∀ (n : ℕ) (a : Fin n → R), densePoly a = toPoly (List.ofFn a)
  | 0, a => by simp [densePoly, toPoly]
  | n + 1, a => by
    rw [List.ofFn_succ]
    simp only [toPoly]
    rw [← densePoly_eq_toPoly n (fun i => a i.succ)]
    simp only [densePoly, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one, Fin.val_succ,
      pow_succ, Finset.mul_sum]
    exact congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun j _ => by ring)

theorem ops_polyMulG (n : ℕ) (as bs : List ℕ) (ha : as.length ≤ n) (hb : bs.length ≤ n) (m : ℕ) :
    (polyMulG n as bs).ops m ≤ 10 ^ 9 * (n + 1) * (Nat.log 2 (n + 1) + 1) ^ 10 := by
  unfold polyMulG
  simp only [ops_bind]
  have hr0 : as.length ≤ (2 - 1) * 2 ^ k2P n := by
    have := k2P_ok n; omega
  have hr1 : bs.length ≤ (2 - 1) * 2 ^ k2P n := by
    have := k2P_ok n; omega
  have hs0 : as.length ≤ (3 - 1) * 3 ^ k3P n := by
    have := k3P_ok n; omega
  have hs1 : bs.length ≤ (3 - 1) * 3 ^ k3P n := by
    have := k3P_ok n; omega
  have o1 := ops_polyMulP 2 (k2P n) (Or.inl rfl) _ _ hr0 hr1 m
  have o2 := ops_polyMulP 3 (k3P n) (Or.inr rfl) _ _ hs0 hs1
    ((polyMulP 2 (k2P n) as bs) m).2.2
  have o3 := ops_combGen n ((polyMulP 2 (k2P n) as bs) m).1
    ((polyMulP 3 (k3P n) as bs)
      ((polyMulP 2 (k2P n) as bs) m).2.2).1
    ((polyMulP 3 (k3P n) as bs)
      ((polyMulP 2 (k2P n) as bs) m).2.2).2.2
  have l1 := polyMulP_length 2 (k2P n) as bs m
  have l2 := polyMulP_length 3 (k3P n) as bs
    ((polyMulP 2 (k2P n) as bs) m).2.2
  -- size facts
  set L := Nat.log 2 (n + 1) with hL
  have F1 : 2 ^ k2P n ≤ 4 * (n + 1) := by
    unfold k2P
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have := Nat.pow_log_le_self 2 (show 2 * n ≠ 0 by omega)
      rw [pow_succ]; omega
  have F2 : k2P n ≤ L + 2 := by
    unfold k2P
    have h1 : Nat.log 2 (2 * n) ≤ Nat.log 2 ((n + 1) * 2) := Nat.log_mono_right (by omega)
    rw [Nat.log_mul_base (by norm_num) (by omega)] at h1
    omega
  have F3 : 3 ^ k3P n ≤ 3 * (n + 1) := by
    unfold k3P
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have := Nat.pow_log_le_self 3 (show n ≠ 0 by omega)
      rw [pow_succ]; omega
  have F4 : k3P n ≤ L + 1 := by
    unfold k3P
    have h1 : Nat.log 3 n ≤ Nat.log 2 n := Nat.log_anti_left (by norm_num) (by norm_num)
    have h2 : Nat.log 2 n ≤ Nat.log 2 (n + 1) := Nat.log_mono_right (by omega)
    omega
  obtain ⟨-, hu, hw⟩ := bzUW_spec n
  have F5 : Nat.log 2 (bzUW n).1 ≤ 8 * (L + 1) := by
    obtain ⟨E3, hE3, h3⟩ := scl_pow 3 (k3P n)
    have h4 : (bzUW n).1 ≤ 2 ^ (8 * k3P n) := by
      calc (bzUW n).1 ≤ 3 ^ E3 := h3 ▸ hu
        _ ≤ 3 ^ (4 * k3P n) := Nat.pow_le_pow_right (by norm_num) hE3
        _ ≤ 4 ^ (4 * k3P n) := Nat.pow_le_pow_left (by norm_num) _
        _ = 2 ^ (8 * k3P n) := by rw [show 8 * k3P n = 2 * (4 * k3P n) by ring, pow_mul 2 2]; norm_num
    have h5 := Nat.log_mono_right (b := 2) h4
    rw [Nat.log_pow (by norm_num)] at h5
    omega
  have F6 : Nat.log 2 (bzUW n).2 ≤ 8 * (L + 1) := by
    obtain ⟨E2, hE2, h2⟩ := scl_pow 2 (k2P n)
    have h4 : (bzUW n).2 ≤ 2 ^ (4 * k2P n) :=
      le_trans (h2 ▸ hw) (Nat.pow_le_pow_right (by norm_num) hE2)
    have h5 := Nat.log_mono_right (b := 2) h4
    rw [Nat.log_pow (by norm_num)] at h5
    omega
  have hQ1 : L + 1 ≤ (L + 1) ^ 10 := by
    calc L + 1 = (L + 1) ^ 1 := (pow_one _).symm
      _ ≤ (L + 1) ^ 10 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have G2 : (k2P n + 1) ^ 10 ≤ 3 ^ 10 * (L + 1) ^ 10 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  have G3 : (k3P n + 1) ^ 10 ≤ 3 ^ 10 * (L + 1) ^ 10 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) _
  generalize (L + 1) ^ 10 = Q at hQ1 G2 G3 ⊢
  generalize (k2P n + 1) ^ 10 = A2 at G2 o1
  generalize (k3P n + 1) ^ 10 = A3 at G3 o2
  generalize 2 ^ k2P n = B2 at F1 o1 l1
  generalize 3 ^ k3P n = B3 at F3 o2 l2
  have m1 : 1000 * B2 * A2 ≤ 1000 * (4 * (n + 1)) * (3 ^ 10 * Q) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ F1) G2
  have m2 : 1000 * B3 * A3 ≤ 1000 * (3 * (n + 1)) * (3 ^ 10 * Q) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ F3) G3
  have m3 : (L + 1) * 1 ≤ Q * (n + 1) := Nat.mul_le_mul hQ1 (by omega)
  have m4 : (n + 1) * 1 ≤ (n + 1) * Q := Nat.mul_le_mul_left _ (by omega)
  norm_num at m1 m2 l1 l2 ⊢
  linarith only [o1, o2, o3, l1, l2, m1, m2, m3, m4, F5, F6, hL, hQ1, F1, F3, G2, G3]

theorem ops_polyMulGen (n m : ℕ) :
    (polyMulGen n).ops m ≤ 10 ^ 9 * (n + 1) * (Nat.log 2 (n + 1) + 1) ^ 10 :=
  ops_polyMulG n _ _ (by simp) (by simp) m

/-! ## S2-G9 generated code contains no oracle instruction -/

def NoOr {α : Type} (g : Gen α) : Prop := ∀ n, ∀ i ∈ (g n).2.1, i.isRingOp = true

theorem noOr_pure {α : Type} (a : α) : NoOr (Gen.pure a) := by
  intro n i hi; simp [Gen.pure] at hi

theorem noOr_emit (i : Instr) (h : i.isRingOp = true) : NoOr (Gen.emit i) := by
  intro n j hj; simp only [Gen.emit, List.mem_singleton] at hj; subst hj; exact h

theorem noOr_bind {α β : Type} (g : Gen α) (f : α → Gen β) (hg : NoOr g) (hf : ∀ a, NoOr (f a)) :
    NoOr (Gen.bind g f) := by
  intro n i hi
  simp only [Gen.bind, List.mem_append] at hi
  rcases hi with hi | hi
  · exact hg _ _ hi
  · exact hf _ _ _ hi

theorem noOr_mapGen {α β : Type} (f : α → Gen β) (hf : ∀ a, NoOr (f a)) :
    ∀ as, NoOr (mapGen f as)
  | [] => noOr_pure _
  | a :: as => by
    rw [mapGen]
    exact noOr_bind _ _ (hf a) fun _ => noOr_bind _ _ (noOr_mapGen f hf as) fun _ => noOr_pure _

theorem noOr_vecAddPad : ∀ is js, NoOr (vecAddPad is js)
  | i :: is, j :: js => by
    rw [vecAddPad]
    exact noOr_bind _ _ (noOr_emit _ rfl) fun _ =>
      noOr_bind _ _ (noOr_vecAddPad is js) fun _ => noOr_pure _
  | [], js => by rw [vecAddPad]; exact noOr_pure _
  | i :: is, [] => by simp only [vecAddPad]; exact noOr_pure _

theorem noOr_vecSmul (s : ℕ) : ∀ js, NoOr (vecSmul s js)
  | [] => noOr_pure _
  | j :: js => by
    rw [vecSmul]
    exact noOr_bind _ _ (noOr_emit _ rfl) fun _ =>
      noOr_bind _ _ (noOr_vecSmul s js) fun _ => noOr_pure _

theorem noOr_vecNeg : ∀ js, NoOr (vecNeg js)
  | [] => noOr_pure _
  | j :: js => by
    rw [vecNeg]
    exact noOr_bind _ _ (noOr_emit _ rfl) fun _ =>
      noOr_bind _ _ (noOr_vecNeg js) fun _ => noOr_pure _

theorem noOr_schoolMul : ∀ is js, NoOr (schoolMul is js)
  | [], js => by rw [schoolMul]; exact noOr_pure _
  | i :: is, js => by
    rw [schoolMul]
    refine noOr_bind _ _ (noOr_vecSmul _ _) fun p => noOr_bind _ _ (noOr_schoolMul is js) fun q => ?_
    rcases p with _ | ⟨p₀, p'⟩
    · exact noOr_pure _
    · exact noOr_bind _ _ (noOr_vecAddPad _ _) fun _ => noOr_pure _

theorem noOr_shiftAdd (e nt : ℕ) : ∀ k rs, NoOr (shiftAdd e nt k rs)
  | _, [] => by simp only [shiftAdd]; exact noOr_pure _
  | 0, r :: rs => by
    rw [shiftAdd]
    exact noOr_bind _ _ (noOr_emit _ rfl) fun _ =>
      noOr_bind _ _ (noOr_shiftAdd e nt _ rs) fun _ => noOr_pure _
  | k + 1, r :: rs => by
    rw [shiftAdd]
    exact noOr_bind _ _ (noOr_shiftAdd e nt k rs) fun _ => noOr_pure _

theorem noOr_mulXGen (e D : ℕ) (blk : List ℕ) : NoOr (mulXGen e D blk) := by
  unfold mulXGen
  exact noOr_bind _ _ (noOr_emit _ rfl) fun _ =>
    noOr_bind _ _ (noOr_shiftAdd _ _ _ _) fun _ => noOr_pure _

theorem noOr_mulXPow (e D : ℕ) : ∀ j blk, NoOr (mulXPow e D j blk)
  | 0, blk => by rw [mulXPow]; exact noOr_pure _
  | j + 1, blk => by
    rw [mulXPow]
    exact noOr_bind _ _ (noOr_mulXGen _ _ _) fun _ => noOr_mulXPow e D j _

theorem noOr_sumBlocks : ∀ bs, NoOr (sumBlocks bs)
  | [] => by rw [sumBlocks]; exact noOr_pure _
  | [b] => by rw [sumBlocks]; exact noOr_pure _
  | b :: b' :: bs => by
    rw [sumBlocks]
    exact noOr_bind _ _ (noOr_sumBlocks (b' :: bs)) fun _ => noOr_vecAddPad _ _

theorem noOr_twGen (p e s k M : ℕ) (subs : List (List (List ℕ))) : NoOr (twGen p e s k M subs) := by
  unfold twGen
  exact noOr_bind _ _ (noOr_mapGen _ (fun _ => noOr_mulXPow _ _ _ _) _) fun _ => noOr_sumBlocks _

theorem noOr_fftGen (p e : ℕ) : ∀ l s blks, NoOr (fftGen p e l s blks)
  | 0, s, blks => by rw [fftGen]; exact noOr_pure _
  | l + 1, s, blks => by
    rw [fftGen]
    exact noOr_bind _ _ (noOr_mapGen _ (fun _ => noOr_fftGen p e l _ _) _) fun _ =>
      noOr_mapGen _ (fun _ => noOr_twGen _ _ _ _ _ _) _

theorem noOr_convGen (p e l s : ℕ) (mulB : List ℕ → List ℕ → Gen (List ℕ))
    (hm : ∀ b₁ b₂, NoOr (mulB b₁ b₂)) (as bs : List (List ℕ)) : NoOr (convGen p e l s mulB as bs) := by
  unfold convGen
  exact noOr_bind _ _ (noOr_fftGen _ _ _ _ _) fun _ => noOr_bind _ _ (noOr_fftGen _ _ _ _ _) fun _ =>
    noOr_bind _ _ (noOr_mapGen _ (fun _ => hm _ _) _) fun _ => noOr_fftGen _ _ _ _ _

theorem noOr_reduceGen (p n : ℕ) (H : List ℕ) : NoOr (reduceGen p n H) := by
  unfold reduceGen
  refine noOr_bind _ _ (noOr_vecNeg _) fun _ => noOr_bind _ _ (noOr_mapGen _ (fun q => ?_) _)
    fun _ => noOr_pure _
  split_ifs
  · exact noOr_bind _ _ (noOr_vecAddPad _ _) fun _ => noOr_vecAddPad _ _
  · exact noOr_vecAddPad _ _

theorem noOr_overlapGen (m : ℕ) : ∀ k acc bs, NoOr (overlapGen m k acc bs)
  | k, acc, [] => by rw [overlapGen]; exact noOr_pure _
  | k, acc, b :: bs => by
    rw [overlapGen]
    exact noOr_bind _ _ (by unfold addAt; exact noOr_bind _ _ (noOr_vecAddPad _ _) fun _ => noOr_pure _)
      fun _ => noOr_overlapGen m _ _ bs

theorem noOr_mulRec (p : ℕ) : ∀ k b₁ b₂, NoOr (mulRec p k b₁ b₂) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro b₁ b₂
    rw [mulRec]
    split_ifs with hk
    · unfold baseMul
      exact noOr_bind _ _ (noOr_schoolMul _ _) fun _ => noOr_bind _ _ (noOr_emit _ rfl) fun _ =>
        noOr_reduceGen _ _ _
    · unfold stepGen
      exact noOr_bind _ _ (noOr_emit _ rfl) fun _ =>
        noOr_bind _ _ (noOr_convGen _ _ _ _ _ (ih _ (muP'_lt p k hk)) _ _) fun _ =>
        noOr_bind _ _ (noOr_overlapGen _ _ _ _) fun _ => noOr_reduceGen _ _ _

theorem noOr_natConst (c : ℕ) : NoOr (natConst c) := by
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    rcases c with _ | c
    · rw [natConst]; exact noOr_emit _ rfl
    · rw [natConst]
      refine noOr_bind _ _ (ih _ (by omega)) fun _ => noOr_bind _ _ (noOr_emit _ rfl) fun _ => ?_
      split_ifs
      · exact noOr_pure _
      · exact noOr_bind _ _ (noOr_emit _ rfl) fun _ => noOr_emit _ rfl

theorem noOr_polyMulG (n : ℕ) (as bs : List ℕ) : NoOr (polyMulG n as bs) := by
  have hP : ∀ p k as bs, NoOr (polyMulP p k as bs) := fun p k as bs => by
    unfold polyMulP; exact noOr_bind _ _ (noOr_emit _ rfl) fun _ => noOr_mulRec _ _ _ _
  unfold polyMulG combGen
  exact noOr_bind _ _ (hP _ _ _ _) fun _ => noOr_bind _ _ (hP _ _ _ _) fun _ =>
    noOr_bind _ _ (noOr_natConst _) fun _ => noOr_bind _ _ (noOr_natConst _) fun _ =>
    noOr_bind _ _ (noOr_vecSmul _ _) fun _ => noOr_bind _ _ (noOr_vecSmul _ _) fun _ =>
    noOr_bind _ _ (noOr_vecNeg _) fun _ => noOr_bind _ _ (noOr_vecAddPad _ _) fun _ => noOr_pure _

theorem noOr_polyMulGen (n : ℕ) : NoOr (polyMulGen n) := noOr_polyMulG n _ _

/-- **ChildA (Cantor–Kaltofen)**: quasi-linear polynomial multiplication over any commutative
ring by a straight-line program without oracle calls. -/
theorem polyMul_main : ∃ (C k : ℕ) (M : ℕ → SLP), ∀ n : ℕ,
    ringOps (M n) ≤ C * (n + 1) * (Nat.log 2 (n + 1) + 1) ^ k ∧ oracleCalls (M n) = [] ∧
    ∀ (R : Type) [CommRing R] (ι : R → R) (a b : Fin n → R),
      run ι (M n) (List.ofFn a ++ List.ofFn b) =
        List.ofFn (fun j : Fin (2 * n) => (densePoly a * densePoly b).coeff (j : ℕ)) := by
  refine ⟨10 ^ 9, 10, fun n => ⟨((polyMulGen n) (n + n)).2.1, ((polyMulGen n) (n + n)).1⟩,
    fun n => ⟨?_, ?_, ?_⟩⟩
  · rw [ringOps_gen]; exact ops_polyMulGen n _
  · exact oracleCalls_gen_nil _ _ (noOr_polyMulGen n (n + n))
  · intro R _ ι a b
    have hlen : (List.ofFn a ++ List.ofFn b).length = n + n := by simp
    let P : List R → Prop := fun regs => HoldsVec regs (List.range' 0 n) (List.ofFn a) ∧
      HoldsVec regs (List.range' n n) (List.ofFn b)
    have hP : Stable P := stable_and _ _ (stable_holdsVec _ _) (stable_holdsVec _ _)
    have T := triple_polyMulGen ι n (List.ofFn a) (List.ofFn b) (by simp) (by simp) P hP
      (fun _ h => h.1) (fun _ h => h.2)
    have h0 : P (List.ofFn a ++ List.ofFn b) := by
      refine ⟨?_, ?_⟩
      · have := holdsVec_range' (List.ofFn a) []
        simp only [List.nil_append, List.length_nil, List.length_ofFn] at this
        exact holdsVec_append _ _ _ _ this
      · have := holdsVec_range' (List.ofFn b) (List.ofFn a)
        simpa only [List.length_ofFn] using this
    have := run_of_triple ι (polyMulGen n) P _
      (fun vs => vs = List.ofFn (fun j : Fin (2 * n) => (densePoly a * densePoly b).coeff (j : ℕ)))
      T (fun out regs h => by
        obtain ⟨-, zs, h1, h2⟩ := h
        refine ⟨zs, h1, ?_⟩
        rw [h2, densePoly_eq_toPoly n a, densePoly_eq_toPoly n b]) _ h0
    rw [hlen] at this
    exact this

/-! ## S3a Newton inversion of a power series with constant term 1 -/

open Polynomial in
theorem toPoly_ofFn_coeff {R : Type*} [CommRing R] (N : ℕ) (F : R[X])
    (hF : F.natDegree < N ∨ F = 0) :
    toPoly (List.ofFn (fun j : Fin N => F.coeff (j : ℕ))) = F := by
  ext q
  rw [toPoly_coeff]
  by_cases hq : q < N
  · simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hq]
  · have h0 : F.coeff q = 0 := by
      rcases hF with hF | hF
      · exact coeff_eq_zero_of_natDegree_lt (by omega)
      · simp [hF]
    simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hq, h0]

open Polynomial in
theorem toPoly_mul_deg {R : Type*} [CommRing R] (n : ℕ) (av bv : List R) (hla : av.length ≤ n)
    (hlb : bv.length ≤ n) :
    (toPoly av * toPoly bv).natDegree < 2 * n ∨ toPoly av * toPoly bv = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · right
    rw [List.length_eq_zero_iff.mp (by omega : av.length = 0)]
    simp [toPoly]
  · left
    have h1 := toPoly_natDegree_le av
    have h2 := toPoly_natDegree_le bv
    exact lt_of_le_of_lt natDegree_mul_le (by omega)

open Polynomial in
theorem toPoly_polyMul_out {R : Type*} [CommRing R] (n : ℕ) (av bv : List R)
    (hla : av.length ≤ n) (hlb : bv.length ≤ n) :
    toPoly (List.ofFn (fun j : Fin (2 * n) => (toPoly av * toPoly bv).coeff (j : ℕ))) =
      toPoly av * toPoly bv :=
  toPoly_ofFn_coeff _ _ (toPoly_mul_deg n av bv hla hlb)

open Polynomial in
theorem dvd_sub_take {R : Type*} [CommRing R] (vs : List R) (m : ℕ) :
    X ^ m ∣ toPoly vs - toPoly (vs.take m) := by
  by_cases h : m ≤ vs.length
  · rw [toPoly_take_drop vs m h]; exact ⟨toPoly (vs.drop m), by ring⟩
  · rw [List.take_of_length_le (by omega), sub_self]; exact dvd_zero _

open Polynomial in
theorem newton_alg {R : Type*} [CommRing R] (l : ℕ) (f f' g e e' : R[X])
    (hfg : X ^ l ∣ f * g - 1) (hf : X ^ (2 * l) ∣ f - f') (he : e = f' * g)
    (he' : X ^ (2 * l) ∣ e - e') :
    X ^ (2 * l) ∣ f * (2 * g - g * e') - 1 := by
  obtain ⟨a, ha⟩ := hfg
  obtain ⟨b, hb⟩ := hf
  obtain ⟨c, hc⟩ := he'
  have hf' : f' = f - X ^ (2 * l) * b := by rw [← hb]; ring
  have hee : e' = e - X ^ (2 * l) * c := by rw [← hc]; ring
  subst hf' hee he
  refine ⟨-a ^ 2 + f * g * g * b + f * g * c, ?_⟩
  linear_combination (-(f * g - 1 + X ^ l * a)) * ha

/-- One Newton step at precision `l`: `g ↦ 2g - g (f g)` truncated to `2l`. -/
noncomputable def newtonStep (l : ℕ) (fs g : List ℕ) : Gen (List ℕ) :=
  Gen.bind (polyMulG (2 * l) (fs.take (2 * l)) g) fun e =>
  Gen.bind (polyMulG (2 * l) g (e.take (2 * l))) fun ge =>
  Gen.bind (vecAddPad g g) fun g2 =>
  Gen.bind (vecNeg ge) fun nge =>
  Gen.bind (vecAddPad g2 nge) fun s =>
  Gen.pure (s.take (2 * l))

open Polynomial in
theorem triple_newtonStep {R : Type*} [CommRing R] (ι : R → R) (l : ℕ) (fs g : List ℕ)
    (fv gv : List R) (hgl : gv.length ≤ l) (hfg : X ^ l ∣ toPoly fv * toPoly gv - 1)
    (P : List R → Prop) (hP : Stable P) (hfs : ∀ regs, P regs → HoldsVec regs fs fv)
    (hg : ∀ regs, P regs → HoldsVec regs g gv) :
    Triple ι (newtonStep l fs g) P (fun out regs => P regs ∧ ∃ gv' : List R,
      HoldsVec regs out gv' ∧ gv'.length ≤ 2 * l ∧ X ^ (2 * l) ∣ toPoly fv * toPoly gv' - 1) := by
  unfold newtonStep
  refine triple_bind ι _ _ P _ _ (triple_polyMulG ι (2 * l) _ _ (fv.take (2 * l)) gv
    (by simp) (by omega) P hP (fun r h => List.forall₂_take _ (hfs r h)) hg) fun e => ?_
  intro regs hr
  obtain ⟨hr0, ev, hev, hevv⟩ := hr
  let P1 : List R → Prop := fun r => P r ∧ HoldsVec r e ev
  have hP1 : Stable P1 := stable_and _ _ hP (stable_holdsVec _ _)
  have hevl : (ev.take (2 * l)).length ≤ 2 * l := by simp
  suffices T : Triple ι (Gen.bind (polyMulG (2 * l) g (e.take (2 * l))) fun ge =>
      Gen.bind (vecAddPad g g) fun g2 => Gen.bind (vecNeg ge) fun nge =>
      Gen.bind (vecAddPad g2 nge) fun s => Gen.pure (s.take (2 * l))) P1
      (fun out regs => P regs ∧ ∃ gv' : List R, HoldsVec regs out gv' ∧ gv'.length ≤ 2 * l ∧
        X ^ (2 * l) ∣ toPoly fv * toPoly gv' - 1) from T regs ⟨hr0, hev⟩
  refine triple_bind ι _ _ P1 _ _ (triple_polyMulG ι (2 * l) _ _ gv (ev.take (2 * l)) (by omega)
    hevl P1 hP1 (fun r h => hg r h.1) (fun r h => List.forall₂_take _ h.2)) fun ge => ?_
  intro regs' hr'
  obtain ⟨hr1, gev, hgev, hgevv⟩ := hr'
  let P2 : List R → Prop := fun r => P1 r ∧ HoldsVec r ge gev
  have hP2 : Stable P2 := stable_and _ _ hP1 (stable_holdsVec _ _)
  suffices T : Triple ι (Gen.bind (vecAddPad g g) fun g2 => Gen.bind (vecNeg ge) fun nge =>
      Gen.bind (vecAddPad g2 nge) fun s => Gen.pure (s.take (2 * l))) P2
      (fun out regs => P regs ∧ ∃ gv' : List R, HoldsVec regs out gv' ∧ gv'.length ≤ 2 * l ∧
        X ^ (2 * l) ∣ toPoly fv * toPoly gv' - 1) from T regs' ⟨hr1, hgev⟩
  refine triple_bind ι _ _ P2 _ _ (triple_vecAddPad ι g g gv gv P2 hP2 (fun r h => hg r h.1.1)
    (fun r h => hg r h.1.1)) fun g2 => ?_
  have S3 := stable_and _ _ hP2 (stable_holdsVec g2 (listAddPad gv gv))
  refine triple_bind ι _ _ _ _ _ (triple_vecNeg ι ge gev _ S3 (fun r h => h.1.2)) fun nge => ?_
  have S4 := stable_and _ _ S3 (stable_holdsVec nge (gev.map Neg.neg))
  refine triple_bind ι _ _ _ _ _ (triple_vecAddPad ι g2 nge _ _ _ S4 (fun r h => h.1.2)
    (fun r h => h.2)) fun s => ?_
  refine triple_pure ι _ _ _ fun r h => ⟨h.1.1.1.1.1, _, List.forall₂_take _ h.2, by simp, ?_⟩
  have hE : toPoly ev = toPoly (fv.take (2 * l)) * toPoly gv := by
    rw [hevv]; exact toPoly_polyMul_out _ _ _ (by simp) (by omega)
  have hGE : toPoly gev = toPoly gv * toPoly (ev.take (2 * l)) := by
    rw [hgevv]; exact toPoly_polyMul_out _ _ _ (by omega) hevl
  have hs : toPoly (listAddPad (listAddPad gv gv) (gev.map Neg.neg)) =
      2 * toPoly gv - toPoly gv * toPoly (ev.take (2 * l)) := by
    rw [toPoly_listAddPad, toPoly_listAddPad, toPoly_map_neg, hGE]; ring
  have h1 := newton_alg l (toPoly fv) (toPoly (fv.take (2 * l))) (toPoly gv) (toPoly ev)
    (toPoly (ev.take (2 * l))) hfg (dvd_sub_take fv (2 * l)) hE (dvd_sub_take ev (2 * l))
  rw [← hs] at h1
  have h2 := dvd_sub h1 (Dvd.dvd.mul_left (dvd_sub_take
    (listAddPad (listAddPad gv gv) (gev.map Neg.neg)) (2 * l)) (toPoly fv))
  convert h2 using 1
  ring

/-- `t` Newton steps from `g = 1`: an inverse of `f` modulo `X^(2^t)`. -/
noncomputable def newtonGen (fs : List ℕ) : ℕ → Gen (List ℕ)
  | 0 => Gen.bind (Gen.emit .one) fun o => Gen.pure [o]
  | t + 1 => Gen.bind (newtonGen fs t) fun g => newtonStep (2 ^ t) fs g

open Polynomial in
theorem triple_newtonGen {R : Type*} [CommRing R] (ι : R → R) (fs : List ℕ) (fv : List R)
    (hf0 : (toPoly fv).coeff 0 = 1) (P : List R → Prop) (hP : Stable P)
    (hfs : ∀ regs, P regs → HoldsVec regs fs fv) :
    ∀ t, Triple ι (newtonGen fs t) P (fun out regs => P regs ∧ ∃ gv : List R,
      HoldsVec regs out gv ∧ gv.length ≤ 2 ^ t ∧ X ^ (2 ^ t) ∣ toPoly fv * toPoly gv - 1)
  | 0 => by
    rw [newtonGen]
    refine triple_bind ι _ _ P _ _ (triple_emit_one ι P hP) fun o => ?_
    refine triple_pure ι _ _ _ fun regs h => ⟨h.1, [1], List.Forall₂.cons h.2 List.Forall₂.nil,
      by simp, ?_⟩
    rw [X_pow_dvd_iff]
    intro d hd
    have : d = 0 := by simpa using hd
    subst this
    simp [toPoly, hf0]
  | t + 1 => by
    rw [newtonGen]
    refine triple_bind ι _ _ P _ _ (triple_newtonGen ι fs fv hf0 P hP hfs t) fun g => ?_
    intro regs hr
    obtain ⟨hr0, gv, hgv, hgl, hgd⟩ := hr
    let P1 : List R → Prop := fun r => P r ∧ HoldsVec r g gv
    have hP1 : Stable P1 := stable_and _ _ hP (stable_holdsVec _ _)
    obtain ⟨new, e1, e2, e3⟩ := triple_newtonStep ι (2 ^ t) fs g fv gv hgl hgd P1 hP1
      (fun r h => hfs r h.1) (fun r h => h.2) regs ⟨hr0, hgv⟩
    obtain ⟨⟨e4, -⟩, gv', h5, h6, h7⟩ := e3
    refine ⟨new, e1, e2, e4, gv', h5, by rw [pow_succ]; omega, ?_⟩
    rw [pow_succ, mul_comm]
    exact h7

/-! ## S3b reversal algebra for the quotient -/

open Polynomial in
theorem toPoly_coeff_ge {R : Type*} [CommRing R] (vs : List R) (j : ℕ) (h : vs.length ≤ j) :
    (toPoly vs).coeff j = 0 := by
  rw [toPoly_coeff]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

open Polynomial in
theorem toPoly_reverse {R : Type*} [CommRing R] (vs : List R) :
    toPoly vs.reverse = reflect (vs.length - 1) (toPoly vs) := by
  ext i
  rw [coeff_reflect, toPoly_coeff, toPoly_coeff]
  by_cases hi : i < vs.length
  · rw [revAt_le (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_reverse hi]
  · rcases Nat.eq_zero_or_pos vs.length with h0 | hpos
    · simp [List.length_eq_zero_iff.mp h0]
    · rw [revAt_eq_self_of_lt (by omega)]
      have h1 : vs.reverse.length ≤ i := by simp; omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h1,
        List.getElem?_eq_none (by omega : vs.length ≤ i)]

open Polynomial in
theorem reflect_reflect_eq {R : Type*} [CommRing R] (N : ℕ) (f : R[X]) :
    reflect N (reflect N f) = f := by
  ext i; rw [coeff_reflect, coeff_reflect, revAt_invol]

open Polynomial in
theorem eq_of_dvd_coeff {R : Type*} [CommRing R] (k : ℕ) (A B : R[X])
    (hA : ∀ j, k ≤ j → A.coeff j = 0) (hB : ∀ j, k ≤ j → B.coeff j = 0) (h : X ^ k ∣ A - B) :
    A = B := by
  ext j
  by_cases hj : j < k
  · have := (X_pow_dvd_iff.mp h) j hj
    rw [coeff_sub, sub_eq_zero] at this; exact this
  · rw [hA j (by omega), hB j (by omega)]

open Polynomial in
/-- The reversed quotient is the reversed dividend times the inverse of the reversed divisor. -/
theorem quot_reflect {R : Type*} [CommRing R] [Nontrivial R] (P H g : R[X]) (n k : ℕ)
    (hk : 1 ≤ k) (hH : H.Monic) (hHd : H.natDegree = n) (hP : P.natDegree ≤ n + k - 1)
    (hg : X ^ k ∣ reflect n H * g - 1) :
    X ^ k ∣ reflect (n + k - 1) P * g - reflect (k - 1) (P /ₘ H) := by
  have hQ : (P /ₘ H).natDegree ≤ k - 1 := by
    rw [natDegree_divByMonic P hH, hHd]; omega
  have hsplit := modByMonic_add_div P H
  have hRm : X ^ k ∣ reflect (n + k - 1) (P %ₘ H) := by
    rw [X_pow_dvd_iff]
    intro d hd
    rw [coeff_reflect, revAt_le (by omega)]
    apply coeff_eq_zero_of_degree_lt
    refine lt_of_lt_of_le (degree_modByMonic_lt P hH) ?_
    rw [degree_eq_natDegree hH.ne_zero, hHd]
    exact_mod_cast (by omega : n ≤ n + k - 1 - d)
  have hmul : reflect (n + k - 1) (H * (P /ₘ H)) = reflect n H * reflect (k - 1) (P /ₘ H) := by
    rw [show n + k - 1 = n + (k - 1) by omega]
    exact reflect_mul _ _ (le_of_eq hHd) hQ
  have e2 : reflect (n + k - 1) P =
      reflect (n + k - 1) (P %ₘ H) + reflect n H * reflect (k - 1) (P /ₘ H) := by
    rw [← hmul, ← reflect_add, hsplit]
  have e : reflect (n + k - 1) P * g - reflect (k - 1) (P /ₘ H) =
      reflect (n + k - 1) (P %ₘ H) * g + reflect (k - 1) (P /ₘ H) * (reflect n H * g - 1) := by
    rw [e2]; ring
  rw [e]
  exact dvd_add (Dvd.dvd.mul_right hRm g) (Dvd.dvd.mul_left hg _)

/-! ## S3c the division program: stages C (quotient), D (q * h), E (remainder) -/

theorem holdsVec_padBlk {R : Type*} [CommRing R] (regs : List R) (z : ℕ) (hz : Holds regs z 0)
    (c : List ℕ) (cv : List R) (hc : HoldsVec regs c cv) (D : ℕ) :
    HoldsVec regs (padBlk z D c) (cv ++ List.replicate (D - cv.length) 0) := by
  have hcl := holdsVec_length _ _ _ hc
  unfold padBlk; rw [hcl]; exact List.rel_append hc (holdsVec_replicate regs z 0 hz _)

def modUE (n : ℕ) (ps : List ℕ) (z : ℕ) (qh : List ℕ) : Gen (List ℕ) :=
  Gen.bind (vecNeg (qh.take n)) fun nqh =>
  Gen.bind (vecAddPad (ps.take n) nqh) fun r => Gen.pure (padBlk z n r)

open Polynomial in
theorem triple_modUE {R : Type*} [CommRing R] (ι : R → R) (n : ℕ) (ps qh : List ℕ) (z : ℕ)
    (pv qhv : List R) (Rm : R[X]) (hE : X ^ n ∣ toPoly pv - toPoly qhv - Rm)
    (hRm : ∀ j, n ≤ j → Rm.coeff j = 0) (P : List R → Prop) (hP : Stable P)
    (hps : ∀ regs, P regs → HoldsVec regs ps pv) (hz : ∀ regs, P regs → Holds regs z 0)
    (hq : ∀ regs, P regs → HoldsVec regs qh qhv) :
    Triple ι (modUE n ps z qh) P (fun out regs => P regs ∧ ∃ rv : List R,
      HoldsVec regs out rv ∧ rv.length = n ∧ toPoly rv = Rm) := by
  unfold modUE
  refine triple_bind ι _ _ P _ _ (triple_vecNeg ι _ (qhv.take n) P hP
    (fun r h => List.forall₂_take _ (hq r h))) fun nqh => ?_
  have S1 := stable_and _ _ hP (stable_holdsVec nqh ((qhv.take n).map Neg.neg))
  refine triple_bind ι _ _ _ _ _ (triple_vecAddPad ι _ _ (pv.take n) _ _ S1
    (fun r h => List.forall₂_take _ (hps r h.1)) (fun r h => h.2)) fun rr => ?_
  have hL : (listAddPad (pv.take n) ((qhv.take n).map Neg.neg)).length ≤ n := by
    rw [listAddPad_length, List.length_map]
    exact max_le (List.length_take_le _ _) (List.length_take_le _ _)
  refine triple_pure ι _ _ _ fun regs h => ⟨h.1.1, _,
    holdsVec_padBlk regs z (hz regs h.1.1) _ _ h.2 n, ?_, ?_⟩
  · rw [List.length_append, List.length_replicate]; omega
  · rw [toPoly_append, toPoly_replicate_zero, mul_zero, add_zero]
    refine eq_of_dvd_coeff n _ _ (fun j hj => toPoly_coeff_ge _ _ (by omega)) hRm ?_
    have h1 := dvd_sub_take pv n
    have h2 := dvd_sub_take qhv n
    have h3 := dvd_add (dvd_sub hE h1) h2
    convert h3 using 1
    rw [toPoly_listAddPad, toPoly_map_neg]; ring

noncomputable def modUD (M n : ℕ) (ps hm : List ℕ) (z : ℕ) (t : List ℕ) : Gen (List ℕ) :=
  Gen.bind (polyMulG (M + n + 1) (padBlk z (M - n) (t.take (M - n))).reverse hm) fun qh =>
  modUE n ps z qh

open Polynomial in
theorem triple_modUD {R : Type*} [CommRing R] [Nontrivial R] (ι : R → R) (M n : ℕ)
    (ps hm t : List ℕ) (z : ℕ) (pv hmv tv : List R) (hpl : pv.length = M)
    (hml : hmv.length = n + 1) (hH : (toPoly hmv).Monic) (hHd : (toPoly hmv).natDegree = n)
    (ht : toPoly (tv.take (M - n)) = reflect (M - n - 1) (toPoly pv /ₘ toPoly hmv))
    (P : List R → Prop) (hP : Stable P) (hps : ∀ regs, P regs → HoldsVec regs ps pv)
    (hhm : ∀ regs, P regs → HoldsVec regs hm hmv) (hz : ∀ regs, P regs → Holds regs z 0)
    (htv : ∀ regs, P regs → HoldsVec regs t tv) :
    Triple ι (modUD M n ps hm z t) P (fun out regs => P regs ∧ ∃ rv : List R,
      HoldsVec regs out rv ∧ rv.length = n ∧ toPoly rv = toPoly pv %ₘ toPoly hmv) := by
  have hpad : ((tv.take (M - n)) ++
      List.replicate (M - n - (tv.take (M - n)).length) 0).length = M - n := by
    have := List.length_take_le (M - n) tv
    rw [List.length_append, List.length_replicate]; omega
  have hqvp : toPoly ((tv.take (M - n)) ++
      List.replicate (M - n - (tv.take (M - n)).length) 0).reverse =
      toPoly pv /ₘ toPoly hmv := by
    rw [toPoly_reverse, hpad, toPoly_append, toPoly_replicate_zero, mul_zero, add_zero, ht,
      reflect_reflect_eq]
  unfold modUD
  refine triple_bind ι _ _ P _ _ (triple_polyMulG ι (M + n + 1) _ _ _ hmv
    (by rw [List.length_reverse, hpad]; omega) (by omega) P hP
    (fun r h => List.forall₂_reverse_iff.mpr (holdsVec_padBlk r z (hz r h) _ _
      (List.forall₂_take _ (htv r h)) (M - n))) hhm) fun qh => ?_
  intro regs hr
  obtain ⟨hr0, qhv, hqh, hqhv⟩ := hr
  let P1 : List R → Prop := fun r => P r ∧ HoldsVec r qh qhv
  have hP1 : Stable P1 := stable_and _ _ hP (stable_holdsVec _ _)
  have hQH : toPoly qhv = (toPoly pv /ₘ toPoly hmv) * toPoly hmv := by
    rw [hqhv, toPoly_polyMul_out _ _ _ (by rw [List.length_reverse, hpad]; omega) (by omega),
      hqvp]
  have hE : X ^ n ∣ toPoly pv - toPoly qhv - toPoly pv %ₘ toPoly hmv := by
    have e0 := modByMonic_add_div (toPoly pv) (toPoly hmv)
    have e : toPoly pv - toPoly qhv - toPoly pv %ₘ toPoly hmv = 0 := by
      rw [hQH]; linear_combination (-1 : R[X]) * e0
    rw [e]; exact dvd_zero _
  have hRm : ∀ j, n ≤ j → (toPoly pv %ₘ toPoly hmv).coeff j = 0 := by
    intro j hj
    apply coeff_eq_zero_of_degree_lt
    refine lt_of_lt_of_le (degree_modByMonic_lt _ hH) ?_
    rw [degree_eq_natDegree hH.ne_zero, hHd]
    exact_mod_cast hj
  obtain ⟨new, e1, e2, e3⟩ := triple_modUE ι n ps qh z pv qhv _ hE hRm P1 hP1
    (fun r h => hps r h.1) (fun r h => hz r h.1) (fun r h => h.2) regs ⟨hr0, hqh⟩
  exact ⟨new, e1, e2, e3.1.1, e3.2⟩

noncomputable def modUC (M n : ℕ) (ps hm : List ℕ) (z : ℕ) (g : List ℕ) : Gen (List ℕ) :=
  Gen.bind (polyMulG M ps.reverse (g.take (M - n))) fun t => modUD M n ps hm z t

open Polynomial in
theorem triple_modUC {R : Type*} [CommRing R] [Nontrivial R] (ι : R → R) (M n : ℕ)
    (ps hm g : List ℕ) (z : ℕ) (pv hmv gv : List R) (hpl : pv.length = M)
    (hml : hmv.length = n + 1) (hH : (toPoly hmv).Monic) (hHd : (toPoly hmv).natDegree = n)
    (T : ℕ) (hT : M - n ≤ 2 ^ T) (hg : X ^ (2 ^ T) ∣ toPoly hmv.reverse * toPoly gv - 1)
    (P : List R → Prop) (hP : Stable P) (hps : ∀ regs, P regs → HoldsVec regs ps pv)
    (hhm : ∀ regs, P regs → HoldsVec regs hm hmv) (hz : ∀ regs, P regs → Holds regs z 0)
    (hgv : ∀ regs, P regs → HoldsVec regs g gv) :
    Triple ι (modUC M n ps hm z g) P (fun out regs => P regs ∧ ∃ rv : List R,
      HoldsVec regs out rv ∧ rv.length = n ∧ toPoly rv = toPoly pv %ₘ toPoly hmv) := by
  unfold modUC
  refine triple_bind ι _ _ P _ _ (triple_polyMulG ι M _ _ pv.reverse (gv.take (M - n))
    (by rw [List.length_reverse]; omega) (le_trans (List.length_take_le _ _) (by omega)) P hP
    (fun r h => List.forall₂_reverse_iff.mpr (hps r h))
    (fun r h => List.forall₂_take _ (hgv r h))) fun t => ?_
  intro regs hr
  obtain ⟨hr0, tv, htv, htvv⟩ := hr
  let P1 : List R → Prop := fun r => P r ∧ HoldsVec r t tv
  have hP1 : Stable P1 := stable_and _ _ hP (stable_holdsVec _ _)
  have hdeg : (toPoly pv).natDegree ≤ M - 1 := by
    have := toPoly_natDegree_le pv; omega
  have ht : toPoly (tv.take (M - n)) = reflect (M - n - 1) (toPoly pv /ₘ toPoly hmv) := by
    rcases Nat.eq_zero_or_pos (M - n) with hk | hk
    · rw [hk, List.take_zero]
      have hQ0 : toPoly pv /ₘ toPoly hmv = 0 := by
        rw [divByMonic_eq_zero_iff hH, degree_eq_natDegree hH.ne_zero, hHd]
        exact lt_of_lt_of_le (toPoly_degree_lt pv M (le_of_eq hpl)) (by exact_mod_cast (by omega))
      rw [hQ0, reflect_zero]; rfl
    · have hQd : (toPoly pv /ₘ toPoly hmv).natDegree ≤ M - n - 1 := by
        rw [natDegree_divByMonic _ hH, hHd]; omega
      apply eq_of_dvd_coeff (M - n)
      · intro j hj; exact toPoly_coeff_ge _ _ (le_trans (List.length_take_le _ _) hj)
      · intro j hj
        rw [coeff_reflect, revAt_eq_self_of_lt (by omega)]
        exact coeff_eq_zero_of_natDegree_lt (by omega)
      · have hrevP : toPoly pv.reverse = reflect (n + (M - n) - 1) (toPoly pv) := by
          rw [toPoly_reverse, hpl, show n + (M - n) - 1 = M - 1 by omega]
        have hrevH : toPoly hmv.reverse = reflect n (toPoly hmv) := by
          rw [toPoly_reverse, hml, Nat.add_sub_cancel]
        have hgk : X ^ (M - n) ∣ reflect n (toPoly hmv) * toPoly (gv.take (M - n)) - 1 := by
          have h1 : X ^ (M - n) ∣ X ^ (2 ^ T) := pow_dvd_pow (X : R[X]) hT
          rw [hrevH] at hg
          have e : reflect n (toPoly hmv) * toPoly (gv.take (M - n)) - 1 =
              (reflect n (toPoly hmv) * toPoly gv - 1) -
                reflect n (toPoly hmv) * (toPoly gv - toPoly (gv.take (M - n))) := by ring
          rw [e]
          exact dvd_sub (dvd_trans h1 hg) (Dvd.dvd.mul_left (dvd_sub_take gv _) _)
        have hq := quot_reflect (toPoly pv) (toPoly hmv) (toPoly (gv.take (M - n))) n (M - n) hk
          hH hHd (by omega) hgk
        rw [← hrevP] at hq
        have hT2 : toPoly tv = toPoly pv.reverse * toPoly (gv.take (M - n)) := by
          rw [htvv]; exact toPoly_polyMul_out _ _ _ (by rw [List.length_reverse]; omega)
            (le_trans (List.length_take_le _ _) (by omega))
        have h3 := dvd_sub_take tv (M - n)
        rw [hT2] at h3
        have e : toPoly (tv.take (M - n)) - reflect (M - n - 1) (toPoly pv /ₘ toPoly hmv) =
            (toPoly pv.reverse * toPoly (gv.take (M - n)) -
              reflect (M - n - 1) (toPoly pv /ₘ toPoly hmv)) -
            (toPoly pv.reverse * toPoly (gv.take (M - n)) - toPoly (tv.take (M - n))) := by ring
        rw [e]; exact dvd_sub hq h3
  obtain ⟨new, e1, e2, e3⟩ := triple_modUD ι M n ps hm t z pv hmv tv hpl hml hH hHd ht P1 hP1
    (fun r h => hps r h.1) (fun r h => hhm r h.1) (fun r h => hz r h.1) (fun r h => h.2) regs
    ⟨hr0, htv⟩
  exact ⟨new, e1, e2, e3.1.1, e3.2⟩


/-! ## S3d the full division program: normalise `h`, Newton inverse, divide -/

theorem gen_bind_fst {α β : Type} (g : Gen α) (f : α → Gen β) (m : ℕ) :
    (Gen.bind g f m).1 = (f (g m).1 (g m).2.2).1 := rfl

theorem polyMulG_length (n : ℕ) (as bs : List ℕ) (m : ℕ) :
    ((polyMulG n as bs) m).1.length ≤ 2 * n := by
  simp only [polyMulG, combGen, gen_bind_fst, Gen.pure]
  exact List.length_take_le _ _

theorem newtonStep_length (l : ℕ) (fs g : List ℕ) (m : ℕ) :
    ((newtonStep l fs g) m).1.length ≤ 2 * l := by
  simp only [newtonStep, gen_bind_fst, Gen.pure]
  exact List.length_take_le _ _

theorem newtonGen_length (fs : List ℕ) : ∀ t m, ((newtonGen fs t) m).1.length ≤ 2 ^ t
  | 0, m => by simp [newtonGen, gen_bind_fst, Gen.pure]
  | t + 1, m => by
    rw [newtonGen, gen_bind_fst]
    have := newtonStep_length (2 ^ t) fs ((newtonGen fs t) m).1 ((newtonGen fs t) m).2.2
    rw [pow_succ]; omega

theorem ops_bind_le {α β : Type} (g : Gen α) (f : α → Gen β) (Q : α → Prop) (a b n : ℕ)
    (hg : g.ops n ≤ a) (hQ : Q (g n).1) (hf : ∀ x n', Q x → (f x).ops n' ≤ b) :
    (Gen.bind g f).ops n ≤ a + b := by
  rw [ops_bind]; exact add_le_add hg (hf _ _ hQ)

/-- The cost bound of `polyMulG`. -/
def Bd (x : ℕ) : ℕ := 10 ^ 9 * (x + 1) * (Nat.log 2 (x + 1) + 1) ^ 10

theorem Bd_mono {x y : ℕ} (h : x ≤ y) : Bd x ≤ Bd y := by
  unfold Bd
  have := Nat.log_mono_right (b := 2) (show x + 1 ≤ y + 1 by omega)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (Nat.pow_le_pow_left (by omega) _)

theorem ops_polyMulG_Bd (n : ℕ) (as bs : List ℕ) (ha : as.length ≤ n) (hb : bs.length ≤ n)
    (m : ℕ) : (polyMulG n as bs).ops m ≤ Bd n := ops_polyMulG n as bs ha hb m

theorem ops_newtonStep (l : ℕ) (fs g : List ℕ) (hg : g.length ≤ 2 * l) (m : ℕ) :
    (newtonStep l fs g).ops m ≤ 2 * Bd (2 * l) + 10 * l := by
  unfold newtonStep
  refine le_trans (ops_bind_le _ _ (fun _ => True) (Bd (2 * l)) (Bd (2 * l) + 10 * l) m
    (ops_polyMulG_Bd _ _ _ (List.length_take_le _ _) hg m) trivial fun e n1 _ => ?_) (by omega)
  refine le_trans (ops_bind_le _ _ (fun ge => ge.length ≤ 4 * l) (Bd (2 * l)) (10 * l) n1
    (ops_polyMulG_Bd _ _ _ hg (List.length_take_le _ _) n1)
    (by have := polyMulG_length (2 * l) g (e.take (2 * l)) n1; omega) fun ge n2 hge => ?_)
    (le_refl _)
  refine le_trans (ops_bind_le _ _ (fun _ => True) (2 * l) (8 * l) n2
    (by rw [ops_vecAddPad]; omega) trivial fun g2 n3 _ => ?_) (by omega)
  refine le_trans (ops_bind_le _ _ (fun nge => nge.length ≤ 4 * l) (4 * l) (4 * l) n3
    (by rw [ops_vecNeg]; omega) (by rw [vecNeg_length]; exact hge) fun nge n4 hn => ?_)
    (by omega)
  refine le_trans (ops_bind_le _ _ (fun _ => True) (4 * l) 0 n4
    (by rw [ops_vecAddPad]; omega) trivial fun _ _ _ => by rw [ops_pure]) (by omega)

theorem ops_newtonGen (fs : List ℕ) :
    ∀ t m, (newtonGen fs t).ops m ≤ 1 + t * (2 * Bd (2 ^ t) + 10 * 2 ^ t)
  | 0, m => by
    rw [newtonGen, ops_bind, ops_emit, ops_pure]; simp [Instr.isRingOp]
  | t + 1, m => by
    rw [newtonGen]
    refine le_trans (ops_bind_le _ _ (fun g => g.length ≤ 2 ^ t) _
      (2 * Bd (2 * 2 ^ t) + 10 * 2 ^ t) m (ops_newtonGen fs t m) (newtonGen_length fs t m)
      fun g n' hg => ops_newtonStep _ _ _ (by omega) n') ?_
    have hB : Bd (2 ^ t) ≤ Bd (2 * 2 ^ t) := Bd_mono (by omega)
    rw [pow_succ, mul_comm (2 ^ t) 2]
    have h1 : t * (2 * Bd (2 ^ t) + 10 * 2 ^ t) ≤ t * (2 * Bd (2 * 2 ^ t) + 10 * (2 * 2 ^ t)) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : (t + 1) * (2 * Bd (2 * 2 ^ t) + 10 * (2 * 2 ^ t)) =
        t * (2 * Bd (2 * 2 ^ t) + 10 * (2 * 2 ^ t)) + (2 * Bd (2 * 2 ^ t) + 10 * (2 * 2 ^ t)) := by
      ring
    omega

theorem ops_modUE (n : ℕ) (ps : List ℕ) (z : ℕ) (qh : List ℕ) (m : ℕ) :
    (modUE n ps z qh).ops m ≤ 2 * n := by
  unfold modUE
  refine le_trans (ops_bind_le _ _ (fun nqh => nqh.length ≤ n) n n m
    (by rw [ops_vecNeg]; exact List.length_take_le _ _)
    (by rw [vecNeg_length]; exact List.length_take_le _ _) fun nqh n1 h1 => ?_) (by omega)
  refine le_trans (ops_bind_le _ _ (fun _ => True) n 0 n1
    (by rw [ops_vecAddPad]; omega) trivial fun _ _ _ => by rw [ops_pure]) (by omega)

theorem modUE_length (n : ℕ) (ps : List ℕ) (z : ℕ) (qh : List ℕ) (m : ℕ) :
    ((modUE n ps z qh) m).1.length = n := by
  simp only [modUE, gen_bind_fst, Gen.pure]
  apply padBlk_length
  rw [vecAddPad_length, vecNeg_length]
  have := List.length_take_le n ps
  have := List.length_take_le n qh
  omega

theorem ops_modUD (M n : ℕ) (ps hm : List ℕ) (z : ℕ) (t : List ℕ) (hhm : hm.length ≤ n + 1)
    (m : ℕ) : (modUD M n ps hm z t).ops m ≤ Bd (M + n + 1) + 2 * n := by
  unfold modUD
  refine ops_bind_le _ _ (fun _ => True) _ _ m (ops_polyMulG_Bd _ _ _ ?_ (by omega) m) trivial
    fun qh n1 _ => ops_modUE _ _ _ _ _
  rw [List.length_reverse, padBlk_length _ _ _ (List.length_take_le _ _)]; omega

theorem ops_modUC (M n : ℕ) (ps hm : List ℕ) (z : ℕ) (g : List ℕ) (hps : ps.length = M)
    (hhm : hm.length ≤ n + 1) (m : ℕ) :
    (modUC M n ps hm z g).ops m ≤ Bd M + (Bd (M + n + 1) + 2 * n) := by
  unfold modUC
  refine ops_bind_le _ _ (fun _ => True) _ _ m (ops_polyMulG_Bd _ _ _ (by simp [hps])
    (le_trans (List.length_take_le _ _) (by omega)) m) trivial
    fun t n1 _ => ops_modUD _ _ _ _ _ _ hhm _

theorem modUC_length (M n : ℕ) (ps hm : List ℕ) (z : ℕ) (g : List ℕ) (m : ℕ) :
    ((modUC M n ps hm z g) m).1.length = n := by
  simp only [modUC, modUD, gen_bind_fst]
  exact modUE_length _ _ _ _ _

/-- Stage B: Newton inverse of the reversed monic divisor, then divide. -/
noncomputable def modUB (M n : ℕ) (ps hm : List ℕ) (z : ℕ) : Gen (List ℕ) :=
  Gen.bind (newtonGen hm.reverse (Nat.log 2 (M - n) + 1)) fun g => modUC M n ps hm z g

theorem pow_log_succ_ge (k : ℕ) : k ≤ 2 ^ (Nat.log 2 k + 1) :=
  (Nat.lt_pow_succ_log_self (by norm_num) k).le

open Polynomial in
theorem triple_modUB {R : Type*} [CommRing R] [Nontrivial R] (ι : R → R) (M n : ℕ)
    (ps hm : List ℕ) (z : ℕ) (pv hmv : List R) (hpl : pv.length = M)
    (hml : hmv.length = n + 1) (hcoef : (toPoly hmv).coeff n = 1)
    (P : List R → Prop) (hP : Stable P) (hps : ∀ regs, P regs → HoldsVec regs ps pv)
    (hhm : ∀ regs, P regs → HoldsVec regs hm hmv) (hz : ∀ regs, P regs → Holds regs z 0) :
    Triple ι (modUB M n ps hm z) P (fun out regs => P regs ∧ ∃ rv : List R,
      HoldsVec regs out rv ∧ rv.length = n ∧ toPoly rv = toPoly pv %ₘ toPoly hmv) := by
  have hdl : (toPoly hmv).natDegree ≤ n := by have := toPoly_natDegree_le hmv; omega
  have hH : (toPoly hmv).Monic := monic_of_natDegree_le_of_coeff_eq_one n hdl hcoef
  have hHd : (toPoly hmv).natDegree = n :=
    natDegree_eq_of_le_of_coeff_ne_zero hdl (by rw [hcoef]; exact one_ne_zero)
  have hf0 : (toPoly hmv.reverse).coeff 0 = 1 := by
    rw [toPoly_reverse, coeff_reflect, hml, revAt_le (by omega),
      show n + 1 - 1 - 0 = n by omega, hcoef]
  unfold modUB
  refine triple_bind ι _ _ P _ _ (triple_newtonGen ι hm.reverse hmv.reverse hf0 P hP
    (fun r h => List.forall₂_reverse_iff.mpr (hhm r h)) _) fun g => ?_
  intro regs hr
  obtain ⟨hr0, gv, hgv, -, hgd⟩ := hr
  let P1 : List R → Prop := fun r => P r ∧ HoldsVec r g gv
  have hP1 : Stable P1 := stable_and _ _ hP (stable_holdsVec _ _)
  obtain ⟨new, e1, e2, e3⟩ := triple_modUC ι M n ps hm g z pv hmv gv hpl hml hH hHd
    (Nat.log 2 (M - n) + 1) (pow_log_succ_ge _) hgd P1 hP1 (fun r h => hps r h.1)
    (fun r h => hhm r h.1) (fun r h => hz r h.1) (fun r h => h.2) regs ⟨hr0, hgv⟩
  exact ⟨new, e1, e2, e3.1.1, e3.2⟩

/-- The whole remainder program: `ui = ι h_n`, `hm = ui · h`, a zero register, stage B. -/
noncomputable def modUGen (M n : ℕ) (ps hs : List ℕ) : Gen (List ℕ) :=
  Gen.bind (Gen.emit (.inv (hs.getD n 0))) fun ui =>
  Gen.bind (vecSmul ui hs) fun hm =>
  Gen.bind (Gen.emit .zero) fun z =>
  modUB M n ps hm z

theorem modUGen_length (M n : ℕ) (ps hs : List ℕ) (m : ℕ) :
    ((modUGen M n ps hs) m).1.length = n := by
  simp only [modUGen, modUB, gen_bind_fst]
  exact modUC_length _ _ _ _ _ _ _

open Polynomial in
theorem triple_modUGen {R : Type*} [CommRing R] [Nontrivial R] (ι : R → R) (M n : ℕ)
    (ps hs : List ℕ) (pv hv : List R) (hpl : pv.length = M) (hhl : hv.length = n + 1)
    (u : Rˣ) (hu : (u : R) = hv.getD n 0) (hι : ι (u : R) = ((u⁻¹ : Rˣ) : R))
    (P : List R → Prop) (hP : Stable P) (hps : ∀ regs, P regs → HoldsVec regs ps pv)
    (hhs : ∀ regs, P regs → HoldsVec regs hs hv) :
    Triple ι (modUGen M n ps hs) P (fun out regs => P regs ∧ ∃ rv : List R,
      HoldsVec regs out rv ∧ rv.length = n ∧
        toPoly rv = toPoly pv %ₘ (toPoly hv * C ((u⁻¹ : Rˣ) : R))) := by
  have hget : ∀ regs, P regs → Holds regs (hs.getD n 0) (u : R) := fun regs h => by
    rw [hu]
    exact holdsVec_getD regs hs hv (hhs regs h) n
      (by rw [holdsVec_length _ _ _ (hhs regs h), hhl]; omega)
  have hn : n < hv.length := by omega
  have hu' : (u : R) = hv[n] := by
    rw [hu, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some]
  have hml : (hv.map (ι (u : R) * ·)).length = n + 1 := by rw [List.length_map, hhl]
  have hmp : toPoly (hv.map (ι (u : R) * ·)) = toPoly hv * C ((u⁻¹ : Rˣ) : R) := by
    rw [toPoly_map_mul, hι, mul_comm]
  have hcoef : (toPoly (hv.map (ι (u : R) * ·))).coeff n = 1 := by
    rw [toPoly_coeff, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hn, Option.map_some, Option.getD_some, ← hu', hι]
    exact Units.inv_mul u
  unfold modUGen
  refine triple_bind ι _ _ P _ _ (triple_emit_inv ι _ _ P hP hget) fun ui => ?_
  have S1 := stable_and _ _ hP (stable_holds ui (ι (u : R)))
  refine triple_bind ι _ _ _ _ _ (triple_vecSmul ι ui (ι (u : R)) hs hv _ S1 (fun _ h => h.2)
    (fun _ h => hhs _ h.1)) fun hm => ?_
  have S2 := stable_and _ _ S1 (stable_holdsVec hm (hv.map (ι (u : R) * ·)))
  refine triple_bind ι _ _ _ _ _ (triple_emit_zero ι _ S2) fun z => ?_
  have S3 := stable_and _ _ S2 (stable_holds z (0 : R))
  intro regs hr
  obtain ⟨new, e1, e2, e3⟩ := triple_modUB ι M n ps hm z pv _ hpl hml hcoef _ S3
    (fun r h => hps r h.1.1.1) (fun r h => h.1.2) (fun r h => h.2) regs hr
  refine ⟨new, e1, e2, e3.1.1.1.1, ?_⟩
  obtain ⟨rv, h1, h2, h3⟩ := e3.2
  exact ⟨rv, h1, h2, by rw [h3, hmp]⟩

theorem ops_modUGen (M n : ℕ) (ps hs : List ℕ) (hps : ps.length = M) (hhs : hs.length = n + 1)
    (m : ℕ) : (modUGen M n ps hs).ops m ≤
      1 + ((n + 1) + (1 + ((1 + (Nat.log 2 (M - n) + 1) *
        (2 * Bd (2 ^ (Nat.log 2 (M - n) + 1)) + 10 * 2 ^ (Nat.log 2 (M - n) + 1))) +
        (Bd M + (Bd (M + n + 1) + 2 * n))))) := by
  unfold modUGen
  refine ops_bind_le _ _ (fun _ => True) _ _ m (by rw [ops_emit]; simp [Instr.isRingOp]) trivial
    fun ui n1 _ => ?_
  refine ops_bind_le _ _ (fun hm => hm.length = n + 1) _ _ n1 (by rw [ops_vecSmul, hhs])
    (by rw [vecSmul_length, hhs]) fun hm n2 hhm => ?_
  refine ops_bind_le _ _ (fun _ => True) _ _ n2 (by rw [ops_emit]; simp [Instr.isRingOp]) trivial
    fun z n3 _ => ?_
  unfold modUB
  exact ops_bind_le _ _ (fun _ => True) _ _ n3 (ops_newtonGen _ _ n3) trivial
    fun g n4 _ => ops_modUC _ _ _ _ _ _ hps hhm.le _

/-- Pure arithmetic: the division cost is quasi-linear. -/
theorem modU_cost_arith (M n : ℕ) :
    1 + ((n + 1) + (1 + ((1 + (Nat.log 2 (M - n) + 1) *
        (2 * Bd (2 ^ (Nat.log 2 (M - n) + 1)) + 10 * 2 ^ (Nat.log 2 (M - n) + 1))) +
        (Bd M + (Bd (M + n + 1) + 2 * n))))) ≤
      10 ^ 16 * (M + n + 1) * (Nat.log 2 (M + n + 1) + 1) ^ 11 := by
  set L := M + n + 1
  set A := Nat.log 2 L + 1
  set T := Nat.log 2 (M - n) + 1 with hT
  have hL1 : 1 ≤ L := by omega
  have hA1 : 1 ≤ A := by omega
  have hTA : T ≤ A := by
    have := Nat.log_mono_right (b := 2) (show M - n ≤ L by omega); omega
  have h2T : 2 ^ T ≤ 2 * L := by
    rcases Nat.eq_zero_or_pos (M - n) with h0 | hpos
    · rw [hT, h0]; simp; omega
    · have := Nat.pow_log_le_self 2 (show M - n ≠ 0 by omega)
      rw [hT, pow_succ]; omega
  have hlog4 : Nat.log 2 (2 * L + 1) ≤ Nat.log 2 L + 2 := by
    have e : Nat.log 2 (L * 2 * 2) = Nat.log 2 L + 2 := by
      rw [Nat.log_mul_base (by norm_num) (by omega), Nat.log_mul_base (by norm_num) (by omega)]
    rw [← e]; exact Nat.log_mono_right (by omega)
  set W := L * A ^ 10 with hW
  have hAp : 1 ≤ A ^ 10 := Nat.one_le_pow _ _ hA1
  have hLW : L ≤ W := by rw [hW]; exact Nat.le_mul_of_pos_right _ hAp
  have hB2L : Bd (2 * L) ≤ 10 ^ 9 * 3 * 3 ^ 10 * W := by
    unfold Bd
    have h3 : Nat.log 2 (2 * L + 1) + 1 ≤ 3 * A := by omega
    have h4 : (Nat.log 2 (2 * L + 1) + 1) ^ 10 ≤ (3 * A) ^ 10 := Nat.pow_le_pow_left h3 _
    rw [mul_pow] at h4
    calc 10 ^ 9 * (2 * L + 1) * (Nat.log 2 (2 * L + 1) + 1) ^ 10
        ≤ 10 ^ 9 * (3 * L) * (3 ^ 10 * A ^ 10) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) h4
      _ = 10 ^ 9 * 3 * 3 ^ 10 * W := by rw [hW]; ring
  have hBT : Bd (2 ^ T) ≤ 10 ^ 9 * 3 * 3 ^ 10 * W := le_trans (Bd_mono h2T) hB2L
  have hBM : Bd M ≤ 10 ^ 9 * 3 * 3 ^ 10 * W := le_trans (Bd_mono (by omega)) hB2L
  have hBL : Bd L ≤ 10 ^ 9 * 3 * 3 ^ 10 * W := le_trans (Bd_mono (by omega)) hB2L
  have hmid : T * (2 * Bd (2 ^ T) + 10 * 2 ^ T) ≤
      A * (2 * (10 ^ 9 * 3 * 3 ^ 10 * W) + 20 * W) :=
    Nat.mul_le_mul hTA (by omega)
  have hAW : W ≤ A * W := Nat.le_mul_of_pos_left _ hA1
  have hR : 10 ^ 16 * L * A ^ 11 = 10 ^ 16 * (A * W) := by rw [hW]; ring
  have hE : A * (2 * (10 ^ 9 * 3 * 3 ^ 10 * W) + 20 * W) =
      (2 * (10 ^ 9 * 3 * 3 ^ 10) + 20) * (A * W) := by ring
  rw [hR]
  rw [hE] at hmid
  omega

/-- Lists over a trivial ring are determined by their length. -/
theorem list_eq_of_subsingleton {R : Type*} [Subsingleton R] (xs ys : List R)
    (h : xs.length = ys.length) : xs = ys :=
  List.ext_get h fun _ _ _ => Subsingleton.elim _ _

theorem list_eq_ofFn_coeff {R : Type*} [CommRing R] (n : ℕ) (rv : List R) (hl : rv.length = n) :
    rv = List.ofFn (fun j : Fin n => (toPoly rv).coeff (j : ℕ)) := by
  apply List.ext_get (by simp [hl])
  intro i h1 h2
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_ofFn, toPoly_coeff,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- The remainder program on the standard input layout. -/
noncomputable def modUProg (M n : ℕ) : Gen (List ℕ) :=
  modUGen M n (List.range' 0 M) (List.range' M (n + 1))

theorem noOr_newtonStep (l : ℕ) (fs g : List ℕ) : NoOr (newtonStep l fs g) := by
  unfold newtonStep
  exact noOr_bind _ _ (noOr_polyMulG _ _ _) fun _ => noOr_bind _ _ (noOr_polyMulG _ _ _) fun _ =>
    noOr_bind _ _ (noOr_vecAddPad _ _) fun _ => noOr_bind _ _ (noOr_vecNeg _) fun _ =>
    noOr_bind _ _ (noOr_vecAddPad _ _) fun _ => noOr_pure _

theorem noOr_newtonGen (fs : List ℕ) : ∀ t, NoOr (newtonGen fs t)
  | 0 => by rw [newtonGen]; exact noOr_bind _ _ (noOr_emit _ rfl) fun _ => noOr_pure _
  | t + 1 => by
    rw [newtonGen]; exact noOr_bind _ _ (noOr_newtonGen fs t) fun _ => noOr_newtonStep _ _ _

theorem noOr_modUGen (M n : ℕ) (ps hs : List ℕ) : NoOr (modUGen M n ps hs) := by
  unfold modUGen modUB modUC modUD modUE
  exact noOr_bind _ _ (noOr_emit _ rfl) fun _ => noOr_bind _ _ (noOr_vecSmul _ _) fun _ =>
    noOr_bind _ _ (noOr_emit _ rfl) fun _ => noOr_bind _ _ (noOr_newtonGen _ _) fun _ =>
    noOr_bind _ _ (noOr_polyMulG _ _ _) fun _ => noOr_bind _ _ (noOr_polyMulG _ _ _) fun _ =>
    noOr_bind _ _ (noOr_vecNeg _) fun _ => noOr_bind _ _ (noOr_vecAddPad _ _) fun _ => noOr_pure _

/-- **ChildB (division with remainder, MCA Thm 9.6)**. -/
theorem modU_main : ∃ (C k : ℕ) (D : ℕ → ℕ → SLP), ∀ M n : ℕ,
    ringOps (D M n) ≤ C * (M + n + 1) * (Nat.log 2 (M + n + 1) + 1) ^ k ∧
    oracleCalls (D M n) = [] ∧
    ∀ (R : Type) [CommRing R] (ι : R → R), (∀ x : Rˣ, ι (x : R) = ((x⁻¹ : Rˣ) : R)) →
      ∀ (p : Fin M → R) (h : Fin (n + 1) → R) (u : Rˣ), (u : R) = h (Fin.last n) →
        run ι (D M n) (List.ofFn p ++ List.ofFn h) =
          List.ofFn (fun j : Fin n => (modU (densePoly p) (densePoly h) u).coeff (j : ℕ)) := by
  refine ⟨10 ^ 16, 11, fun M n => ⟨((modUProg M n) (M + (n + 1))).2.1,
    ((modUProg M n) (M + (n + 1))).1⟩, fun M n => ⟨?_, ?_, ?_⟩⟩
  · rw [ringOps_gen]
    exact le_trans (ops_modUGen M n _ _ (by simp) (by simp) _) (modU_cost_arith M n)
  · exact oracleCalls_gen_nil _ _ (noOr_modUGen M n _ _ _)
  · intro R _ ι hι p h u hu
    have hlen : (List.ofFn p ++ List.ofFn h).length = M + (n + 1) := by simp
    rcases subsingleton_or_nontrivial R with hR | hR
    · apply list_eq_of_subsingleton
      simp only [run, List.length_map, List.length_ofFn]
      exact modUGen_length _ _ _ _ _
    · let P : List R → Prop := fun regs => HoldsVec regs (List.range' 0 M) (List.ofFn p) ∧
        HoldsVec regs (List.range' M (n + 1)) (List.ofFn h)
      have hP : Stable P := stable_and _ _ (stable_holdsVec _ _) (stable_holdsVec _ _)
      have hu2 : (u : R) = (List.ofFn h).getD n 0 := by
        rw [hu, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp [Fin.last]
      have T := triple_modUGen ι M n _ _ (List.ofFn p) (List.ofFn h) (by simp) (by simp) u hu2
        (hι u) P hP (fun _ h => h.1) (fun _ h => h.2)
      have h0 : P (List.ofFn p ++ List.ofFn h) := by
        refine ⟨?_, ?_⟩
        · have := holdsVec_range' (List.ofFn p) []
          simp only [List.nil_append, List.length_nil, List.length_ofFn] at this
          exact holdsVec_append _ _ _ _ this
        · have := holdsVec_range' (List.ofFn h) (List.ofFn p)
          simpa only [List.length_ofFn] using this
      have := run_of_triple ι (modUProg M n) P _
        (fun vs => vs = List.ofFn (fun j : Fin n => (modU (densePoly p) (densePoly h) u).coeff
          (j : ℕ))) T (fun out regs hq => by
          obtain ⟨-, rv, h1, h2, h3⟩ := hq
          refine ⟨rv, h1, ?_⟩
          rw [list_eq_ofFn_coeff n rv h2, h3, modU, densePoly_eq_toPoly M p,
            densePoly_eq_toPoly (n + 1) h]) _ h0
      rw [hlen] at this
      exact this


/-! ## S4 ChildC: fast multipoint evaluation (subproduct tree + remainder tree, MCA 10.8) -/

/-- Bind whose first stage produces a vector with a pure property `F`. -/
theorem triple_bind_vec {R : Type*} [CommRing R] (ι : R → R) {β : Type} (g : Gen (List ℕ))
    (f : List ℕ → Gen β) (P : List R → Prop) (F : List R → Prop) (S : β → List R → Prop)
    (hg : Triple ι g P (fun a regs => P regs ∧ ∃ v, HoldsVec regs a v ∧ F v))
    (hf : ∀ v a, F v → a.length = v.length →
      Triple ι (f a) (fun regs => P regs ∧ HoldsVec regs a v) S) :
    Triple ι (Gen.bind g f) P S := by
  intro regs hP
  obtain ⟨n1, c1, l1, hq0, v, hv, hF⟩ := hg regs hP
  obtain ⟨n2, c2, l2, q2⟩ := hf v (g regs.length).1 hF (holdsVec_length _ _ _ hv) (regs ++ n1)
    ⟨hq0, hv⟩
  rw [l1] at c2 l2 q2
  refine ⟨n1 ++ n2, ?_, ?_, ?_⟩
  · simp only [Gen.bind]
    rw [List.foldl_append, c1, c2, List.append_assoc]
  · simpa [Gen.bind, List.append_assoc] using l2
  · simpa [Gen.bind, List.append_assoc] using q2

open Polynomial in
/-- `∏ (X - x)` over a list of points. -/
noncomputable def prodX {R : Type*} [CommRing R] (xv : List R) : R[X] :=
  (xv.map (fun x => X - C x)).prod

open Polynomial in
theorem prodX_cons {R : Type*} [CommRing R] (x : R) (xv : List R) :
    prodX (x :: xv) = (X - C x) * prodX xv := by simp [prodX]

open Polynomial in
theorem prodX_append {R : Type*} [CommRing R] (xv yv : List R) :
    prodX (xv ++ yv) = prodX xv * prodX yv := by simp [prodX, List.prod_append]

open Polynomial in
theorem prodX_natDegree_le {R : Type*} [CommRing R] :
    ∀ xv : List R, (prodX xv).natDegree ≤ xv.length
  | [] => by simp [prodX]
  | x :: xv => by
    rw [prodX_cons, List.length_cons]
    refine le_trans natDegree_mul_le ?_
    have h1 := natDegree_X_sub_C_le x
    have h2 := prodX_natDegree_le xv
    omega

open Polynomial in
theorem prodX_coeff_length {R : Type*} [CommRing R] :
    ∀ xv : List R, (prodX xv).coeff xv.length = 1
  | [] => by simp [prodX]
  | x :: xv => by
    rw [prodX_cons, List.length_cons, mul_comm, coeff_mul_X_sub_C, prodX_coeff_length xv,
      coeff_eq_zero_of_natDegree_lt (by have := prodX_natDegree_le xv; omega), zero_mul, sub_zero]

open Polynomial in
theorem prodX_eval_mem {R : Type*} [CommRing R] (xv : List R) (x : R) (hx : x ∈ xv) :
    (prodX xv).eval x = 0 := by
  have h : X - C x ∣ prodX xv := List.dvd_prod (List.mem_map.mpr ⟨x, hx, rfl⟩)
  exact dvd_iff_isRoot.mp h

open Polynomial in
theorem eval_modByMonic_of_root {R : Type*} [CommRing R] (p q : R[X]) (x : R)
    (hq : q.eval x = 0) : (p %ₘ q).eval x = p.eval x := by
  have h := modByMonic_add_div p q
  conv_rhs => rw [← h]
  simp [eval_add, eval_mul, hq]

open Polynomial in
theorem toPoly_take_of_deg {R : Type*} [CommRing R] (zs : List R) (m : ℕ)
    (hd : (toPoly zs).natDegree < m) : toPoly (zs.take m) = toPoly zs := by
  apply eq_of_dvd_coeff m
  · intro j hj; exact toPoly_coeff_ge _ _ (le_trans (List.length_take_le _ _) hj)
  · intro j hj; exact coeff_eq_zero_of_natDegree_lt (by omega)
  · have := dvd_sub_take zs m
    rw [← neg_sub]; exact dvd_neg.mpr this

/-- Subproduct: the coefficients of `∏ (X - x_i)` (length `k + 1`). -/
noncomputable def prodGen : List ℕ → Gen (List ℕ)
  | [] => Gen.bind (Gen.emit .one) fun o => Gen.pure [o]
  | [p] => Gen.bind (Gen.emit (.neg p)) fun np => Gen.bind (Gen.emit .one) fun o => Gen.pure [np, o]
  | p :: q :: rest =>
    Gen.bind (prodGen ((p :: q :: rest).take ((rest.length + 2) / 2))) fun a =>
    Gen.bind (prodGen ((p :: q :: rest).drop ((rest.length + 2) / 2))) fun b =>
    Gen.bind (polyMulG (rest.length + 3) a b) fun c =>
    Gen.pure (c.take (rest.length + 3))
termination_by pts => pts.length
decreasing_by
  all_goals (simp only [List.length_take, List.length_drop, List.length_cons] <;> omega)

open Polynomial in
theorem triple_prodGen {R : Type*} [CommRing R] (ι : R → R) (k : ℕ) :
    ∀ (pts : List ℕ) (xv : List R), pts.length = k → xv.length = k →
    ∀ (P : List R → Prop), Stable P → (∀ regs, P regs → HoldsVec regs pts xv) →
    Triple ι (prodGen pts) P (fun out regs => P regs ∧ ∃ cv : List R,
      HoldsVec regs out cv ∧ cv.length = k + 1 ∧ toPoly cv = prodX xv) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro pts xv hpl hxl P hP hpts
  rcases pts with _ | ⟨p, _ | ⟨q, rest⟩⟩
  · have hk : k = 0 := by simp at hpl; omega
    subst hk
    rcases xv with _ | ⟨x, xr⟩
    · rw [prodGen]
      refine triple_bind ι _ _ P _ _ (triple_emit_one ι P hP) fun o => ?_
      exact triple_pure ι _ _ _ fun regs h => ⟨h.1, [1], List.Forall₂.cons h.2 List.Forall₂.nil,
        rfl, by simp [toPoly, prodX]⟩
    · simp at hxl
  · have hk : k = 1 := by simp at hpl; omega
    subst hk
    rcases xv with _ | ⟨x, _ | ⟨y, xr⟩⟩
    · simp at hxl
    · have hp : ∀ regs, P regs → Holds regs p x := fun regs h => (List.forall₂_cons.1 (hpts regs h)).1
      rw [prodGen]
      refine triple_bind ι _ _ P _ _ (triple_emit_neg ι p x P hP hp) fun np => ?_
      have S1 := stable_and _ _ hP (stable_holds np (-x))
      refine triple_bind ι _ _ _ _ _ (triple_emit_one ι _ S1) fun o => ?_
      exact triple_pure ι _ _ _ fun regs h => ⟨h.1.1, [-x, 1],
        List.Forall₂.cons h.1.2 (List.Forall₂.cons h.2 List.Forall₂.nil), rfl, by
          simp only [toPoly, prodX, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
            C_neg, C_1]; ring⟩
    · simp at hxl
  · have hk : k = rest.length + 2 := by simp at hpl; omega
    subst hk
    rcases xv with _ | ⟨x, _ | ⟨y, xr⟩⟩
    · simp at hxl
    · simp at hxl
    have hxl2 : xr.length = rest.length := by simp at hxl; omega
    have hh1 : (rest.length + 2) / 2 < rest.length + 2 := by omega
    have hh2 : rest.length + 2 - (rest.length + 2) / 2 < rest.length + 2 := by omega
    rw [prodGen]
    refine triple_bind_vec ι _ _ P (fun cv => cv.length = (rest.length + 2) / 2 + 1 ∧
      toPoly cv = prodX ((x :: y :: xr).take ((rest.length + 2) / 2))) _
      (ih _ hh1 _ _ (by simp only [List.length_take, List.length_cons] <;> omega)
        (by simp only [List.length_take, List.length_cons] <;> omega) P hP
        (fun r hr => List.forall₂_take _ (hpts r hr))) fun av a ha _ => ?_
    have S1 := stable_and _ _ hP (stable_holdsVec a av)
    refine triple_bind_vec ι _ _ _ (fun cv => cv.length = rest.length + 2 - (rest.length + 2) / 2 + 1 ∧
      toPoly cv = prodX ((x :: y :: xr).drop ((rest.length + 2) / 2))) _
      (ih _ hh2 _ _ (by simp only [List.length_drop, List.length_cons] <;> omega)
        (by simp only [List.length_drop, List.length_cons] <;> omega) _ S1
        (fun r hr => List.forall₂_drop _ (hpts r hr.1))) fun bv b hb _ => ?_
    have S2 := stable_and _ _ S1 (stable_holdsVec b bv)
    refine triple_bind_vec ι _ _ _ (fun zs => zs = List.ofFn (fun j : Fin (2 * (rest.length + 3)) =>
      (toPoly av * toPoly bv).coeff (j : ℕ))) _
      (triple_polyMulG ι (rest.length + 3) a b av bv (by omega) (by omega) _ S2
        (fun r hr => hr.1.2) (fun r hr => hr.2)) fun zv c hc _ => ?_
    have hz : toPoly zv = toPoly av * toPoly bv := by
      rw [hc]; exact toPoly_polyMul_out _ _ _ (by omega) (by omega)
    have hdeg : (toPoly av * toPoly bv).natDegree < rest.length + 3 := by
      have h1 := toPoly_natDegree_le av
      have h2 := toPoly_natDegree_le bv
      have h3 := natDegree_mul_le (p := toPoly av) (q := toPoly bv)
      omega
    refine triple_pure ι _ _ _ fun regs hr => ⟨hr.1.1.1, zv.take (rest.length + 3),
      List.forall₂_take _ hr.2, ?_, ?_⟩
    · rw [hc, List.length_take, List.length_ofFn]; omega
    · rw [toPoly_take_of_deg zv _ (by rw [hz]; exact hdeg), hz, ha.2, hb.2, ← prodX_append,
        List.take_append_drop]

theorem prodGen_length_le : ∀ (pts : List ℕ) (m : ℕ), ((prodGen pts) m).1.length ≤ pts.length + 1
  | [], m => by rw [prodGen]; simp [gen_bind_fst, Gen.pure]
  | [p], m => by rw [prodGen]; simp [gen_bind_fst, Gen.pure]
  | p :: q :: rest, m => by
    rw [prodGen]; simp only [gen_bind_fst, Gen.pure]
    exact le_trans (List.length_take_le _ _) (by simp)

/-! ### Cost of tree recursions -/

/-- Quasi-linear cost shape `c k (log₂ (2k) + 1)^e`. -/
def gG (c e k : ℕ) : ℕ := c * k * (Nat.log 2 (2 * k) + 1) ^ e

theorem gG_sup (c e a b : ℕ) : gG c e a + gG c e b ≤ gG c e (a + b) := by
  unfold gG
  have la : (Nat.log 2 (2 * a) + 1) ^ e ≤ (Nat.log 2 (2 * (a + b)) + 1) ^ e :=
    Nat.pow_le_pow_left (by have := Nat.log_mono_right (b := 2) (show 2 * a ≤ 2 * (a + b) by omega); omega) _
  have lb : (Nat.log 2 (2 * b) + 1) ^ e ≤ (Nat.log 2 (2 * (a + b)) + 1) ^ e :=
    Nat.pow_le_pow_left (by have := Nat.log_mono_right (b := 2) (show 2 * b ≤ 2 * (a + b) by omega); omega) _
  calc c * a * (Nat.log 2 (2 * a) + 1) ^ e + c * b * (Nat.log 2 (2 * b) + 1) ^ e
      ≤ c * a * (Nat.log 2 (2 * (a + b)) + 1) ^ e + c * b * (Nat.log 2 (2 * (a + b)) + 1) ^ e :=
        Nat.add_le_add (Nat.mul_le_mul_left _ la) (Nat.mul_le_mul_left _ lb)
    _ = c * (a + b) * (Nat.log 2 (2 * (a + b)) + 1) ^ e := by ring

theorem gG_mono (c e : ℕ) {a b : ℕ} (h : a ≤ b) : gG c e a ≤ gG c e b := by
  have := gG_sup c e a (b - a)
  rw [show a + (b - a) = b by omega] at this
  omega

theorem tree_step (g : ℕ → ℕ) (hsup : ∀ a b, g a + g b ≤ g (a + b)) (k : ℕ) (hk : 2 ≤ k)
    (x y w : ℕ) (hx : x ≤ g (k / 2) * (Nat.clog 2 (k / 2) + 1) + 1)
    (hy : y ≤ g (k - k / 2) * (Nat.clog 2 (k - k / 2) + 1) + 1) (hw : w + 2 ≤ g k) :
    x + (y + w) ≤ g k * (Nat.clog 2 k + 1) + 1 := by
  have hc : Nat.clog 2 k = Nat.clog 2 ((k + 2 - 1) / 2) + 1 := Nat.clog_of_two_le (by norm_num) hk
  rw [show (k + 2 - 1) / 2 = k - k / 2 by omega] at hc
  have hm : Nat.clog 2 (k / 2) ≤ Nat.clog 2 (k - k / 2) := Nat.clog_mono_right 2 (by omega)
  have h1 : g (k / 2) * (Nat.clog 2 (k / 2) + 1) ≤ g (k / 2) * (Nat.clog 2 (k - k / 2) + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have hs := hsup (k / 2) (k - k / 2)
  rw [show k / 2 + (k - k / 2) = k by omega] at hs
  have h2 : g (k / 2) * (Nat.clog 2 (k - k / 2) + 1) + g (k - k / 2) * (Nat.clog 2 (k - k / 2) + 1)
      ≤ g k * (Nat.clog 2 (k - k / 2) + 1) := by
    rw [← add_mul]; exact Nat.mul_le_mul_right _ hs
  rw [hc]
  have h3 : g k * (Nat.clog 2 (k - k / 2) + 1 + 1) = g k * (Nat.clog 2 (k - k / 2) + 1) + g k := by
    ring
  omega

theorem Bd_le_gP (k : ℕ) (hk : 2 ≤ k) : Bd (k + 1) + 3 ≤ gG (10 ^ 10) 10 k := by
  unfold Bd gG
  have hl : Nat.log 2 (k + 1 + 1) ≤ Nat.log 2 (2 * k) := Nat.log_mono_right (by omega)
  have hp : (Nat.log 2 (k + 1 + 1) + 1) ^ 10 ≤ (Nat.log 2 (2 * k) + 1) ^ 10 :=
    Nat.pow_le_pow_left (by omega) _
  have hX : 1 ≤ (Nat.log 2 (2 * k) + 1) ^ 10 := Nat.one_le_pow _ _ (by omega)
  generalize (Nat.log 2 (2 * k) + 1) ^ 10 = X at hp hX ⊢
  have h1 : 10 ^ 9 * (k + 1 + 1) * (Nat.log 2 (k + 1 + 1) + 1) ^ 10 ≤ 10 ^ 9 * (k + 1 + 1) * X :=
    Nat.mul_le_mul_left _ hp
  have h3 : 10 ^ 9 * (k + 1 + 1) * X = 10 ^ 9 * (k * X) + 2 * 10 ^ 9 * X := by ring
  have h4 : 10 ^ 10 * k * X = 10 ^ 10 * (k * X) := by ring
  have h5 : X ≤ k * X := Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem ops_prodGen (k : ℕ) : ∀ (pts : List ℕ) (m : ℕ), pts.length = k →
    (prodGen pts).ops m ≤ gG (10 ^ 10) 10 k * (Nat.clog 2 k + 1) + 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro pts m hpl
  rcases pts with _ | ⟨p, _ | ⟨q, rest⟩⟩
  · rw [prodGen, ops_bind, ops_emit, ops_pure]; simp [Instr.isRingOp]
  · have hk : k = 1 := by simp at hpl; omega
    subst hk
    have h := Nat.one_le_pow 10 (Nat.log 2 2 + 1) (by omega)
    rw [prodGen, ops_bind, ops_emit, ops_bind, ops_emit, ops_pure]
    simp [Instr.isRingOp, gG]
    omega
  · have hk : k = rest.length + 2 := by simp at hpl; omega
    subst hk
    have hh1 : (rest.length + 2) / 2 < rest.length + 2 := by omega
    have hh2 : rest.length + 2 - (rest.length + 2) / 2 < rest.length + 2 := by omega
    rw [prodGen]
    have T := tree_step (gG (10 ^ 10) 10) (gG_sup _ _) (rest.length + 2) (by omega)
      ((prodGen ((p :: q :: rest).take ((rest.length + 2) / 2))).ops m)
    refine le_trans (ops_bind_le _ _ (fun a => a.length ≤ (rest.length + 2) / 2 + 1) _
      (gG (10 ^ 10) 10 (rest.length + 2 - (rest.length + 2) / 2) *
        (Nat.clog 2 (rest.length + 2 - (rest.length + 2) / 2) + 1) + 1 + Bd (rest.length + 3)) m
      (le_refl _)
      (le_trans (prodGen_length_le _ _) (by simp only [List.length_take, List.length_cons] <;> omega))
      fun a n1 ha => ?_) ?_
    · refine le_trans (ops_bind_le _ _ (fun b => b.length ≤ rest.length + 2 - (rest.length + 2) / 2 + 1)
        _ (Bd (rest.length + 3)) n1
        (ih _ hh2 _ n1 (by simp only [List.length_drop, List.length_cons] <;> omega))
        (le_trans (prodGen_length_le _ _) (by simp only [List.length_drop, List.length_cons] <;> omega))
        fun b n2 hb => ?_) (le_refl _)
      refine le_trans (ops_bind_le _ _ (fun _ => True) _ 0 n2
        (ops_polyMulG_Bd _ _ _ (by omega) (by omega) n2) trivial fun _ _ _ => by rw [ops_pure])
        (by omega)
    · have hL := ih _ hh1 ((p :: q :: rest).take ((rest.length + 2) / 2)) m
        (by simp only [List.length_take, List.length_cons] <;> omega)
      have hw := Bd_le_gP (rest.length + 2) (by omega)
      have := T (gG (10 ^ 10) 10 (rest.length + 2 - (rest.length + 2) / 2) *
        (Nat.clog 2 (rest.length + 2 - (rest.length + 2) / 2) + 1) + 1) (Bd (rest.length + 3))
        hL (le_refl _) (by rw [show rest.length + 3 = rest.length + 2 + 1 by omega]; omega)
      omega

/-! ### The remainder tree -/

/-- Multipoint evaluation of the polynomial held in `rs` (length at most the number of points)
at the points `pts`: reduce modulo each half's subproduct and recurse. -/
noncomputable def mpe (z : ℕ) : List ℕ → List ℕ → Gen (List ℕ)
  | [], _ => Gen.pure []
  | [_], rs => Gen.pure [rs.getD 0 z]
  | p :: q :: rest, rs =>
    Gen.bind (prodGen ((p :: q :: rest).take ((rest.length + 2) / 2))) fun mL =>
    Gen.bind (modUB rs.length ((rest.length + 2) / 2) rs mL z) fun rL =>
    Gen.bind (mpe z ((p :: q :: rest).take ((rest.length + 2) / 2)) rL) fun oL =>
    Gen.bind (prodGen ((p :: q :: rest).drop ((rest.length + 2) / 2))) fun mR =>
    Gen.bind (modUB rs.length (rest.length + 2 - (rest.length + 2) / 2) rs mR z) fun rR =>
    Gen.bind (mpe z ((p :: q :: rest).drop ((rest.length + 2) / 2)) rR) fun oR =>
    Gen.pure (oL ++ oR)
termination_by pts _ => pts.length
decreasing_by
  all_goals (simp only [List.length_take, List.length_drop, List.length_cons] <;> omega)

open Polynomial in
theorem triple_mpe {R : Type*} [CommRing R] [Nontrivial R] (ι : R → R) (z : ℕ) (F : R[X])
    (k : ℕ) : ∀ (pts rs : List ℕ) (xv rv : List R), pts.length = k → xv.length = k →
    rv.length = rs.length → rv.length ≤ k → (∀ x ∈ xv, (toPoly rv).eval x = F.eval x) →
    ∀ (P : List R → Prop), Stable P → (∀ regs, P regs → HoldsVec regs pts xv) →
    (∀ regs, P regs → HoldsVec regs rs rv) → (∀ regs, P regs → Holds regs z 0) →
    Triple ι (mpe z pts rs) P
      (fun out regs => P regs ∧ HoldsVec regs out (xv.map (fun x => F.eval x))) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro pts rs xv rv hpl hxl hrl hrk hev P hP hpts hrs hz
  rcases pts with _ | ⟨p, _ | ⟨q, rest⟩⟩
  · have hk : k = 0 := by simp at hpl; omega
    subst hk
    rcases xv with _ | ⟨x, xr⟩
    · rw [mpe]; exact triple_pure ι _ _ _ fun regs h => ⟨h, List.Forall₂.nil⟩
    · simp at hxl
  · have hk : k = 1 := by simp at hpl; omega
    subst hk
    rcases xv with _ | ⟨x, _ | ⟨y, xr⟩⟩
    · simp at hxl
    · rw [mpe]
      refine triple_pure ι _ _ _ fun regs h => ⟨h, List.Forall₂.cons ?_ List.Forall₂.nil⟩
      show Holds regs (rs.getD 0 z) (F.eval x)
      rw [← hev x (by simp)]
      rcases rv with _ | ⟨c, _ | ⟨c', rr⟩⟩
      · have : rs = [] := List.eq_nil_of_length_eq_zero (by simpa using hrl.symm)
        subst this
        simpa [toPoly] using hz regs h
      · rcases rs with _ | ⟨r, rs'⟩
        · simp at hrl
        · have hh := (List.forall₂_cons.1 (hrs regs h)).1
          simpa [toPoly] using hh
      · simp at hrk
    · simp at hxl
  · have hk : k = rest.length + 2 := by simp at hpl; omega
    subst hk
    rcases xv with _ | ⟨x, _ | ⟨y, xr⟩⟩
    · simp at hxl
    · simp at hxl
    have hxl2 : xr.length = rest.length := by simp at hxl; omega
    have hh1 : (rest.length + 2) / 2 < rest.length + 2 := by omega
    have hh2 : rest.length + 2 - (rest.length + 2) / 2 < rest.length + 2 := by omega
    rw [mpe]
    -- left subproduct
    refine triple_bind_vec ι _ _ P (fun cv => cv.length = (rest.length + 2) / 2 + 1 ∧
      toPoly cv = prodX ((x :: y :: xr).take ((rest.length + 2) / 2))) _
      (triple_prodGen ι _ _ _ (by simp only [List.length_take, List.length_cons] <;> omega)
        (by simp only [List.length_take, List.length_cons] <;> omega) P hP
        (fun r hr => List.forall₂_take _ (hpts r hr))) fun mv mL hmL _ => ?_
    have S1 := stable_and _ _ hP (stable_holdsVec mL mv)
    -- left remainder
    refine triple_bind_vec ι _ _ _ (fun w => w.length = (rest.length + 2) / 2 ∧
      toPoly w = toPoly rv %ₘ toPoly mv) _
      (triple_modUB ι rs.length _ rs mL z rv mv hrl hmL.1 (by
          rw [hmL.2]
          convert prodX_coeff_length ((x :: y :: xr).take ((rest.length + 2) / 2)) using 2
          simp only [List.length_take, List.length_cons] <;> omega) _ S1
        (fun r hr => hrs r hr.1) (fun r hr => hr.2) (fun r hr => hz r hr.1)) fun rLv rL hrL hrLl => ?_
    have S2 := stable_and _ _ S1 (stable_holdsVec rL rLv)
    -- left recursion
    refine triple_bind ι _ _ _ _ _ (ih _ hh1 _ rL ((x :: y :: xr).take ((rest.length + 2) / 2)) rLv
      (by simp only [List.length_take, List.length_cons] <;> omega)
      (by simp only [List.length_take, List.length_cons] <;> omega) hrLl.symm
      (by rw [hrL.1]) (fun x' hx' => by
        rw [hrL.2, hmL.2, eval_modByMonic_of_root _ _ _ (prodX_eval_mem _ _ hx')]
        exact hev x' (List.mem_of_mem_take hx'))
      _ S2 (fun r hr => List.forall₂_take _ (hpts r hr.1.1)) (fun r hr => hr.2)
      (fun r hr => hz r hr.1.1)) fun oL => ?_
    have S3 := stable_and _ _ S2 (stable_holdsVec oL
      (((x :: y :: xr).take ((rest.length + 2) / 2)).map (fun x => F.eval x)))
    -- right subproduct
    refine triple_bind_vec ι _ _ _ (fun cv => cv.length = rest.length + 2 - (rest.length + 2) / 2 + 1 ∧
      toPoly cv = prodX ((x :: y :: xr).drop ((rest.length + 2) / 2))) _
      (triple_prodGen ι _ _ _ (by simp only [List.length_drop, List.length_cons] <;> omega)
        (by simp only [List.length_drop, List.length_cons] <;> omega) _ S3
        (fun r hr => List.forall₂_drop _ (hpts r hr.1.1.1))) fun mv' mR hmR _ => ?_
    have S4 := stable_and _ _ S3 (stable_holdsVec mR mv')
    -- right remainder
    refine triple_bind_vec ι _ _ _ (fun w => w.length = rest.length + 2 - (rest.length + 2) / 2 ∧
      toPoly w = toPoly rv %ₘ toPoly mv') _
      (triple_modUB ι rs.length _ rs mR z rv mv' hrl hmR.1 (by
          rw [hmR.2]
          convert prodX_coeff_length ((x :: y :: xr).drop ((rest.length + 2) / 2)) using 2
          simp only [List.length_drop, List.length_cons] <;> omega) _ S4
        (fun r hr => hrs r hr.1.1.1.1) (fun r hr => hr.2) (fun r hr => hz r hr.1.1.1.1))
        fun rRv rR hrR hrRl => ?_
    have S5 := stable_and _ _ S4 (stable_holdsVec rR rRv)
    -- right recursion
    refine triple_bind ι _ _ _ _ _ (ih _ hh2 _ rR ((x :: y :: xr).drop ((rest.length + 2) / 2)) rRv
      (by simp only [List.length_drop, List.length_cons] <;> omega)
      (by simp only [List.length_drop, List.length_cons] <;> omega) hrRl.symm
      (by rw [hrR.1]) (fun x' hx' => by
        rw [hrR.2, hmR.2, eval_modByMonic_of_root _ _ _ (prodX_eval_mem _ _ hx')]
        exact hev x' (List.mem_of_mem_drop hx'))
      _ S5 (fun r hr => List.forall₂_drop _ (hpts r hr.1.1.1.1.1)) (fun r hr => hr.2)
      (fun r hr => hz r hr.1.1.1.1.1)) fun oR => ?_
    refine triple_pure ι _ _ _ fun regs hr => ⟨hr.1.1.1.1.1.1, ?_⟩
    have := List.rel_append hr.1.1.1.2 hr.2
    rw [← List.take_append_drop ((rest.length + 2) / 2) (x :: y :: xr), List.map_append]
    exact this

theorem mpe_length (z : ℕ) (k : ℕ) : ∀ (pts rs : List ℕ) (m : ℕ), pts.length = k →
    ((mpe z pts rs) m).1.length = k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro pts rs m hpl
  rcases pts with _ | ⟨p, _ | ⟨q, rest⟩⟩
  · rw [mpe]; simp only [Gen.pure, List.length_nil]; simp at hpl; omega
  · rw [mpe]; simp only [Gen.pure, List.length_singleton]; simp at hpl; omega
  · have hk : k = rest.length + 2 := by simp at hpl; omega
    subst hk
    rw [mpe]
    simp only [gen_bind_fst, Gen.pure, List.length_append]
    rw [ih ((rest.length + 2) / 2) (by omega) _ _ _
        (by simp only [List.length_take, List.length_cons] <;> omega),
      ih (rest.length + 2 - (rest.length + 2) / 2) (by omega) _ _ _
        (by simp only [List.length_drop, List.length_cons] <;> omega)]
    omega

theorem modUB_length (M n : ℕ) (ps hm : List ℕ) (z : ℕ) (m : ℕ) :
    ((modUB M n ps hm z) m).1.length = n := by
  simp only [modUB, gen_bind_fst]
  exact modUC_length _ _ _ _ _ _ _

theorem ops_modUB (M n : ℕ) (ps hm : List ℕ) (z : ℕ) (hps : ps.length = M)
    (hhm : hm.length ≤ n + 1) (m : ℕ) :
    (modUB M n ps hm z).ops m ≤ 10 ^ 16 * (M + n + 1) * (Nat.log 2 (M + n + 1) + 1) ^ 11 := by
  refine le_trans (ops_bind_le _ _ (fun _ => True) _ _ m (ops_newtonGen _ _ m) trivial
    fun g n4 _ => ops_modUC _ _ _ _ _ _ hps hhm _) (le_trans ?_ (modU_cost_arith M n))
  omega

/-- `H y = 10^16 y (log₂ y + 1)^11` is monotone. -/
theorem HU_mono {y y' : ℕ} (h : y ≤ y') :
    10 ^ 16 * y * (Nat.log 2 y + 1) ^ 11 ≤ 10 ^ 16 * y' * (Nat.log 2 y' + 1) ^ 11 :=
  Nat.mul_le_mul (Nat.mul_le_mul_left _ h)
    (Nat.pow_le_pow_left (by have := Nat.log_mono_right (b := 2) h; omega) _)

theorem clog_le_log2 (k : ℕ) (hk : 1 ≤ k) : Nat.clog 2 k ≤ Nat.log 2 (2 * k) := by
  apply Nat.clog_le_of_le_pow
  have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (2 * k)
  rw [Nat.pow_succ] at this
  omega

/-- Node cost of the remainder tree is dominated by `gG (10^21) 12`. -/
theorem mpe_node_arith (k : ℕ) (hk : 2 ≤ k) :
    2 * (gG (10 ^ 10) 10 k * (Nat.clog 2 k + 1) + 1) +
      2 * (10 ^ 16 * (2 * k + 1) * (Nat.log 2 (2 * k + 1) + 1) ^ 11) + 2 ≤ gG (10 ^ 21) 12 k := by
  unfold gG
  have hc := clog_le_log2 k (by omega)
  have hl : Nat.log 2 (2 * k + 1) ≤ Nat.log 2 (2 * k) + 1 := by
    have e : Nat.log 2 (k * 2 * 2) = Nat.log 2 (k * 2) + 1 :=
      Nat.log_mul_base (by norm_num) (by omega)
    have h1 := Nat.log_mono_right (b := 2) (show 2 * k + 1 ≤ k * 2 * 2 by omega)
    rw [show k * 2 = 2 * k by ring] at e h1
    omega
  generalize hA : Nat.log 2 (2 * k) + 1 = A at hc hl
  have hA1 : 1 ≤ A := by omega
  have hp1 : (Nat.log 2 (2 * k + 1) + 1) ^ 11 ≤ (2 * A) ^ 11 := Nat.pow_le_pow_left (by omega) _
  rw [mul_pow] at hp1
  have hU : 10 ^ 16 * (2 * k + 1) * (Nat.log 2 (2 * k + 1) + 1) ^ 11 ≤
      10 ^ 16 * (3 * k) * (2 ^ 11 * A ^ 11) := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hp1
  have hP : 10 ^ 10 * k * A ^ 10 * (Nat.clog 2 k + 1) ≤ 10 ^ 10 * k * A ^ 10 * A :=
    Nat.mul_le_mul_left _ (by omega)
  have hW1 : 1 ≤ k * A ^ 11 := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hW2 : k * A ^ 11 ≤ k * A ^ 12 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hA1 (by omega))
  have e1 : 10 ^ 10 * k * A ^ 10 * A = 10 ^ 10 * (k * A ^ 11) := by ring
  have e2 : 10 ^ 16 * (3 * k) * (2 ^ 11 * A ^ 11) = 10 ^ 16 * 3 * 2 ^ 11 * (k * A ^ 11) := by ring
  have e3 : 10 ^ 21 * k * A ^ 12 = 10 ^ 21 * (k * A ^ 12) := by ring
  omega

theorem ops_mpe (z : ℕ) (k : ℕ) : ∀ (pts rs : List ℕ) (m : ℕ), pts.length = k → rs.length ≤ k →
    (mpe z pts rs).ops m ≤ gG (10 ^ 21) 12 k * (Nat.clog 2 k + 1) + 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro pts rs m hpl hrl
  rcases pts with _ | ⟨p, _ | ⟨q, rest⟩⟩
  · rw [mpe, ops_pure]; omega
  · rw [mpe, ops_pure]; omega
  · have hk : k = rest.length + 2 := by simp at hpl; omega
    subst hk
    have hh1 : (rest.length + 2) / 2 < rest.length + 2 := by omega
    have hh2 : rest.length + 2 - (rest.length + 2) / 2 < rest.length + 2 := by omega
    have hPL := ops_prodGen ((rest.length + 2) / 2)
    have hPR := ops_prodGen (rest.length + 2 - (rest.length + 2) / 2)
    have mP : ∀ j, j ≤ rest.length + 2 → gG (10 ^ 10) 10 j * (Nat.clog 2 j + 1) + 1 ≤
        gG (10 ^ 10) 10 (rest.length + 2) * (Nat.clog 2 (rest.length + 2) + 1) + 1 := fun j hj =>
      Nat.add_le_add_right (Nat.mul_le_mul (gG_mono _ _ hj)
        (Nat.add_le_add_right (Nat.clog_mono_right 2 hj) _)) _
    have mU : ∀ j, j ≤ rest.length + 2 → 10 ^ 16 * (rs.length + j + 1) *
        (Nat.log 2 (rs.length + j + 1) + 1) ^ 11 ≤
        10 ^ 16 * (2 * (rest.length + 2) + 1) * (Nat.log 2 (2 * (rest.length + 2) + 1) + 1) ^ 11 :=
      fun j hj => HU_mono (by omega)
    set PB := gG (10 ^ 10) 10 (rest.length + 2) * (Nat.clog 2 (rest.length + 2) + 1) + 1
    set UB := 10 ^ 16 * (2 * (rest.length + 2) + 1) *
      (Nat.log 2 (2 * (rest.length + 2) + 1) + 1) ^ 11 with hUB
    set EL := gG (10 ^ 21) 12 ((rest.length + 2) / 2) *
      (Nat.clog 2 ((rest.length + 2) / 2) + 1) + 1 with hEL
    set ER := gG (10 ^ 21) 12 (rest.length + 2 - (rest.length + 2) / 2) *
      (Nat.clog 2 (rest.length + 2 - (rest.length + 2) / 2) + 1) + 1 with hER
    rw [mpe]
    refine le_trans (ops_bind_le _ _ (fun mL => mL.length ≤ (rest.length + 2) / 2 + 1) PB
      (UB + (EL + (PB + (UB + ER)))) m
      (le_trans (hPL _ m (by simp only [List.length_take, List.length_cons] <;> omega)) (mP _ (by omega)))
      (le_trans (prodGen_length_le _ _) (by simp only [List.length_take, List.length_cons] <;> omega))
      fun mL n1 hmL => ?_) ?_
    · refine ops_bind_le _ _ (fun rL => rL.length ≤ (rest.length + 2) / 2) UB _ n1
        (le_trans (ops_modUB _ _ _ _ _ rfl hmL n1) (mU _ (by omega)))
        (by rw [modUB_length]) fun rL n2 hrL => ?_
      refine ops_bind_le _ _ (fun _ => True) EL _ n2
        (ih _ hh1 _ _ n2 (by simp only [List.length_take, List.length_cons] <;> omega) hrL) trivial
        fun oL n3 _ => ?_
      refine ops_bind_le _ _ (fun mR => mR.length ≤ rest.length + 2 - (rest.length + 2) / 2 + 1) PB _ n3
        (le_trans (hPR _ n3 (by simp only [List.length_drop, List.length_cons] <;> omega)) (mP _ (by omega)))
        (le_trans (prodGen_length_le _ _) (by simp only [List.length_drop, List.length_cons] <;> omega))
        fun mR n4 hmR => ?_
      refine ops_bind_le _ _ (fun rR => rR.length ≤ rest.length + 2 - (rest.length + 2) / 2) UB _ n4
        (le_trans (ops_modUB _ _ _ _ _ rfl hmR n4) (mU _ (by omega)))
        (by rw [modUB_length]) fun rR n5 hrR => ?_
      refine le_trans (ops_bind_le _ _ (fun _ => True) ER 0 n5
        (ih _ hh2 _ _ n5 (by simp only [List.length_drop, List.length_cons] <;> omega) hrR) trivial
        fun _ _ _ => by rw [ops_pure]) (by omega)
    · exact le_trans (le_of_eq (by ring))
        (tree_step (gG (10 ^ 21) 12) (gG_sup _ _) (rest.length + 2) (Nat.le_add_left 2 _) EL ER
          (2 * PB + 2 * UB) le_rfl le_rfl (mpe_node_arith (rest.length + 2) (Nat.le_add_left 2 _)))


/-! ### No oracle calls, and the top-level evaluation program -/

theorem noOr_prodGen (k : ℕ) : ∀ pts : List ℕ, pts.length = k → NoOr (prodGen pts) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro pts hpl
  rcases pts with _ | ⟨p, _ | ⟨q, rest⟩⟩
  · rw [prodGen]; exact noOr_bind _ _ (noOr_emit _ rfl) fun _ => noOr_pure _
  · rw [prodGen]
    exact noOr_bind _ _ (noOr_emit _ rfl) fun _ => noOr_bind _ _ (noOr_emit _ rfl) fun _ =>
      noOr_pure _
  · have hk : k = rest.length + 2 := by simp at hpl; omega
    subst hk
    rw [prodGen]
    exact noOr_bind _ _ (ih ((rest.length + 2) / 2) (by omega) _
        (by simp only [List.length_take, List.length_cons] <;> omega)) fun _ =>
      noOr_bind _ _ (ih (rest.length + 2 - (rest.length + 2) / 2) (by omega) _
        (by simp only [List.length_drop, List.length_cons] <;> omega)) fun _ =>
      noOr_bind _ _ (noOr_polyMulG _ _ _) fun _ => noOr_pure _

theorem noOr_modUB (M n : ℕ) (ps hm : List ℕ) (z : ℕ) : NoOr (modUB M n ps hm z) := by
  unfold modUB modUC modUD modUE
  exact noOr_bind _ _ (noOr_newtonGen _ _) fun _ => noOr_bind _ _ (noOr_polyMulG _ _ _) fun _ =>
    noOr_bind _ _ (noOr_polyMulG _ _ _) fun _ => noOr_bind _ _ (noOr_vecNeg _) fun _ =>
    noOr_bind _ _ (noOr_vecAddPad _ _) fun _ => noOr_pure _

theorem noOr_mpe (z : ℕ) (k : ℕ) : ∀ pts rs : List ℕ, pts.length = k → NoOr (mpe z pts rs) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro pts rs hpl
  rcases pts with _ | ⟨p, _ | ⟨q, rest⟩⟩
  · rw [mpe]; exact noOr_pure _
  · rw [mpe]; exact noOr_pure _
  · have hk : k = rest.length + 2 := by simp at hpl; omega
    subst hk
    rw [mpe]
    exact noOr_bind _ _ (noOr_prodGen _ _ rfl) fun _ => noOr_bind _ _ (noOr_modUB _ _ _ _ _) fun _ =>
      noOr_bind _ _ (ih ((rest.length + 2) / 2) (by omega) _ _
        (by simp only [List.length_take, List.length_cons] <;> omega)) fun _ =>
      noOr_bind _ _ (noOr_prodGen _ _ rfl) fun _ => noOr_bind _ _ (noOr_modUB _ _ _ _ _) fun _ =>
      noOr_bind _ _ (ih (rest.length + 2 - (rest.length + 2) / 2) (by omega) _ _
        (by simp only [List.length_drop, List.length_cons] <;> omega)) fun _ => noOr_pure _

/-- Top level: reduce the input modulo the full subproduct, then the remainder tree. -/
noncomputable def mpeProg (n K : ℕ) : Gen (List ℕ) :=
  Gen.bind (Gen.emit .zero) fun z =>
  Gen.bind (prodGen (List.range' n K)) fun mA =>
  Gen.bind (modUB n K (List.range' 0 n) mA z) fun r =>
  mpe z (List.range' n K) r

theorem noOr_mpeProg (n K : ℕ) : NoOr (mpeProg n K) := by
  unfold mpeProg
  exact noOr_bind _ _ (noOr_emit _ rfl) fun _ => noOr_bind _ _ (noOr_prodGen _ _ rfl) fun _ =>
    noOr_bind _ _ (noOr_modUB _ _ _ _ _) fun _ => noOr_mpe _ _ _ _ rfl

theorem mpeProg_length (n K m : ℕ) : ((mpeProg n K) m).1.length = K := by
  simp only [mpeProg, gen_bind_fst]
  exact mpe_length _ _ _ _ _ (by simp)

open Polynomial in
theorem triple_mpeProg {R : Type*} [CommRing R] [Nontrivial R] (ι : R → R) (n K : ℕ)
    (a : Fin n → R) (x : Fin K → R) (P : List R → Prop) (hP : Stable P)
    (ha : ∀ regs, P regs → HoldsVec regs (List.range' 0 n) (List.ofFn a))
    (hx : ∀ regs, P regs → HoldsVec regs (List.range' n K) (List.ofFn x)) :
    Triple ι (mpeProg n K) P (fun out regs => P regs ∧
      HoldsVec regs out ((List.ofFn x).map (fun y => (toPoly (List.ofFn a)).eval y))) := by
  unfold mpeProg
  refine triple_bind ι _ _ P _ _ (triple_emit_zero ι P hP) fun z => ?_
  have S1 := stable_and _ _ hP (stable_holds z (0 : R))
  refine triple_bind_vec ι _ _ _ (fun cv => cv.length = K + 1 ∧ toPoly cv = prodX (List.ofFn x)) _
    (triple_prodGen ι K _ _ (by simp) (by simp) _ S1 (fun r h => hx r h.1)) fun mv mA hmA _ => ?_
  have S2 := stable_and _ _ S1 (stable_holdsVec mA mv)
  refine triple_bind_vec ι _ _ _ (fun w => w.length = K ∧
      toPoly w = toPoly (List.ofFn a) %ₘ toPoly mv) _
    (triple_modUB ι n K _ mA z (List.ofFn a) mv (by simp) hmA.1 (by
        rw [hmA.2]; have := prodX_coeff_length (List.ofFn x); rwa [List.length_ofFn] at this)
      _ S2 (fun r h => ha r h.1.1) (fun r h => h.2) (fun r h => h.1.2)) fun rv r hr hrl => ?_
  have S3 := stable_and _ _ S2 (stable_holdsVec r rv)
  intro regs h
  obtain ⟨new, e1, e2, e3⟩ := triple_mpe ι z (toPoly (List.ofFn a)) K (List.range' n K) r
    (List.ofFn x) rv (by simp) (by simp) hrl.symm (by rw [hr.1]) (fun y hy => by
      rw [hr.2, hmA.2, eval_modByMonic_of_root _ _ _ (prodX_eval_mem _ _ hy)])
    _ S3 (fun r h => hx r h.1.1.1) (fun r h => h.2) (fun r h => h.1.1.2) regs h
  exact ⟨new, e1, e2, e3.1.1.1.1, e3.2⟩

theorem ops_mpeProg (n K m : ℕ) : (mpeProg n K).ops m ≤
    1 + ((gG (10 ^ 10) 10 K * (Nat.clog 2 K + 1) + 1) +
      (10 ^ 16 * (n + K + 1) * (Nat.log 2 (n + K + 1) + 1) ^ 11 +
        (gG (10 ^ 21) 12 K * (Nat.clog 2 K + 1) + 1))) := by
  unfold mpeProg
  refine ops_bind_le _ _ (fun _ => True) _ _ m (by rw [ops_emit]; simp [Instr.isRingOp]) trivial
    fun z n1 _ => ?_
  refine ops_bind_le _ _ (fun mA => mA.length ≤ K + 1) _ _ n1 (ops_prodGen K _ n1 (by simp))
    (le_trans (prodGen_length_le _ _) (by simp)) fun mA n2 hmA => ?_
  refine ops_bind_le _ _ (fun r => r.length ≤ K) _ _ n2 (ops_modUB _ _ _ _ _ (by simp) hmA n2)
    (by rw [modUB_length]) fun r n3 hr => ?_
  exact ops_mpe z K _ _ n3 (by simp) hr

theorem mpeProg_cost_arith (n K : ℕ) :
    1 + ((gG (10 ^ 10) 10 K * (Nat.clog 2 K + 1) + 1) +
      (10 ^ 16 * (n + K + 1) * (Nat.log 2 (n + K + 1) + 1) ^ 11 +
        (gG (10 ^ 21) 12 K * (Nat.clog 2 K + 1) + 1))) ≤
      10 ^ 26 * (n + K + 1) * (Nat.log 2 (n + K + 1) + 1) ^ 13 := by
  unfold gG
  generalize hL : n + K + 1 = L
  have hKL : K < L := by omega
  have h2L : Nat.log 2 (2 * L) = Nat.log 2 L + 1 := by
    rw [mul_comm]; exact Nat.log_mul_base (by norm_num) (by omega)
  have hlK : Nat.log 2 (2 * K) ≤ Nat.log 2 L + 1 := by
    rw [← h2L]; exact Nat.log_mono_right (by omega)
  have hcK : Nat.clog 2 K ≤ Nat.log 2 L + 1 := by
    apply Nat.clog_le_of_le_pow
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) L
    omega
  generalize hA : Nat.log 2 L + 1 = A at hlK hcK ⊢
  have hA1 : 1 ≤ A := by omega
  have hp10 : (Nat.log 2 (2 * K) + 1) ^ 10 ≤ (2 * A) ^ 10 := Nat.pow_le_pow_left (by omega) _
  have hp12 : (Nat.log 2 (2 * K) + 1) ^ 12 ≤ (2 * A) ^ 12 := Nat.pow_le_pow_left (by omega) _
  rw [mul_pow] at hp10 hp12
  have hc1 : Nat.clog 2 K + 1 ≤ 2 * A := by omega
  have t1 : 10 ^ 10 * K * (Nat.log 2 (2 * K) + 1) ^ 10 * (Nat.clog 2 K + 1) ≤
      10 ^ 10 * L * (2 ^ 10 * A ^ 10) * (2 * A) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hKL.le) hp10) hc1
  have t2 : 10 ^ 21 * K * (Nat.log 2 (2 * K) + 1) ^ 12 * (Nat.clog 2 K + 1) ≤
      10 ^ 21 * L * (2 ^ 12 * A ^ 12) * (2 * A) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hKL.le) hp12) hc1
  have e1 : 10 ^ 10 * L * (2 ^ 10 * A ^ 10) * (2 * A) = 10 ^ 10 * 2 ^ 11 * (L * A ^ 11) := by ring
  have e2 : 10 ^ 21 * L * (2 ^ 12 * A ^ 12) * (2 * A) = 10 ^ 21 * 2 ^ 13 * (L * A ^ 13) := by ring
  have e3 : 10 ^ 16 * L * A ^ 11 = 10 ^ 16 * (L * A ^ 11) := by ring
  have e4 : 10 ^ 26 * L * A ^ 13 = 10 ^ 26 * (L * A ^ 13) := by ring
  have h11 : L * A ^ 11 ≤ L * A ^ 13 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hA1 (by omega))
  have h1 : 1 ≤ L * A ^ 11 :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
  omega

/-- **ChildC (fast multipoint evaluation, MCA Cor 10.8)**. -/
theorem mpe_main : ∃ (C k : ℕ) (E : ℕ → ℕ → SLP), ∀ n K : ℕ,
    ringOps (E n K) ≤ C * (n + K + 1) * (Nat.log 2 (n + K + 1) + 1) ^ k ∧
    oracleCalls (E n K) = [] ∧
    ∀ (R : Type) [CommRing R] (ι : R → R) (a : Fin n → R) (x : Fin K → R),
      run ι (E n K) (List.ofFn a ++ List.ofFn x) =
        List.ofFn (fun i : Fin K => (densePoly a).eval (x i)) := by
  refine ⟨10 ^ 26, 13, fun n K => ⟨((mpeProg n K) (n + K)).2.1, ((mpeProg n K) (n + K)).1⟩,
    fun n K => ⟨?_, ?_, ?_⟩⟩
  · rw [ringOps_gen]; exact le_trans (ops_mpeProg n K _) (mpeProg_cost_arith n K)
  · exact oracleCalls_gen_nil _ _ (noOr_mpeProg n K _)
  · intro R _ ι a x
    have hlen : (List.ofFn a ++ List.ofFn x).length = n + K := by simp
    rcases subsingleton_or_nontrivial R with hR | hR
    · apply list_eq_of_subsingleton
      simp only [run, List.length_map, List.length_ofFn]
      exact mpeProg_length _ _ _
    · let P : List R → Prop := fun regs => HoldsVec regs (List.range' 0 n) (List.ofFn a) ∧
        HoldsVec regs (List.range' n K) (List.ofFn x)
      have hP : Stable P := stable_and _ _ (stable_holdsVec _ _) (stable_holdsVec _ _)
      have T := triple_mpeProg ι n K a x P hP (fun _ h => h.1) (fun _ h => h.2)
      have h0 : P (List.ofFn a ++ List.ofFn x) := by
        refine ⟨?_, ?_⟩
        · have := holdsVec_range' (List.ofFn a) []
          simp only [List.nil_append, List.length_nil, List.length_ofFn] at this
          exact holdsVec_append _ _ _ _ this
        · have := holdsVec_range' (List.ofFn x) (List.ofFn a)
          simpa only [List.length_ofFn] using this
      have := run_of_triple ι (mpeProg n K) P _
        (fun vs => vs = List.ofFn (fun i : Fin K => (densePoly a).eval (x i))) T
        (fun out regs hq => ⟨_, hq.2, by rw [List.map_ofFn, densePoly_eq_toPoly n a]; rfl⟩) _ h0
      rw [hlen] at this
      exact this


/-! ## S5 ChildD: fast interpolation by the halving recursion `f = fL * mR + fR * mL` -/

/-- Elementwise `v_i * ι e_i`. -/
def scaleInv : List ℕ → List ℕ → Gen (List ℕ)
  | [], _ => Gen.pure []
  | _ :: _, [] => Gen.pure []
  | v :: vs, e :: es =>
    Gen.bind (Gen.emit (.inv e)) fun i => Gen.bind (Gen.emit (.mul v i)) fun r =>
    Gen.bind (scaleInv vs es) fun rs => Gen.pure (r :: rs)

theorem triple_scaleInv {R : Type*} [CommRing R] (ι : R → R) :
    ∀ (vs es : List ℕ) (vv ev : List R) (P : List R → Prop), Stable P →
      (∀ regs, P regs → HoldsVec regs vs vv) → (∀ regs, P regs → HoldsVec regs es ev) →
      Triple ι (scaleInv vs es) P
        (fun out regs => P regs ∧ HoldsVec regs out (List.zipWith (fun a b => a * ι b) vv ev))
  | [], es, vv, ev, P, hP, hv, he => by
    rw [scaleInv]
    exact triple_pure ι _ _ _ fun regs h => ⟨h, by
      rw [List.forall₂_nil_left_iff.mp (hv regs h)]; exact List.Forall₂.nil⟩
  | v :: vs, [], vv, ev, P, hP, hv, he => by
    rw [scaleInv]
    exact triple_pure ι _ _ _ fun regs h => ⟨h, by
      rw [List.forall₂_nil_left_iff.mp (he regs h), List.zipWith_nil_right]; exact List.Forall₂.nil⟩
  | v :: vs, e :: es, [], ev, P, hP, hv, he =>
    triple_of_false ι _ P _ fun regs h => nomatch hv regs h
  | v :: vs, e :: es, a :: vv, [], P, hP, hv, he =>
    triple_of_false ι _ P _ fun regs h => nomatch he regs h
  | v :: vs, e :: es, a :: vv, b :: ev, P, hP, hv, he => by
    have hv1 : ∀ regs, P regs → Holds regs v a := fun regs h => (List.forall₂_cons.1 (hv regs h)).1
    have he1 : ∀ regs, P regs → Holds regs e b := fun regs h => (List.forall₂_cons.1 (he regs h)).1
    rw [scaleInv]
    refine triple_bind ι _ _ P _ _ (triple_emit_inv ι e b P hP he1) fun i => ?_
    have S1 := stable_and _ _ hP (stable_holds i (ι b))
    refine triple_bind ι _ _ _ _ _ (triple_emit_mul ι v i a (ι b) _ S1 (fun r h => hv1 r h.1)
      (fun r h => h.2)) fun r => ?_
    have S2 := stable_and _ _ S1 (stable_holds r (a * ι b))
    refine triple_bind ι _ _ _ _ _ (triple_scaleInv ι vs es vv ev _ S2
      (fun r h => (List.forall₂_cons.1 (hv r h.1.1)).2)
      (fun r h => (List.forall₂_cons.1 (he r h.1.1)).2)) fun rs => ?_
    exact triple_pure ι _ _ _ fun regs h => ⟨h.1.1.1, List.Forall₂.cons h.1.2 h.2⟩

theorem ops_scaleInv : ∀ (vs es : List ℕ) (n : ℕ), (scaleInv vs es).ops n ≤ 2 * es.length
  | [], es, n => by rw [scaleInv, ops_pure]; omega
  | v :: vs, [], n => by rw [scaleInv, ops_pure]; omega
  | v :: vs, e :: es, n => by
    rw [scaleInv, ops_bind, ops_emit, ops_bind, ops_emit, ops_bind, ops_pure, List.length_cons]
    have := ops_scaleInv vs es
      ((Gen.emit (Instr.mul v (Gen.emit (Instr.inv e) n).1)) (Gen.emit (Instr.inv e) n).2.2).2.2
    simp only [Instr.isRingOp, if_true] at *
    omega

theorem noOr_scaleInv : ∀ vs es, NoOr (scaleInv vs es)
  | [], es => by rw [scaleInv]; exact noOr_pure _
  | v :: vs, [] => by rw [scaleInv]; exact noOr_pure _
  | v :: vs, e :: es => by
    rw [scaleInv]
    exact noOr_bind _ _ (noOr_emit _ rfl) fun _ => noOr_bind _ _ (noOr_emit _ rfl) fun _ =>
      noOr_bind _ _ (noOr_scaleInv vs es) fun _ => noOr_pure _

/-- Values of a polynomial (registers `poly`) at points `pts` whose subproduct is in `mpts`. -/
noncomputable def evalAtGen (z : ℕ) (poly pts mpts : List ℕ) : Gen (List ℕ) :=
  Gen.bind (modUB poly.length pts.length poly mpts z) fun r => mpe z pts r

open Polynomial in
theorem triple_evalAt {R : Type*} [CommRing R] [Nontrivial R] (ι : R → R) (z : ℕ)
    (poly pts mpts : List ℕ) (pv xv mv : List R) (hpl : pv.length = poly.length)
    (hxl : xv.length = pts.length) (hml : mv.length = pts.length + 1) (hm : toPoly mv = prodX xv)
    (P : List R → Prop) (hP : Stable P) (hpoly : ∀ regs, P regs → HoldsVec regs poly pv)
    (hpts : ∀ regs, P regs → HoldsVec regs pts xv) (hmpts : ∀ regs, P regs → HoldsVec regs mpts mv)
    (hz : ∀ regs, P regs → Holds regs z 0) :
    Triple ι (evalAtGen z poly pts mpts) P (fun out regs => P regs ∧
      HoldsVec regs out (xv.map (fun x => (toPoly pv).eval x))) := by
  unfold evalAtGen
  refine triple_bind_vec ι _ _ P (fun w => w.length = pts.length ∧
      toPoly w = toPoly pv %ₘ toPoly mv) _
    (triple_modUB ι poly.length pts.length poly mpts z pv mv hpl hml (by
        rw [hm]; have := prodX_coeff_length xv; rwa [hxl] at this) P hP hpoly hmpts hz)
    fun rv r hr hrl => ?_
  have S1 := stable_and _ _ hP (stable_holdsVec r rv)
  intro regs h
  obtain ⟨new, e1, e2, e3⟩ := triple_mpe ι z (toPoly pv) pts.length pts r xv rv rfl hxl hrl.symm
    (by rw [hr.1]) (fun y hy => by
      rw [hr.2, hm, eval_modByMonic_of_root _ _ _ (prodX_eval_mem _ _ hy)])
    _ S1 (fun r h => hpts r h.1) (fun r h => h.2) (fun r h => hz r h.1) regs h
  exact ⟨new, e1, e2, e3.1.1, e3.2⟩

theorem evalAt_length (z : ℕ) (poly pts mpts : List ℕ) (m : ℕ) :
    ((evalAtGen z poly pts mpts) m).1.length = pts.length := by
  simp only [evalAtGen, gen_bind_fst]
  exact mpe_length _ _ _ _ _ rfl

theorem ops_evalAt (z : ℕ) (poly pts mpts : List ℕ) (hm : mpts.length ≤ pts.length + 1) (m : ℕ) :
    (evalAtGen z poly pts mpts).ops m ≤
      10 ^ 16 * (poly.length + pts.length + 1) * (Nat.log 2 (poly.length + pts.length + 1) + 1) ^ 11 +
      (gG (10 ^ 21) 12 pts.length * (Nat.clog 2 pts.length + 1) + 1) := by
  unfold evalAtGen
  exact ops_bind_le _ _ (fun r => r.length ≤ pts.length) _ _ m (ops_modUB _ _ _ _ _ rfl hm m)
    (by rw [modUB_length]) fun r n1 hr => ops_mpe z _ _ _ n1 rfl hr

theorem noOr_evalAt (z : ℕ) (poly pts mpts : List ℕ) : NoOr (evalAtGen z poly pts mpts) := by
  unfold evalAtGen
  exact noOr_bind _ _ (noOr_modUB _ _ _ _ _) fun _ => noOr_mpe _ _ _ _ rfl

open Polynomial in
theorem prodX_eval_unit {R : Type*} [CommRing R] (x : R) :
    ∀ ys : List R, (∀ y ∈ ys, IsUnit (x - y)) → IsUnit ((prodX ys).eval x)
  | [], _ => by simp [prodX]
  | y :: ys, h => by
    rw [prodX_cons, eval_mul]
    exact IsUnit.mul (by simpa using h y (by simp))
      (prodX_eval_unit x ys fun y' hy' => h y' (by simp [hy']))

open Polynomial in
theorem forall2_scale {R : Type*} [CommRing R] (ι : R → R) (F g G : R[X]) :
    ∀ (xl vl : List R), xl.length = vl.length →
    List.Forall₂ (fun x w => F.eval x = w) xl
      (List.zipWith (fun a b => a * ι b) vl (xl.map (fun x => g.eval x))) →
    (∀ x ∈ xl, ι (g.eval x) * g.eval x = 1) →
    (∀ x ∈ xl, G.eval x = F.eval x * g.eval x) →
    List.Forall₂ (fun x v => G.eval x = v) xl vl
  | [], [], _, _, _, _ => List.Forall₂.nil
  | x :: xl, v :: vl, hl, h, hu, hG => by
    simp only [List.map_cons, List.zipWith_cons_cons, List.forall₂_cons] at h
    refine List.Forall₂.cons ?_ (forall2_scale ι F g G xl vl (by simpa using hl) h.2
      (fun y hy => hu y (by simp [hy])) (fun y hy => hG y (by simp [hy])))
    rw [hG x (by simp), h.1, mul_assoc, hu x (by simp), mul_one]
  | [], _ :: _, hl, _, _, _ => by simp at hl
  | _ :: _, [], hl, _, _, _ => by simp at hl

/-- Interpolation: values (registers `vals`) at points `pts` to coefficients (length `#pts`). -/
noncomputable def interp (z : ℕ) : List ℕ → List ℕ → Gen (List ℕ)
  | [], _ => Gen.pure []
  | [_], vals => Gen.pure [vals.getD 0 z]
  | p :: q :: rest, vals =>
    Gen.bind (prodGen ((p :: q :: rest).take ((rest.length + 2) / 2))) fun mL =>
    Gen.bind (prodGen ((p :: q :: rest).drop ((rest.length + 2) / 2))) fun mR =>
    Gen.bind (evalAtGen z mR ((p :: q :: rest).take ((rest.length + 2) / 2)) mL) fun eR =>
    Gen.bind (scaleInv (vals.take ((rest.length + 2) / 2)) eR) fun vL =>
    Gen.bind (interp z ((p :: q :: rest).take ((rest.length + 2) / 2)) vL) fun fL =>
    Gen.bind (evalAtGen z mL ((p :: q :: rest).drop ((rest.length + 2) / 2)) mR) fun eL =>
    Gen.bind (scaleInv (vals.drop ((rest.length + 2) / 2)) eL) fun vR =>
    Gen.bind (interp z ((p :: q :: rest).drop ((rest.length + 2) / 2)) vR) fun fR =>
    Gen.bind (polyMulG (rest.length + 2) fL mR) fun p1 =>
    Gen.bind (polyMulG (rest.length + 2) fR mL) fun p2 =>
    Gen.bind (vecAddPad p1 p2) fun s =>
    Gen.pure (padBlk z (rest.length + 2) (s.take (rest.length + 2)))
termination_by pts _ => pts.length
decreasing_by
  all_goals (simp only [List.length_take, List.length_drop, List.length_cons] <;> omega)

theorem interp_length (z : ℕ) : ∀ (pts vals : List ℕ) (m : ℕ),
    ((interp z pts vals) m).1.length = pts.length
  | [], vals, m => by rw [interp]; rfl
  | [p], vals, m => by rw [interp]; rfl
  | p :: q :: rest, vals, m => by
    rw [interp]; simp only [gen_bind_fst, Gen.pure]
    rw [padBlk_length _ _ _ (List.length_take_le _ _)]; simp


open Polynomial in
theorem triple_interp {R : Type*} [CommRing R] [Nontrivial R] (ι : R → R)
    (hι : ∀ u : Rˣ, ι (u : R) = ((u⁻¹ : Rˣ) : R)) (z : ℕ) (k : ℕ) :
    ∀ (pts vals : List ℕ) (xv vv : List R), pts.length = k → xv.length = k → vv.length = k →
    xv.Pairwise (fun a b => IsUnit (a - b)) →
    ∀ (P : List R → Prop), Stable P → (∀ regs, P regs → HoldsVec regs pts xv) →
    (∀ regs, P regs → HoldsVec regs vals vv) → (∀ regs, P regs → Holds regs z 0) →
    Triple ι (interp z pts vals) P (fun out regs => P regs ∧ ∃ fv : List R,
      HoldsVec regs out fv ∧ fv.length = k ∧
        List.Forall₂ (fun x v => (toPoly fv).eval x = v) xv vv) := by
  have hιu : ∀ c : R, IsUnit c → ι c * c = 1 := fun c ⟨u, hu⟩ => by
    rw [← hu, hι u]; exact Units.inv_mul u
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro pts vals xv vv hpl hxl hvl hpw P hP hpts hvals hz
  rcases pts with _ | ⟨p, _ | ⟨q, rest⟩⟩
  · have hk : k = 0 := by simp at hpl; omega
    subst hk
    rw [List.length_eq_zero_iff.mp hxl, List.length_eq_zero_iff.mp hvl, interp]
    exact triple_pure ι _ _ _ fun regs h => ⟨h, [], List.Forall₂.nil, rfl, List.Forall₂.nil⟩
  · have hk : k = 1 := by simp at hpl; omega
    subst hk
    rcases xv with _ | ⟨x, _ | ⟨y, xr⟩⟩
    · simp at hxl
    · rcases vv with _ | ⟨w, _ | ⟨w', vr⟩⟩
      · simp at hvl
      · rw [interp]
        refine triple_pure ι _ _ _ fun regs h => ⟨h, [w], List.Forall₂.cons ?_ List.Forall₂.nil, rfl,
          List.Forall₂.cons (by simp [toPoly]) List.Forall₂.nil⟩
        have hv := hvals regs h
        rcases vals with _ | ⟨r, rs⟩
        · exact nomatch hv
        · simpa using (List.forall₂_cons.1 hv).1
      · simp at hvl
    · simp at hxl
  · have hk : k = rest.length + 2 := by simp at hpl; omega
    subst hk
    rcases xv with _ | ⟨x, _ | ⟨y, xr⟩⟩
    · simp at hxl
    · simp at hxl
    have hxl2 : xr.length = rest.length := by simp at hxl; omega
    have hh1 : (rest.length + 2) / 2 < rest.length + 2 := by omega
    have hh2 : rest.length + 2 - (rest.length + 2) / 2 < rest.length + 2 := by omega
    have hpw' := hpw
    rw [← List.take_append_drop ((rest.length + 2) / 2) (x :: y :: xr), List.pairwise_append] at hpw'
    obtain ⟨pwL, pwR, cross⟩ := hpw'
    rw [interp]
    -- left subproduct
    refine triple_bind_vec ι _ _ P (fun cv => cv.length = (rest.length + 2) / 2 + 1 ∧
      toPoly cv = prodX ((x :: y :: xr).take ((rest.length + 2) / 2))) _
      (triple_prodGen ι _ _ _ (by simp only [List.length_take, List.length_cons] <;> omega)
        (by simp only [List.length_take, List.length_cons] <;> omega) P hP
        (fun r hr => List.forall₂_take _ (hpts r hr))) fun mLv mL hmL hmLl => ?_
    have S1 := stable_and _ _ hP (stable_holdsVec mL mLv)
    -- right subproduct
    refine triple_bind_vec ι _ _ _ (fun cv => cv.length = rest.length + 2 - (rest.length + 2) / 2 + 1 ∧
      toPoly cv = prodX ((x :: y :: xr).drop ((rest.length + 2) / 2))) _
      (triple_prodGen ι _ _ _ (by simp only [List.length_drop, List.length_cons] <;> omega)
        (by simp only [List.length_drop, List.length_cons] <;> omega) _ S1
        (fun r hr => List.forall₂_drop _ (hpts r hr.1))) fun mRv mR hmR hmRl => ?_
    have S2 := stable_and _ _ S1 (stable_holdsVec mR mRv)
    -- values of mR at the left points
    refine triple_bind ι _ _ _ _ _ (triple_evalAt ι z mR ((p :: q :: rest).take ((rest.length + 2) / 2)) mL mRv
      ((x :: y :: xr).take ((rest.length + 2) / 2)) mLv hmRl.symm
      (by simp only [List.length_take, List.length_cons] <;> omega)
      (by rw [hmL.1]; simp only [List.length_take, List.length_cons] <;> omega) hmL.2 _ S2
      (fun r hr => hr.2) (fun r hr => List.forall₂_take _ (hpts r hr.1.1)) (fun r hr => hr.1.2)
      (fun r hr => hz r hr.1.1)) fun eR => ?_
    have S3 := stable_and _ _ S2 (stable_holdsVec eR
      (((x :: y :: xr).take ((rest.length + 2) / 2)).map (fun x => (toPoly mRv).eval x)))
    -- scaled left values
    refine triple_bind ι _ _ _ _ _ (triple_scaleInv ι (vals.take ((rest.length + 2) / 2)) eR
      (vv.take ((rest.length + 2) / 2)) _ _ S3
      (fun r hr => List.forall₂_take _ (hvals r hr.1.1.1)) (fun r hr => hr.2)) fun vL => ?_
    have S4 := stable_and _ _ S3 (stable_holdsVec vL (List.zipWith (fun a b => a * ι b)
      (vv.take ((rest.length + 2) / 2))
      (((x :: y :: xr).take ((rest.length + 2) / 2)).map (fun x => (toPoly mRv).eval x))))
    -- left interpolant
    refine triple_bind_vec ι _ _ _ (fun fv => fv.length = (rest.length + 2) / 2 ∧
      List.Forall₂ (fun x v => (toPoly fv).eval x = v) ((x :: y :: xr).take ((rest.length + 2) / 2))
        (List.zipWith (fun a b => a * ι b) (vv.take ((rest.length + 2) / 2))
          (((x :: y :: xr).take ((rest.length + 2) / 2)).map (fun x => (toPoly mRv).eval x)))) _
      (ih _ hh1 _ vL _ _ (by simp only [List.length_take, List.length_cons] <;> omega)
        (by simp only [List.length_take, List.length_cons] <;> omega)
        (by simp only [List.length_zipWith, List.length_map, List.length_take, List.length_cons]
            <;> omega) pwL _ S4
        (fun r ⟨⟨⟨⟨hP0, _⟩, _⟩, _⟩, _⟩ => List.forall₂_take _ (hpts r hP0)) (fun r hr => hr.2)
        (fun r ⟨⟨⟨⟨hP0, _⟩, _⟩, _⟩, _⟩ => hz r hP0)) fun fLv fL hfL hfLl => ?_
    have S5 := stable_and _ _ S4 (stable_holdsVec fL fLv)
    -- values of mL at the right points
    refine triple_bind ι _ _ _ _ _ (triple_evalAt ι z mL ((p :: q :: rest).drop ((rest.length + 2) / 2)) mR mLv
      ((x :: y :: xr).drop ((rest.length + 2) / 2)) mRv hmLl.symm
      (by simp only [List.length_drop, List.length_cons] <;> omega)
      (by rw [hmR.1]; simp only [List.length_drop, List.length_cons] <;> omega) hmR.2 _ S5
      (fun r ⟨⟨⟨⟨⟨_, h1⟩, _⟩, _⟩, _⟩, _⟩ => h1)
      (fun r ⟨⟨⟨⟨⟨hP0, _⟩, _⟩, _⟩, _⟩, _⟩ => List.forall₂_drop _ (hpts r hP0))
      (fun r ⟨⟨⟨⟨_, h2⟩, _⟩, _⟩, _⟩ => h2)
      (fun r ⟨⟨⟨⟨⟨hP0, _⟩, _⟩, _⟩, _⟩, _⟩ => hz r hP0)) fun eL => ?_
    have S6 := stable_and _ _ S5 (stable_holdsVec eL
      (((x :: y :: xr).drop ((rest.length + 2) / 2)).map (fun x => (toPoly mLv).eval x)))
    -- scaled right values
    refine triple_bind ι _ _ _ _ _ (triple_scaleInv ι (vals.drop ((rest.length + 2) / 2)) eL
      (vv.drop ((rest.length + 2) / 2)) _ _ S6
      (fun r ⟨⟨⟨⟨⟨⟨hP0, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ => List.forall₂_drop _ (hvals r hP0))
      (fun r hr => hr.2)) fun vR => ?_
    have S7 := stable_and _ _ S6 (stable_holdsVec vR (List.zipWith (fun a b => a * ι b)
      (vv.drop ((rest.length + 2) / 2))
      (((x :: y :: xr).drop ((rest.length + 2) / 2)).map (fun x => (toPoly mLv).eval x))))
    -- right interpolant
    refine triple_bind_vec ι _ _ _ (fun fv => fv.length = rest.length + 2 - (rest.length + 2) / 2 ∧
      List.Forall₂ (fun x v => (toPoly fv).eval x = v) ((x :: y :: xr).drop ((rest.length + 2) / 2))
        (List.zipWith (fun a b => a * ι b) (vv.drop ((rest.length + 2) / 2))
          (((x :: y :: xr).drop ((rest.length + 2) / 2)).map (fun x => (toPoly mLv).eval x)))) _
      (ih _ hh2 _ vR _ _ (by simp only [List.length_drop, List.length_cons] <;> omega)
        (by simp only [List.length_drop, List.length_cons] <;> omega)
        (by simp only [List.length_zipWith, List.length_map, List.length_drop, List.length_cons]
            <;> omega) pwR _ S7
        (fun r ⟨⟨⟨⟨⟨⟨⟨hP0, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ => List.forall₂_drop _ (hpts r hP0))
        (fun r hr => hr.2)
        (fun r ⟨⟨⟨⟨⟨⟨⟨hP0, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ => hz r hP0)) fun fRv fR hfR hfRl => ?_
    have S8 := stable_and _ _ S7 (stable_holdsVec fR fRv)
    have hfLk : fLv.length ≤ rest.length + 2 := by omega
    have hmRk : mRv.length ≤ rest.length + 2 := by omega
    have hfRk : fRv.length ≤ rest.length + 2 := by omega
    have hmLk : mLv.length ≤ rest.length + 2 := by omega
    -- products
    refine triple_bind_vec ι _ _ _ (fun zs => zs = List.ofFn (fun j : Fin (2 * (rest.length + 2)) =>
      (toPoly fLv * toPoly mRv).coeff (j : ℕ))) _
      (triple_polyMulG ι (rest.length + 2) fL mR fLv mRv hfLk hmRk _ S8
        (fun r ⟨⟨⟨⟨_, h⟩, _⟩, _⟩, _⟩ => h)
        (fun r ⟨⟨⟨⟨⟨⟨⟨_, h⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ => h)) fun p1v p1 hp1 _ => ?_
    have S9 := stable_and _ _ S8 (stable_holdsVec p1 p1v)
    refine triple_bind_vec ι _ _ _ (fun zs => zs = List.ofFn (fun j : Fin (2 * (rest.length + 2)) =>
      (toPoly fRv * toPoly mLv).coeff (j : ℕ))) _
      (triple_polyMulG ι (rest.length + 2) fR mL fRv mLv hfRk hmLk _ S9
        (fun r ⟨⟨_, h⟩, _⟩ => h)
        (fun r ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, h⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ => h)) fun p2v p2 hp2 _ => ?_
    have S10 := stable_and _ _ S9 (stable_holdsVec p2 p2v)
    refine triple_bind ι _ _ _ _ _ (triple_vecAddPad ι p1 p2 p1v p2v _ S10
      (fun r ⟨⟨_, h⟩, _⟩ => h) (fun r hr => hr.2)) fun s => ?_
    -- algebra of the result
    have hdeg : (toPoly fLv * toPoly mRv + toPoly fRv * toPoly mLv).natDegree < rest.length + 2 := by
      have h1 := toPoly_natDegree_le fLv
      have h2 := toPoly_natDegree_le mRv
      have h3 := toPoly_natDegree_le fRv
      have h4 := toPoly_natDegree_le mLv
      have h5 := natDegree_mul_le (p := toPoly fLv) (q := toPoly mRv)
      have h6 := natDegree_mul_le (p := toPoly fRv) (q := toPoly mLv)
      have h7 := natDegree_add_le (toPoly fLv * toPoly mRv) (toPoly fRv * toPoly mLv)
      omega
    have hS : toPoly (listAddPad p1v p2v) = toPoly fLv * toPoly mRv + toPoly fRv * toPoly mLv := by
      rw [toPoly_listAddPad, hp1, hp2, toPoly_polyMul_out _ _ _ hfLk hmRk,
        toPoly_polyMul_out _ _ _ hfRk hmLk]
    have hG : ∀ c : List R, c = (listAddPad p1v p2v).take (rest.length + 2) →
        toPoly (c ++ List.replicate (rest.length + 2 - c.length) 0) =
          toPoly fLv * toPoly mRv + toPoly fRv * toPoly mLv := by
      intro c hc
      rw [toPoly_append, toPoly_replicate_zero, mul_zero, add_zero, hc,
        toPoly_take_of_deg _ _ (by rw [hS]; exact hdeg), hS]
    have hmLx : ∀ x' ∈ (x :: y :: xr).take ((rest.length + 2) / 2), (toPoly mLv).eval x' = 0 :=
      fun x' hx' => by rw [hmL.2]; exact prodX_eval_mem _ _ hx'
    have hmRx : ∀ x' ∈ (x :: y :: xr).drop ((rest.length + 2) / 2), (toPoly mRv).eval x' = 0 :=
      fun x' hx' => by rw [hmR.2]; exact prodX_eval_mem _ _ hx'
    refine triple_pure ι _ _ _ fun regs hr => ?_
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hP0, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hs0⟩ := hr
    have hz0 := hz regs hP0
    have hfin := holdsVec_padBlk regs z hz0 _ _ (List.forall₂_take (rest.length + 2) hs0)
      (rest.length + 2)
    refine ⟨hP0, _, hfin, ?_, ?_⟩
    · rw [List.length_append, List.length_replicate]
      have := List.length_take_le (rest.length + 2) (listAddPad p1v p2v)
      omega
    · rw [hG _ rfl]
      have hL := forall2_scale ι (toPoly fLv) (toPoly mRv)
        (toPoly fLv * toPoly mRv + toPoly fRv * toPoly mLv)
        ((x :: y :: xr).take ((rest.length + 2) / 2)) (vv.take ((rest.length + 2) / 2))
        (by simp only [List.length_take, List.length_cons] <;> omega) hfL.2
        (fun x' hx' => hιu _ (by
          rw [hmR.2]
          exact prodX_eval_unit x' _ fun y' hy' => cross x' hx' y' hy'))
        (fun x' hx' => by simp only [eval_add, eval_mul, hmLx x' hx', mul_zero, add_zero])
      have hR := forall2_scale ι (toPoly fRv) (toPoly mLv)
        (toPoly fLv * toPoly mRv + toPoly fRv * toPoly mLv)
        ((x :: y :: xr).drop ((rest.length + 2) / 2)) (vv.drop ((rest.length + 2) / 2))
        (by simp only [List.length_drop, List.length_cons] <;> omega) hfR.2
        (fun x' hx' => hιu _ (by
          rw [hmL.2]
          exact prodX_eval_unit x' _ fun y' hy' => by
            rw [← neg_sub]; exact (cross y' hy' x' hx').neg))
        (fun x' hx' => by simp only [eval_add, eval_mul, hmRx x' hx', mul_zero, zero_add])
      have := List.rel_append hL hR
      simp only [List.take_append_drop] at this
      exact this


theorem noOr_interp (z : ℕ) (k : ℕ) : ∀ pts vals : List ℕ, pts.length = k →
    NoOr (interp z pts vals) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro pts vals hpl
  rcases pts with _ | ⟨p, _ | ⟨q, rest⟩⟩
  · rw [interp]; exact noOr_pure _
  · rw [interp]; exact noOr_pure _
  · have hk : k = rest.length + 2 := by simp at hpl; omega
    subst hk
    rw [interp]
    exact noOr_bind _ _ (noOr_prodGen _ _ rfl) fun _ => noOr_bind _ _ (noOr_prodGen _ _ rfl) fun _ =>
      noOr_bind _ _ (noOr_evalAt _ _ _ _) fun _ => noOr_bind _ _ (noOr_scaleInv _ _) fun _ =>
      noOr_bind _ _ (ih ((rest.length + 2) / 2) (by omega) _ _
        (by simp only [List.length_take, List.length_cons] <;> omega)) fun _ =>
      noOr_bind _ _ (noOr_evalAt _ _ _ _) fun _ => noOr_bind _ _ (noOr_scaleInv _ _) fun _ =>
      noOr_bind _ _ (ih (rest.length + 2 - (rest.length + 2) / 2) (by omega) _ _
        (by simp only [List.length_drop, List.length_cons] <;> omega)) fun _ =>
      noOr_bind _ _ (noOr_polyMulG _ _ _) fun _ => noOr_bind _ _ (noOr_polyMulG _ _ _) fun _ =>
      noOr_bind _ _ (noOr_vecAddPad _ _) fun _ => noOr_pure _

theorem interp_node_arith (k : ℕ) (hk : 2 ≤ k) :
    (gG (10 ^ 10) 10 k * (Nat.clog 2 k + 1) + 1) + (gG (10 ^ 10) 10 k * (Nat.clog 2 k + 1) + 1) +
      (10 ^ 16 * (2 * k + 1) * (Nat.log 2 (2 * k + 1) + 1) ^ 11 +
        (gG (10 ^ 21) 12 k * (Nat.clog 2 k + 1) + 1)) + 2 * k +
      (10 ^ 16 * (2 * k + 1) * (Nat.log 2 (2 * k + 1) + 1) ^ 11 +
        (gG (10 ^ 21) 12 k * (Nat.clog 2 k + 1) + 1)) + 2 * k + Bd k + Bd k + 2 * k + 2 ≤
      gG (10 ^ 23) 14 k := by
  have hn := mpe_node_arith k hk
  have hc := clog_le_log2 k (by omega)
  have hBk : Bd k ≤ 10 ^ 9 * (2 * k) * (Nat.log 2 (2 * k) + 1) ^ 10 := by
    unfold Bd
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
      (Nat.pow_le_pow_left (by have := Nat.log_mono_right (b := 2) (show k + 1 ≤ 2 * k by omega); omega) _)
  unfold gG at hn ⊢
  generalize hA : Nat.log 2 (2 * k) + 1 = A at hc hBk hn ⊢
  have hA1 : 1 ≤ A := by omega
  have hEM : 10 ^ 21 * k * A ^ 12 * (Nat.clog 2 k + 1) ≤ 10 ^ 21 * k * A ^ 12 * A :=
    Nat.mul_le_mul_left _ (by omega)
  have hV1 : 1 ≤ k * A ^ 13 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
  have h12 : k * A ^ 12 ≤ k * A ^ 13 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hA1 (by omega))
  have h10 : k * A ^ 10 ≤ k * A ^ 13 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hA1 (by omega))
  have h0 : k ≤ k * A ^ 13 := Nat.le_mul_of_pos_right _ (by positivity)
  have h14 : k * A ^ 13 ≤ k * A ^ 14 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hA1 (by omega))
  have e1 : 10 ^ 21 * k * A ^ 12 * A = 10 ^ 21 * (k * A ^ 13) := by ring
  have e2 : 10 ^ 21 * k * A ^ 12 = 10 ^ 21 * (k * A ^ 12) := by ring
  have e3 : 10 ^ 9 * (2 * k) * A ^ 10 = 2 * 10 ^ 9 * (k * A ^ 10) := by ring
  have e4 : 10 ^ 23 * k * A ^ 14 = 10 ^ 23 * (k * A ^ 14) := by ring
  omega

theorem ops_interp (z : ℕ) (k : ℕ) : ∀ (pts vals : List ℕ) (m : ℕ), pts.length = k →
    (interp z pts vals).ops m ≤ gG (10 ^ 23) 14 k * (Nat.clog 2 k + 1) + 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro pts vals m hpl
  rcases pts with _ | ⟨p, _ | ⟨q, rest⟩⟩
  · rw [interp, ops_pure]; omega
  · rw [interp, ops_pure]; omega
  · have hk : k = rest.length + 2 := by simp at hpl; omega
    subst hk
    have hh1 : (rest.length + 2) / 2 < rest.length + 2 := by omega
    have hh2 : rest.length + 2 - (rest.length + 2) / 2 < rest.length + 2 := by omega
    have hPL := ops_prodGen ((rest.length + 2) / 2)
    have hPR := ops_prodGen (rest.length + 2 - (rest.length + 2) / 2)
    have mP : ∀ j, j ≤ rest.length + 2 → gG (10 ^ 10) 10 j * (Nat.clog 2 j + 1) + 1 ≤
        gG (10 ^ 10) 10 (rest.length + 2) * (Nat.clog 2 (rest.length + 2) + 1) + 1 := fun j hj =>
      Nat.add_le_add_right (Nat.mul_le_mul (gG_mono _ _ hj)
        (Nat.add_le_add_right (Nat.clog_mono_right 2 hj) _)) _
    set PB := gG (10 ^ 10) 10 (rest.length + 2) * (Nat.clog 2 (rest.length + 2) + 1) + 1
    set UE := 10 ^ 16 * (2 * (rest.length + 2) + 1) *
      (Nat.log 2 (2 * (rest.length + 2) + 1) + 1) ^ 11 +
      (gG (10 ^ 21) 12 (rest.length + 2) * (Nat.clog 2 (rest.length + 2) + 1) + 1) with hUE
    have mUE : ∀ a b, a + b ≤ 2 * (rest.length + 2) → b ≤ rest.length + 2 →
        10 ^ 16 * (a + b + 1) * (Nat.log 2 (a + b + 1) + 1) ^ 11 +
          (gG (10 ^ 21) 12 b * (Nat.clog 2 b + 1) + 1) ≤ UE := fun a b hab hb =>
      Nat.add_le_add (HU_mono (by omega)) (Nat.add_le_add_right (Nat.mul_le_mul (gG_mono _ _ hb)
        (Nat.add_le_add_right (Nat.clog_mono_right 2 hb) _)) _)
    set EIL := gG (10 ^ 23) 14 ((rest.length + 2) / 2) *
      (Nat.clog 2 ((rest.length + 2) / 2) + 1) + 1 with hEIL
    set EIR := gG (10 ^ 23) 14 (rest.length + 2 - (rest.length + 2) / 2) *
      (Nat.clog 2 (rest.length + 2 - (rest.length + 2) / 2) + 1) + 1 with hEIR
    set BK := Bd (rest.length + 2)
    set K2 := 2 * (rest.length + 2)
    rw [interp]
    refine le_trans (ops_bind_le _ _ (fun mL => mL.length ≤ (rest.length + 2) / 2 + 1) PB
      (PB + (UE + (K2 + (EIL + (UE + (K2 + (EIR + (BK + (BK + K2))))))))) m
      (le_trans (hPL _ m (by simp only [List.length_take, List.length_cons] <;> omega)) (mP _ (by omega)))
      (le_trans (prodGen_length_le _ _) (by simp only [List.length_take, List.length_cons] <;> omega))
      fun mL n1 hmL => ?_) ?_
    · refine ops_bind_le _ _ (fun mR => mR.length ≤ rest.length + 2 - (rest.length + 2) / 2 + 1) PB _ n1
        (le_trans (hPR _ n1 (by simp only [List.length_drop, List.length_cons] <;> omega)) (mP _ (by omega)))
        (le_trans (prodGen_length_le _ _) (by simp only [List.length_drop, List.length_cons] <;> omega))
        fun mR n2 hmR => ?_
      refine ops_bind_le _ _ (fun eR => eR.length ≤ rest.length + 2) UE _ n2
        (le_trans (ops_evalAt z mR _ mL
          (by simp only [List.length_take, List.length_cons]; omega) n2)
          (mUE _ _ (by simp only [List.length_take, List.length_cons]; omega)
            (by simp only [List.length_take, List.length_cons]; omega)))
        (by rw [evalAt_length]; simp only [List.length_take, List.length_cons]; omega)
        fun eR n3 heR => ?_
      refine ops_bind_le _ _ (fun _ => True) K2 _ n3 (le_trans (ops_scaleInv _ _ n3) (by omega))
        trivial fun vL n4 _ => ?_
      refine ops_bind_le _ _ (fun fL => fL.length = (rest.length + 2) / 2) EIL _ n4
        (ih _ hh1 _ _ n4 (by simp only [List.length_take, List.length_cons] <;> omega))
        (by rw [interp_length]; simp only [List.length_take, List.length_cons] <;> omega)
        fun fL n5 hfL => ?_
      refine ops_bind_le _ _ (fun eL => eL.length ≤ rest.length + 2) UE _ n5
        (le_trans (ops_evalAt z mL _ mR
          (by simp only [List.length_drop, List.length_cons]; omega) n5)
          (mUE _ _ (by simp only [List.length_drop, List.length_cons]; omega)
            (by simp only [List.length_drop, List.length_cons]; omega)))
        (by rw [evalAt_length]; simp only [List.length_drop, List.length_cons]; omega)
        fun eL n6 heL => ?_
      refine ops_bind_le _ _ (fun _ => True) K2 _ n6 (le_trans (ops_scaleInv _ _ n6) (by omega))
        trivial fun vR n7 _ => ?_
      refine ops_bind_le _ _ (fun fR => fR.length = rest.length + 2 - (rest.length + 2) / 2) EIR _ n7
        (ih _ hh2 _ _ n7 (by simp only [List.length_drop, List.length_cons] <;> omega))
        (by rw [interp_length]; simp only [List.length_drop, List.length_cons] <;> omega)
        fun fR n8 hfR => ?_
      refine ops_bind_le _ _ (fun p1 => p1.length ≤ 2 * (rest.length + 2)) BK _ n8
        (ops_polyMulG_Bd _ _ _ (by omega) (by omega) n8) (polyMulG_length _ _ _ _) fun p1 n9 hp1 => ?_
      refine ops_bind_le _ _ (fun p2 => p2.length ≤ 2 * (rest.length + 2)) BK _ n9
        (ops_polyMulG_Bd _ _ _ (by omega) (by omega) n9) (polyMulG_length _ _ _ _) fun p2 n10 hp2 => ?_
      refine le_trans (ops_bind_le _ _ (fun _ => True) K2 0 n10 (by rw [ops_vecAddPad]; omega) trivial
        fun _ _ _ => by rw [ops_pure]) (by omega)
    · exact le_trans (le_of_eq (by ac_rfl))
        (tree_step (gG (10 ^ 23) 14) (gG_sup _ _) (rest.length + 2) (Nat.le_add_left 2 _) EIL EIR
          (PB + PB + UE + K2 + UE + K2 + BK + BK + K2) le_rfl le_rfl
          (interp_node_arith (rest.length + 2) (Nat.le_add_left 2 _)))

/-- Top level: a zero register, then the interpolation recursion. -/
noncomputable def interpProg (K : ℕ) : Gen (List ℕ) :=
  Gen.bind (Gen.emit .zero) fun z => interp z (List.range' 0 K) (List.range' K K)

theorem interpProg_length (K m : ℕ) : ((interpProg K) m).1.length = K := by
  simp only [interpProg, gen_bind_fst]
  rw [interp_length]; simp

theorem noOr_interpProg (K : ℕ) : NoOr (interpProg K) := by
  unfold interpProg
  exact noOr_bind _ _ (noOr_emit _ rfl) fun _ => noOr_interp _ K _ _ (by simp)

theorem ops_interpProg (K m : ℕ) : (interpProg K).ops m ≤
    1 + (gG (10 ^ 23) 14 K * (Nat.clog 2 K + 1) + 1) := by
  unfold interpProg
  exact ops_bind_le _ _ (fun _ => True) _ _ m (by rw [ops_emit]; simp [Instr.isRingOp]) trivial
    fun z n1 _ => ops_interp z K _ _ n1 (by simp)

theorem interpProg_cost_arith (K : ℕ) :
    1 + (gG (10 ^ 23) 14 K * (Nat.clog 2 K + 1) + 1) ≤
      10 ^ 28 * (K + 1) * (Nat.log 2 (K + 1) + 1) ^ 15 := by
  unfold gG
  generalize hL : K + 1 = L
  have hKL : K < L := by omega
  have h2L : Nat.log 2 (2 * L) = Nat.log 2 L + 1 := by
    rw [mul_comm]; exact Nat.log_mul_base (by norm_num) (by omega)
  have hlK : Nat.log 2 (2 * K) ≤ Nat.log 2 L + 1 := by
    rw [← h2L]; exact Nat.log_mono_right (by omega)
  have hcK : Nat.clog 2 K ≤ Nat.log 2 L + 1 := by
    apply Nat.clog_le_of_le_pow
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) L
    omega
  generalize hA : Nat.log 2 L + 1 = A at hlK hcK ⊢
  have hA1 : 1 ≤ A := by omega
  have hp : (Nat.log 2 (2 * K) + 1) ^ 14 ≤ (2 * A) ^ 14 := Nat.pow_le_pow_left (by omega) _
  rw [mul_pow] at hp
  have t : 10 ^ 23 * K * (Nat.log 2 (2 * K) + 1) ^ 14 * (Nat.clog 2 K + 1) ≤
      10 ^ 23 * L * (2 ^ 14 * A ^ 14) * (2 * A) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hKL.le) hp) (by omega)
  have e1 : 10 ^ 23 * L * (2 ^ 14 * A ^ 14) * (2 * A) = 10 ^ 23 * 2 ^ 15 * (L * A ^ 15) := by ring
  have e2 : 10 ^ 28 * L * A ^ 15 = 10 ^ 28 * (L * A ^ 15) := by ring
  have h1 : 1 ≤ L * A ^ 15 :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
  omega

theorem forall2_ofFn {α β : Type*} (Rel : α → β → Prop) :
    ∀ (K : ℕ) (x : Fin K → α) (v : Fin K → β), List.Forall₂ Rel (List.ofFn x) (List.ofFn v) →
      ∀ i, Rel (x i) (v i)
  | 0, x, v, _, i => i.elim0
  | K + 1, x, v, h, i => by
    rw [List.ofFn_succ, List.ofFn_succ, List.forall₂_cons] at h
    exact Fin.cases h.1 (fun j => forall2_ofFn Rel K _ _ h.2 j) i

theorem ofFn_getD_eq {R : Type*} [Zero R] (K : ℕ) (l : List R) (hl : l.length = K) :
    List.ofFn (fun i : Fin K => l.getD i 0) = l := by
  apply List.ext_get (by simp [hl])
  intro i h1 h2
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_ofFn,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

open Polynomial in
theorem triple_interpProg {R : Type*} [CommRing R] [Nontrivial R] (ι : R → R)
    (hι : ∀ u : Rˣ, ι (u : R) = ((u⁻¹ : Rˣ) : R)) (K : ℕ) (x v : Fin K → R)
    (hx : ∀ i j, i ≠ j → IsUnit (x i - x j)) (P : List R → Prop) (hP : Stable P)
    (hxs : ∀ regs, P regs → HoldsVec regs (List.range' 0 K) (List.ofFn x))
    (hvs : ∀ regs, P regs → HoldsVec regs (List.range' K K) (List.ofFn v)) :
    Triple ι (interpProg K) P (fun out regs => P regs ∧ ∃ fv : List R,
      HoldsVec regs out fv ∧ fv.length = K ∧
        List.Forall₂ (fun x v => (toPoly fv).eval x = v) (List.ofFn x) (List.ofFn v)) := by
  unfold interpProg
  refine triple_bind ι _ _ P _ _ (triple_emit_zero ι P hP) fun z => ?_
  have S1 := stable_and _ _ hP (stable_holds z (0 : R))
  have hpw : (List.ofFn x).Pairwise (fun a b => IsUnit (a - b)) :=
    List.pairwise_ofFn.mpr fun i j hij => hx i j (ne_of_lt hij)
  intro regs h
  obtain ⟨new, e1, e2, e3⟩ := triple_interp ι hι z K _ _ (List.ofFn x) (List.ofFn v) (by simp)
    (by simp) (by simp) hpw _ S1 (fun r h => hxs r h.1) (fun r h => hvs r h.1) (fun r h => h.2)
    regs h
  exact ⟨new, e1, e2, e3.1.1, e3.2⟩

/-- **ChildD (fast interpolation, MCA Cor 10.12)**. -/
theorem interp_main : ∃ (C k : ℕ) (I : ℕ → SLP), ∀ K : ℕ,
    ringOps (I K) ≤ C * (K + 1) * (Nat.log 2 (K + 1) + 1) ^ k ∧ oracleCalls (I K) = [] ∧
    ∀ (R : Type) [CommRing R] (ι : R → R), (∀ x : Rˣ, ι (x : R) = ((x⁻¹ : Rˣ) : R)) →
      ∀ (x v : Fin K → R), (∀ i j, i ≠ j → IsUnit (x i - x j)) →
        ∃ a : Fin K → R, (∀ i, (densePoly a).eval (x i) = v i) ∧
          run ι (I K) (List.ofFn x ++ List.ofFn v) = List.ofFn a := by
  refine ⟨10 ^ 28, 15, fun K => ⟨((interpProg K) (K + K)).2.1, ((interpProg K) (K + K)).1⟩,
    fun K => ⟨?_, ?_, ?_⟩⟩
  · rw [ringOps_gen]; exact le_trans (ops_interpProg K _) (interpProg_cost_arith K)
  · exact oracleCalls_gen_nil _ _ (noOr_interpProg K _)
  · intro R _ ι hι x v hx
    have hlen : (List.ofFn x ++ List.ofFn v).length = K + K := by simp
    have hol : (run ι ⟨((interpProg K) (K + K)).2.1, ((interpProg K) (K + K)).1⟩
        (List.ofFn x ++ List.ofFn v)).length = K := by
      simp only [run, List.length_map]; exact interpProg_length _ _
    refine ⟨fun i => (run ι ⟨((interpProg K) (K + K)).2.1, ((interpProg K) (K + K)).1⟩
        (List.ofFn x ++ List.ofFn v)).getD i 0, ?_, (ofFn_getD_eq K _ hol).symm⟩
    rcases subsingleton_or_nontrivial R with hR | hR
    · intro i; exact Subsingleton.elim _ _
    · let P : List R → Prop := fun regs => HoldsVec regs (List.range' 0 K) (List.ofFn x) ∧
        HoldsVec regs (List.range' K K) (List.ofFn v)
      have hP : Stable P := stable_and _ _ (stable_holdsVec _ _) (stable_holdsVec _ _)
      have T := triple_interpProg ι hι K x v hx P hP (fun _ h => h.1) (fun _ h => h.2)
      have h0 : P (List.ofFn x ++ List.ofFn v) := by
        refine ⟨?_, ?_⟩
        · have := holdsVec_range' (List.ofFn x) []
          simp only [List.nil_append, List.length_nil, List.length_ofFn] at this
          exact holdsVec_append _ _ _ _ this
        · have := holdsVec_range' (List.ofFn v) (List.ofFn x)
          simpa only [List.length_ofFn] using this
      have := run_of_triple ι (interpProg K) P _
        (fun vs => ∀ i, (toPoly vs).eval (x i) = v i) T
        (fun out regs hq => by
          obtain ⟨-, fv, h1, -, h3⟩ := hq
          exact ⟨fv, h1, forall2_ofFn _ K x v h3⟩) _ h0
      rw [hlen] at this
      intro i
      rw [densePoly_eq_toPoly, ofFn_getD_eq K _ hol]
      exact this i



/-! S7: Kronecker substitution identity and interpolation uniqueness (pure algebra). -/

/-- Regrouping the `l * m` base-`d₀` digits into `m` numbers below `d₀ ^ l`. -/
def kronE (l m d₀ : ℕ) : (Fin (l * m) → Fin d₀) ≃ (Fin m → Fin (d₀ ^ l)) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl (Fin d₀))).trans <|
  (Equiv.arrowCongr (Equiv.prodComm (Fin l) (Fin m)) (Equiv.refl (Fin d₀))).trans <|
  (Equiv.curry (Fin m) (Fin l) (Fin d₀)).trans <|
  Equiv.arrowCongr (Equiv.refl (Fin m)) finFunctionFinEquiv

theorem kronE_apply (l m d₀ : ℕ) (e : Fin (l * m) → Fin d₀) (i : Fin m) :
    kronE l m d₀ e i = finFunctionFinEquiv (fun j : Fin l => e (finProdFinEquiv (j, i))) := rfl

theorem prod_kron {S : Type*} [CommRing S] (l m d₀ : ℕ) (a : Fin m → S)
    (e : Fin (l * m) → Fin d₀) :
    ∏ t : Fin (l * m), a (finProdFinEquiv.symm t).2 ^
        (d₀ ^ ((finProdFinEquiv.symm t).1 : ℕ) * (e t : ℕ)) =
      ∏ i, a i ^ (kronE l m d₀ e i : ℕ) := by
  rw [← Equiv.prod_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.prod_prod_type, Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [kronE_apply, finFunctionFinEquiv_apply, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem kron_sum {S : Type*} [CommRing S] (l m d₀ : ℕ) (a : Fin m → S)
    (c : (Fin m → Fin (d₀ ^ l)) → S) :
    ∑ e : Fin (l * m) → Fin d₀, c (kronE l m d₀ e) *
        ∏ t : Fin (l * m), a (finProdFinEquiv.symm t).2 ^
          (d₀ ^ ((finProdFinEquiv.symm t).1 : ℕ) * (e t : ℕ)) =
      ∑ E : Fin m → Fin (d₀ ^ l), c E * ∏ i, a i ^ (E i : ℕ) := by
  simp_rw [prod_kron]
  exact Equiv.sum_comp (kronE l m d₀) (fun E => c E * ∏ i, a i ^ (E i : ℕ))

/-- Extension of a coefficient table by zero to larger digit ranges. -/
noncomputable def extF {S : Type*} [Zero S] {m d D : ℕ} (f : (Fin m → Fin d) → S)
    (E : Fin m → Fin D) : S :=
  if h : ∀ i, (E i : ℕ) < d then f (fun i => ⟨E i, h i⟩) else 0

theorem ext_sum {S : Type*} [CommRing S] {m d D : ℕ} (hdD : d ≤ D) (f : (Fin m → Fin d) → S)
    (a : Fin m → S) :
    ∑ E : Fin m → Fin D, extF f E * ∏ i, a i ^ (E i : ℕ) =
      ∑ e : Fin m → Fin d, f e * ∏ i, a i ^ (e i : ℕ) := by
  symm
  refine Fintype.sum_of_injective (fun e i => Fin.castLE hdD (e i)) ?_ _ _ ?_ ?_
  · intro e₁ e₂ h
    funext i
    have := congrFun h i
    exact Fin.castLE_injective hdD this
  · intro E hE
    have : ¬ ∀ i, (E i : ℕ) < d := by
      intro h
      exact hE ⟨fun i => ⟨E i, h i⟩, funext fun i => Fin.ext rfl⟩
    simp [extF, this]
  · intro e
    have h : ∀ i, ((e i : Fin d) : ℕ) < d := fun i => (e i).2
    simp only [extF, Fin.val_castLE]
    rw [dif_pos h]

/-- The full Kronecker identity. -/
theorem kron_full {S : Type*} [CommRing S] (l m d d₀ : ℕ) (hd : d ≤ d₀ ^ l)
    (f : (Fin m → Fin d) → S) (a : Fin m → S) :
    ∑ e : Fin (l * m) → Fin d₀, extF f (kronE l m d₀ e) *
        ∏ t : Fin (l * m), a (finProdFinEquiv.symm t).2 ^
          (d₀ ^ ((finProdFinEquiv.symm t).1 : ℕ) * (e t : ℕ)) =
      ∑ e : Fin m → Fin d, f e * ∏ i, a i ^ (e i : ℕ) := by
  rw [kron_sum l m d₀ a (extF f), ext_sum hd]

open Polynomial in
theorem aeval_densePolyMv {R : Type*} [CommRing R] {m d : ℕ} (f : (Fin m → Fin d) → R)
    (P : Fin m → R[X]) :
    MvPolynomial.aeval P (densePolyMv f) = ∑ e : Fin m → Fin d, C (f e) * ∏ i, P i ^ (e i : ℕ) := by
  unfold densePolyMv
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  simp

open Polynomial in
/-- A polynomial of degree below the number of nodes (pairwise unit differences) that
vanishes at every node is zero. -/
theorem interp_unique {R : Type*} [CommRing R] [Nontrivial R] :
    ∀ (xs : List R), xs.Pairwise (fun a b => IsUnit (a - b)) → ∀ P : R[X],
      (∀ x ∈ xs, P.eval x = 0) → P.natDegree < xs.length → P = 0
  | [], _, P, _, h => by simp at h
  | x :: xs, hpw, P, hz, hdeg => by
    have hroot : IsRoot P x := hz x (by simp)
    have hfac := mul_divByMonic_eq_iff_isRoot.mpr hroot
    set Q := P /ₘ (X - C x)
    rw [List.pairwise_cons] at hpw
    have hQ : Q = 0 := by
      by_contra hQ0
      have hdeg' : P.natDegree = 1 + Q.natDegree := by
        rw [← hfac, (monic_X_sub_C x).natDegree_mul' hQ0, natDegree_X_sub_C]
      refine hQ0 (interp_unique xs hpw.2 Q (fun y hy => ?_) (by simp at hdeg; omega))
      have h1 : P.eval y = 0 := hz y (by simp [hy])
      rw [← hfac, eval_mul, eval_sub, eval_X, eval_C] at h1
      have hu : IsUnit (y - x) := by
        have := hpw.1 y hy
        rw [show y - x = -(x - y) by ring]
        exact this.neg
      exact (hu.mul_right_eq_zero).mp h1
    rw [← hfac, hQ, mul_zero]

open Polynomial in
theorem natDegree_mmePoly_le {R : Type*} [CommRing R] (m' d₀ D : ℕ)
    (c : (Fin m' → Fin d₀) → R) (Q : Fin m' → R[X]) (hQ : ∀ t, (Q t).natDegree ≤ D) :
    (∑ e : Fin m' → Fin d₀, C (c e) * ∏ t, Q t ^ (e t : ℕ)).natDegree ≤ m' * ((d₀ - 1) * D) := by
  refine natDegree_sum_le_of_forall_le _ _ fun e _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ t, (Q t ^ (e t : ℕ)).natDegree ≤ ∑ _t : Fin m', (d₀ - 1) * D := by
        refine Finset.sum_le_sum fun t _ => (natDegree_pow_le).trans ?_
        exact Nat.mul_le_mul (by have := (e t).2; omega) (hQ t)
    _ = m' * ((d₀ - 1) * D) := by simp

open Polynomial in
theorem eval_mmePoly {R : Type*} [CommRing R] (m' d₀ : ℕ)
    (c : (Fin m' → Fin d₀) → R) (Q : Fin m' → R[X]) (x : R) :
    (∑ e : Fin m' → Fin d₀, C (c e) * ∏ t, Q t ^ (e t : ℕ)).eval x =
      ∑ e : Fin m' → Fin d₀, c e * ∏ t, (Q t).eval x ^ (e t : ℕ) := by
  simp [eval_finsetSum, eval_prod]

open Polynomial in
/-- Congruence modulo a monic polynomial gives equal remainders. -/
theorem modByMonic_eq_of_mk_eq {R : Type*} [CommRing R] (p r q : R[X]) (hq : q.Monic)
    (h : Ideal.Quotient.mk (Ideal.span {q}) p = Ideal.Quotient.mk (Ideal.span {q}) r) :
    p %ₘ q = r %ₘ q := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  have := (modByMonic_eq_zero_iff_dvd hq).mpr h
  rw [sub_modByMonic, sub_eq_zero] at this
  exact this

open Polynomial in
theorem mk_modByMonic {R : Type*} [CommRing R] (p q : R[X]) :
    Ideal.Quotient.mk (Ideal.span {q}) (p %ₘ q) = Ideal.Quotient.mk (Ideal.span {q}) p := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  refine ⟨-(p /ₘ q), ?_⟩
  have := modByMonic_add_div p q
  linear_combination this


open Polynomial

/-! ## S6: powers `g^{d₀^j} mod h` -/

/-- `acc * p^k mod hm`, one multiplication and one reduction per factor. -/
noncomputable def mulModIter (N n : ℕ) (hm : List ℕ) (z : ℕ) (p : List ℕ) :
    ℕ → List ℕ → Gen (List ℕ)
  | 0, acc => Gen.pure acc
  | k + 1, acc => Gen.bind (polyMulG N acc p) fun q => Gen.bind (modUB q.length n q hm z) fun r =>
      mulModIter N n hm z p k r

/-- Being congruent to `Q` modulo `hmv`, with at most `N` coefficients. -/
def PolyAt {R : Type*} [CommRing R] (hmv : List R) (N : ℕ) (regs : List R) (rs : List ℕ)
    (Q : R[X] ⧸ Ideal.span {toPoly hmv}) : Prop :=
  ∃ vs : List R, HoldsVec regs rs vs ∧ vs.length ≤ N ∧ Ideal.Quotient.mk _ (toPoly vs) = Q

theorem stable_polyAt {R : Type*} [CommRing R] (hmv : List R) (N : ℕ) (rs : List ℕ)
    (Q : R[X] ⧸ Ideal.span {toPoly hmv}) : Stable (fun regs => PolyAt hmv N regs rs Q) :=
  fun regs new ⟨vs, h1, h2, h3⟩ => ⟨vs, holdsVec_append _ _ _ _ h1, h2, h3⟩

theorem triple_mulModIter {R : Type*} [CommRing R] [Nontrivial R] (ι : R → R) (N n : ℕ)
    (hm : List ℕ) (z : ℕ) (p : List ℕ) (hmv pv : List R) (hml : hmv.length = n + 1)
    (hcoef : (toPoly hmv).coeff n = 1) (hnN : n ≤ N) (hpl : pv.length ≤ N) :
    ∀ (k : ℕ) (acc : List ℕ) (av : List R), av.length ≤ N →
    ∀ (P : List R → Prop), Stable P → (∀ regs, P regs → HoldsVec regs p pv) →
      (∀ regs, P regs → HoldsVec regs hm hmv) → (∀ regs, P regs → Holds regs z 0) →
      (∀ regs, P regs → HoldsVec regs acc av) →
      Triple ι (mulModIter N n hm z p k acc) P (fun out regs => P regs ∧ ∃ rv : List R,
        HoldsVec regs out rv ∧ rv.length ≤ N ∧
        Ideal.Quotient.mk (Ideal.span {toPoly hmv}) (toPoly rv) =
          Ideal.Quotient.mk (Ideal.span {toPoly hmv}) (toPoly av * toPoly pv ^ k))
  | 0, acc, av, hal, P, hP, hp, hhm, hz, hacc => by
    rw [mulModIter]
    exact triple_pure ι _ _ _ fun regs h => ⟨h, av, hacc regs h, hal, by simp⟩
  | k + 1, acc, av, hal, P, hP, hp, hhm, hz, hacc => by
    rw [mulModIter]
    refine triple_bind_vec ι _ _ P
      (fun zs => toPoly zs = toPoly av * toPoly pv ∧ zs.length = 2 * N) _ ?_ ?_
    · intro regs h
      obtain ⟨new, e1, e2, e3⟩ := triple_polyMulG ι N acc p av pv hal hpl P hP hacc hp regs h
      obtain ⟨hP', zs, hzs, hzeq⟩ := e3
      refine ⟨new, e1, e2, hP', zs, hzs, ?_, ?_⟩
      · rw [hzeq]; exact toPoly_polyMul_out N av pv hal hpl
      · rw [hzeq]; simp
    · intro zs q ⟨hzp, hzl⟩ hql
      have S1 := stable_and _ _ hP (stable_holdsVec q zs)
      refine triple_bind_vec ι _ _ _
        (fun rv => rv.length = n ∧ toPoly rv = toPoly zs %ₘ toPoly hmv) _ ?_ ?_
      · intro regs h
        obtain ⟨new, e1, e2, e3⟩ := triple_modUB ι q.length n q hm z zs hmv hql.symm hml hcoef _ S1
          (fun r h => h.2) (fun r h => hhm r h.1) (fun r h => hz r h.1) regs h
        obtain ⟨hP', rv, h1, h2, h3⟩ := e3
        exact ⟨new, e1, e2, hP', rv, h1, h2, h3⟩
      · intro rv r ⟨hrl, hrp⟩ _
        have S2 := stable_and _ _ S1 (stable_holdsVec r rv)
        have T := triple_mulModIter ι N n hm z p hmv pv hml hcoef hnN hpl k r rv (by omega) _ S2
          (fun r h => hp r h.1.1) (fun r h => hhm r h.1.1) (fun r h => hz r h.1.1) (fun r h => h.2)
        intro regs h
        obtain ⟨new, e1, e2, e3⟩ := T regs h
        refine ⟨new, e1, e2, e3.1.1.1, ?_⟩
        obtain ⟨rv', h1, h2, h3⟩ := e3.2
        refine ⟨rv', h1, h2, ?_⟩
        rw [h3, map_mul, hrp, mk_modByMonic, hzp]
        simp only [map_mul, map_pow]
        ring

/-- The chain `p, p^{d₀}, p^{d₀^2}, …` (`k` entries) modulo `hm`. -/
noncomputable def powChain (N n d₀ : ℕ) (hm : List ℕ) (z : ℕ) : ℕ → List ℕ → Gen (List (List ℕ))
  | 0, _ => Gen.pure []
  | k + 1, p => Gen.bind (mulModIter N n hm z p (d₀ - 1) p) fun q =>
      Gen.bind (powChain N n d₀ hm z k q) fun rest => Gen.pure (p :: rest)

theorem triple_powChain {R : Type*} [CommRing R] [Nontrivial R] (ι : R → R) (N n d₀ : ℕ)
    (hd₀ : 1 ≤ d₀) (hm : List ℕ) (z : ℕ) (hmv : List R) (hml : hmv.length = n + 1)
    (hcoef : (toPoly hmv).coeff n = 1) (hnN : n ≤ N) :
    ∀ (k : ℕ) (p : List ℕ) (pv : List R), pv.length ≤ N →
    ∀ (P : List R → Prop), Stable P → (∀ regs, P regs → HoldsVec regs p pv) →
      (∀ regs, P regs → HoldsVec regs hm hmv) → (∀ regs, P regs → Holds regs z 0) →
      Triple ι (powChain N n d₀ hm z k p) P (fun out regs => P regs ∧ out.length = k ∧
        ∀ j < k, PolyAt hmv N regs (out.getD j [])
          (Ideal.Quotient.mk (Ideal.span {toPoly hmv}) (toPoly pv) ^ (d₀ ^ j)))
  | 0, p, pv, hpl, P, hP, hp, hhm, hz => by
    rw [powChain]
    exact triple_pure ι _ _ _ fun regs h => ⟨h, rfl, fun j hj => absurd hj (by omega)⟩
  | k + 1, p, pv, hpl, P, hP, hp, hhm, hz => by
    rw [powChain]
    refine triple_bind_vec ι _ _ P (fun rv => rv.length ≤ N ∧
      Ideal.Quotient.mk (Ideal.span {toPoly hmv}) (toPoly rv) =
        Ideal.Quotient.mk (Ideal.span {toPoly hmv}) (toPoly pv) ^ d₀) _ ?_ ?_
    · intro regs h
      obtain ⟨new, e1, e2, e3⟩ := triple_mulModIter ι N n hm z p hmv pv hml hcoef hnN hpl
        (d₀ - 1) p pv hpl P hP hp hhm hz hp regs h
      obtain ⟨hP', rv, h1, h2, h3⟩ := e3
      refine ⟨new, e1, e2, hP', rv, h1, h2, ?_⟩
      rw [h3, map_mul, map_pow, ← pow_succ']
      congr 1; omega
    · intro rv q ⟨hrl, hrq⟩ _
      have S1 := stable_and _ _ hP (stable_holdsVec q rv)
      refine triple_bind ι _ _ _ _ _ (triple_powChain ι N n d₀ hd₀ hm z hmv hml hcoef hnN k q rv
        hrl _ S1 (fun r h => h.2) (fun r h => hhm r h.1) (fun r h => hz r h.1)) fun rest => ?_
      refine triple_pure ι _ _ _ fun regs h => ⟨h.1.1, by simp [h.2.1], fun j hj => ?_⟩
      rcases j with _ | j
      · exact ⟨pv, hp regs h.1.1, hpl, by simp⟩
      · have := h.2.2 j (by omega)
        simp only [List.getD_cons_succ]
        rw [hrq, ← pow_mul, ← pow_succ'] at this
        exact this

/-! ## S8a: oracle argument lists and the tail (oracle call, interpolation, reduction) -/

/-- Coefficient registers for the oracle: `f` re-expanded in `l*m` variables of degree `< d₀`. -/
noncomputable def csList (l m d d₀ z : ℕ) : List ℕ :=
  List.ofFn fun p : Fin (d₀ ^ (l * m)) =>
    if h : ∀ i, (kronE l m d₀ (finFunctionFinEquiv.symm p) i : ℕ) < d then
      (finFunctionFinEquiv (fun i => (⟨kronE l m d₀ (finFunctionFinEquiv.symm p) i, h i⟩ : Fin d)) : ℕ)
    else z

/-- Point registers for the oracle: coordinate `t` of point `k` at position `k * M + t`. -/
def psList (M K : ℕ) (outs : List (List ℕ)) : List ℕ :=
  List.ofFn fun q : Fin (K * M) => (outs.getD (q % M) []).getD (q / M) 0

theorem regAt_ofFn {R : Type*} [CommRing R] (regs : List R) (L : ℕ) (F : Fin L → ℕ) (p : ℕ)
    (hp : p < L) : regAt regs (List.ofFn F) p = reg regs (F ⟨p, hp⟩) := by
  unfold regAt
  rw [List.getElem?_ofFn, dif_pos hp]

theorem holds_getD_ofFn {R : Type*} [CommRing R] (regs : List R) (rs : List ℕ) (L : ℕ)
    (w : Fin L → R) (h : HoldsVec regs rs (List.ofFn w)) (k : Fin L) :
    Holds regs (rs.getD k 0) (w k) := by
  have hl := holdsVec_length _ _ _ h
  have := holdsVec_getD regs rs _ h k (by rw [hl]; simp)
  rwa [List.getD_eq_getElem?_getD (l := List.ofFn w), List.getElem?_ofFn, dif_pos k.2,
    Option.getD_some] at this

theorem holds_range_ofFn {R : Type*} [CommRing R] (regs : List R) (s L : ℕ) (w : Fin L → R)
    (h : HoldsVec regs (List.range' s L) (List.ofFn w)) (k : Fin L) :
    Holds regs (s + k) (w k) := by
  have := holds_getD_ofFn regs _ L w h k
  have e : (List.range' s L).getD k 0 = s + k := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_range' k.2]
    simp
  rwa [e] at this

theorem regAt_csList {R : Type*} [CommRing R] (regs : List R) (l m d d₀ z : ℕ)
    (f : (Fin m → Fin d) → R)
    (hf : HoldsVec regs (List.range' 0 (d ^ m))
      (List.ofFn fun k : Fin (d ^ m) => f (finFunctionFinEquiv.symm k)))
    (hz : Holds regs z 0) (e : Fin (l * m) → Fin d₀) :
    regAt regs (csList l m d d₀ z) (finFunctionFinEquiv e) = extF f (kronE l m d₀ e) := by
  unfold csList
  rw [regAt_ofFn _ _ _ _ (finFunctionFinEquiv e).2]
  simp only [Fin.eta, Equiv.symm_apply_apply]
  unfold extF
  split_ifs with h
  · have := holds_range_ofFn regs 0 _ _ hf
      (finFunctionFinEquiv (fun i => (⟨kronE l m d₀ e i, h i⟩ : Fin d)))
    rw [zero_add] at this
    rw [holds_reg _ _ _ this, Equiv.symm_apply_apply]
  · exact holds_reg _ _ _ hz

theorem regAt_psList {R : Type*} [CommRing R] (regs : List R) (M K : ℕ) (outs : List (List ℕ))
    (w : Fin K → Fin M → R)
    (h : ∀ t : Fin M, HoldsVec regs (outs.getD t []) (List.ofFn fun k => w k t))
    (k : Fin K) (t : Fin M) : regAt regs (psList M K outs) (k * M + t) = w k t := by
  have h3 : ((k : ℕ) + 1) * M ≤ K * M := Nat.mul_le_mul_right M (Nat.succ_le_of_lt k.2)
  rw [Nat.add_mul, one_mul] at h3
  have hlt : (k : ℕ) * M + t < K * M := by have := t.2; omega
  unfold psList
  rw [regAt_ofFn _ _ _ _ hlt]
  have h1 : ((k : ℕ) * M + t) % M = t := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt t.2]
  have h2 : ((k : ℕ) * M + t) / M = k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by have := t.2; omega), Nat.div_eq_of_lt t.2,
      zero_add]
  show reg regs ((outs.getD (((k : ℕ) * M + t) % M) []).getD (((k : ℕ) * M + t) / M) 0) = _
  rw [h1, h2]
  exact holds_reg _ _ _ (holds_getD_ofFn regs _ K (fun k => w k t) (h t) k)

theorem triple_tail {R : Type*} [CommRing R] [Nontrivial R] (ι : R → R)
    (hι : ∀ u : Rˣ, ι (u : R) = ((u⁻¹ : Rˣ) : R)) (d₀ M K n : ℕ) (cs bs hm : List ℕ) (z : ℕ)
    (outs : List (List ℕ)) (cf : (Fin M → Fin d₀) → R) (Qf : Fin M → R[X]) (β : Fin K → R)
    (hmv : List R) (hml : hmv.length = n + 1) (hcoef : (toPoly hmv).coeff n = 1)
    (hbl : bs.length = K) (hβ : ∀ i j, i ≠ j → IsUnit (β i - β j))
    (hdeg : (∑ e : Fin M → Fin d₀, C (cf e) * ∏ t, Qf t ^ (e t : ℕ)).natDegree < K)
    (P : List R → Prop) (hP : Stable P)
    (hcs : ∀ regs, P regs → ∀ e, regAt regs cs (finFunctionFinEquiv e) = cf e)
    (hout : ∀ regs, P regs → ∀ t : Fin M,
      HoldsVec regs (outs.getD t []) (List.ofFn fun k => (Qf t).eval (β k)))
    (hbs : ∀ regs, P regs → HoldsVec regs bs (List.ofFn β))
    (hhm : ∀ regs, P regs → HoldsVec regs hm hmv) (hz : ∀ regs, P regs → Holds regs z 0) :
    Triple ι (Gen.bind (Gen.emitMME d₀ M K cs (psList M K outs)) fun vals =>
        Gen.bind (interp z bs vals) fun fv => modUB fv.length n fv hm z) P
      (fun out regs => P regs ∧ ∃ rv : List R, HoldsVec regs out rv ∧ rv.length = n ∧
        toPoly rv = (∑ e : Fin M → Fin d₀, C (cf e) * ∏ t, Qf t ^ (e t : ℕ)) %ₘ toPoly hmv) := by
  set Fp := ∑ e : Fin M → Fin d₀, C (cf e) * ∏ t, Qf t ^ (e t : ℕ) with hFp
  have hK : 0 < K := by omega
  have hmme : mmeSpec cf (fun k t => (Qf t).eval (β k)) = fun k => Fp.eval (β k) := by
    funext k; rw [hFp, eval_mmePoly]; rfl
  refine triple_bind ι _ _ P _ _ (triple_emitMME ι d₀ M K cs (psList M K outs) cf
    (fun k t => (Qf t).eval (β k)) P hP hcs
    (fun regs h k t => regAt_psList regs M K outs (fun k t => (Qf t).eval (β k)) (hout regs h) k t))
    fun vals => ?_
  rw [hmme]
  have S1 := stable_and _ _ hP (stable_holdsVec vals (List.ofFn fun k => Fp.eval (β k)))
  have hpw : (List.ofFn β).Pairwise (fun a b => IsUnit (a - b)) :=
    List.pairwise_ofFn.mpr fun i j hij => hβ i j (ne_of_lt hij)
  refine triple_bind_vec ι _ _ _ (fun fv => fv.length = K ∧ toPoly fv = Fp) _ ?_ ?_
  · intro regs h
    obtain ⟨new, e1, e2, e3⟩ := triple_interp ι hι z K bs vals (List.ofFn β)
      (List.ofFn fun k => Fp.eval (β k)) hbl (by simp) (by simp) hpw _ S1
      (fun r h => hbs r h.1) (fun r h => h.2) (fun r h => hz r h.1) regs h
    obtain ⟨hP', fv, h1, h2, h3⟩ := e3
    refine ⟨new, e1, e2, hP', fv, h1, h2, ?_⟩
    have hz' := interp_unique (List.ofFn β) hpw (toPoly fv - Fp) ?_ ?_
    · exact sub_eq_zero.mp hz'
    · intro x hx
      rw [List.mem_ofFn] at hx
      obtain ⟨k, rfl⟩ := hx
      have := forall2_ofFn _ K β _ h3 k
      rw [eval_sub, this, sub_self]
    · have a1 := toPoly_natDegree_le fv
      have a2 := natDegree_sub_le (toPoly fv) Fp
      simp only [List.length_ofFn]
      omega
  · intro fvv fv ⟨hfl, hfp⟩ hl
    have S2 := stable_and _ _ S1 (stable_holdsVec fv fvv)
    intro regs h
    obtain ⟨new, e1, e2, e3⟩ := triple_modUB ι fv.length n fv hm z fvv hmv hl.symm hml hcoef _ S2
      (fun r h => h.2) (fun r h => hhm r h.1.1) (fun r h => hz r h.1.1) regs h
    obtain ⟨hP', rv, h1, h2, h3⟩ := e3
    exact ⟨new, e1, e2, hP'.1.1, rv, h1, h2, by rw [h3, hfp]⟩

/-! ## S8b: the main program (case `m ≥ 1`) and its correctness -/

/-- Coefficients of `g_i` (empty out of range). -/
noncomputable def gpL {R : Type*} {m N : ℕ} (g : Fin m → Fin N → R) (i : ℕ) : List R :=
  if hi : i < m then List.ofFn (g ⟨i, hi⟩) else []

theorem kron_mod {R : Type*} [CommRing R] (l m d d₀ N : ℕ) (hdl : d ≤ d₀ ^ l) (q : R[X])
    (f : (Fin m → Fin d) → R) (g : Fin m → Fin N → R) (Qf : Fin (l * m) → R[X])
    (hQ : ∀ t, Ideal.Quotient.mk (Ideal.span {q}) (Qf t) =
      Ideal.Quotient.mk (Ideal.span {q}) (densePoly (g (finProdFinEquiv.symm t).2)) ^
        (d₀ ^ ((finProdFinEquiv.symm t).1 : ℕ))) :
    Ideal.Quotient.mk (Ideal.span {q})
        (∑ e : Fin (l * m) → Fin d₀, C (extF f (kronE l m d₀ e)) * ∏ t, Qf t ^ (e t : ℕ)) =
      Ideal.Quotient.mk (Ideal.span {q}) (MvPolynomial.aeval (fun i => densePoly (g i))
        (densePolyMv f)) := by
  rw [aeval_densePolyMv]
  simp only [map_sum, map_mul, map_prod, map_pow, hQ, ← pow_mul]
  rw [← kron_full l m d d₀ hdl (fun e => Ideal.Quotient.mk (Ideal.span {q}) (C (f e)))
    (fun i => Ideal.Quotient.mk (Ideal.span {q}) (densePoly (g i)))]
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 1
  unfold extF
  split_ifs <;> simp

noncomputable def mainGen (d d₀ m N n l D K : ℕ) : Gen (List ℕ) :=
  Gen.bind (Gen.emit (.inv (D + m * N + n))) fun ui =>
  Gen.bind (vecSmul ui (List.range' (D + m * N) (n + 1))) fun hm =>
  Gen.bind (Gen.emit .zero) fun z =>
  Gen.bind (mapGen (fun i => powChain N n d₀ hm z l (List.range' (D + i * N) N))
    (List.range' 0 m)) fun pw =>
  Gen.bind (mapGen (fun t => mpe z (List.range' (D + m * N + (n + 1)) K)
    ((pw.getD (t % m) []).getD (t / m) [])) (List.range' 0 (l * m))) fun outs =>
  Gen.bind (Gen.emitMME d₀ (l * m) K (csList l m d d₀ z) (psList (l * m) K outs)) fun vals =>
  Gen.bind (interp z (List.range' (D + m * N + (n + 1)) K) vals) fun fv =>
  modUB fv.length n fv hm z

set_option maxHeartbeats 1000000 in
theorem triple_main {R : Type*} [CommRing R] [Nontrivial R] (ι : R → R)
    (hι : ∀ u : Rˣ, ι (u : R) = ((u⁻¹ : Rˣ) : R)) (d d₀ m N n l D K : ℕ) (hd₀ : 2 ≤ d₀)
    (hm1 : 1 ≤ m) (hnN : n + 1 ≤ N) (hl1 : 1 ≤ l) (hdl : d ≤ d₀ ^ l) (hD : D = d ^ m)
    (hK : K = N * m * l * d₀)
    (f : (Fin m → Fin d) → R) (g : Fin m → Fin N → R) (h : Fin (n + 1) → R) (u : Rˣ)
    (β : Fin K → R) (hu : (u : R) = h (Fin.last n))
    (hβ : ∀ i j, i ≠ j → IsUnit (β i - β j))
    (P : List R → Prop) (hP : Stable P)
    (hf : ∀ regs, P regs → HoldsVec regs (List.range' 0 (d ^ m))
      (List.ofFn fun k : Fin (d ^ m) => f (finFunctionFinEquiv.symm k)))
    (hg : ∀ regs, P regs → ∀ i : Fin m,
      HoldsVec regs (List.range' (D + i * N) N) (List.ofFn (g i)))
    (hh : ∀ regs, P regs → HoldsVec regs (List.range' (D + m * N) (n + 1)) (List.ofFn h))
    (hb : ∀ regs, P regs → HoldsVec regs (List.range' (D + m * N + (n + 1)) K) (List.ofFn β)) :
    Triple ι (mainGen d d₀ m N n l D K) P
      (fun out regs => P regs ∧ ∃ rv : List R, HoldsVec regs out rv ∧ rv.length = n ∧
        toPoly rv = (MvPolynomial.aeval (fun i => densePoly (g i)) (densePolyMv f)) %ₘ
          (densePoly h * C ((u⁻¹ : Rˣ) : R))) := by
  have hNK : N ≤ K := by
    rw [hK]
    calc N = N * 1 * 1 * 1 := by ring
      _ ≤ N * m * l * d₀ := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl hm1) hl1)
          (by omega)
  -- the monic associate of h
  set hmv : List R := (List.ofFn h).map (ι (u : R) * ·) with hhmv
  have hml : hmv.length = n + 1 := by simp [hhmv]
  have hmp : toPoly hmv = densePoly h * C ((u⁻¹ : Rˣ) : R) := by
    rw [hhmv, toPoly_map_mul, hι, mul_comm, densePoly_eq_toPoly]
  have hcoef : (toPoly hmv).coeff n = 1 := by
    rw [toPoly_coeff, hhmv, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_ofFn,
      dif_pos (by omega)]
    simp only [Option.map_some, Option.getD_some]
    rw [show (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n from rfl, ← hu, hι]
    exact Units.inv_mul u
  have hmonic : (toPoly hmv).Monic :=
    monic_of_natDegree_le_of_coeff_eq_one n
      (by have := toPoly_natDegree_le hmv; rw [hml] at this; omega) hcoef
  have hget : ∀ regs, P regs → Holds regs (D + m * N + n) (u : R) := fun regs hr => by
    have := holds_range_ofFn regs _ _ h (hh regs hr) (Fin.last n)
    rwa [Fin.val_last, ← hu] at this
  unfold mainGen
  refine triple_bind ι _ _ P _ _ (triple_emit_inv ι _ _ P hP hget) fun ui => ?_
  have S1 := stable_and _ _ hP (stable_holds ui (ι (u : R)))
  refine triple_bind ι _ _ _ _ _ (triple_vecSmul ι ui (ι (u : R)) _ (List.ofFn h) _ S1
    (fun _ h => h.2) (fun _ h => hh _ h.1)) fun hm => ?_
  have S2 := stable_and _ _ S1 (stable_holdsVec hm hmv)
  refine triple_bind ι _ _ _ _ _ (triple_emit_zero ι _ S2) fun z => ?_
  have S3 := stable_and _ _ S2 (stable_holds z (0 : R))
  -- powers
  set π := Ideal.Quotient.mk (Ideal.span {toPoly hmv})
  let Sp : ℕ → List (List ℕ) → List R → Prop := fun i pw regs => pw.length = l ∧
    ∀ j < l, PolyAt hmv N regs (pw.getD j []) (π (toPoly (gpL g i)) ^ (d₀ ^ j))
  have hSp : ∀ i pw, Stable (Sp i pw) := fun i pw regs new hr =>
    ⟨hr.1, fun j hj => stable_polyAt _ _ _ _ regs new (hr.2 j hj)⟩
  refine triple_bind ι _ _ _ _ _ (triple_mapGen ι _ Sp hSp (List.range' 0 m) _ S3
    (fun a ha P' hP' hPP => by
      have ha' : a < m := by rw [List.mem_range'_1] at ha; omega
      have hgl : (gpL g a).length ≤ N := by simp [gpL, ha']
      exact triple_powChain ι N n d₀ (by omega) hm z hmv hml hcoef (by omega) l _ (gpL g a) hgl
        P' hP' (fun r hr => by
          have := hg r (hPP r hr).1.1.1 ⟨a, ha'⟩
          simpa [gpL, ha'] using this)
        (fun r hr => (hPP r hr).1.2) (fun r hr => (hPP r hr).2))) fun pw => ?_
  have S4 := stable_and _ _ S3 (fun regs new (hr : List.Forall₂ (fun a b => Sp a b regs)
      (List.range' 0 m) pw) => List.Forall₂.imp (fun a b hab => hSp a b regs new hab) hr)
  -- evaluations
  let Se : ℕ → List ℕ → List R → Prop := fun t out regs => ∃ Q : R[X], Q.natDegree ≤ N - 1 ∧
    π Q = π (toPoly (gpL g (t % m))) ^ (d₀ ^ (t / m)) ∧
    HoldsVec regs out (List.ofFn fun k => Q.eval (β k))
  have hSe : ∀ t out, Stable (Se t out) := fun t out regs new ⟨Q, h1, h2, h3⟩ =>
    ⟨Q, h1, h2, holdsVec_append _ _ _ _ h3⟩
  refine triple_bind ι _ _ _ _ _ (triple_mapGen ι _ Se hSe (List.range' 0 (l * m)) _ S4
    (fun t ht P' hP' hPP => by
      have ht' : t < l * m := by rw [List.mem_range'_1] at ht; omega
      intro regs hr
      have h4 := hPP regs hr
      obtain ⟨-, hpw⟩ := forall₂_range_getD (S := fun a b => Sp a b regs) [] m 0 pw h4.2
      have htm : t % m < m := Nat.mod_lt _ (by omega)
      have htl : t / m < l := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]; exact ht'
      obtain ⟨-, hj⟩ := hpw (t % m) htm
      obtain ⟨vs, hvs, hvl, hvq⟩ := hj (t / m) htl
      have S5 := stable_and _ _ hP' (stable_holdsVec ((pw.getD (t % m) []).getD (t / m) []) vs)
      obtain ⟨new, e1, e2, e3⟩ := triple_mpe ι z (toPoly vs) K _ _ (List.ofFn β) vs
        (by simp) (by simp) (holdsVec_length _ _ _ hvs).symm (by omega) (fun _ _ => rfl) _ S5
        (fun r hr => hb r (hPP r hr.1).1.1.1.1) (fun r hr => hr.2) (fun r hr => (hPP r hr.1).1.2)
        regs ⟨hr, hvs⟩
      refine ⟨new, e1, e2, e3.1.1, toPoly vs, ?_, by rwa [Nat.zero_add] at hvq, ?_⟩
      · have := toPoly_natDegree_le vs; omega
      · rw [List.map_ofFn] at e3; exact e3.2)) fun outs => ?_
  -- fix the evaluated polynomials and run the tail
  intro regs hr
  obtain ⟨-, hout⟩ := forall₂_range_getD (S := fun a b => Se a b regs) [] (l * m) 0 outs hr.2
  have hQex : ∀ t : Fin (l * m), Se t (outs.getD t []) regs := fun t => by
    simpa using hout t t.2
  choose Qf hQdeg hQπ hQv using hQex
  have hQ' : ∀ t : Fin (l * m), π (Qf t) =
      π (densePoly (g (finProdFinEquiv.symm t).2)) ^ (d₀ ^ ((finProdFinEquiv.symm t).1 : ℕ)) := by
    intro t
    rw [hQπ t]
    have htm : (t : ℕ) % m < m := Nat.mod_lt _ (by omega)
    rw [gpL, dif_pos htm, densePoly_eq_toPoly]
    rfl
  let Pt : List R → Prop := fun r => (((((P r ∧ Holds r ui (ι (u : R))) ∧ HoldsVec r hm hmv) ∧
    Holds r z 0) ∧ List.Forall₂ (fun a b => Sp a b r) (List.range' 0 m) pw) ∧
    List.Forall₂ (fun a b => Se a b r) (List.range' 0 (l * m)) outs) ∧
    ∀ t : Fin (l * m), HoldsVec r (outs.getD t []) (List.ofFn fun k => (Qf t).eval (β k))
  have hPt : Stable Pt := by
    refine stable_and _ _ ?_ ?_
    · exact stable_and _ _ S4 (fun regs new (hr : List.Forall₂ (fun a b => Se a b regs)
        (List.range' 0 (l * m)) outs) => List.Forall₂.imp (fun a b hab => hSe a b regs new hab) hr)
    · exact fun regs new hr t => holdsVec_append _ _ _ _ (hr t)
  have hdeg : (∑ e : Fin (l * m) → Fin d₀, C (extF f (kronE l m d₀ e)) *
      ∏ t, Qf t ^ (e t : ℕ)).natDegree < K := by
    refine lt_of_le_of_lt (natDegree_mmePoly_le (l * m) d₀ (N - 1) _ Qf hQdeg) ?_
    have hlm : 0 < l * m := Nat.mul_pos (by omega) (by omega)
    have e1 : K = l * m * (N * d₀) := by rw [hK]; ring
    rw [e1]
    refine Nat.mul_lt_mul_of_pos_left ?_ hlm
    have := Nat.mul_le_mul (Nat.sub_le d₀ 1) (Nat.sub_le N 1)
    have h2 : d₀ * (N - 1) < N * d₀ := by
      rw [mul_comm N]; exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    calc (d₀ - 1) * (N - 1) ≤ d₀ * (N - 1) := Nat.mul_le_mul_right _ (Nat.sub_le d₀ 1)
      _ < N * d₀ := h2
  obtain ⟨new, e1, e2, e3⟩ := triple_tail ι hι d₀ (l * m) K n (csList l m d d₀ z)
    (List.range' (D + m * N + (n + 1)) K) hm z outs (fun e => extF f (kronE l m d₀ e)) Qf β hmv
    hml hcoef (by simp) hβ hdeg Pt hPt
    (fun r hr e => regAt_csList r l m d d₀ z f (hf r hr.1.1.1.1.1.1) hr.1.1.1.2 e)
    (fun r hr => hr.2) (fun r hr => hb r hr.1.1.1.1.1.1) (fun r hr => hr.1.1.1.1.2)
    (fun r hr => hr.1.1.1.2) regs ⟨hr, fun t => hQv t⟩
  refine ⟨new, e1, e2, e3.1.1.1.1.1.1.1, ?_⟩
  obtain ⟨rv, h1, h2, h3⟩ := e3.2
  refine ⟨rv, h1, h2, ?_⟩
  rw [h3, ← hmp]
  exact modByMonic_eq_of_mk_eq _ _ _ hmonic (kron_mod l m d d₀ N hdl _ f g Qf hQ')

/-! ## S8c: input layout, the case `m = 0`, run correctness -/

theorem holdsVec_flattenK {R : Type*} [CommRing R] (N : ℕ) :
    ∀ (bl : List (List R)) (pre post : List R) (i : ℕ) (hi : i < bl.length),
      (∀ b ∈ bl, b.length = N) →
      HoldsVec (pre ++ bl.flatten ++ post) (List.range' (pre.length + i * N) N) (bl[i])
  | b :: bl, pre, post, 0, _, hN => by
    have h1 := holdsVec_range' b pre
    rw [hN b (by simp)] at h1
    have := holdsVec_append _ (bl.flatten ++ post) _ _ h1
    simpa [List.append_assoc] using this
  | b :: bl, pre, post, i + 1, hi, hN => by
    have := holdsVec_flattenK N bl (pre ++ b) post i (by simp at hi; omega)
      (fun b' hb' => hN b' (by simp [hb']))
    have hb := hN b (by simp)
    rw [List.length_append, hb] at this
    simp only [List.flatten_cons, List.getElem_cons_succ]
    rw [show pre.length + (i + 1) * N = pre.length + N + i * N by ring]
    simpa [List.append_assoc] using this

theorem length_flatten_constK {α : Type*} (N : ℕ) :
    ∀ (bl : List (List α)), (∀ b ∈ bl, b.length = N) → bl.flatten.length = bl.length * N
  | [], _ => by simp
  | b :: bl, h => by
    rw [List.flatten_cons, List.length_append, h b (by simp),
      length_flatten_constK N bl (fun b' hb' => h b' (by simp [hb'])), List.length_cons]
    ring

theorem layout_holds {R : Type*} [CommRing R] {d m N n K : ℕ} (f : (Fin m → Fin d) → R)
    (g : Fin m → Fin N → R) (h : Fin (n + 1) → R) (β : Fin K → R) :
    HoldsVec (layout f g h β) (List.range' 0 (d ^ m))
        (List.ofFn fun k : Fin (d ^ m) => f (finFunctionFinEquiv.symm k)) ∧
      (∀ i : Fin m, HoldsVec (layout f g h β) (List.range' (d ^ m + i * N) N)
        (List.ofFn (g i))) ∧
      HoldsVec (layout f g h β) (List.range' (d ^ m + m * N) (n + 1)) (List.ofFn h) ∧
      HoldsVec (layout f g h β) (List.range' (d ^ m + m * N + (n + 1)) K) (List.ofFn β) ∧
      (layout f g h β).length = d ^ m + m * N + (n + 1) + K := by
  have hN : ∀ b ∈ List.ofFn (fun i => List.ofFn (g i)), b.length = N := by
    intro b hb
    rw [List.mem_ofFn] at hb
    obtain ⟨i, rfl⟩ := hb
    simp
  have hL2 : ((List.ofFn fun i => List.ofFn (g i)).flatten).length = m * N := by
    rw [length_flatten_constK N _ hN, List.length_ofFn]
  unfold layout
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := holdsVec_range' (List.ofFn fun k : Fin (d ^ m) => f (finFunctionFinEquiv.symm k)) []
    rw [List.nil_append, List.length_nil, List.length_ofFn] at this
    have := holdsVec_append _ ((List.ofFn fun i => List.ofFn (g i)).flatten ++ List.ofFn h ++
      List.ofFn β) _ _ this
    simpa only [List.append_assoc] using this
  · intro i
    have := holdsVec_flattenK N (List.ofFn fun i => List.ofFn (g i))
      (List.ofFn fun k : Fin (d ^ m) => f (finFunctionFinEquiv.symm k))
      (List.ofFn h ++ List.ofFn β) i (by simp) hN
    simp only [List.length_ofFn, List.getElem_ofFn] at this
    simpa only [List.append_assoc] using this
  · have := holdsVec_range' (List.ofFn h)
      ((List.ofFn fun k : Fin (d ^ m) => f (finFunctionFinEquiv.symm k)) ++
        (List.ofFn fun i => List.ofFn (g i)).flatten)
    rw [List.length_append, hL2, List.length_ofFn, List.length_ofFn] at this
    have := holdsVec_append _ (List.ofFn β) _ _ this
    simpa only [List.append_assoc] using this
  · have := holdsVec_range' (List.ofFn β)
      ((List.ofFn fun k : Fin (d ^ m) => f (finFunctionFinEquiv.symm k)) ++
        (List.ofFn fun i => List.ofFn (g i)).flatten ++ List.ofFn h)
    rw [List.length_append, List.length_append, hL2, List.length_ofFn, List.length_ofFn,
      List.length_ofFn] at this
    exact this
  · simp only [List.length_append, hL2, List.length_ofFn]

theorem mainGen_length (d d₀ m N n l D K s : ℕ) :
    ((mainGen d d₀ m N n l D K) s).1.length = n := by
  simp only [mainGen, gen_bind_fst, modUB_length]

/-- The program for `m ≥ 1`, generated at the input length. -/
noncomputable def progMain (d d₀ m N n : ℕ) : SLP :=
  ⟨((mainGen d d₀ m N n (Nat.clog d₀ d) (d ^ m) (N * m * Nat.clog d₀ d * d₀))
      (d ^ m + m * N + (n + 1) + N * m * Nat.clog d₀ d * d₀)).2.1,
    ((mainGen d d₀ m N n (Nat.clog d₀ d) (d ^ m) (N * m * Nat.clog d₀ d * d₀))
      (d ^ m + m * N + (n + 1) + N * m * Nat.clog d₀ d * d₀)).1⟩

theorem run_progMain (R : Type) [CommRing R] (ι : R → R)
    (hι : ∀ x : Rˣ, ι (x : R) = ((x⁻¹ : Rˣ) : R)) (d d₀ m N n : ℕ) (hd₀ : 2 ≤ d₀) (hd : d₀ < d)
    (hm1 : 1 ≤ m) (hnN : n + 1 ≤ N)
    (f : (Fin m → Fin d) → R) (g : Fin m → Fin N → R) (h : Fin (n + 1) → R) (u : Rˣ)
    (β : Fin (N * m * Nat.clog d₀ d * d₀) → R) (hu : (u : R) = h (Fin.last n))
    (hβ : ∀ i j, i ≠ j → IsUnit (β i - β j)) :
    run ι (progMain d d₀ m N n) (layout f g h β) = List.ofFn (modCompSpec f g h u) := by
  obtain ⟨hF, hG, hH, hB, hlen⟩ := layout_holds f g h β
  rcases subsingleton_or_nontrivial R with hR | hR
  · apply list_eq_of_subsingleton
    simp only [run, progMain, List.length_map, mainGen_length, List.length_ofFn]
  · let P : List R → Prop := fun regs =>
      HoldsVec regs (List.range' 0 (d ^ m))
        (List.ofFn fun k : Fin (d ^ m) => f (finFunctionFinEquiv.symm k)) ∧
      (∀ i : Fin m, HoldsVec regs (List.range' (d ^ m + i * N) N) (List.ofFn (g i))) ∧
      HoldsVec regs (List.range' (d ^ m + m * N) (n + 1)) (List.ofFn h) ∧
      HoldsVec regs (List.range' (d ^ m + m * N + (n + 1)) (N * m * Nat.clog d₀ d * d₀))
        (List.ofFn β)
    have hP : Stable P := fun regs new hr =>
      ⟨holdsVec_append _ _ _ _ hr.1, fun i => holdsVec_append _ _ _ _ (hr.2.1 i),
        holdsVec_append _ _ _ _ hr.2.2.1, holdsVec_append _ _ _ _ hr.2.2.2⟩
    have T := triple_main ι hι d d₀ m N n (Nat.clog d₀ d) (d ^ m) (N * m * Nat.clog d₀ d * d₀)
      hd₀ hm1 hnN (Nat.clog_pos (by omega) (by omega)) (Nat.le_pow_clog (by omega) d) rfl rfl
      f g h u β hu hβ P hP (fun _ hr => hr.1) (fun _ hr => hr.2.1) (fun _ hr => hr.2.2.1)
      (fun _ hr => hr.2.2.2)
    have := run_of_triple ι _ P _ (fun vs => vs = List.ofFn (modCompSpec f g h u)) T
      (fun out regs hq => by
        obtain ⟨-, rv, h1, h2, h3⟩ := hq
        refine ⟨rv, h1, ?_⟩
        rw [← ofFn_getD_eq n rv h2]
        congr 1
        funext j
        rw [← toPoly_coeff, h3]
        rfl) _ ⟨hF, hG, hH, hB⟩
    rw [hlen] at this
    exact this

/-- The program for `m = 0`: `f` is a constant, its remainder is itself (or nothing if `n = 0`);
out-of-range registers read `0`. -/
def prog0 (d d₀ m N n : ℕ) : SLP :=
  ⟨[.mme d₀ (Nat.clog d₀ d * m) (N * m * Nat.clog d₀ d * d₀) [] []],
    if n = 0 then [] else 0 :: List.replicate (n - 1) (n + 2)⟩

theorem run_prog0 (R : Type) [CommRing R] (ι : R → R) (d d₀ N n : ℕ)
    (f : (Fin 0 → Fin d) → R) (g : Fin 0 → Fin N → R) (h : Fin (n + 1) → R) (u : Rˣ)
    (β : Fin (N * 0 * Nat.clog d₀ d * d₀) → R) (hu : (u : R) = h (Fin.last n)) :
    run ι (prog0 d d₀ 0 N n) (layout f g h β) = List.ofFn (modCompSpec f g h u) := by
  obtain ⟨hF, -, -, -, hlen⟩ := layout_holds f g h β
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [run, prog0]
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rcases subsingleton_or_nontrivial R with hR | hR
  · apply list_eq_of_subsingleton
    simp [run, prog0]
  set regs := (prog0 d d₀ 0 N (n' + 1)).code.foldl (step ι) (layout f g h β) with hregs
  have hrl : regs.length = n' + 3 := by
    simp only [hregs, prog0, List.foldl_cons, List.foldl_nil, step, List.length_append,
      List.length_ofFn, hlen]
    simp <;> omega
  have hr0 : reg regs 0 = f (finFunctionFinEquiv.symm 0) := by
    have := holds_range_ofFn (layout f g h β) 0 (d ^ 0) _ hF ⟨0, by simp⟩
    have h2 := holds_append _ (List.ofFn (mmeSpec (d := d₀) (m := Nat.clog d₀ d * 0)
      (N := N * 0 * Nat.clog d₀ d * d₀)
      (fun e => regAt (layout f g h β) [] (finFunctionFinEquiv e))
      (fun k i => regAt (layout f g h β) [] ((k : ℕ) * (Nat.clog d₀ d * 0) + i)))) _ _ this
    simp only [zero_add] at h2
    rw [hregs]
    simp only [prog0, List.foldl_cons, List.foldl_nil, step]
    exact holds_reg _ _ _ h2
  have hrz : reg regs (n' + 1 + 2) = 0 := by
    unfold reg
    rw [List.getD_eq_default _ _ (by omega)]
  -- the remainder of a constant
  set c := f (finFunctionFinEquiv.symm 0) with hc
  have hfg : MvPolynomial.aeval (fun i => densePoly (g i)) (densePolyMv f) = C c := by
    rw [aeval_densePolyMv, Fintype.sum_unique]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, hc]
    congr 2
    funext i; exact i.elim0
  have hcoef : (densePoly h * C ((u⁻¹ : Rˣ) : R)).coeff (n' + 1) = 1 := by
    rw [coeff_mul_C, densePoly_eq_toPoly, toPoly_coeff, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, dif_pos (by omega)]
    simp only [Option.getD_some]
    rw [show (⟨n' + 1, by omega⟩ : Fin (n' + 1 + 1)) = Fin.last (n' + 1) from rfl, ← hu]
    exact Units.mul_inv u
  have hmonic : (densePoly h * C ((u⁻¹ : Rˣ) : R)).Monic := by
    refine monic_of_natDegree_le_of_coeff_eq_one (n' + 1) ?_ hcoef
    refine (natDegree_mul_C_le _ _).trans ?_
    rw [densePoly_eq_toPoly]
    have := toPoly_natDegree_le (List.ofFn h)
    simpa using this
  have hmod : C c %ₘ (densePoly h * C ((u⁻¹ : Rˣ) : R)) = C c := by
    rw [modByMonic_eq_self_iff hmonic]
    refine lt_of_le_of_lt degree_C_le ?_
    refine lt_of_lt_of_le ?_ (le_degree_of_ne_zero (n := n' + 1) (by rw [hcoef]; exact one_ne_zero))
    exact WithBot.coe_lt_coe.mpr (by omega)
  have hrhs : List.ofFn (modCompSpec f g h u) = c :: List.replicate n' 0 := by
    unfold modCompSpec modU
    rw [hfg, hmod, List.ofFn_succ]
    simp [coeff_C]
  rw [hrhs]
  unfold run
  rw [← hregs]
  simp only [prog0, Nat.add_one_ne_zero, if_false, List.map_cons, List.map_replicate, hr0,
    Nat.add_sub_cancel]
  rw [hrz]



/-! ## S9a: oracle log and operation counts of the main program -/

theorem noOr_mulModIter (N n : ℕ) (hm : List ℕ) (z : ℕ) (p : List ℕ) :
    ∀ k acc, NoOr (mulModIter N n hm z p k acc)
  | 0, acc => by rw [mulModIter]; exact noOr_pure _
  | k + 1, acc => by
    rw [mulModIter]
    exact noOr_bind _ _ (noOr_polyMulG _ _ _) fun q => noOr_bind _ _ (noOr_modUB _ _ _ _ _)
      fun r => noOr_mulModIter N n hm z p k r

theorem noOr_powChain (N n d₀ : ℕ) (hm : List ℕ) (z : ℕ) :
    ∀ k p, NoOr (powChain N n d₀ hm z k p)
  | 0, p => by rw [powChain]; exact noOr_pure _
  | k + 1, p => by
    rw [powChain]
    exact noOr_bind _ _ (noOr_mulModIter _ _ _ _ _ _ _) fun q =>
      noOr_bind _ _ (noOr_powChain N n d₀ hm z k q) fun _ => noOr_pure _

theorem oc_noOr {α : Type} (g : Gen α) (hg : NoOr g) (n : ℕ) :
    (g n).2.1.filterMap Instr.oracleParams = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro i hi
  have := hg n i hi
  clear hi
  revert this
  cases i <;> simp [Instr.isRingOp, Instr.oracleParams]

theorem oc_bind {α β : Type} (g : Gen α) (f : α → Gen β) (n : ℕ) :
    (Gen.bind g f n).2.1.filterMap Instr.oracleParams =
      (g n).2.1.filterMap Instr.oracleParams ++
        (f (g n).1 (g n).2.2).2.1.filterMap Instr.oracleParams := by
  simp only [Gen.bind, List.filterMap_append]

theorem oracleCalls_progMain (d d₀ m N n : ℕ) :
    oracleCalls (progMain d d₀ m N n) =
      [(d₀, Nat.clog d₀ d * m, N * m * Nat.clog d₀ d * d₀)] := by
  unfold oracleCalls progMain
  simp only [mainGen]
  rw [oc_bind, oc_noOr _ (noOr_emit _ rfl), oc_bind, oc_noOr _ (noOr_vecSmul _ _), oc_bind,
    oc_noOr _ (noOr_emit _ rfl), oc_bind,
    oc_noOr _ (noOr_mapGen _ (fun _ => noOr_powChain _ _ _ _ _ _ _) _), oc_bind,
    oc_noOr _ (noOr_mapGen _ (fun _ => noOr_mpe _ _ _ _ rfl) _), oc_bind, oc_bind,
    oc_noOr _ (noOr_interp _ _ _ _ rfl), oc_noOr _ (noOr_modUB _ _ _ _ _)]
  simp [Gen.emitMME, Instr.oracleParams]

theorem oracleCalls_prog0 (d d₀ m N n : ℕ) :
    oracleCalls (prog0 d d₀ m N n) =
      [(d₀, Nat.clog d₀ d * m, N * m * Nat.clog d₀ d * d₀)] := by
  simp [oracleCalls, prog0, Instr.oracleParams]

theorem ringOps_prog0 (d d₀ m N n : ℕ) : ringOps (prog0 d d₀ m N n) = 0 := by
  simp [ringOps, prog0, Instr.isRingOp]

/-- Cost shape of `modUB`. -/
def Cm (x : ℕ) : ℕ := 10 ^ 16 * (x + 1) * (Nat.log 2 (x + 1) + 1) ^ 11

theorem Cm_mono {x y : ℕ} (h : x ≤ y) : Cm x ≤ Cm y := by
  unfold Cm
  have := Nat.log_mono_right (b := 2) (show x + 1 ≤ y + 1 by omega)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (Nat.pow_le_pow_left (by omega) _)

theorem mulModIter_length (N n : ℕ) (hm : List ℕ) (z : ℕ) (p : List ℕ) (hnN : n ≤ N) :
    ∀ k acc s, acc.length ≤ N → ((mulModIter N n hm z p k acc) s).1.length ≤ N
  | 0, acc, s, h => by rw [mulModIter]; exact h
  | k + 1, acc, s, _ => by
    rw [mulModIter]
    simp only [gen_bind_fst]
    exact mulModIter_length N n hm z p hnN k _ _ (by rw [modUB_length]; exact hnN)

theorem ops_mulModIter (N n : ℕ) (hm : List ℕ) (z : ℕ) (p : List ℕ) (hp : p.length ≤ N)
    (hhm : hm.length ≤ n + 1) (hnN : n ≤ N) :
    ∀ k acc s, acc.length ≤ N → (mulModIter N n hm z p k acc).ops s ≤ k * (Bd N + Cm (2 * N + n))
  | 0, acc, s, _ => by rw [mulModIter]; simp [ops_pure]
  | k + 1, acc, s, hacc => by
    rw [mulModIter]
    refine le_trans (ops_bind_le _ _ (fun q => q.length ≤ 2 * N) _
      (Cm (2 * N + n) + k * (Bd N + Cm (2 * N + n))) s (ops_polyMulG_Bd N acc p hacc hp s)
      (polyMulG_length N acc p s) fun q s' hq => ?_)
      (by rw [Nat.add_mul, Nat.one_mul]; omega)
    refine ops_bind_le _ _ (fun r => r.length ≤ N) _ _ s'
      (le_trans (ops_modUB q.length n q hm z rfl hhm s') (Cm_mono (by omega)))
      (by rw [modUB_length]; exact hnN) fun r s'' hr => ops_mulModIter N n hm z p hp hhm hnN k r s'' hr

theorem ops_powChain (N n d₀ : ℕ) (hm : List ℕ) (z : ℕ) (hhm : hm.length ≤ n + 1) (hnN : n ≤ N) :
    ∀ k p s, p.length ≤ N →
      (powChain N n d₀ hm z k p).ops s ≤ k * ((d₀ - 1) * (Bd N + Cm (2 * N + n)))
  | 0, p, s, _ => by rw [powChain]; simp [ops_pure]
  | k + 1, p, s, hp => by
    rw [powChain]
    refine le_trans (ops_bind_le _ _ (fun q => q.length ≤ N) _
      (k * ((d₀ - 1) * (Bd N + Cm (2 * N + n))) + 0) s
      (ops_mulModIter N n hm z p hp hhm hnN (d₀ - 1) p s hp)
      (mulModIter_length N n hm z p hnN _ _ _ hp) fun q s' hq => ?_)
      (by rw [Nat.add_mul, Nat.one_mul]; omega)
    exact ops_bind_le _ _ (fun _ => True) _ _ s' (ops_powChain N n d₀ hm z hhm hnN k q s' hq)
      trivial fun _ _ _ => by rw [ops_pure]

theorem powChain_mem (N n d₀ : ℕ) (hm : List ℕ) (z : ℕ) (hnN : n ≤ N) :
    ∀ k p s, p.length ≤ N → ∀ x ∈ ((powChain N n d₀ hm z k p) s).1, x.length ≤ N
  | 0, p, s, _ => by rw [powChain]; simp [Gen.pure]
  | k + 1, p, s, hp => by
    rw [powChain]
    simp only [gen_bind_fst, Gen.pure, List.mem_cons]
    rintro x (rfl | hx)
    · exact hp
    · exact powChain_mem N n d₀ hm z hnN k _ _ (mulModIter_length N n hm z p hnN _ _ _ hp) x hx

theorem mapGen_memK {α β : Type} (f : α → Gen β) (Pr : β → Prop) (hf : ∀ a s, Pr ((f a) s).1) :
    ∀ (as : List α) s, ∀ b ∈ ((mapGen f as) s).1, Pr b
  | [], s => by simp [mapGen, Gen.pure]
  | a :: as, s => by
    simp only [mapGen, gen_bind_fst, Gen.pure, List.mem_cons]
    rintro b (rfl | hb)
    · exact hf a s
    · exact mapGen_memK f Pr hf as _ b hb

theorem getD_mem_or {α : Type*} (l : List α) (i : ℕ) (d : α) : l.getD i d = d ∨ l.getD i d ∈ l := by
  rcases lt_or_ge i l.length with h | h
  · right; rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h
  · left; exact List.getD_eq_default _ _ h

theorem ops_mainGen (d d₀ m N n l D K s : ℕ) (hnN : n + 1 ≤ N) (hNK : N ≤ K) :
    (mainGen d d₀ m N n l D K).ops s ≤
      1 + ((n + 1) + (1 + (m * (l * ((d₀ - 1) * (Bd N + Cm (2 * N + n)))) +
        ((l * m) * (gG (10 ^ 21) 12 K * (Nat.clog 2 K + 1) + 1) +
          (0 + ((gG (10 ^ 23) 14 K * (Nat.clog 2 K + 1) + 1) + Cm (K + n))))))) := by
  unfold mainGen
  refine ops_bind_le _ _ (fun _ => True) _ _ s (by rw [ops_emit]; simp [Instr.isRingOp]) trivial
    fun ui s1 _ => ?_
  refine ops_bind_le _ _ (fun hm => hm.length = n + 1) _ _ s1
    (by rw [ops_vecSmul]; simp) (by rw [vecSmul_length]; simp) fun hm s2 hhm => ?_
  refine ops_bind_le _ _ (fun _ => True) _ _ s2 (by rw [ops_emit]; simp [Instr.isRingOp]) trivial
    fun z s3 _ => ?_
  refine ops_bind_le _ _ (fun pw => ∀ x ∈ pw, ∀ y ∈ x, y.length ≤ N) _ _ s3
    (by
      have := ops_mapGen (fun i => powChain N n d₀ hm z l (List.range' (D + i * N) N))
        (l * ((d₀ - 1) * (Bd N + Cm (2 * N + n))))
        (fun a s' => ops_powChain N n d₀ hm z (by omega) (by omega) l _ s' (by simp))
        (List.range' 0 m) s3
      simpa using this)
    (mapGen_memK _ _ (fun a s' => powChain_mem N n d₀ hm z (by omega) l _ s' (by simp)) _ _)
    fun pw s4 hpw => ?_
  refine ops_bind_le _ _ (fun _ => True) _ _ s4
    (by
      have := ops_mapGen (fun t => mpe z (List.range' (D + m * N + (n + 1)) K)
        ((pw.getD (t % m) []).getD (t / m) []))
        (gG (10 ^ 21) 12 K * (Nat.clog 2 K + 1) + 1)
        (fun t s' => ops_mpe z K _ _ s' (by simp) (by
          rcases getD_mem_or pw (t % m) [] with h1 | h1
          · rw [h1]; simp
          · rcases getD_mem_or (pw.getD (t % m) []) (t / m) [] with h2 | h2
            · rw [h2]; simp
            · exact le_trans (hpw _ h1 _ h2) hNK))
        (List.range' 0 (l * m)) s4
      simpa using this) trivial fun outs s5 _ => ?_
  refine ops_bind_le _ _ (fun _ => True) _ _ s5 (by rw [ops_emitMME]) trivial
    fun vals s6 _ => ?_
  refine ops_bind_le _ _ (fun fv => fv.length = K) _ _ s6
    (ops_interp z K _ vals s6 (by simp)) (by rw [interp_length]; simp) fun fv s7 hfv => ?_
  refine le_trans (ops_modUB fv.length n fv hm z rfl (by omega) s7) ?_
  rw [hfv]
  exact le_refl _


/-! ## S9b: cost arithmetic -/

theorem logQ {y Q : ℕ} (h : y + 1 < 2 ^ Q) : Nat.log 2 (y + 1) + 1 ≤ Q := by
  have := Nat.log_lt_of_lt_pow (b := 2) (by omega : y + 1 ≠ 0) h
  omega

theorem Cm_le {y Q : ℕ} (h : y + 1 < 2 ^ Q) : Cm y ≤ 10 ^ 16 * (y + 1) * Q ^ 11 := by
  unfold Cm
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (logQ h) _)

theorem Bd_le {y Q : ℕ} (h : y + 1 < 2 ^ Q) : Bd y ≤ 10 ^ 9 * (y + 1) * Q ^ 11 := by
  unfold Bd
  have h1 := logQ h
  calc 10 ^ 9 * (y + 1) * (Nat.log 2 (y + 1) + 1) ^ 10 ≤ 10 ^ 9 * (y + 1) * Q ^ 10 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
    _ ≤ 10 ^ 9 * (y + 1) * Q ^ 11 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))

theorem gG_le {c e K Q : ℕ} (h : 2 * K + 1 < 2 ^ Q) : gG c e K ≤ c * K * Q ^ e := by
  unfold gG
  have h1 := logQ h
  have h2 : Nat.log 2 (2 * K) ≤ Nat.log 2 (2 * K + 1) := Nat.log_mono_right (by omega)
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

theorem cost_core (X L m l K N n d₀ : ℕ) (hd₀ : 2 ≤ d₀) (hN : N ≤ X) (hd0X : d₀ ≤ X)
    (hLX : L ≤ X) (hXL : X < 2 ^ L) (hml : m * l ≤ 2 * L) (hK : K ≤ 2 * (X * L * d₀))
    (hnN : n + 1 ≤ N) (hL1 : 1 ≤ L) :
    1 + ((n + 1) + (1 + (m * (l * ((d₀ - 1) * (Bd N + Cm (2 * N + n)))) +
      ((l * m) * (gG (10 ^ 21) 12 K * (Nat.clog 2 K + 1) + 1) +
        (0 + ((gG (10 ^ 23) 14 K * (Nat.clog 2 K + 1) + 1) + Cm (K + n))))))) ≤
      10 ^ 40 * X * d₀ * L ^ 20 := by
  have hX3 : X ^ 3 < 2 ^ (3 * L) := by
    rw [show 3 * L = L * 3 from mul_comm _ _, pow_mul]
    exact Nat.pow_lt_pow_left hXL (by norm_num)
  have hXX3 : X ≤ X ^ 3 := Nat.le_self_pow (by norm_num) X
  have hXLd : X * L * d₀ ≤ X ^ 3 := by
    calc X * L * d₀ ≤ X * X * X := Nat.mul_le_mul (Nat.mul_le_mul_left X hLX) hd0X
      _ = X ^ 3 := by ring
  have hQ : ∀ y, y ≤ 4 * X ^ 3 → y + 1 < 2 ^ (5 * L) := by
    have e : 2 ^ (5 * L) = 2 ^ (3 * L) * 2 ^ (2 * L) := by
      rw [← pow_add]; congr 1; ring
    have h4 : 4 ≤ 2 ^ (2 * L) :=
      le_trans (by norm_num : 4 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h5 := Nat.mul_le_mul_left (2 ^ (3 * L)) h4
    intro y hy
    rw [e]
    omega
  have hBd := Bd_le (hQ N (by omega))
  have hC1 := Cm_le (hQ (2 * N + n) (by omega))
  have hC2 := Cm_le (hQ (K + n) (by omega))
  have hG1 : gG (10 ^ 21) 12 K ≤ 10 ^ 21 * K * (5 * L) ^ 12 := gG_le (hQ (2 * K) (by omega))
  have hG2 : gG (10 ^ 23) 14 K ≤ 10 ^ 23 * K * (5 * L) ^ 14 := gG_le (hQ (2 * K) (by omega))
  have hc : Nat.clog 2 K + 1 ≤ 2 * (5 * L) := by
    have h0 := hQ (2 * K) (by omega)
    have : Nat.clog 2 K ≤ 5 * L := Nat.clog_le_of_le_pow (by omega)
    omega
  have hA : m * (l * ((d₀ - 1) * (Bd N + Cm (2 * N + n)))) ≤
      16 * 10 ^ 16 * 5 ^ 11 * (X * d₀ * L ^ 20) := by
    have hlin : 10 ^ 9 * (N + 1) + 10 ^ 16 * (2 * N + n + 1) ≤ 8 * 10 ^ 16 * X := by omega
    have hS : Bd N + Cm (2 * N + n) ≤ 8 * 10 ^ 16 * X * (5 * L) ^ 11 := by
      calc Bd N + Cm (2 * N + n) ≤
            10 ^ 9 * (N + 1) * (5 * L) ^ 11 + 10 ^ 16 * (2 * N + n + 1) * (5 * L) ^ 11 :=
            add_le_add hBd hC1
        _ = (10 ^ 9 * (N + 1) + 10 ^ 16 * (2 * N + n + 1)) * (5 * L) ^ 11 := by ring
        _ ≤ (8 * 10 ^ 16 * X) * (5 * L) ^ 11 := Nat.mul_le_mul_right _ hlin
    calc m * (l * ((d₀ - 1) * (Bd N + Cm (2 * N + n))))
        ≤ m * (l * (d₀ * (8 * 10 ^ 16 * X * (5 * L) ^ 11))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) hS))
      _ = (m * l) * (8 * 10 ^ 16 * 5 ^ 11 * (X * d₀ * L ^ 11)) := by ring
      _ ≤ (2 * L) * (8 * 10 ^ 16 * 5 ^ 11 * (X * d₀ * L ^ 11)) := Nat.mul_le_mul_right _ hml
      _ = 16 * 10 ^ 16 * 5 ^ 11 * (X * d₀ * L ^ 12) := by ring
      _ ≤ 16 * 10 ^ 16 * 5 ^ 11 * (X * d₀ * L ^ 20) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hL1 (by norm_num)))
  have hV14 : 1 ≤ X * d₀ * L ^ 14 :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (pow_pos (by omega) _)
  have hU : 1 ≤ X * d₀ * L ^ 20 :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (pow_pos (by omega) _)
  have hB : (l * m) * (gG (10 ^ 21) 12 K * (Nat.clog 2 K + 1) + 1) ≤
      2 * (4 * 10 ^ 21 * 5 ^ 13 + 1) * (X * d₀ * L ^ 20) := by
    have h1 : gG (10 ^ 21) 12 K * (Nat.clog 2 K + 1) ≤ 4 * 10 ^ 21 * 5 ^ 13 * (X * d₀ * L ^ 14) :=
      calc gG (10 ^ 21) 12 K * (Nat.clog 2 K + 1)
          ≤ 10 ^ 21 * (2 * (X * L * d₀)) * (5 * L) ^ 12 * (2 * (5 * L)) :=
            Nat.mul_le_mul (le_trans hG1 (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hK))) hc
        _ = 4 * 10 ^ 21 * 5 ^ 13 * (X * d₀ * L ^ 14) := by ring
    have h2 : gG (10 ^ 21) 12 K * (Nat.clog 2 K + 1) + 1 ≤
        (4 * 10 ^ 21 * 5 ^ 13 + 1) * (X * d₀ * L ^ 14) := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    calc (l * m) * (gG (10 ^ 21) 12 K * (Nat.clog 2 K + 1) + 1)
        ≤ (2 * L) * ((4 * 10 ^ 21 * 5 ^ 13 + 1) * (X * d₀ * L ^ 14)) :=
          Nat.mul_le_mul (by rw [mul_comm]; exact hml) h2
      _ = 2 * (4 * 10 ^ 21 * 5 ^ 13 + 1) * (X * d₀ * L ^ 15) := by ring
      _ ≤ 2 * (4 * 10 ^ 21 * 5 ^ 13 + 1) * (X * d₀ * L ^ 20) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hL1 (by norm_num)))
  have hXLd1 : X ≤ X * L * d₀ := by
    have : X * 1 * 1 ≤ X * L * d₀ := Nat.mul_le_mul (Nat.mul_le_mul_left X hL1) (by omega)
    simpa using this
  have hC : (gG (10 ^ 23) 14 K * (Nat.clog 2 K + 1) + 1) + Cm (K + n) ≤
      (4 * 10 ^ 23 * 5 ^ 15 + 1 + 3 * 10 ^ 16 * 5 ^ 11) * (X * d₀ * L ^ 20) := by
    have h1 : gG (10 ^ 23) 14 K * (Nat.clog 2 K + 1) ≤ 4 * 10 ^ 23 * 5 ^ 15 * (X * d₀ * L ^ 20) :=
      calc gG (10 ^ 23) 14 K * (Nat.clog 2 K + 1)
          ≤ 10 ^ 23 * (2 * (X * L * d₀)) * (5 * L) ^ 14 * (2 * (5 * L)) :=
            Nat.mul_le_mul (le_trans hG2 (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hK))) hc
        _ = 4 * 10 ^ 23 * 5 ^ 15 * (X * d₀ * L ^ 16) := by ring
        _ ≤ 4 * 10 ^ 23 * 5 ^ 15 * (X * d₀ * L ^ 20) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hL1 (by norm_num)))
    have hKn : K + n + 1 ≤ 3 * (X * L * d₀) := by omega
    have h2 : Cm (K + n) ≤ 3 * 10 ^ 16 * 5 ^ 11 * (X * d₀ * L ^ 20) :=
      calc Cm (K + n) ≤ 10 ^ 16 * (K + n + 1) * (5 * L) ^ 11 := hC2
        _ ≤ 10 ^ 16 * (3 * (X * L * d₀)) * (5 * L) ^ 11 :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hKn)
        _ = 3 * 10 ^ 16 * 5 ^ 11 * (X * d₀ * L ^ 12) := by ring
        _ ≤ 3 * 10 ^ 16 * 5 ^ 11 * (X * d₀ * L ^ 20) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hL1 (by norm_num)))
    rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]; omega
  have hXU : X ≤ X * d₀ * L ^ 20 := by
    have : X * 1 * 1 ≤ X * d₀ * L ^ 20 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left X (by omega)) (Nat.one_le_pow _ _ (by omega))
    simpa using this
  have hR : 10 ^ 40 * X * d₀ * L ^ 20 = 10 ^ 40 * (X * d₀ * L ^ 20) := by ring
  rw [hR]
  omega

theorem cost_arith (d d₀ m N n : ℕ) (hd₀ : 2 ≤ d₀) (hd : d₀ < d) (hm : 1 ≤ m) (hnN : n + 1 ≤ N) :
    1 + ((n + 1) + (1 + (m * (Nat.clog d₀ d * ((d₀ - 1) * (Bd N + Cm (2 * N + n)))) +
      ((Nat.clog d₀ d * m) * (gG (10 ^ 21) 12 (N * m * Nat.clog d₀ d * d₀) *
          (Nat.clog 2 (N * m * Nat.clog d₀ d * d₀) + 1) + 1) +
        (0 + ((gG (10 ^ 23) 14 (N * m * Nat.clog d₀ d * d₀) *
          (Nat.clog 2 (N * m * Nat.clog d₀ d * d₀) + 1) + 1) +
            Cm (N * m * Nat.clog d₀ d * d₀ + n))))))) ≤
      10 ^ 40 * (d ^ m + m * N) * d₀ * (Nat.log 2 (d ^ m + m * N) + 1) ^ 20 := by
  have hdm : d ≤ d ^ m := Nat.le_self_pow (by omega) d
  have hNmN : N ≤ m * N := Nat.le_mul_of_pos_left N (by omega)
  have hld : 1 ≤ Nat.log 2 d := Nat.log_pos (by norm_num) (by omega)
  have hl : Nat.clog d₀ d ≤ Nat.log 2 d + 1 :=
    Nat.clog_le_of_le_pow (le_trans (Nat.lt_pow_succ_log_self (by norm_num) d).le
      (Nat.pow_le_pow_left (by omega) _))
  have hmld : m * Nat.log 2 d ≤ Nat.log 2 (d ^ m + m * N) := by
    apply Nat.le_log_of_pow_le (by norm_num)
    rw [show m * Nat.log 2 d = Nat.log 2 d * m from mul_comm _ _, pow_mul]
    exact le_trans (Nat.pow_le_pow_left (Nat.pow_log_le_self 2 (by omega)) m) (by omega)
  have hXL : d ^ m + m * N < 2 ^ (Nat.log 2 (d ^ m + m * N) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hLX : Nat.log 2 (d ^ m + m * N) + 1 ≤ d ^ m + m * N := by
    have h1 := Nat.pow_log_le_self 2 (show d ^ m + m * N ≠ 0 by omega)
    have h2 : Nat.log 2 (d ^ m + m * N) < 2 ^ Nat.log 2 (d ^ m + m * N) := Nat.lt_two_pow_self
    omega
  have hml : m * Nat.clog d₀ d ≤ 2 * (Nat.log 2 (d ^ m + m * N) + 1) := by
    have h1 := Nat.mul_le_mul_left m hl
    have h2 := Nat.mul_le_mul_left m (show Nat.log 2 d + 1 ≤ 2 * Nat.log 2 d by omega)
    have h3 : m * (2 * Nat.log 2 d) = 2 * (m * Nat.log 2 d) := by ring
    omega
  have hK : N * m * Nat.clog d₀ d * d₀ ≤
      2 * ((d ^ m + m * N) * (Nat.log 2 (d ^ m + m * N) + 1) * d₀) := by
    calc N * m * Nat.clog d₀ d * d₀ = N * (m * Nat.clog d₀ d) * d₀ := by ring
      _ ≤ (d ^ m + m * N) * (2 * (Nat.log 2 (d ^ m + m * N) + 1)) * d₀ :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) hml)
      _ = 2 * ((d ^ m + m * N) * (Nat.log 2 (d ^ m + m * N) + 1) * d₀) := by ring
  exact cost_core (d ^ m + m * N) (Nat.log 2 (d ^ m + m * N) + 1) m (Nat.clog d₀ d)
    (N * m * Nat.clog d₀ d * d₀) N n d₀ hd₀ (by omega) (by omega) hLX hXL hml hK hnN (by omega)

end KUDecomp
end KUModComp

open KUModComp in
theorem solution :
    ∃ (C k : ℕ) (A : ℕ → ℕ → ℕ → ℕ → ℕ → SLP), ∀ d d₀ m N n : ℕ, 2 ≤ d₀ → d₀ < d → n + 1 ≤ N →
      ringOps (A d d₀ m N n) ≤
          C * (d ^ m + m * N) * d₀ * (Nat.log 2 (d ^ m + m * N) + 1) ^ k ∧
        oracleCalls (A d d₀ m N n) =
          [(d₀, Nat.clog d₀ d * m, N * m * Nat.clog d₀ d * d₀)] ∧
        ∀ (R : Type) [CommRing R] (ι : R → R), (∀ x : Rˣ, ι (x : R) = ((x⁻¹ : Rˣ) : R)) →
          ∀ (f : (Fin m → Fin d) → R) (g : Fin m → Fin N → R) (h : Fin (n + 1) → R) (u : Rˣ)
            (β : Fin (N * m * Nat.clog d₀ d * d₀) → R),
            (u : R) = h (Fin.last n) → Function.Injective β →
            (∀ i j, i ≠ j → IsUnit (β i - β j)) →
            run ι (A d d₀ m N n) (layout f g h β) = List.ofFn (modCompSpec f g h u) := by
  refine ⟨10 ^ 40, 20, fun d d₀ m N n =>
    if m = 0 then KUDecomp.prog0 d d₀ m N n else KUDecomp.progMain d d₀ m N n, ?_⟩
  intro d d₀ m N n hd₀ hd hnN
  beta_reduce
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [if_pos rfl]
    refine ⟨by rw [KUDecomp.ringOps_prog0]; exact Nat.zero_le _,
      KUDecomp.oracleCalls_prog0 _ _ _ _ _, ?_⟩
    intro R _ ι _ f g h u β hu _ _
    exact KUDecomp.run_prog0 R ι d d₀ N n f g h u β hu
  · rw [if_neg (by omega)]
    refine ⟨?_, KUDecomp.oracleCalls_progMain _ _ _ _ _, ?_⟩
    · have hl1 : 0 < Nat.clog d₀ d := Nat.clog_pos (by omega) (by omega)
      have hNK : N ≤ N * m * Nat.clog d₀ d * d₀ := by
        have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left N hm) hl1)
          (show 1 ≤ d₀ by omega)
        simpa using this
      unfold KUDecomp.progMain
      rw [KUDecomp.ringOps_gen]
      exact le_trans (KUDecomp.ops_mainGen d d₀ m N n (Nat.clog d₀ d) (d ^ m)
        (N * m * Nat.clog d₀ d * d₀) _ hnN hNK) (KUDecomp.cost_arith d d₀ m N n hd₀ hd hm hnN)
    · intro R _ ι hι f g h u β hu _ hβ
      exact KUDecomp.run_progMain R ι hι d d₀ m N n hd₀ hd hm hnN f g h u β hu hβ
