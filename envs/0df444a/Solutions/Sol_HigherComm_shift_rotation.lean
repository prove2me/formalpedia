-- Prove2me | solution 1 for HigherComm.shift_rotation
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-07T07:31:36.555382+00:00
-- url     : https://prove2.me/submissions/110cab65-7f75-4edb-bf49-808d11d4c049

import Definitions.Def_HigherComm_defs
import Mathlib.Tactic.FinCases

universe u₁ v₁ w₁

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

namespace HigherComm
namespace HCAux

variable {L : FirstOrder.Language.{u₁, v₁}} {M : Type w₁} [L.Structure M]

/-- Terms preserve congruences. -/
theorem realize_rel (δ : Congruence (L := L) M) {α : Type*} (t : L.Term α) {x y : α → M}
    (h : ∀ a, δ.r (x a) (y a)) : δ.r (t.realize x) (t.realize y) := by
  induction t with
  | var a => exact h a
  | func f ts ih => exact δ.fun_compat f _ _ ih

theorem rel_of_eq (δ : Congruence (L := L) M) {x y : M} (h : x = y) : δ.r x y :=
  h ▸ δ.iseqv.refl x

theorem rel_trans (δ : Congruence (L := L) M) {x y z : M} (h1 : δ.r x y) (h2 : δ.r y z) :
    δ.r x z := δ.iseqv.trans h1 h2

theorem rel_symm (δ : Congruence (L := L) M) {x y : M} (h : δ.r x y) : δ.r y x :=
  δ.iseqv.symm h

/-- Realizing a 4-ary term on congruent 4-tuples. -/
theorem realize4_rel (δ : Congruence (L := L) M) (t : L.Term (Fin 4)) {a b c d a' b' c' d' : M}
    (ha : δ.r a a') (hb : δ.r b b') (hc : δ.r c c') (hd : δ.r d d') :
    δ.r (t.realize ![a, b, c, d]) (t.realize ![a', b', c', d']) :=
  realize_rel δ t (fun i => by fin_cases i <;> assumption)

/-- If `r ≡ u` and `s ≡ v` then `mₑ(s,r,u,v) ≡ mₑ(s,s,v,v)` (both are `≡ s`). -/
theorem day_pair_of_rel {n : ℕ} {m : Fin (n + 1) → L.Term (Fin 4)} (hm : IsDayTerms M m)
    (δ : Congruence (L := L) M) {r s u v : M} (hru : δ.r r u) (hsv : δ.r s v) (e : Fin (n + 1)) :
    δ.r ((m e).realize ![s, r, u, v]) ((m e).realize ![s, s, v, v]) := by
  have h1 : δ.r ((m e).realize ![s, r, u, v]) s :=
    rel_trans δ (realize4_rel δ (m e) (δ.iseqv.refl s) (δ.iseqv.refl r)
      (rel_symm δ hru) (rel_symm δ hsv)) (rel_of_eq δ (hm.1 e s r))
  have h2 : δ.r ((m e).realize ![s, s, v, v]) s :=
    rel_trans δ (realize4_rel δ (m e) (δ.iseqv.refl s) (δ.iseqv.refl s)
      (rel_symm δ hsv) (rel_symm δ hsv)) (rel_of_eq δ (hm.1 e s s))
  exact rel_trans δ h1 (rel_symm δ h2)

/-- Day's shifting argument: if `r ≡ u` and `mₑ(s,r,u,v) ≡ mₑ(s,s,v,v)` for all `e`,
then `s ≡ v`. -/
theorem day_rel_of_pairs {n : ℕ} {m : Fin (n + 1) → L.Term (Fin 4)} (hm : IsDayTerms M m)
    (δ : Congruence (L := L) M) {r s u v : M} (hru : δ.r r u)
    (hp : ∀ e, δ.r ((m e).realize ![s, r, u, v]) ((m e).realize ![s, s, v, v])) :
    δ.r s v := by
  have key : ∀ i (hi : i ≤ n), δ.r s ((m ⟨i, by omega⟩).realize ![s, s, v, v]) := by
    intro i
    induction i with
    | zero => intro _; exact rel_of_eq δ (hm.2.1 s s v v).symm
    | succ i ih =>
      intro hi
      have ih' := ih (by omega)
      have hc : (⟨i, by omega⟩ : Fin (n + 1)) = (⟨i, by omega⟩ : Fin n).castSucc := rfl
      have hs : (⟨i + 1, by omega⟩ : Fin (n + 1)) = (⟨i, by omega⟩ : Fin n).succ := rfl
      refine rel_trans δ ih' ?_
      rcases Nat.even_or_odd i with he | ho
      · rw [hc, hs]; exact rel_of_eq δ (hm.2.2.2.1 ⟨i, by omega⟩ he s v)
      · rw [hc, hs]
        refine rel_trans δ (rel_symm δ (hp _)) ?_
        refine rel_trans δ (realize4_rel δ (m _) (δ.iseqv.refl s) (δ.iseqv.refl r)
          (rel_symm δ hru) (δ.iseqv.refl v)) ?_
        rw [hm.2.2.2.2 ⟨i, by omega⟩ ho s r v]
        exact rel_trans δ (realize4_rel δ (m _) (δ.iseqv.refl s) (δ.iseqv.refl r)
          hru (δ.iseqv.refl v)) (hp _)
  have := key n le_rfl
  rwa [show (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n from rfl, hm.2.2.1] at this

/-! ### Pinning blocks of a polynomial to constants -/

variable {k : ℕ} {r : Fin k → ℕ}

/-- Substitute, in block `i`, the constants `aᵢ` (if `ρ i = some false`) or `bᵢ`
(if `ρ i = some true`); blocks with `ρ i = none` stay variables. -/
def pinSub (a b : (i : Fin k) → Fin (r i) → M) (ρ : Fin k → Option Bool) :
    ((Σ i : Fin k, Fin (r i)) ⊕ M) → L.Term ((Σ i : Fin k, Fin (r i)) ⊕ M)
  | Sum.inl x => match ρ x.1 with
    | none => Term.var (Sum.inl x)
    | some false => Term.var (Sum.inr (a x.1 x.2))
    | some true => Term.var (Sum.inr (b x.1 x.2))
  | Sum.inr c => Term.var (Sum.inr c)

theorem cubeEval_pin (t : L.Term ((Σ i : Fin k, Fin (r i)) ⊕ M))
    (a b : (i : Fin k) → Fin (r i) → M) (ρ : Fin k → Option Bool) (f : Fin k → Bool) :
    cubeEval (t.subst (pinSub a b ρ)) a b f = cubeEval t a b (fun i => (ρ i).getD (f i)) := by
  unfold cubeEval
  rw [Term.realize_subst]
  congr 1
  funext x
  rcases x with ⟨i, p⟩ | c
  · simp only [pinSub]
    rcases hρ : ρ i with _ | _ | _ <;> simp [hρ]
  · simp [pinSub]

theorem getD_update (ρ : Fin k → Option Bool) (f : Fin k → Bool) (x : Fin k) (c : Bool) :
    (fun i => (Function.update ρ x (some c) i).getD (f i)) =
      Function.update (fun i => (ρ i).getD (f i)) x c := by
  funext i
  by_cases h : i = x
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem getD_none (f : Fin k → Bool) :
    (fun i => ((fun _ => none : Fin k → Option Bool) i).getD (f i)) = f := rfl

end HCAux

open HCAux

variable {L : FirstOrder.Language.{u₁, v₁}} {M : Type w₁} [L.Structure M]

/-- The shift-rotation maps (explicit formula of Lemma 3.1(1)). -/
def shiftRot {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (j l : Fin (k + 2)) (e : Fin (n + 1))
    (h : (Fin (k + 2) → Bool) → M) (f : Fin (k + 2) → Bool) : M :=
  let g := Function.update (Function.update f j false) l false
  let r := h g
  let s := h (Function.update g l true)
  let u := h (Function.update g j true)
  let v := h (Function.update (Function.update g j true) l true)
  if f j then (if f l then (m e).realize ![s, s, v, v] else (m e).realize ![s, r, u, v]) else s

theorem shift_rotation_main {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (hm : IsDayTerms M m)
    (T : Fin (k + 2) → Congruence (L := L) M) (j l : Fin (k + 2)) (hjl : j ≠ l) :
    ∃ R : Fin (n + 1) → ((Fin (k + 2) → Bool) → M) → ((Fin (k + 2) → Bool) → M),
      ∀ h, IsTMatrix T h →
        (∀ e, IsTMatrix T (R e h)) ∧
        (∀ e (f : Fin (k + 2) → Bool),
          let g := Function.update (Function.update f j false) l false
          let r := h g
          let s := h (Function.update g l true)
          let u := h (Function.update g j true)
          let v := h (Function.update (Function.update g j true) l true)
          R e h f = if f j then (if f l then (m e).realize ![s, s, v, v]
            else (m e).realize ![s, r, u, v]) else s) ∧
        (∀ δ : Congruence (L := L) M, SupportingRel δ h j → ∀ e, SupportingRel δ (R e h) l) ∧
        (∀ δ : Congruence (L := L) M,
          LineRel δ h j (Function.update (fun _ => true) l false) →
            (PivotRel δ h j ↔ ∀ e, PivotRel δ (R e h) l)) := by
  have hlj : l ≠ j := Ne.symm hjl
  -- generic vertex bookkeeping: `V` proves equalities of updated vertices pointwise
  have gl : ∀ (f : Fin (k + 2) → Bool) c,
      Function.update (Function.update (Function.update f l c) j false) l false =
        Function.update (Function.update f j false) l false := by
    intro f c; funext i; simp only [Function.update_apply]; split_ifs <;> simp_all
  refine ⟨fun e h => shiftRot m j l e h, fun h hh => ?_⟩
  refine ⟨?_, fun e f => rfl, ?_, ?_⟩
  · -- membership in `M(T)`
    intro e
    obtain ⟨r, t, a, b, hab, ht⟩ := hh
    let N : Fin (k + 2) → Option Bool := fun _ => none
    let t1 := t.subst (pinSub a b (Function.update (Function.update N j (some false)) l (some true)))
    let t2 := t.subst (pinSub a b (Function.update N j (some false)))
    let t4 := t.subst (pinSub a b (Function.update N l (some true)))
    refine ⟨r, (m e).subst ![t1, t2, t, t4], a, b, hab, fun f => ?_⟩
    have e1 : cubeEval t1 a b f = h (Function.update (Function.update f j false) l true) := by
      simp only [t1]; rw [cubeEval_pin, getD_update, getD_update, getD_none, ht]
    have e2 : cubeEval t2 a b f = h (Function.update f j false) := by
      simp only [t2]; rw [cubeEval_pin, getD_update, getD_none, ht]
    have e3 : cubeEval t a b f = h f := (ht f).symm
    have e4 : cubeEval t4 a b f = h (Function.update f l true) := by
      simp only [t4]; rw [cubeEval_pin, getD_update, getD_none, ht]
    have hc : cubeEval ((m e).subst ![t1, t2, t, t4]) a b f = (m e).realize
        ![h (Function.update (Function.update f j false) l true),
          h (Function.update f j false), h f, h (Function.update f l true)] := by
      unfold cubeEval; rw [Term.realize_subst]; congr 1; funext q
      fin_cases q
      · exact e1
      · exact e2
      · exact e3
      · exact e4
    rw [hc]
    simp only [shiftRot]
    cases hfj : f j <;> cases hfl : f l
    · have v1 : Function.update f j false = f := Function.update_eq_self_iff.mpr hfj.symm
      have v2 : Function.update (Function.update (Function.update f j false) l false) l true =
          Function.update f l true := by
        rw [Function.update_idem, v1]
      simp only [Bool.false_eq_true, if_false]
      rw [v2, v1, hm.1]
    · have v1 : Function.update f j false = f := Function.update_eq_self_iff.mpr hfj.symm
      have v2 : Function.update (Function.update (Function.update f j false) l false) l true =
          Function.update f l true := by
        rw [Function.update_idem, v1]
      simp only [Bool.false_eq_true, if_false]
      rw [v2, v1, hm.1]
    · have v1 : Function.update (Function.update (Function.update f j false) l false) l true =
          Function.update (Function.update f j false) l true := by
        funext i; simp only [Function.update_apply]; split_ifs <;> simp_all
      have v2 : Function.update (Function.update f j false) l false = Function.update f j false := by
        funext i; simp only [Function.update_apply]; split_ifs <;> simp_all
      have v3 : Function.update (Function.update (Function.update f j false) l false) j true = f := by
        funext i; simp only [Function.update_apply]; split_ifs <;> simp_all
      simp only [if_true, Bool.false_eq_true, if_false]
      rw [v1, v3, v2]
    · have v1 : Function.update (Function.update (Function.update f j false) l false) l true =
          Function.update f j false := by
        funext i; simp only [Function.update_apply]; split_ifs <;> simp_all
      have v3 : Function.update (Function.update (Function.update (Function.update f j false) l false) j true) l true = f := by
        funext i; simp only [Function.update_apply]; split_ifs <;> simp_all
      have v4 : Function.update f l true = f := by
        funext i; simp only [Function.update_apply]; split_ifs <;> simp_all
      have v5 : Function.update (Function.update f j false) l true = Function.update f j false := by
        funext i; simp only [Function.update_apply]; split_ifs <;> simp_all
      simp only [if_true]
      rw [v1, v3, v4, v5]
  · -- supporting lines
    intro δ hS e f ⟨i, hil, hfi⟩
    unfold LineRel
    simp only [shiftRot, gl, Function.update_of_ne hjl, Function.update_self]
    set g := Function.update (Function.update f j false) l false with hg
    cases hfj : f j
    · exact δ.iseqv.refl _
    · simp only [if_true, if_false, Bool.false_eq_true]
      have hij : i ≠ j := by rintro rfl; simp_all
      have hru : δ.r (h g) (h (Function.update g j true)) := by
        have := hS g ⟨l, hlj, by simp [hg]⟩
        unfold LineRel at this
        have vg : Function.update g j false = g := by
          funext x; simp only [hg, Function.update_apply]; split_ifs <;> simp_all
        rwa [vg] at this
      have hsv : δ.r (h (Function.update g l true))
          (h (Function.update (Function.update g j true) l true)) := by
        have := hS (Function.update g l true) ⟨i, hij, by
          simp [hg, Function.update_of_ne hil, Function.update_of_ne hij, hfi]⟩
        unfold LineRel at this
        have w1 : Function.update (Function.update g l true) j false = Function.update g l true := by
          funext x; simp only [hg, Function.update_apply]; split_ifs <;> simp_all
        have w2 : Function.update (Function.update g l true) j true =
            Function.update (Function.update g j true) l true := Function.update_comm hlj _ _ _
        rwa [w1, w2] at this
      exact day_pair_of_rel hm δ hru hsv e
  · -- pivot lines
    intro δ hL
    set g := Function.update (Function.update (fun _ : Fin (k + 2) => true) j false) l false with hg
    have w1 : Function.update (Function.update (fun _ : Fin (k + 2) => true) l false) j false = g := by
      funext x; simp only [hg, Function.update_apply]; split_ifs <;> simp_all
    have w2 : Function.update (Function.update (fun _ : Fin (k + 2) => true) l false) j true =
        Function.update g j true := by
      funext x; simp only [hg, Function.update_apply]; split_ifs <;> simp_all
    have w3 : Function.update g l true = Function.update (fun _ : Fin (k + 2) => true) j false := by
      funext x; simp only [hg, Function.update_apply]; split_ifs <;> simp_all
    have w4 : Function.update (Function.update g j true) l true =
        Function.update (fun _ : Fin (k + 2) => true) j true := by
      funext x; simp only [hg, Function.update_apply]; split_ifs <;> simp_all
    unfold LineRel at hL
    rw [w1, w2] at hL
    unfold PivotRel LineRel
    simp only [shiftRot, gl, Function.update_of_ne hjl, Function.update_self, if_true,
      Bool.false_eq_true, if_false]
    constructor
    · intro hp e
      rw [w3, w4]
      exact day_pair_of_rel hm δ hL hp e
    · intro hp
      have := day_rel_of_pairs hm δ hL hp
      rwa [w3, w4] at this

end HigherComm

open FirstOrder FirstOrder.Language

theorem solution {L : FirstOrder.Language.{u₁, v₁}} {M : Type w₁} [L.Structure M] {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (hm : HigherComm.IsDayTerms M m)
    (T : Fin (k + 2) → HigherComm.Congruence (L := L) M) (j l : Fin (k + 2)) (hjl : j ≠ l) :
    ∃ R : Fin (n + 1) → ((Fin (k + 2) → Bool) → M) → ((Fin (k + 2) → Bool) → M),
      ∀ h, HigherComm.IsTMatrix T h →
        (∀ e, HigherComm.IsTMatrix T (R e h)) ∧
        (∀ e (f : Fin (k + 2) → Bool),
          let g := Function.update (Function.update f j false) l false
          let r := h g
          let s := h (Function.update g l true)
          let u := h (Function.update g j true)
          let v := h (Function.update (Function.update g j true) l true)
          R e h f = if f j then (if f l then (m e).realize ![s, s, v, v]
            else (m e).realize ![s, r, u, v]) else s) ∧
        (∀ δ : HigherComm.Congruence (L := L) M, HigherComm.SupportingRel δ h j → ∀ e, HigherComm.SupportingRel δ (R e h) l) ∧
        (∀ δ : HigherComm.Congruence (L := L) M,
          HigherComm.LineRel δ h j (Function.update (fun _ => true) l false) →
            (HigherComm.PivotRel δ h j ↔ ∀ e, HigherComm.PivotRel δ (R e h) l)) :=
  HigherComm.shift_rotation_main m hm T j l hjl
