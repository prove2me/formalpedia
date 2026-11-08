-- Prove2me | solution 1 for HigherComm.additivity
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-07T07:53:49.899199+00:00
-- url     : https://prove2.me/submissions/3757ed8d-d362-4aa3-895a-fac745ddb9de

import Definitions.Def_HigherComm_defs
import Theorems.Thm_HigherComm_centralAt_of_centralAt
import Theorems.Thm_HigherComm_centralAt_iff_le
import Mathlib.Tactic.FinCases
import Mathlib.Logic.Relation

universe u₁ v₁ w₁

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open FirstOrder FirstOrder.Language

namespace HigherComm
namespace HCAdd

variable {L : FirstOrder.Language.{u₁, v₁}} {M : Type w₁} [L.Structure M]

/-! ### Congruence basics and Day-term facts -/

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

theorem realize4_rel (δ : Congruence (L := L) M) (t : L.Term (Fin 4)) {a b c d a' b' c' d' : M}
    (ha : δ.r a a') (hb : δ.r b b') (hc : δ.r c c') (hd : δ.r d d') :
    δ.r (t.realize ![a, b, c, d]) (t.realize ![a', b', c', d']) :=
  realize_rel δ t (fun i => by fin_cases i <;> assumption)

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

theorem cong_ext {φ ψ : Congruence (L := L) M} (h : ∀ x y, φ.r x y ↔ ψ.r x y) : φ = ψ := by
  obtain ⟨⟨r, hr⟩, f1, r1⟩ := φ
  obtain ⟨⟨s, hs⟩, f2, r2⟩ := ψ
  have : r = s := funext fun x => funext fun y => propext (h x y)
  subst this
  rfl

/-! ### Joins of congruences are reached by chains -/

/-- Changing the coordinates of a tuple one at a time. -/
theorem coordwise (R : M → M → Prop) {q : ℕ} (P : (Fin q → M) → (Fin q → M) → Prop)
    (hrefl : ∀ c, P c c) (hsymm : ∀ c d, P c d → P d c)
    (htrans : ∀ c d e, P c d → P d e → P c e)
    (hlink : ∀ c p x y, R x y → P (Function.update c p x) (Function.update c p y))
    (a b : Fin q → M) (hab : ∀ p, Relation.EqvGen R (a p) (b p)) : P a b := by
  have hl : ∀ c p x y, Relation.EqvGen R x y →
      P (Function.update c p x) (Function.update c p y) := by
    intro c p x y h
    induction h with
    | rel x y h => exact hlink c p x y h
    | refl x => exact hrefl _
    | symm x y _ ih => exact hsymm _ _ ih
    | trans x y z _ _ ih1 ih2 => exact htrans _ _ _ ih1 ih2
  let mix : ℕ → Fin q → M := fun s p => if p.val < s then b p else a p
  have hstep : ∀ s, P a (mix s) := by
    intro s
    induction s with
    | zero =>
      have : mix 0 = a := by funext p; simp [mix]
      rw [this]; exact hrefl a
    | succ s ih =>
      by_cases hs : s < q
      · have e1 : mix s = Function.update (mix s) ⟨s, hs⟩ (a ⟨s, hs⟩) := by
          funext p
          by_cases hp : p = ⟨s, hs⟩
          · subst hp; simp [mix]
          · rw [Function.update_of_ne hp]
        have e2 : mix (s + 1) = Function.update (mix s) ⟨s, hs⟩ (b ⟨s, hs⟩) := by
          funext p
          by_cases hp : p = ⟨s, hs⟩
          · subst hp; simp [mix]
          · rw [Function.update_of_ne hp]
            have : p.val ≠ s := fun h => hp (Fin.ext h)
            simp only [mix]
            by_cases h1 : p.val < s
            · simp [h1, show p.val < s + 1 by omega]
            · simp [h1, show ¬ p.val < s + 1 by omega]
        refine htrans _ _ _ ih ?_
        rw [e2]; conv => lhs; rw [e1]
        exact hl _ _ _ _ (hab _)
      · have : mix (s + 1) = mix s := by
          funext p; simp only [mix]
          have := p.isLt
          simp [show p.val < s by omega, show p.val < s + 1 by omega]
        rw [this]; exact ih
  have : mix q = b := by funext p; simp [mix, p.isLt]
  rw [← this]; exact hstep q

/-- The equivalence closure of `⋃ γᵢ`, which is a congruence. -/
def joinCong [L.IsAlgebraic] {I : Type*} (γ : I → Congruence (L := L) M) :
    Congruence (L := L) M where
  r := Relation.EqvGen (fun x y => ∃ i, (γ i).r x y)
  iseqv := Relation.EqvGen.is_equivalence _
  fun_compat {n} f x y h := by
    refine coordwise (fun x y => ∃ i, (γ i).r x y)
      (fun x y => Relation.EqvGen (fun x y => ∃ i, (γ i).r x y) (Structure.funMap f x)
        (Structure.funMap f y))
      (fun c => Relation.EqvGen.refl _) (fun c d h => Relation.EqvGen.symm _ _ h)
      (fun c d e h1 h2 => Relation.EqvGen.trans _ _ _ h1 h2) ?_ x y h
    intro c p a b ⟨i, hi⟩
    refine Relation.EqvGen.rel _ _ ⟨i, (γ i).fun_compat f _ _ (fun q => ?_)⟩
    by_cases hq : q = p
    · subst hq; simpa using hi
    · rw [Function.update_of_ne hq, Function.update_of_ne hq]
  rel_compat R _ _ _ := isEmptyElim R

theorem iSup_le_joinCong [L.IsAlgebraic] {I : Type*} (γ : I → Congruence (L := L) M) {x y : M}
    (h : (Congruence.iSup γ).r x y) : (joinCong γ).r x y :=
  h (joinCong γ) (fun i x y hxy => Relation.EqvGen.rel _ _ ⟨i, hxy⟩)

/-! ### Evaluation through block selections -/

variable {K : ℕ} {r : Fin K → ℕ}

/-- The tuple selected at vertex `f`: block `i` is `bᵢ` if `f i` and `aᵢ` otherwise. -/
def sel (a b : (i : Fin K) → Fin (r i) → M) (f : Fin K → Bool) : (i : Fin K) → Fin (r i) → M :=
  fun i => bif f i then b i else a i

/-- Evaluate a polynomial at a choice of tuples for the blocks. -/
def evS (t : L.Term ((Σ i : Fin K, Fin (r i)) ⊕ M)) (S : (i : Fin K) → Fin (r i) → M) : M :=
  t.realize (Sum.elim (fun x => S x.1 x.2) id)

theorem cubeEval_eq (t : L.Term ((Σ i : Fin K, Fin (r i)) ⊕ M))
    (a b : (i : Fin K) → Fin (r i) → M) (f : Fin K → Bool) :
    cubeEval t a b f = evS t (sel a b f) := by
  unfold cubeEval evS sel
  congr 1
  funext x
  rcases x with ⟨i, p⟩ | c
  · show (if f i = true then b i p else a i p) = (bif f i then b i else a i) p
    cases f i <;> rfl
  · rfl

theorem sel_update (a b : (i : Fin K) → Fin (r i) → M) (f : Fin K → Bool) (x : Fin K)
    (c : Bool) : sel a b (Function.update f x c) =
      Function.update (sel a b f) x (bif c then b x else a x) := by
  funext i
  by_cases h : i = x
  · subst h; simp [sel]
  · simp [sel, Function.update_of_ne h]

theorem sel_false (a b : (i : Fin K) → Fin (r i) → M) (f : Fin K → Bool) (x : Fin K) :
    sel a b (Function.update f x false) = Function.update (sel a b f) x (a x) := by
  rw [sel_update]; rfl

theorem sel_true (a b : (i : Fin K) → Fin (r i) → M) (f : Fin K → Bool) (x : Fin K) :
    sel a b (Function.update f x true) = Function.update (sel a b f) x (b x) := by
  rw [sel_update]; rfl

theorem sel_one (a b : (i : Fin K) → Fin (r i) → M) : sel a b (fun _ => true) = b := rfl

theorem sel_upd_lab (a b : (i : Fin K) → Fin (r i) → M) (f : Fin K → Bool) (x : Fin K)
    (c c' : Fin (r x) → M) :
    sel (Function.update a x c) (Function.update b x c') f =
      Function.update (sel a b f) x (bif f x then c' else c) := by
  funext i
  by_cases h : i = x
  · subst h; simp [sel]
  · simp [sel, Function.update_of_ne h]

/-- Pin block `i` to the tuple `w` when `ρ i = some w`. -/
def pinS (ρ : (i : Fin K) → Option (Fin (r i) → M)) :
    ((Σ i : Fin K, Fin (r i)) ⊕ M) → L.Term ((Σ i : Fin K, Fin (r i)) ⊕ M)
  | Sum.inl x => match ρ x.1 with
    | none => Term.var (Sum.inl x)
    | some w => Term.var (Sum.inr (w x.2))
  | Sum.inr c => Term.var (Sum.inr c)

theorem evS_pin (t : L.Term ((Σ i : Fin K, Fin (r i)) ⊕ M))
    (ρ : (i : Fin K) → Option (Fin (r i) → M)) (S : (i : Fin K) → Fin (r i) → M) :
    evS (t.subst (pinS ρ)) S = evS t (fun i => (ρ i).getD (S i)) := by
  unfold evS
  rw [Term.realize_subst]
  congr 1
  funext x
  rcases x with ⟨i, p⟩ | c
  · simp only [pinS]
    rcases hρ : ρ i with _ | w <;> simp [hρ]
  · simp [pinS]

theorem getD_upd (ρ : (i : Fin K) → Option (Fin (r i) → M)) (S : (i : Fin K) → Fin (r i) → M)
    (x : Fin K) (w : Fin (r x) → M) :
    (fun i => (Function.update ρ x (some w) i).getD (S i)) =
      Function.update (fun i => (ρ i).getD (S i)) x w := by
  funext i
  by_cases h : i = x
  · subst h; simp
  · simp [Function.update_of_ne h]

/-- The polynomial of the shift rotation at `(J, Lc)` with pinned tuples `wJ`, `wL`:
`mₑ(t[J:=wJ, Lc:=wL], t[J:=wJ], t, t[Lc:=wL])`. -/
def rotT {n : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (e : Fin (n + 1)) (J Lc : Fin K)
    (wJ : Fin (r J) → M) (wL : Fin (r Lc) → M) (t : L.Term ((Σ i : Fin K, Fin (r i)) ⊕ M)) :
    L.Term ((Σ i : Fin K, Fin (r i)) ⊕ M) :=
  let N : (i : Fin K) → Option (Fin (r i) → M) := fun _ => none
  (m e).subst ![t.subst (pinS (Function.update (Function.update N J (some wJ)) Lc (some wL))),
    t.subst (pinS (Function.update N J (some wJ))), t,
    t.subst (pinS (Function.update N Lc (some wL)))]

theorem evS_rotT {n : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (e : Fin (n + 1)) (J Lc : Fin K)
    (wJ : Fin (r J) → M) (wL : Fin (r Lc) → M) (t : L.Term ((Σ i : Fin K, Fin (r i)) ⊕ M))
    (S : (i : Fin K) → Fin (r i) → M) :
    evS (rotT m e J Lc wJ wL t) S = (m e).realize
      ![evS t (Function.update (Function.update S J wJ) Lc wL),
        evS t (Function.update S J wJ), evS t S, evS t (Function.update S Lc wL)] := by
  unfold rotT
  conv => lhs; unfold evS
  rw [Term.realize_subst]
  congr 1
  funext q
  fin_cases q
  · refine (evS_pin _ _ S).trans ?_
    rw [getD_upd, getD_upd]; rfl
  · refine (evS_pin _ _ S).trans ?_
    rw [getD_upd]; rfl
  · rfl
  · refine (evS_pin _ _ S).trans ?_
    rw [getD_upd]; rfl

/-! ### Shift rotations as functions on matrices -/

def shiftRot {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (j l : Fin (k + 2)) (e : Fin (n + 1))
    (h : (Fin (k + 2) → Bool) → M) (f : Fin (k + 2) → Bool) : M :=
  let g := Function.update (Function.update f j false) l false
  let r := h g
  let s := h (Function.update g l true)
  let u := h (Function.update g j true)
  let v := h (Function.update (Function.update g j true) l true)
  if f j then (if f l then (m e).realize ![s, s, v, v] else (m e).realize ![s, r, u, v]) else s

theorem base_update_l {K : ℕ} (j l : Fin K) (f : Fin K → Bool) (c : Bool) :
    Function.update (Function.update (Function.update f l c) j false) l false =
      Function.update (Function.update f j false) l false := by
  funext i; simp only [Function.update_apply]; split_ifs <;> simp_all

theorem shiftRot_eq {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (hm : IsDayTerms M m)
    (j l : Fin (k + 2)) (hjl : j ≠ l) (e : Fin (n + 1)) (h : (Fin (k + 2) → Bool) → M)
    (f : Fin (k + 2) → Bool) :
    (m e).realize ![h (Function.update (Function.update f j false) l true),
      h (Function.update f j false), h f, h (Function.update f l true)] =
      shiftRot m j l e h f := by
  simp only [shiftRot]
  cases hfj : f j <;> cases hfl : f l
  · have v1 : Function.update f j false = f := Function.update_eq_self_iff.mpr hfj.symm
    have v2 : Function.update (Function.update (Function.update f j false) l false) l true =
        Function.update f l true := by rw [Function.update_idem, v1]
    simp only [Bool.false_eq_true, if_false]
    rw [v2, v1, hm.1]
  · have v1 : Function.update f j false = f := Function.update_eq_self_iff.mpr hfj.symm
    have v2 : Function.update (Function.update (Function.update f j false) l false) l true =
        Function.update f l true := by rw [Function.update_idem, v1]
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
    have v3 : Function.update (Function.update (Function.update (Function.update f j false) l
        false) j true) l true = f := by
      funext i; simp only [Function.update_apply]; split_ifs <;> simp_all
    have v4 : Function.update f l true = f := by
      funext i; simp only [Function.update_apply]; split_ifs <;> simp_all
    have v5 : Function.update (Function.update f j false) l true = Function.update f j false := by
      funext i; simp only [Function.update_apply]; split_ifs <;> simp_all
    simp only [if_true]
    rw [v1, v3, v4, v5]

/-- A rotated polynomial evaluates to the shift rotation of the original matrix. -/
theorem cubeEval_rotT {n k : ℕ} {r : Fin (k + 2) → ℕ} (m : Fin (n + 1) → L.Term (Fin 4))
    (hm : IsDayTerms M m) (e : Fin (n + 1)) (j l : Fin (k + 2)) (hjl : j ≠ l)
    (t : L.Term ((Σ i : Fin (k + 2), Fin (r i)) ⊕ M)) (a b : (i : Fin (k + 2)) → Fin (r i) → M)
    (wJ : Fin (r j) → M) (wL : Fin (r l) → M) (hJ : a j = wJ) (hL : b l = wL) :
    cubeEval (rotT m e j l wJ wL t) a b = shiftRot m j l e (cubeEval t a b) := by
  subst hJ; subst hL
  funext f
  rw [← shiftRot_eq m hm j l hjl e]
  simp only [cubeEval_eq, evS_rotT, sel_true, sel_false]

theorem shiftRot_supp {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (hm : IsDayTerms M m)
    (j l : Fin (k + 2)) (hjl : j ≠ l) (δ : Congruence (L := L) M) (h : (Fin (k + 2) → Bool) → M)
    (hS : SupportingRel δ h j) (e : Fin (n + 1)) : SupportingRel δ (shiftRot m j l e h) l := by
  have hlj : l ≠ j := Ne.symm hjl
  intro f ⟨i, hil, hfi⟩
  unfold LineRel
  simp only [shiftRot, base_update_l, Function.update_of_ne hjl, Function.update_self]
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

theorem shiftRot_piv {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (hm : IsDayTerms M m)
    (j l : Fin (k + 2)) (hjl : j ≠ l) (δ : Congruence (L := L) M) (h : (Fin (k + 2) → Bool) → M)
    (hL : LineRel δ h j (Function.update (fun _ => true) l false))
    (hp : ∀ e, PivotRel δ (shiftRot m j l e h) l) : PivotRel δ h j := by
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
  unfold PivotRel LineRel at hp ⊢
  simp only [shiftRot, base_update_l, Function.update_of_ne hjl, Function.update_self, if_true,
    Bool.false_eq_true, if_false] at hp
  have := day_rel_of_pairs hm δ hL hp
  rwa [w3, w4] at this

/-- Lemma 4.2's constancy computation for consecutive coordinates `(i, i+1)`. -/
theorem shiftRot_const {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (hm : IsDayTerms M m)
    (i : ℕ) (J Lc : Fin (k + 2)) (hJv : J.val = i) (hLv : Lc.val = i + 1)
    (h : (Fin (k + 2) → Bool) → M)
    (hb : ∀ f : Fin (k + 2) → Bool, (∃ j : Fin (k + 2), j.val < i ∧ f j = false) →
      h (Function.update f J false) = h (Function.update f J true))
    (e : Fin (n + 1)) (f : Fin (k + 2) → Bool)
    (hf : ∃ j : Fin (k + 2), j.val < i + 1 ∧ f j = false) :
    shiftRot m J Lc e h (Function.update f Lc false) =
      shiftRot m J Lc e h (Function.update f Lc true) := by
  have hJL : J ≠ Lc := by intro h; have := congrArg Fin.val h; omega
  have hLJ : Lc ≠ J := Ne.symm hJL
  obtain ⟨j, hj, hfj⟩ := hf
  simp only [shiftRot, base_update_l, Function.update_of_ne hJL, Function.update_self]
  set g := Function.update (Function.update f J false) Lc false with hg
  cases hfJ : f J
  · rfl
  · simp only [if_true, if_false, Bool.false_eq_true]
    have hjJ : j ≠ J := by rintro rfl; simp_all
    have hjv : j.val < i := by
      have : j.val ≠ i := fun e => hjJ (Fin.ext (e.trans hJv.symm))
      omega
    have hjL : j ≠ Lc := by
      intro e; have := congrArg Fin.val e; omega
    have hru : h g = h (Function.update g J true) := by
      have := hb g ⟨j, hjv, by
        simp [hg, Function.update_of_ne hjL, Function.update_of_ne hjJ, hfj]⟩
      have vg : Function.update g J false = g := by
        funext x; simp only [hg, Function.update_apply]; split_ifs <;> simp_all
      rwa [vg] at this
    have hsv : h (Function.update g Lc true) =
        h (Function.update (Function.update g J true) Lc true) := by
      have := hb (Function.update g Lc true) ⟨j, hjv, by
        simp [hg, Function.update_of_ne hjL, Function.update_of_ne hjJ, hfj]⟩
      have w1 : Function.update (Function.update g Lc true) J false =
          Function.update g Lc true := by
        funext x; simp only [hg, Function.update_apply]; split_ifs <;> simp_all
      have w2 : Function.update (Function.update g Lc true) J true =
          Function.update (Function.update g J true) Lc true :=
        Function.update_comm hLJ _ _ _
      rwa [w1, w2] at this
    rw [← hru, ← hsv, hm.1, hm.1]

end HCAdd
end HigherComm

namespace HigherComm
namespace HCAdd

variable {L : FirstOrder.Language.{u₁, v₁}} {M : Type w₁} [L.Structure M]

/-! ### The penultimate coordinate: chains through the join -/

/-- The pivot values of the rotated polynomial with last block `w`. -/
def chainVal {n k : ℕ} {r : Fin (k + 2) → ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (e : Fin (n + 1))
    (t : L.Term ((Σ i : Fin (k + 2), Fin (r i)) ⊕ M)) (b : (i : Fin (k + 2)) → Fin (r i) → M)
    (J Lc : Fin (k + 2)) (aJ : Fin (r J) → M) (w : Fin (r Lc) → M) : M :=
  (m e).realize
    ![evS t (Function.update (Function.update (Function.update b Lc w) J aJ) Lc (b Lc)),
      evS t (Function.update (Function.update b Lc w) J aJ),
      evS t (Function.update b Lc w),
      evS t (Function.update (Function.update b Lc w) Lc (b Lc))]

theorem lemF [L.IsAlgebraic] {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (hm : IsDayTerms M m)
    {r : Fin (k + 2) → ℕ} (J Lc : Fin (k + 2)) (hJL : J ≠ Lc)
    (a b : (i : Fin (k + 2)) → Fin (r i) → M) {I : Type*} (γ : I → Congruence (L := L) M)
    (T' : I → Fin (k + 2) → Congruence (L := L) M)
    (hab : ∀ j, j ≠ Lc → ∀ i p, (T' i j).r (a j p) (b j p))
    (habL : ∀ p, (Congruence.iSup γ).r (a Lc p) (b Lc p))
    (hT'L : ∀ i, T' i Lc = γ i)
    (α : Congruence (L := L) M) (hC : ∀ i, CentralAt (T' i) Lc α)
    (t : L.Term ((Σ i : Fin (k + 2), Fin (r i)) ⊕ M))
    (hA : LineRel α (cubeEval t a b) J (Function.update (fun _ => true) Lc false))
    (hB : ∀ (w : Fin (r Lc) → M) (f : Fin (k + 2) → Bool),
      (∃ j, j ≠ J ∧ j ≠ Lc ∧ f j = false) →
      evS t (Function.update (Function.update (sel a b f) Lc w) J (a J)) =
        evS t (Function.update (Function.update (sel a b f) Lc w) J (b J))) :
    PivotRel α (cubeEval t a b) J := by
  have hLJ : Lc ≠ J := Ne.symm hJL
  have hchain : ∀ e, α.r (chainVal m e t b J Lc (a J) (a Lc))
      (chainVal m e t b J Lc (a J) (b Lc)) := by
    intro e
    refine coordwise (fun x y => ∃ i, (γ i).r x y)
      (fun c d => α.r (chainVal m e t b J Lc (a J) c) (chainVal m e t b J Lc (a J) d))
      (fun c => α.iseqv.refl _) (fun c d h => α.iseqv.symm h)
      (fun c d e h1 h2 => α.iseqv.trans h1 h2) ?_ (a Lc) (b Lc)
      (fun p => iSup_le_joinCong γ (habL p))
    intro c p x y ⟨i, hxy⟩
    show α.r (chainVal m e t b J Lc (a J) (Function.update c p x))
      (chainVal m e t b J Lc (a J) (Function.update c p y))
    have hmem : IsTMatrix (T' i) (cubeEval (rotT m e J Lc (a J) (b Lc) t)
        (Function.update a Lc (Function.update c p x))
        (Function.update b Lc (Function.update c p y))) := by
      refine ⟨r, rotT m e J Lc (a J) (b Lc) t, Function.update a Lc (Function.update c p x),
        Function.update b Lc (Function.update c p y), fun j q => ?_, fun f => rfl⟩
      by_cases hj : j = Lc
      · subst hj
        simp only [Function.update_self]
        rw [hT'L]
        by_cases hq : q = p
        · subst hq; simpa using hxy
        · rw [Function.update_of_ne hq, Function.update_of_ne hq]
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]; exact hab j hj i q
    have hval : ∀ (f : Fin (k + 2) → Bool) (cc : Bool),
        cubeEval (rotT m e J Lc (a J) (b Lc) t) (Function.update a Lc (Function.update c p x))
          (Function.update b Lc (Function.update c p y)) (Function.update f Lc cc) =
        (m e).realize
          ![evS t (Function.update (Function.update (Function.update (sel a b f) Lc
              (bif cc then Function.update c p y else Function.update c p x)) J (a J)) Lc (b Lc)),
            evS t (Function.update (Function.update (sel a b f) Lc
              (bif cc then Function.update c p y else Function.update c p x)) J (a J)),
            evS t (Function.update (sel a b f) Lc
              (bif cc then Function.update c p y else Function.update c p x)),
            evS t (Function.update (Function.update (sel a b f) Lc
              (bif cc then Function.update c p y else Function.update c p x)) Lc (b Lc))] := by
      intro f cc
      rw [cubeEval_eq, evS_rotT, sel_upd_lab, sel_update, Function.update_idem,
        Function.update_self]
    have hsupp : SupportingRel α (cubeEval (rotT m e J Lc (a J) (b Lc) t)
        (Function.update a Lc (Function.update c p x))
        (Function.update b Lc (Function.update c p y))) Lc := by
      intro f ⟨j, hjL, hfj⟩
      unfold LineRel
      rw [hval, hval]
      apply rel_of_eq
      have key : ∀ w : Fin (r Lc) → M, (m e).realize
          ![evS t (Function.update (Function.update (Function.update (sel a b f) Lc w) J (a J))
              Lc (b Lc)),
            evS t (Function.update (Function.update (sel a b f) Lc w) J (a J)),
            evS t (Function.update (sel a b f) Lc w),
            evS t (Function.update (Function.update (sel a b f) Lc w) Lc (b Lc))] =
          evS t (Function.update (Function.update (sel a b f) J (a J)) Lc (b Lc)) := by
        intro w
        have e1 : Function.update (Function.update (Function.update (sel a b f) Lc w) J (a J))
            Lc (b Lc) = Function.update (Function.update (sel a b f) J (a J)) Lc (b Lc) := by
          rw [Function.update_comm hLJ, Function.update_idem]
        have e2 : Function.update (Function.update (sel a b f) Lc w) Lc (b Lc) =
            Function.update (sel a b f) Lc (b Lc) := Function.update_idem _ _ _
        rw [e1, e2]
        cases hfJ : f J
        · have hs : sel a b f J = a J := by simp [sel, hfJ]
          have e3 : Function.update (Function.update (sel a b f) Lc w) J (a J) =
              Function.update (sel a b f) Lc w :=
            Function.update_eq_self_iff.mpr (by rw [Function.update_of_ne hJL, hs])
          have e4 : Function.update (sel a b f) J (a J) = sel a b f :=
            Function.update_eq_self_iff.mpr hs.symm
          rw [e3, e4, hm.1]
        · have hs : sel a b f J = b J := by simp [sel, hfJ]
          have hjJ : j ≠ J := by rintro rfl; simp_all
          have hB1 := hB w f ⟨j, hjJ, hjL, hfj⟩
          have hB2 := hB (b Lc) f ⟨j, hjJ, hjL, hfj⟩
          have e5 : Function.update (Function.update (sel a b f) Lc w) J (b J) =
              Function.update (sel a b f) Lc w :=
            Function.update_eq_self_iff.mpr (by rw [Function.update_of_ne hJL, hs])
          have e6 : Function.update (Function.update (sel a b f) Lc (b Lc)) J (b J) =
              Function.update (sel a b f) Lc (b Lc) :=
            Function.update_eq_self_iff.mpr (by rw [Function.update_of_ne hJL, hs])
          rw [e5] at hB1
          rw [e6] at hB2
          rw [hB1]
          have e7 : Function.update (Function.update (sel a b f) J (a J)) Lc (b Lc) =
              Function.update (Function.update (sel a b f) Lc (b Lc)) J (a J) :=
            Function.update_comm hJL _ _ _
          rw [e7, hB2, hm.1]
      rw [key, key]
    have hpiv := hC i _ hmem hsupp
    unfold PivotRel LineRel at hpiv
    rw [hval, hval] at hpiv
    simp only [sel_one, cond_false, cond_true] at hpiv
    unfold chainVal
    exact hpiv
  -- the original matrix
  have f1 : ∀ w : Fin (r Lc) → M, Function.update (Function.update (Function.update b Lc w) J
      (a J)) Lc (b Lc) = Function.update b J (a J) := by
    intro w
    rw [Function.update_comm hLJ, Function.update_idem,
      Function.update_eq_self_iff.mpr (by rw [Function.update_of_ne hLJ])]
  have f2 : Function.update b Lc (b Lc) = b := Function.update_eq_self _ _
  have f4 : ∀ w : Fin (r Lc) → M, Function.update (Function.update b Lc w) Lc (b Lc) = b := by
    intro w; rw [Function.update_idem, f2]
  have f5 : Function.update (Function.update b J (a J)) Lc (b Lc) = Function.update b J (a J) :=
    Function.update_eq_self_iff.mpr (by rw [Function.update_of_ne hLJ])
  have hp : ∀ e, α.r ((m e).realize ![evS t (Function.update b J (a J)),
      evS t (Function.update (Function.update b Lc (a Lc)) J (a J)),
      evS t (Function.update b Lc (a Lc)), evS t b])
      ((m e).realize ![evS t (Function.update b J (a J)), evS t (Function.update b J (a J)),
        evS t b, evS t b]) := by
    intro e
    have := hchain e
    unfold chainVal at this
    simp only [f1, f4, f2, f5] at this
    exact this
  unfold LineRel at hA
  simp only [cubeEval_eq, sel_false, sel_true, sel_one] at hA
  have e8 : Function.update (Function.update b Lc (a Lc)) J (b J) = Function.update b Lc (a Lc) :=
    Function.update_eq_self_iff.mpr (by rw [Function.update_of_ne hJL])
  rw [e8] at hA
  unfold PivotRel LineRel
  simp only [cubeEval_eq, sel_false, sel_true, sel_one]
  rw [Function.update_eq_self]
  exact day_rel_of_pairs hm α hA hp

/-! ### Descending induction over the coordinates below the last one -/

/-- `QA i`: the invariant of the descending induction, for a fixed labelling `(a, b)` and an
arbitrary polynomial `t`; the constancy hypothesis is required for every value of the last
block. -/
def QA {k : ℕ} {r : Fin (k + 2) → ℕ} (α : Congruence (L := L) M)
    (a b : (i : Fin (k + 2)) → Fin (r i) → M) (i : ℕ) (hi : i < k + 2) : Prop :=
  ∀ t : L.Term ((Σ i : Fin (k + 2), Fin (r i)) ⊕ M),
    SupportingRel α (cubeEval t a b) ⟨i, hi⟩ →
    (∀ (c c' : Fin (r (Fin.last (k + 1))) → M) (f : Fin (k + 2) → Bool),
      (∃ j : Fin (k + 2), j.val < i ∧ f j = false) →
      cubeEval t (Function.update a (Fin.last (k + 1)) c) (Function.update b (Fin.last (k + 1)) c')
          (Function.update f ⟨i, hi⟩ false) =
        cubeEval t (Function.update a (Fin.last (k + 1)) c)
          (Function.update b (Fin.last (k + 1)) c') (Function.update f ⟨i, hi⟩ true)) →
    PivotRel α (cubeEval t a b) ⟨i, hi⟩

theorem QA_step {n k : ℕ} {r : Fin (k + 2) → ℕ} (m : Fin (n + 1) → L.Term (Fin 4))
    (hm : IsDayTerms M m) (α : Congruence (L := L) M) (a b : (i : Fin (k + 2)) → Fin (r i) → M)
    (i : ℕ) (hi : i + 1 < k + 1) (hQ : QA α a b (i + 1) (by omega)) :
    QA α a b i (by omega) := by
  intro t hS hB
  have hJL : (⟨i, by omega⟩ : Fin (k + 2)) ≠ ⟨i + 1, by omega⟩ := by simp [Fin.ext_iff]
  have hJl : (⟨i, by omega⟩ : Fin (k + 2)) ≠ Fin.last (k + 1) := by
    simp [Fin.ext_iff, Fin.last]; omega
  have hLl : (⟨i + 1, by omega⟩ : Fin (k + 2)) ≠ Fin.last (k + 1) := by
    simp [Fin.ext_iff, Fin.last]; omega
  have hrot : ∀ e, cubeEval (rotT m e ⟨i, by omega⟩ ⟨i + 1, by omega⟩ (a ⟨i, by omega⟩)
      (b ⟨i + 1, by omega⟩) t) a b =
      shiftRot m ⟨i, by omega⟩ ⟨i + 1, by omega⟩ e (cubeEval t a b) := fun e =>
    cubeEval_rotT m hm e _ _ hJL t a b _ _ rfl rfl
  apply shiftRot_piv m hm _ _ hJL α _ (hS _ ⟨⟨i + 1, by omega⟩, Ne.symm hJL, by simp⟩)
  intro e
  rw [← hrot e]
  apply hQ
  · rw [hrot e]; exact shiftRot_supp m hm _ _ hJL α _ hS e
  · intro c c' f hf
    rw [cubeEval_rotT m hm e _ _ hJL t _ _ _ _ (Function.update_of_ne hJl _ _)
      (Function.update_of_ne hLl _ _)]
    exact shiftRot_const m hm i _ _ rfl rfl _ (fun f hf => hB c c' f hf) e f hf

theorem QA_all [L.IsAlgebraic] {n k : ℕ} {r : Fin (k + 2) → ℕ} (m : Fin (n + 1) → L.Term (Fin 4))
    (hm : IsDayTerms M m) (a b : (i : Fin (k + 2)) → Fin (r i) → M) {I : Type*}
    (γ : I → Congruence (L := L) M) (T' : I → Fin (k + 2) → Congruence (L := L) M)
    (hab : ∀ j, j ≠ Fin.last (k + 1) → ∀ i p, (T' i j).r (a j p) (b j p))
    (habL : ∀ p, (Congruence.iSup γ).r (a (Fin.last (k + 1)) p) (b (Fin.last (k + 1)) p))
    (hT'L : ∀ i, T' i (Fin.last (k + 1)) = γ i)
    (α : Congruence (L := L) M) (hC : ∀ i, CentralAt (T' i) (Fin.last (k + 1)) α) :
    ∀ d i (hi : i < k + 2), i + d = k → QA α a b i hi := by
  intro d
  induction d with
  | zero =>
    intro i hi hd
    have hik : i = k := by omega
    intro t hS hB
    have hJL : (⟨i, hi⟩ : Fin (k + 2)) ≠ Fin.last (k + 1) := by
      simp [Fin.ext_iff, Fin.last]; omega
    refine lemF m hm _ _ hJL a b γ T' hab habL hT'L α hC t
      (hS _ ⟨Fin.last (k + 1), Ne.symm hJL, by simp⟩) ?_
    intro w f ⟨j, hjJ, hjL, hfj⟩
    have hjv : j.val < i := by
      have h1 : j.val ≠ i := fun e => hjJ (Fin.ext e)
      have h2 : j.val ≠ k + 1 := fun e => hjL (Fin.ext e)
      have := j.isLt
      omega
    have := hB w w f ⟨j, hjv, hfj⟩
    simp only [cubeEval_eq, sel_upd_lab, sel_false, sel_true, Bool.cond_self] at this
    rwa [Function.update_of_ne hJL, Function.update_of_ne hJL] at this
  | succ d ih =>
    intro i hi hd
    exact QA_step m hm α a b i (by omega) (ih (i + 1) (by omega) (by omega))

/-! ### Additivity -/

theorem centralAt_mono {K : ℕ} {T T' : Fin K → Congruence (L := L) M}
    (hTT : ∀ j x y, (T' j).r x y → (T j).r x y) {j : Fin K} {δ : Congruence (L := L) M}
    (h : CentralAt T j δ) : CentralAt T' j δ := by
  intro m' hm' hS
  obtain ⟨r, t, a, b, hab, ht⟩ := hm'
  exact h m' ⟨r, t, a, b, fun j p => hTT j _ _ (hab j p), ht⟩ hS

theorem add_main [L.IsAlgebraic] {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4))
    (hm : IsDayTerms M m) (θ : Fin (k + 1) → Congruence (L := L) M) {I : Type*}
    (γ : I → Congruence (L := L) M) :
    higherComm (Fin.snoc θ (Congruence.iSup γ)) =
      Congruence.iSup (fun i => higherComm (Fin.snoc θ (γ i))) := by
  have hT'eq : ∀ i j, j ≠ Fin.last (k + 1) →
      (Fin.snoc θ (γ i) : Fin (k + 2) → Congruence (L := L) M) j =
        (Fin.snoc θ (Congruence.iSup γ) : Fin (k + 2) → Congruence (L := L) M) j := by
    intro i j hj
    obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr hj
    simp [Fin.snoc_castSucc]
  have hlast : ∀ x : Congruence (L := L) M,
      (Fin.snoc θ x : Fin (k + 2) → Congruence (L := L) M) (Fin.last (k + 1)) = x := fun x => by
    simp [Fin.snoc]
  have hγle : ∀ i x y, (γ i).r x y → (Congruence.iSup γ).r x y :=
    fun i x y h φ hφ => hφ i x y h
  have hC : ∀ i, CentralAt (Fin.snoc θ (γ i) : Fin (k + 2) → Congruence (L := L) M)
      (Fin.last (k + 1)) (Congruence.iSup (fun i => higherComm (Fin.snoc θ (γ i)))) :=
    fun i => (centralAt_iff_le m hm _ (Fin.last (k + 1)) _).mpr (fun x y hxy φ hφ => hφ i x y hxy)
  apply cong_ext
  intro x y
  constructor
  · intro hxy
    apply hxy
    have C0 : CentralAt (Fin.snoc θ (Congruence.iSup γ) : Fin (k + 2) → Congruence (L := L) M)
        ⟨0, by omega⟩ (Congruence.iSup (fun i => higherComm (Fin.snoc θ (γ i)))) := by
      intro h hh hS
      obtain ⟨r, t, a, b, hab, ht⟩ := hh
      obtain rfl : h = cubeEval t a b := funext ht
      refine QA_all m hm a b γ (fun i => Fin.snoc θ (γ i)) ?_ ?_ ?_ _ hC k 0 (by omega)
        (by omega) t hS (fun c c' f ⟨j, hj, _⟩ => absurd hj (Nat.not_lt_zero _))
      · intro j hj i p
        rw [hT'eq i j hj]; exact hab j p
      · intro p
        have := hab (Fin.last (k + 1)) p
        rwa [hlast] at this
      · intro i; exact hlast _
    exact centralAt_of_centralAt m hm _ _ _ C0 _
  · intro hxy
    apply hxy
    intro i x' y' h δ hδ
    apply h δ
    refine centralAt_mono (fun j x y hj => ?_) hδ
    by_cases hjl : j = Fin.last (k + 1)
    · subst hjl; rw [hlast] at hj ⊢; exact hγle i x y hj
    · rw [hT'eq i j hjl] at hj; exact hj

end HCAdd
end HigherComm

theorem solution {L : FirstOrder.Language.{u₁, v₁}} {M : Type w₁} [L.Structure M]
    [L.IsAlgebraic] {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (hm : HigherComm.IsDayTerms M m)
    (θ : Fin (k + 1) → HigherComm.Congruence (L := L) M) {I : Type*}
    (γ : I → HigherComm.Congruence (L := L) M) :
    HigherComm.higherComm (Fin.snoc θ (HigherComm.Congruence.iSup γ)) =
      HigherComm.Congruence.iSup (fun i => HigherComm.higherComm (Fin.snoc θ (γ i))) :=
  HigherComm.HCAdd.add_main m hm θ γ
