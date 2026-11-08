-- Prove2me | solution 1 for HigherComm.centralAt_iff_twoTerm
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-07T08:06:27.284025+00:00
-- url     : https://prove2.me/submissions/6a3608ee-e14f-4edb-87b2-f3e922725497

import Definitions.Def_HigherComm_defs
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin

universe u₁ v₁ w₁

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open FirstOrder FirstOrder.Language FirstOrder.Language.Structure

namespace HigherComm
namespace HCTT

variable {L : FirstOrder.Language.{u₁, v₁}} {M : Type w₁} [L.Structure M]

/-! ### Congruence helpers and Day's shifting lemma -/

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

/-! ### Closure properties of `M(T)` -/

/-- `M(T)` is closed under precomposition with a coordinatewise Boolean map
`f ↦ (j ↦ φⱼ (f j))` (pinning or flipping coordinates). -/
theorem isTMatrix_comp {k : ℕ} {T : Fin k → Congruence (L := L) M} {h : (Fin k → Bool) → M}
    (hh : IsTMatrix T h) (φ : Fin k → Bool → Bool) :
    IsTMatrix T (fun f => h (fun j => φ j (f j))) := by
  obtain ⟨r, t, a, b, hab, ht⟩ := hh
  refine ⟨r, t, fun j p => cond (φ j false) (b j p) (a j p),
    fun j p => cond (φ j true) (b j p) (a j p), fun j p => ?_, fun f => ?_⟩
  · show (T j).r (cond (φ j false) (b j p) (a j p)) (cond (φ j true) (b j p) (a j p))
    rcases φ j false <;> rcases φ j true
    · exact (T j).iseqv.refl _
    · exact hab j p
    · exact (T j).iseqv.symm (hab j p)
    · exact (T j).iseqv.refl _
  · show h (fun j => φ j (f j)) = _
    rw [ht]
    unfold cubeEval
    congr 1
    funext x
    rcases x with ⟨j, p⟩ | c
    · rcases hfj : f j <;> simp [hfj, Bool.cond_eq_ite]
    · rfl

/-- `M(T)` is closed under applying a term to finitely many `T`-matrices vertexwise. -/
theorem isTMatrix_combine {k n : ℕ} {T : Fin k → Congruence (L := L) M}
    (h : Fin n → (Fin k → Bool) → M) (hh : ∀ q, IsTMatrix T (h q)) (p : L.Term (Fin n)) :
    IsTMatrix T (fun f => p.realize (fun q => h q f)) := by
  choose r t a b hab ht using hh
  let E : ∀ j : Fin k, (Σ q : Fin n, Fin (r q j)) ≃ Fin (∑ q, r q j) :=
    fun j => finSigmaFinEquiv
  let rel : ∀ q, ((Σ j : Fin k, Fin (r q j)) ⊕ M) → ((Σ j : Fin k, Fin (∑ q, r q j)) ⊕ M) :=
    fun q => Sum.map (fun x => ⟨x.1, E x.1 ⟨q, x.2⟩⟩) id
  refine ⟨fun j => ∑ q, r q j, p.subst (fun q => (t q).relabel (rel q)),
    fun j x => a ((E j).symm x).1 j ((E j).symm x).2,
    fun j x => b ((E j).symm x).1 j ((E j).symm x).2, fun j x => hab _ _ _, fun f => ?_⟩
  show p.realize (fun q => h q f) = _
  unfold cubeEval
  rw [Term.realize_subst]
  congr 1
  funext q
  rw [ht q f, Term.realize_relabel]
  unfold cubeEval
  congr 1
  funext x
  rcases x with ⟨j, y⟩ | c
  · simp [rel]
    rw [Equiv.symm_apply_apply]
  · rfl

/-! ### Vertex maps -/

/-- Pin coordinate `i` to the value `c`. -/
def pin {k : ℕ} (i : Fin k) (c : Bool) (j : Fin k) (x : Bool) : Bool := if j = i then c else x

/-- Flip coordinate `i`. -/
def flip {k : ℕ} (i : Fin k) (j : Fin k) (x : Bool) : Bool := if j = i then !x else x

theorem pin_eq {k : ℕ} (i : Fin k) (c : Bool) (f : Fin k → Bool) :
    (fun j => pin i c j (f j)) = Function.update f i c := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [pin]
  · simp [pin, hj, Function.update_of_ne hj]

theorem flip_eq {k : ℕ} (i : Fin k) (f : Fin k → Bool) :
    (fun j => flip i j (f j)) = Function.update f i (!f i) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [flip]
  · simp [flip, hj, Function.update_of_ne hj]

theorem upd_one {k : ℕ} (i : Fin k) :
    Function.update (fun _ : Fin k => true) i true = fun _ => true :=
  Function.update_eq_self i _

theorem ne_one_of {k : ℕ} (f : Fin k → Bool) (l : Fin k) (hl : f l = false) :
    f ≠ fun _ => true := by
  intro heq; subst heq; simp at hl

/-! ### The two directions -/

/-- `C_tt(T; δ) ⇒ C(T; j; δ)`: compare `h` with `h` pinned to `0` at block `j`. -/
theorem central_of_tt {k : ℕ} (T : Fin (k + 2) → Congruence (L := L) M) (j : Fin (k + 2))
    (δ : Congruence (L := L) M) (hT : TwoTermCentral T δ) : CentralAt T j δ := by
  intro h hh hS
  have hg := isTMatrix_comp hh (pin j false)
  have key := hT h _ hh hg (fun f hf => by
    show δ.r (h f) (h (fun l => pin j false l (f l)))
    rw [pin_eq]
    rcases hfj : f j
    · rw [show Function.update f j false = f from Function.update_eq_self_iff.mpr hfj.symm]
    · obtain ⟨l, hl⟩ : ∃ l, f l = false := by
        by_contra hc
        exact hf (funext fun l => by
          cases hfl : f l
          · exact absurd ⟨l, hfl⟩ hc
          · rfl)
      have hlj : l ≠ j := by
        rintro rfl; rw [hfj] at hl; exact Bool.noConfusion hl
      have := hS f ⟨l, hlj, hl⟩
      unfold LineRel at this
      rw [show Function.update f j true = f from Function.update_eq_self_iff.mpr hfj.symm] at this
      exact rel_symm δ this)
  change δ.r (h (fun _ => true)) (h (fun l => pin j false l ((fun _ => true) l))) at key
  rw [pin_eq] at key
  unfold PivotRel LineRel
  rw [upd_one]
  exact rel_symm δ key

/-- `C(T; i; δ) ⇒ C_tt(T; δ)` (Moorhead Prop 6.4): the matrix
`qₑ(f) = mₑ(h(f[i:=1]), h(f[i:=¬fᵢ]), g(f[i:=¬fᵢ]), g(f[i:=1]))` has `δ`-related supporting
lines, its pivot line is `⟨mₑ(c,c,d,d), mₑ(c,a,b,d)⟩`, and Day's argument finishes. -/
theorem tt_of_central {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (hm : IsDayTerms M m)
    (T : Fin (k + 2) → Congruence (L := L) M) (i : Fin (k + 2)) (δ : Congruence (L := L) M)
    (hC : CentralAt T i δ) : TwoTermCentral T δ := by
  intro h g hh hg hfg
  let H : Fin 4 → (Fin (k + 2) → Bool) → M :=
    ![fun f => h (fun j => pin i true j (f j)), fun f => h (fun j => flip i j (f j)),
      fun f => g (fun j => flip i j (f j)), fun f => g (fun j => pin i true j (f j))]
  have hH : ∀ q, IsTMatrix T (H q) := by
    intro q
    fin_cases q
    · exact isTMatrix_comp hh (pin i true)
    · exact isTMatrix_comp hh (flip i)
    · exact isTMatrix_comp hg (flip i)
    · exact isTMatrix_comp hg (pin i true)
  let Q : Fin (n + 1) → (Fin (k + 2) → Bool) → M :=
    fun e f => (m e).realize (fun q => H q f)
  have hQ : ∀ e f, Q e f = (m e).realize ![h (Function.update f i true),
      h (Function.update f i (!f i)), g (Function.update f i (!f i)),
      g (Function.update f i true)] := by
    intro e f
    simp only [Q]
    congr 1
    funext q
    fin_cases q <;> simp [H, pin_eq, flip_eq]
  have hS : ∀ e, SupportingRel δ (Q e) i := by
    intro e f ⟨l, hli, hfl⟩
    unfold LineRel
    rw [hQ, hQ]
    simp only [Function.update_idem, Function.update_self, Bool.not_false, Bool.not_true]
    have h1 : δ.r (g (Function.update f i true)) (h (Function.update f i true)) :=
      rel_symm δ (hfg _ (ne_one_of _ l (by simp [Function.update_of_ne hli, hfl])))
    have h0 : δ.r (g (Function.update f i false)) (h (Function.update f i false)) :=
      rel_symm δ (hfg _ (ne_one_of _ l (by simp [Function.update_of_ne hli, hfl])))
    have a1 := rel_trans δ (realize4_rel δ (m e) (δ.iseqv.refl _) (δ.iseqv.refl _) h1 h1)
      (rel_of_eq δ (hm.1 e (h (Function.update f i true)) (h (Function.update f i true))))
    have a2 := rel_trans δ (realize4_rel δ (m e) (δ.iseqv.refl _) (δ.iseqv.refl _) h0 h1)
      (rel_of_eq δ (hm.1 e (h (Function.update f i true)) (h (Function.update f i false))))
    exact rel_trans δ a1 (rel_symm δ a2)
  have P : ∀ e, δ.r ((m e).realize ![h (fun _ => true), h (Function.update (fun _ => true) i false),
      g (Function.update (fun _ => true) i false), g (fun _ => true)])
      ((m e).realize ![h (fun _ => true), h (fun _ => true), g (fun _ => true),
        g (fun _ => true)]) := by
    intro e
    have := hC _ (isTMatrix_combine H hH (m e)) (hS e)
    change LineRel δ (Q e) i (fun _ => true) at this
    unfold LineRel at this
    rw [hQ, hQ] at this
    simp only [Function.update_idem, Function.update_self, Bool.not_false, Bool.not_true,
      upd_one] at this
    exact rel_symm δ this
  exact day_rel_of_pairs hm δ
    (hfg _ (ne_one_of _ i (by simp))) P

end HCTT
end HigherComm

open HigherComm.HCTT

theorem solution {L : FirstOrder.Language.{u₁, v₁}} {M : Type w₁} [L.Structure M] [L.IsAlgebraic]
    {n k : ℕ} (m : Fin (n + 1) → L.Term (Fin 4)) (hm : HigherComm.IsDayTerms M m)
    (T : Fin (k + 2) → HigherComm.Congruence (L := L) M) (j : Fin (k + 2))
    (δ : HigherComm.Congruence (L := L) M) :
    HigherComm.CentralAt T j δ ↔ HigherComm.TwoTermCentral T δ :=
  ⟨tt_of_central m hm T j δ, central_of_tt T j δ⟩
