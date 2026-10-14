-- Prove2me | solution 1 for MoritaEquiv.translation
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-12T21:48:25.299486+00:00
-- url     : https://prove2.me/submissions/1034a8d8-bddc-4ef9-85d2-b263529821fc

import Definitions.Def_MoritaEquiv_defs
import Mathlib.Tactic.Tauto
import Theorems.Thm_MoritaEquiv_MoritaData_model_ext_newSorts

open CategoryTheory

namespace MoritaEquiv

namespace EEU
set_option allowUnsafeReducibility true
attribute [local reducible] MoritaData.sig Ctx.cons

/-! ### Realization lemmas -/

section Realize
variable {L : Sig} (M : Str L) {n : ℕ} {Γ : Fin n → L.Srt} (v : (i : Fin n) → M.carrier (Γ i))

theorem r_not (φ : Formula L Γ) : φ.not.Realize M v ↔ ¬ φ.Realize M v := Iff.rfl

theorem r_imp (φ ψ : Formula L Γ) :
    (Formula.imp φ ψ).Realize M v ↔ (φ.Realize M v → ψ.Realize M v) := Iff.rfl

theorem r_and (φ ψ : Formula L Γ) :
    (φ.and ψ).Realize M v ↔ φ.Realize M v ∧ ψ.Realize M v := by
  show ¬(φ.Realize M v → ¬ψ.Realize M v) ↔ _
  tauto

theorem r_or (φ ψ : Formula L Γ) :
    (φ.or ψ).Realize M v ↔ φ.Realize M v ∨ ψ.Realize M v := by
  show (¬φ.Realize M v → ψ.Realize M v) ↔ _
  tauto

theorem r_iff (φ ψ : Formula L Γ) :
    (φ.iff ψ).Realize M v ↔ (φ.Realize M v ↔ ψ.Realize M v) := by
  rw [Formula.iff, r_and]
  exact iff_def.symm

theorem r_allS (s : L.Srt) (φ : Formula L (Ctx.cons s Γ)) :
    (Formula.allS s φ).Realize M v ↔
      ∀ a : M.carrier s, φ.Realize M (Fin.cons (α := fun i => M.carrier (Ctx.cons s Γ i)) a v) :=
  Iff.rfl

theorem r_exS (s : L.Srt) (φ : Formula L (Ctx.cons s Γ)) :
    (Formula.exS s φ).Realize M v ↔
      ∃ a : M.carrier s, φ.Realize M (Fin.cons (α := fun i => M.carrier (Ctx.cons s Γ i)) a v) := by
  show ¬ (∀ a : M.carrier s, ¬ _) ↔ _
  exact not_forall_not

theorem r_equal {s : L.Srt} (t₁ t₂ : Term L Γ s) :
    (Formula.equal t₁ t₂).Realize M v ↔ t₁.realize M v = t₂.realize M v := Iff.rfl

/-- Apply a unary symbol to a value. -/
def ap {a b : L.Srt} (f : L.Func 1 ![a] b) (z : M.carrier a) : M.carrier b :=
  M.funMap f (Fin.cons (α := fun j => M.carrier (![a] j)) z finZeroElim)

theorem fin1_eq {α : Fin 1 → Type} (g : (j : Fin 1) → α j) :
    g = Fin.cons (α := α) (g 0) finZeroElim := by
  funext j; exact Fin.cases rfl (fun k => k.elim0) j

theorem fin2_eq {α : Fin 2 → Type} (g : (j : Fin 2) → α j) :
    g = Fin.cons (α := α) (g 0) (Fin.cons (α := fun j => α j.succ) (g 1) finZeroElim) := by
  funext j
  exact Fin.cases rfl (fun k => Fin.cases rfl (fun l => l.elim0) k) j

theorem consEta {m : ℕ} {α : Fin (m + 1) → Type} (g : (j : Fin (m + 1)) → α j) :
    Fin.cons (α := α) (g 0) (fun j => g j.succ) = g :=
  Fin.cons_self_tail g

theorem r_app1 {a b : L.Srt} (f : L.Func 1 ![a] b) (t : Term L Γ a) :
    (Term.app1 f t).realize M v = ap M f (t.realize M v) := by
  show M.funMap f _ = M.funMap f _
  congr 1
  funext j; exact Fin.cases rfl (fun k => k.elim0) j

theorem r_eqapp {a b : L.Srt} (f : L.Func 1 ![a] b) (t : Term L Γ a) (u : Term L Γ b) :
    (Formula.equal (Term.app1 f t) u).Realize M v ↔ ap M f (t.realize M v) = u.realize M v := by
  rw [r_equal, r_app1]

theorem r_eqapp2 {a a' b : L.Srt} (f : L.Func 1 ![a] b) (g : L.Func 1 ![a'] b) (t : Term L Γ a)
    (t' : Term L Γ a') :
    (Formula.equal (Term.app1 f t) (Term.app1 g t')).Realize M v ↔
      ap M f (t.realize M v) = ap M g (t'.realize M v) := by
  rw [r_equal, r_app1, r_app1]

theorem r_appeq {a a' b : L.Srt} (f : L.Func 1 ![a] b) (g : L.Func 1 ![a'] b) (t : Term L Γ a)
    (t' : Term L Γ a') :
    (Term.app1 f t).realize M v = (Term.app1 g t').realize M v ↔
      ap M f (t.realize M v) = ap M g (t'.realize M v) := by
  rw [r_app1, r_app1]

theorem funMap_unary {a b : L.Srt} (f : L.Func 1 ![a] b) (g : (j : Fin 1) → M.carrier (![a] j)) :
    M.funMap f g = ap M f (g 0) := by
  unfold ap; congr 1; exact fin1_eq g

theorem realize_fin1 {a : L.Srt} (φ : Formula L ![a]) (w : (j : Fin 1) → M.carrier (![a] j)) :
    φ.Realize M w ↔
      φ.Realize M (Fin.cons (α := fun j => M.carrier (![a] j)) (w 0) finZeroElim) := by
  rw [← fin1_eq w]

theorem realize_fin2 {a : L.Srt} (φ : Formula L ![a, a]) (w : (j : Fin 2) → M.carrier (![a, a] j)) :
    φ.Realize M w ↔ φ.Realize M (Fin.cons (α := fun j => M.carrier (![a, a] j)) (w 0)
      (Fin.cons (α := fun j => M.carrier (![a, a] j.succ)) (w 1) finZeroElim)) := by
  rw [← fin2_eq w]

theorem realize_consEta {m : ℕ} {s : L.Srt} {dom : Fin m → L.Srt} (φ : Formula L (Ctx.cons s dom))
    (w : (j : Fin (m + 1)) → M.carrier (Ctx.cons s dom j)) :
    φ.Realize M (Fin.cons (α := fun j => M.carrier (Ctx.cons s dom j)) (w 0) (fun j => w j.succ)) ↔
      φ.Realize M w := by
  rw [consEta w]

end Realize
section Axioms
variable {L : Sig} {T : Theory L} (D : MoritaData L T) (S : Str D.sig)

open MoritaData
theorem sat_func {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt} (f : D.NewFunc m dom s) :
    S.Satisfies (D.funcAx f) ↔
    ∀ v : (i : Fin (m + 1)) → S.carrier ((D.incl.onSrt ∘ Ctx.cons s dom : Fin (m + 1) → D.sig.Srt) i),
      (S.funMap (L := D.sig) (ExtFunc.new f) (fun j => v j.succ) = v 0 ↔
        (D.funcDef f).Realize (S.reduct D.incl) v) := by
  simp only [Str.Satisfies, funcAx]
  refine forall_congr' fun v => ?_
  simp only [r_iff, r_equal, Formula.realize_onFormula]
  repeat' (first
    | exact Iff.rfl
    | exact r_eqapp2 ..
    | exact r_eqapp ..
    | exact r_appeq ..
    | (apply exists_congr; intro)
    | apply and_congr
    | apply or_congr
    | apply iff_congr
    | apply not_congr
    | apply imp_congr
    | (apply forall_congr'; intro))
theorem mem_func {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt} (f : D.NewFunc m dom s) :
    D.funcAx f ∈ D.ext :=
  Or.inr (Or.inl (Or.inr ⟨m, dom, s, f, rfl⟩))
end Axioms
end EEU

namespace PFU

set_option allowUnsafeReducibility true
attribute [local reducible] MoritaData.sig Ctx.cons

open MoritaData EEU

/-! ### Renaming of variables -/

section Ren
variable {L : Sig}

def tren {n k : ℕ} {Γ : Fin n → L.Srt} {Δ : Fin k → L.Srt} (ρ : Fin n → Fin k)
    (h : ∀ i, Δ (ρ i) = Γ i) : {s : L.Srt} → Term L Γ s → Term L Δ s
  | _, .var i => cast (congrArg (Term L Δ) (h i)) (Term.var (ρ i))
  | _, .func f args => .func f (fun j => tren ρ h (args j))

theorem liftEq {n k : ℕ} {Γ' : Fin (n + 1) → L.Srt} {Δ : Fin k → L.Srt} (ρ : Fin n → Fin k)
    (h : ∀ i, Δ (ρ i) = Fin.tail Γ' i) :
    ∀ i, (Fin.cons (Γ' 0) Δ : Fin (k + 1) → L.Srt)
      ((Fin.cons 0 (fun i => (ρ i).succ) : Fin (n + 1) → Fin (k + 1)) i) = Γ' i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact h j

def fren : {n : ℕ} → {Γ : Fin n → L.Srt} → Formula L Γ → {k : ℕ} → {Δ : Fin k → L.Srt} →
    (ρ : Fin n → Fin k) → (∀ i, Δ (ρ i) = Γ i) → Formula L Δ
  | _, _, .falsum, _, _, _, _ => .falsum
  | _, _, .equal t₁ t₂, _, _, ρ, h => .equal (tren ρ h t₁) (tren ρ h t₂)
  | _, _, .rel r args, _, _, ρ, h => .rel r (fun j => tren ρ h (args j))
  | _, _, .imp φ ψ, _, _, ρ, h => .imp (fren φ ρ h) (fren ψ ρ h)
  | _, _, .all (Γ' := Γ') φ, _, Δ, ρ, h =>
      .all (Γ' := Fin.cons (Γ' 0) Δ) (fren φ (Fin.cons 0 (fun i => (ρ i).succ)) (liftEq ρ h))

theorem cast_realize (M : Str L) {k : ℕ} {Δ : Fin k → L.Srt} (w : (j : Fin k) → M.carrier (Δ j))
    {a b : L.Srt} (e : a = b) (t : Term L Δ a) :
    (cast (congrArg (Term L Δ) e) t).realize M w = cast (congrArg M.carrier e) (t.realize M w) := by
  subst e; rfl

theorem tren_realize (M : Str L) {n k : ℕ} {Γ : Fin n → L.Srt} {Δ : Fin k → L.Srt}
    (ρ : Fin n → Fin k) (h : ∀ i, Δ (ρ i) = Γ i) (w : (j : Fin k) → M.carrier (Δ j))
    {s : L.Srt} (t : Term L Γ s) :
    (tren ρ h t).realize M w =
      t.realize M (fun i => cast (congrArg M.carrier (h i)) (w (ρ i))) := by
  induction t with
  | var i => exact cast_realize M w (h i) (Term.var (ρ i))
  | func f args ih =>
    show M.funMap f _ = M.funMap f _
    exact congrArg _ (funext ih)

theorem fren_realize (M : Str L) {n : ℕ} {Γ : Fin n → L.Srt} (φ : Formula L Γ) :
    ∀ {k : ℕ} {Δ : Fin k → L.Srt} (ρ : Fin n → Fin k) (h : ∀ i, Δ (ρ i) = Γ i)
      (w : (j : Fin k) → M.carrier (Δ j)),
      (fren φ ρ h).Realize M w ↔
        φ.Realize M (fun i => cast (congrArg M.carrier (h i)) (w (ρ i))) := by
  induction φ with
  | falsum => intros; exact Iff.rfl
  | equal t₁ t₂ =>
    intro k Δ ρ h w
    show _ = _ ↔ _ = _
    rw [tren_realize, tren_realize]
  | rel r args =>
    intro k Δ ρ h w
    show M.relMap r _ ↔ M.relMap r _
    exact iff_of_eq (congrArg _ (funext fun j => tren_realize M ρ h w (args j)))
  | imp φ ψ ihφ ihψ =>
    intro k Δ ρ h w
    exact imp_congr (ihφ ρ h w) (ihψ ρ h w)
  | all φ ih =>
    intro k Δ ρ h w
    refine forall_congr' fun a => ?_
    refine (ih _ _ _).trans (iff_of_eq (congrArg _ (funext fun i => ?_)))
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

end Ren

/-! ### Concatenated contexts, existential prefixes, finite conjunctions -/

section Ctx

def ctxApp {S : Type} {k : ℕ} (R : Fin k → S) : {n : ℕ} → (Fin n → S) → Fin (k + n) → S
  | 0, _ => R
  | _ + 1, Γ => Fin.cons (Γ 0) (ctxApp R (Fin.tail Γ))

def appVal {S : Type} {α : S → Type} {k : ℕ} {R : Fin k → S} (w : (j : Fin k) → α (R j)) :
    {n : ℕ} → {Γ : Fin n → S} → ((i : Fin n) → α (Γ i)) → (p : Fin (k + n)) → α (ctxApp R Γ p)
  | 0, _, _ => w
  | _ + 1, Γ, u => Fin.cons (α := fun p => α (ctxApp R Γ p)) (u 0)
      (appVal w (Γ := Fin.tail Γ) (fun i => u i.succ))

def posL {k n : ℕ} (i : Fin n) : Fin (k + n) := ⟨i, by omega⟩

def posR {k n : ℕ} (j : Fin k) : Fin (k + n) := ⟨j + n, by omega⟩

theorem ctxApp_L {S : Type} {k : ℕ} (R : Fin k → S) :
    ∀ {n : ℕ} (Γ : Fin n → S) (i : Fin n), ctxApp R Γ (posL i) = Γ i
  | 0, _, i => i.elim0
  | _ + 1, _, ⟨0, _⟩ => rfl
  | _ + 1, Γ, ⟨i + 1, hi⟩ => ctxApp_L R (Fin.tail Γ) ⟨i, by omega⟩

theorem ctxApp_R {S : Type} {k : ℕ} (R : Fin k → S) :
    ∀ {n : ℕ} (Γ : Fin n → S) (j : Fin k), ctxApp R Γ (posR j) = R j
  | 0, _, _ => rfl
  | _ + 1, Γ, j => ctxApp_R R (Fin.tail Γ) j

theorem appVal_L {S : Type} {α : S → Type} {k : ℕ} {R : Fin k → S} (w : (j : Fin k) → α (R j)) :
    ∀ {n : ℕ} {Γ : Fin n → S} (u : (i : Fin n) → α (Γ i)) (i : Fin n),
      HEq (appVal w u (posL i)) (u i)
  | 0, _, _, i => i.elim0
  | _ + 1, _, _, ⟨0, _⟩ => HEq.rfl
  | _ + 1, Γ, u, ⟨i + 1, hi⟩ => appVal_L w (Γ := Fin.tail Γ) (fun i => u i.succ) ⟨i, by omega⟩

theorem appVal_R {S : Type} {α : S → Type} {k : ℕ} {R : Fin k → S} (w : (j : Fin k) → α (R j)) :
    ∀ {n : ℕ} {Γ : Fin n → S} (u : (i : Fin n) → α (Γ i)) (j : Fin k),
      HEq (appVal w u (posR j)) (w j)
  | 0, _, _, _ => HEq.rfl
  | _ + 1, Γ, u, j => appVal_R w (Γ := Fin.tail Γ) (fun i => u i.succ) j

theorem appVal_map {S : Type} {α β : S → Type} (F : ∀ s, α s → β s) {k : ℕ} {R : Fin k → S}
    (w : (j : Fin k) → α (R j)) :
    ∀ {n : ℕ} {Γ : Fin n → S} (u : (i : Fin n) → α (Γ i)),
      (fun p => F _ (appVal w u p)) = appVal (fun j => F _ (w j)) (fun i => F _ (u i))
  | 0, _, _ => rfl
  | _ + 1, Γ, u => by
    funext p
    match p with
    | ⟨0, _⟩ => rfl
    | ⟨q + 1, hq⟩ =>
      exact congrFun (appVal_map F w (Γ := Fin.tail Γ) (fun i => u i.succ)) ⟨q, by omega⟩

variable {L : Sig}

def exAll {k : ℕ} {R : Fin k → L.Srt} :
    {n : ℕ} → (Γ : Fin n → L.Srt) → Formula L (ctxApp R Γ) → Formula L R
  | 0, _, φ => φ
  | m + 1, Γ, φ => exAll (Fin.tail Γ) (@Formula.ex L (k + m) (ctxApp R Γ) φ)

theorem r_ex (M : Str L) {n : ℕ} {Γ' : Fin (n + 1) → L.Srt} (φ : Formula L Γ')
    (v : (i : Fin n) → M.carrier (Fin.tail Γ' i)) :
    (Formula.ex φ).Realize M v ↔
      ∃ a : M.carrier (Γ' 0), φ.Realize M (Fin.cons (α := fun i => M.carrier (Γ' i)) a v) := by
  show ¬ (∀ a : M.carrier (Γ' 0), ¬ _) ↔ _
  exact not_forall_not

theorem realize_exAll (M : Str L) {k : ℕ} {R : Fin k → L.Srt} (w : (j : Fin k) → M.carrier (R j)) :
    ∀ {n : ℕ} (Γ : Fin n → L.Srt) (φ : Formula L (ctxApp R Γ)),
      (exAll Γ φ).Realize M w ↔
        ∃ u : (i : Fin n) → M.carrier (Γ i), φ.Realize M (appVal (α := M.carrier) w u)
  | 0, _, φ => ⟨fun h => ⟨finZeroElim, h⟩, fun ⟨_, h⟩ => h⟩
  | _ + 1, Γ, φ => by
    refine (realize_exAll M w (Fin.tail Γ) _).trans ?_
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨a, ha⟩ := (r_ex M φ _).1 hu
      exact ⟨Fin.cons a u, ha⟩
    · rintro ⟨u, hu⟩
      exact ⟨fun i => u i.succ, (r_ex M φ _).2 ⟨u 0, hu⟩⟩

def andAll {n : ℕ} {Γ : Fin n → L.Srt} : {m : ℕ} → (Fin m → Formula L Γ) → Formula L Γ
  | 0, _ => Formula.not .falsum
  | _ + 1, F => Formula.and (F 0) (andAll fun i => F i.succ)

theorem realize_andAll (M : Str L) {n : ℕ} {Γ : Fin n → L.Srt} (v : (i : Fin n) → M.carrier (Γ i)) :
    ∀ {m : ℕ} (F : Fin m → Formula L Γ), (andAll F).Realize M v ↔ ∀ i, (F i).Realize M v
  | 0, _ => ⟨fun _ i => i.elim0, fun _ h => h⟩
  | _ + 1, F => by
    refine (r_and M v _ _).trans ?_
    rw [realize_andAll M v (fun i => F i.succ)]
    exact ⟨fun ⟨h0, h⟩ i => Fin.cases h0 h i, fun h => ⟨h 0, fun i => h i.succ⟩⟩

end Ctx

/-! ### Representing elements of new sorts by elements of old sorts -/

section Link
variable {L : Sig} {T : Theory L} (D : MoritaData L T)

def rA : D.ExtSrt → L.Srt
  | .old s => s
  | .prod σ => D.prodFst σ
  | .coprod σ => D.coprodFst σ
  | .sub σ => D.subBase σ
  | .quot σ => D.quotBase σ

def rB : D.ExtSrt → L.Srt
  | .old s => s
  | .prod σ => D.prodSnd σ
  | .coprod σ => D.coprodSnd σ
  | .sub σ => D.subBase σ
  | .quot σ => D.quotBase σ

def linkF {m : ℕ} {C : Fin m → D.sig.Srt} : (s : D.ExtSrt) → Bool → Term D.sig C s →
    Term D.sig C (.old (rA D s)) → Term D.sig C (.old (rB D s)) → Formula D.sig C
  | .old _, _, z, a, _ => .equal z a
  | .prod σ, _, z, a, b =>
    Formula.and (.equal (Term.app1 (L := D.sig) (ExtFunc.fst σ) z) a)
      (.equal (Term.app1 (L := D.sig) (ExtFunc.snd σ) z) b)
  | .coprod σ, true, z, a, _ => .equal (Term.app1 (L := D.sig) (ExtFunc.inl σ) a) z
  | .coprod σ, false, z, _, b => .equal (Term.app1 (L := D.sig) (ExtFunc.inr σ) b) z
  | .sub σ, _, z, a, _ => .equal (Term.app1 (L := D.sig) (ExtFunc.incl σ) z) a
  | .quot σ, _, z, a, _ => .equal (Term.app1 (L := D.sig) (ExtFunc.proj σ) a) z

def linkP (K : Str D.sig) : (s : D.ExtSrt) → Bool → K.carrier s →
    K.carrier (.old (rA D s)) → K.carrier (.old (rB D s)) → Prop
  | .old _, _, z, a, _ => z = a
  | .prod σ, _, z, a, b => ap K (ExtFunc.fst σ) z = a ∧ ap K (ExtFunc.snd σ) z = b
  | .coprod σ, true, z, a, _ => ap K (ExtFunc.inl σ) a = z
  | .coprod σ, false, z, _, b => ap K (ExtFunc.inr σ) b = z
  | .sub σ, _, z, a, _ => ap K (ExtFunc.incl σ) z = a
  | .quot σ, _, z, a, _ => ap K (ExtFunc.proj σ) a = z

theorem realize_linkF (K : Str D.sig) {m : ℕ} {C : Fin m → D.sig.Srt}
    (v : (i : Fin m) → K.carrier (C i)) (s : D.ExtSrt) (c : Bool) (z : Term D.sig C s)
    (a : Term D.sig C (.old (rA D s))) (b : Term D.sig C (.old (rB D s))) :
    (linkF D s c z a b).Realize K v ↔
      linkP D K s c (z.realize K v) (a.realize K v) (b.realize K v) := by
  cases s <;> cases c <;>
    first
    | exact Iff.rfl
    | exact r_eqapp K v _ _ _
    | exact (r_and K v _ _).trans (and_congr (r_eqapp K v _ _ _) (r_eqapp K v _ _ _))

theorem link_unique (K : Model D.ext) (s : D.ExtSrt) (c : Bool) (z z' : K.str.carrier s)
    (a : K.str.carrier (.old (rA D s))) (b : K.str.carrier (.old (rB D s)))
    (h : linkP D K.str s c z a b) (h' : linkP D K.str s c z' a b) : z = z' := by
  cases s with
  | old _ => exact h.trans h'.symm
  | prod σ =>
    obtain ⟨h1, h2⟩ := h
    obtain ⟨h1', h2'⟩ := h'
    exact ((model_ext_newSorts D K).1 σ).1 (Prod.ext (h1.trans h1'.symm) (h2.trans h2'.symm))
  | coprod σ => cases c <;> exact h.symm.trans h'
  | sub σ => exact ((model_ext_newSorts D K).2.2.1 σ).1 (h.trans h'.symm)
  | quot σ => exact h.symm.trans h'

theorem link_exists (K : Model D.ext) (s : D.ExtSrt) (z : K.str.carrier s) :
    ∃ (c : Bool) (a : K.str.carrier (.old (rA D s))) (b : K.str.carrier (.old (rB D s))),
      linkP D K.str s c z a b := by
  cases s with
  | old _ => exact ⟨true, z, z, rfl⟩
  | prod σ => exact ⟨true, _, _, rfl, rfl⟩
  | coprod σ =>
    obtain ⟨a | b, h⟩ := ((model_ext_newSorts D K).2.1 σ).2 z
    · exact ⟨true, a, Classical.choice (K.str.nonempty _), h⟩
    · exact ⟨false, Classical.choice (K.str.nonempty _), b, h⟩
  | sub σ => exact ⟨true, ap K.str (ExtFunc.incl σ) z, ap K.str (ExtFunc.incl σ) z, rfl⟩
  | quot σ =>
    obtain ⟨a, h⟩ := ((model_ext_newSorts D K).2.2.2 σ).1 z
    exact ⟨true, a, a, h⟩

theorem link_map {N N' : Model D.ext} (g : ∀ s : D.sig.Srt, N.str.carrier s → N'.str.carrier s)
    (hfun : ∀ {m : ℕ} {dom : Fin m → D.sig.Srt} {s : D.sig.Srt} (F : D.sig.Func m dom s)
      (x : (j : Fin m) → N.str.carrier (dom j)),
      g s (N.str.funMap F x) = N'.str.funMap F (fun j => g (dom j) (x j)))
    (s : D.ExtSrt) (c : Bool) (z : N.str.carrier s)
    (a : N.str.carrier (.old (rA D s))) (b : N.str.carrier (.old (rB D s)))
    (h : linkP D N.str s c z a b) : linkP D N'.str s c (g s z) (g _ a) (g _ b) := by
  have hap : ∀ {a b : D.sig.Srt} (F : D.sig.Func 1 ![a] b) (z : N.str.carrier a),
      g b (ap N.str F z) = ap N'.str F (g a z) := fun F z =>
    (hfun F _).trans (funMap_unary N'.str F _)
  cases s with
  | old _ => exact congrArg (g _) h
  | prod σ =>
    obtain ⟨h1, h2⟩ := h
    exact ⟨(hap _ z).symm.trans (congrArg (g _) h1), (hap _ z).symm.trans (congrArg (g _) h2)⟩
  | coprod σ =>
    cases c
    · exact (hap _ b).symm.trans (congrArg (g _) h)
    · exact (hap _ a).symm.trans (congrArg (g _) h)
  | sub σ => exact (hap _ z).symm.trans (congrArg (g _) h)
  | quot σ => exact (hap _ a).symm.trans (congrArg (g _) h)

end Link
end PFU

namespace TR
set_option allowUnsafeReducibility true
attribute [local reducible] MoritaData.sig Ctx.cons
open MoritaData EEU PFU

section Gen
variable {L : Sig}

def vc2 (M : Str L) {k : ℕ} {B A : L.Srt} {Δ : Fin k → L.Srt} (b : M.carrier B) (a : M.carrier A)
    (w : (j : Fin k) → M.carrier (Δ j)) :
    (j : Fin (k + 2)) → M.carrier ((Fin.cons B (Fin.cons A Δ) : Fin (k + 2) → L.Srt) j) :=
  Fin.cons (α := fun j => M.carrier ((Fin.cons B (Fin.cons A Δ) : Fin (k + 2) → L.Srt) j)) b
    (Fin.cons (α := fun j => M.carrier ((Fin.cons A Δ : Fin (k + 1) → L.Srt) j)) a w)

theorem vc2_eta (M : Str L) {k : ℕ} {B A : L.Srt} {Δ : Fin k → L.Srt}
    (v : (j : Fin (k + 2)) → M.carrier ((Fin.cons B (Fin.cons A Δ) : Fin (k + 2) → L.Srt) j)) :
    vc2 M (v 0) (v 1) (fun i => v i.succ.succ) = v := by
  funext j
  refine Fin.cases rfl (fun j => Fin.cases rfl (fun i => rfl) j) j

theorem realize_vc2 (M : Str L) {k : ℕ} {B A : L.Srt} {Δ : Fin k → L.Srt}
    (φ : Formula L (Fin.cons B (Fin.cons A Δ) : Fin (k + 2) → L.Srt))
    (v : (j : Fin (k + 2)) → M.carrier ((Fin.cons B (Fin.cons A Δ) : Fin (k + 2) → L.Srt) j)) :
    φ.Realize M v ↔ φ.Realize M (vc2 M (v 0) (v 1) (fun i => v i.succ.succ)) :=
  iff_of_eq (congrArg (φ.Realize M) (vc2_eta M v).symm)

theorem realize_congr (M : Str L) {k : ℕ} {Δ : Fin k → L.Srt} (φ : Formula L Δ)
    {v v' : (j : Fin k) → M.carrier (Δ j)} (h : ∀ j, v j = v' j) :
    φ.Realize M v ↔ φ.Realize M v' := by
  rw [funext h]

theorem cons2_forall {k : ℕ} {P : Fin (k + 2) → Prop} (h0 : P 0) (h1 : P 1)
    (h : ∀ i : Fin k, P i.succ.succ) : ∀ j, P j :=
  fun j => Fin.cases h0 (fun j => Fin.cases h1 h j) j

theorem cons1_forall {k : ℕ} {P : Fin (k + 1) → Prop} (h0 : P 0)
    (h : ∀ i : Fin k, P i.succ) : ∀ j, P j :=
  fun j => Fin.cases h0 h j

theorem fin4_forall {P : Fin 4 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) : ∀ j, P j :=
  fun j => Fin.cases h0 (fun j => Fin.cases h1 (fun j => Fin.cases h2
    (fun j => Fin.cases h3 (fun j => j.elim0) j) j) j) j

theorem cast_eq_of_heq {α β : Type} (h : α = β) {x : α} {y : β} (hxy : HEq x y) : cast h x = y :=
  eq_of_heq ((cast_heq h x).trans hxy)

/-- Universal quantification over two new slots. -/
def all2 {k : ℕ} {B A : L.Srt} {Δ : Fin k → L.Srt}
    (φ : Formula L (Fin.cons B (Fin.cons A Δ) : Fin (k + 2) → L.Srt)) : Formula L Δ :=
  Formula.all (Γ' := (Fin.cons A Δ : Fin (k + 1) → L.Srt))
    (Formula.all (Γ' := (Fin.cons B (Fin.cons A Δ) : Fin (k + 2) → L.Srt)) φ)

theorem realize_all2 (M : Str L) {k : ℕ} {B A : L.Srt} {Δ : Fin k → L.Srt}
    (φ : Formula L (Fin.cons B (Fin.cons A Δ) : Fin (k + 2) → L.Srt))
    (w : (j : Fin k) → M.carrier (Δ j)) :
    (all2 φ).Realize M w ↔ ∀ (a : M.carrier A) (b : M.carrier B), φ.Realize M (vc2 M b a w) :=
  Iff.rfl

/-- Existential quantification over two new slots. -/
def ex2 {k : ℕ} {B A : L.Srt} {Δ : Fin k → L.Srt}
    (φ : Formula L (Fin.cons B (Fin.cons A Δ) : Fin (k + 2) → L.Srt)) : Formula L Δ :=
  Formula.ex (Γ' := (Fin.cons A Δ : Fin (k + 1) → L.Srt))
    (Formula.ex (Γ' := (Fin.cons B (Fin.cons A Δ) : Fin (k + 2) → L.Srt)) φ)

theorem realize_ex2 (M : Str L) {k : ℕ} {B A : L.Srt} {Δ : Fin k → L.Srt}
    (φ : Formula L (Fin.cons B (Fin.cons A Δ) : Fin (k + 2) → L.Srt))
    (w : (j : Fin k) → M.carrier (Δ j)) :
    (ex2 φ).Realize M w ↔ ∃ (a : M.carrier A) (b : M.carrier B), φ.Realize M (vc2 M b a w) :=
  (r_ex (Γ' := (Fin.cons A Δ : Fin (k + 1) → L.Srt)) M _ w).trans
    (exists_congr fun a => r_ex M _ _)

/-! Argument builders. -/

section Args
variable {k m : ℕ} (Δ : Fin k → L.Srt) (dom : Fin m → L.Srt)
  (τ : (j : Fin m) → Formula L (Fin.cons (dom j) (Fin.cons (dom j) Δ) : Fin (k + 2) → L.Srt))

/-- Function-term builder: slots `b, a` of sort `s`, then `Δ`. -/
def argsF (s : L.Srt) (β : Formula L (Ctx.cons s dom)) :
    Formula L (Fin.cons s (Fin.cons s Δ) : Fin (k + 2) → L.Srt) :=
  exAll (R := (Fin.cons s (Fin.cons s Δ) : Fin (k + 2) → L.Srt)) dom
    (Formula.and
      (andAll fun j => fren (τ j)
        (Fin.cons (posL (k := k + 2) j) (Fin.cons (posL (k := k + 2) j)
          (fun i => posR (n := m) (i.succ.succ : Fin (k + 2)))))
        (cons2_forall (ctxApp_L _ dom j) (ctxApp_L _ dom j)
          (fun i => ctxApp_R (Fin.cons s (Fin.cons s Δ) : Fin (k + 2) → L.Srt) dom i.succ.succ)))
      (fren β (Fin.cons (posR (n := m) (1 : Fin (k + 2))) (fun j => posL (k := k + 2) j))
        (cons1_forall (ctxApp_R (Fin.cons s (Fin.cons s Δ) : Fin (k + 2) → L.Srt) dom 1)
          (fun j => ctxApp_L _ dom j))))

theorem realize_argsF (s : L.Srt) (β : Formula L (Ctx.cons s dom)) (M : Str L)
    (b a : M.carrier s) (w : (j : Fin k) → M.carrier (Δ j)) :
    (argsF Δ dom τ s β).Realize M (vc2 M b a w) ↔
      ∃ ys : (j : Fin m) → M.carrier (dom j),
        (∀ j, (τ j).Realize M (vc2 M (ys j) (ys j) w)) ∧
          β.Realize M (Fin.cons (α := fun p => M.carrier (Ctx.cons s dom p)) a ys) := by
  unfold argsF
  rw [realize_exAll]
  refine exists_congr fun ys => ?_
  rw [r_and, realize_andAll]
  refine and_congr (forall_congr' fun j => ?_) ?_
  · refine (fren_realize _ _ _ _ _).trans (realize_congr _ _ ?_)
    intro p
    refine Fin.cases ?_ (fun p => Fin.cases ?_ (fun i => ?_) p) p
    · exact cast_eq_of_heq _ (appVal_L _ ys j)
    · exact cast_eq_of_heq _ (appVal_L _ ys j)
    · exact cast_eq_of_heq _ (appVal_R _ ys _)
  · refine (fren_realize _ _ _ _ _).trans (realize_congr _ _ ?_)
    intro p
    refine Fin.cases ?_ (fun j => ?_) p
    · exact cast_eq_of_heq _ (appVal_R _ ys _)
    · exact cast_eq_of_heq _ (appVal_L _ ys j)

/-- Atomic-relation builder: context `Δ`. -/
def relF (β : Formula L dom) : Formula L Δ :=
  exAll (R := Δ) dom
    (Formula.and
      (andAll fun j => fren (τ j)
        (Fin.cons (posL (k := k) j) (Fin.cons (posL (k := k) j) (fun i => posR (n := m) i)))
        (cons2_forall (ctxApp_L _ dom j) (ctxApp_L _ dom j) (fun i => ctxApp_R Δ dom i)))
      (fren β (fun j => posL (k := k) j) (fun j => ctxApp_L _ dom j)))

theorem realize_relF (β : Formula L dom) (M : Str L) (w : (j : Fin k) → M.carrier (Δ j)) :
    (relF Δ dom τ β).Realize M w ↔
      ∃ ys : (j : Fin m) → M.carrier (dom j),
        (∀ j, (τ j).Realize M (vc2 M (ys j) (ys j) w)) ∧ β.Realize M ys := by
  unfold relF
  rw [realize_exAll]
  refine exists_congr fun ys => ?_
  rw [r_and, realize_andAll]
  refine and_congr (forall_congr' fun j => ?_) ?_
  · refine (fren_realize _ _ _ _ _).trans (realize_congr _ _ ?_)
    intro p
    refine Fin.cases ?_ (fun p => Fin.cases ?_ (fun i => ?_) p) p
    · exact cast_eq_of_heq _ (appVal_L _ ys j)
    · exact cast_eq_of_heq _ (appVal_L _ ys j)
    · exact cast_eq_of_heq _ (appVal_R _ ys _)
  · refine (fren_realize _ _ _ _ _).trans (realize_congr _ _ ?_)
    intro p
    exact cast_eq_of_heq _ (appVal_L _ ys p)

end Args
end Gen

theorem r_all {L : Sig} (M : Str L) {n : ℕ} {Γ' : Fin (n + 1) → L.Srt} (φ : Formula L Γ')
    (v : (i : Fin n) → M.carrier (Fin.tail Γ' i)) :
    (Formula.all φ).Realize M v ↔
      ∀ a : M.carrier (Γ' 0), φ.Realize M (Fin.cons (α := fun i => M.carrier (Γ' i)) a v) :=
  Iff.rfl

section Morita
variable {L : Sig} {T : Theory L} (D : MoritaData L T)

theorem sat_rel (S : Str D.sig) {m : ℕ} {dom : Fin m → L.Srt} (r : D.NewRel m dom) :
    S.Satisfies (D.relAx r) ↔
    ∀ v : (i : Fin m) → S.carrier ((D.incl.onSrt ∘ dom : Fin m → D.sig.Srt) i),
      (S.relMap (L := D.sig) (ExtRel.new r) v ↔ (D.relDef r).Realize (S.reduct D.incl) v) := by
  simp only [Str.Satisfies, relAx]
  refine forall_congr' fun v => ?_
  simp only [r_iff, Formula.realize_onFormula]
  exact Iff.rfl

theorem mem_rel {m : ℕ} {dom : Fin m → L.Srt} (r : D.NewRel m dom) : D.relAx r ∈ D.ext :=
  Or.inr (Or.inr ⟨m, dom, r, rfl⟩)

theorem inl_inj (K : Model D.ext) (σ : D.Coprod) {a a' : K.str.carrier (.old (D.coprodFst σ))}
    (h : ap K.str (ExtFunc.inl σ) a = ap K.str (ExtFunc.inl σ) a') : a = a' :=
  Sum.inl_injective (((model_ext_newSorts D K).2.1 σ).1 h)

theorem inr_inj (K : Model D.ext) (σ : D.Coprod) {b b' : K.str.carrier (.old (D.coprodSnd σ))}
    (h : ap K.str (ExtFunc.inr σ) b = ap K.str (ExtFunc.inr σ) b') : b = b' :=
  Sum.inr_injective (((model_ext_newSorts D K).2.1 σ).1 h)

theorem link_disj (K : Model D.ext) (σ : D.Coprod) {z z' : K.str.carrier (.coprod σ)}
    {a a' : K.str.carrier (.old (D.coprodFst σ))} {b b' : K.str.carrier (.old (D.coprodSnd σ))}
    (h : linkP D K.str (.coprod σ) true z a b) (h' : linkP D K.str (.coprod σ) false z' a' b')
    (hz : z = z') : False :=
  Sum.inl_ne_inr (((model_ext_newSorts D K).2.1 σ).1 (h.trans (hz.trans h'.symm)))

def canon : D.ExtSrt → Bool → Bool
  | .coprod _, c => c
  | _, _ => true

theorem linkP_canon (K : Str D.sig) (e : D.ExtSrt) (c : Bool) :
    linkP D K e (canon D e c) = linkP D K e c := by
  cases e <;> cases c <;> rfl

/-- `(a, b) ≈ (a₂, b₂)` as codes of the same element of sort `e` (code type `c`). -/
def E : (e : D.ExtSrt) → Bool → Formula L ![rA D e, rB D e, rA D e, rB D e]
  | .old _, _ => .equal (.var 0) (.var 2)
  | .prod _, _ => Formula.and (.equal (.var 0) (.var 2)) (.equal (.var 1) (.var 3))
  | .coprod _, true => .equal (.var 0) (.var 2)
  | .coprod _, false => .equal (.var 1) (.var 3)
  | .sub _, _ => .equal (.var 0) (.var 2)
  | .quot σ, _ => fren (D.quotDef σ) ![0, 2]
      (fun j => Fin.cases rfl (fun j => Fin.cases rfl (fun j => j.elim0) j) j)

theorem E_spec (K : Model D.ext) (e : D.ExtSrt) (c : Bool) (z : K.str.carrier e)
    (v : (j : Fin 4) → (K.str.reduct D.incl).carrier (![rA D e, rB D e, rA D e, rB D e] j))
    (h : linkP D K.str e c z (v 2) (v 3)) :
    (E D e c).Realize (K.str.reduct D.incl) v ↔ linkP D K.str e c z (v 0) (v 1) := by
  cases e with
  | old s => exact ⟨fun h' => h.trans h'.symm, fun h' => h'.symm.trans h⟩
  | prod σ =>
    rw [E, r_and]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h.1.trans h1.symm, h.2.trans h2.symm⟩,
      fun ⟨h1, h2⟩ => ⟨h1.symm.trans h.1, h2.symm.trans h.2⟩⟩
  | coprod σ =>
    cases c with
    | true => exact ⟨fun h' => (congrArg _ h').trans h, fun h' => inl_inj D K σ (h'.trans h.symm)⟩
    | false => exact ⟨fun h' => (congrArg _ h').trans h, fun h' => inr_inj D K σ (h'.trans h.symm)⟩
  | sub σ => exact ⟨fun h' => h.trans h'.symm, fun h' => h'.symm.trans h⟩
  | quot σ =>
    rw [E, fren_realize, realize_fin2]
    exact (((model_ext_newSorts D K).2.2.2 σ).2 (v 0) (v 2)).symm.trans
      ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩

/-- Condition on codes `(a, b)` saying that they code some element of sort `e`. -/
def cond {k : ℕ} (Δ : Fin k → L.Srt) :
    (e : D.ExtSrt) → Formula L (Fin.cons (rB D e) (Fin.cons (rA D e) Δ) : Fin (k + 2) → L.Srt)
  | .sub σ => fren (D.subDef σ) (fun _ => 1) (fun j => Fin.cases rfl (fun j => j.elim0) j)
  | .old _ => Formula.not .falsum
  | .prod _ => Formula.not .falsum
  | .coprod _ => Formula.not .falsum
  | .quot _ => Formula.not .falsum

theorem cond_spec (K : Model D.ext) {k : ℕ} (Δ : Fin k → L.Srt) (e : D.ExtSrt) (b0 : Bool)
    (a : K.str.carrier (.old (rA D e))) (b : K.str.carrier (.old (rB D e)))
    (w : (j : Fin k) → (K.str.reduct D.incl).carrier (Δ j)) :
    (cond D Δ e).Realize (K.str.reduct D.incl) (vc2 _ b a w) ↔ ∃ z, linkP D K.str e b0 z a b := by
  cases e with
  | old s => exact ⟨fun _ => ⟨a, rfl⟩, fun _ h => h⟩
  | prod σ =>
    refine ⟨fun _ => ?_, fun _ h => h⟩
    obtain ⟨z, hz⟩ := ((model_ext_newSorts D K).1 σ).2 (a, b)
    exact ⟨z, congrArg Prod.fst hz, congrArg Prod.snd hz⟩
  | coprod σ =>
    cases b0 with
    | true => exact ⟨fun _ => ⟨_, rfl⟩, fun _ h => h⟩
    | false => exact ⟨fun _ => ⟨_, rfl⟩, fun _ h => h⟩
  | sub σ =>
    rw [cond, fren_realize, realize_fin1]
    exact (((model_ext_newSorts D K).2.2.1 σ).2 a).symm
  | quot σ => exact ⟨fun _ => ⟨_, rfl⟩, fun _ h => h⟩

/-- `w` (old-sort values) codes `u` (values of the context `Γ`) via positions `pa, pb`. -/
def Linked (K : Model D.ext) {n k : ℕ} (Γ : Fin n → D.ExtSrt) (c : Fin n → Bool)
    (Δ : Fin k → L.Srt) (pa pb : Fin n → Fin k) (hA : ∀ i, Δ (pa i) = rA D (Γ i))
    (hB : ∀ i, Δ (pb i) = rB D (Γ i)) (u : (i : Fin n) → K.str.carrier (Γ i))
    (w : (j : Fin k) → (K.str.reduct D.incl).carrier (Δ j)) : Prop :=
  ∀ i, linkP D K.str (Γ i) (c i) (u i)
    (cast (congrArg (K.str.reduct D.incl).carrier (hA i)) (w (pa i)))
    (cast (congrArg (K.str.reduct D.incl).carrier (hB i)) (w (pb i)))

theorem func_case (K : Model D.ext) {k m : ℕ} (Δ : Fin k → L.Srt) (dom0 : Fin m → L.Srt)
    (s : L.Srt)
    (τ : (j : Fin m) → Formula L (Fin.cons (dom0 j) (Fin.cons (dom0 j) Δ) : Fin (k + 2) → L.Srt))
    (β : Formula L (Ctx.cons s dom0)) {F : D.sig.Func m (ExtSrt.old ∘ dom0) (.old s)}
    (hβ : ∀ (a : (K.str.reduct D.incl).carrier s)
      (ys : (j : Fin m) → (K.str.reduct D.incl).carrier (dom0 j)),
      β.Realize (K.str.reduct D.incl)
        (Fin.cons (α := fun p => (K.str.reduct D.incl).carrier (Ctx.cons s dom0 p)) a ys) ↔
        K.str.funMap F ys = a)
    (xs : (j : Fin m) → K.str.carrier (.old (dom0 j)))
    (w : (j : Fin k) → (K.str.reduct D.incl).carrier (Δ j))
    (hτ : ∀ j (a b : (K.str.reduct D.incl).carrier (dom0 j)),
      (τ j).Realize (K.str.reduct D.incl) (vc2 _ b a w) ↔ xs j = a)
    (a b : (K.str.reduct D.incl).carrier s) :
    (argsF Δ dom0 τ s β).Realize (K.str.reduct D.incl) (vc2 _ b a w) ↔ K.str.funMap F xs = a := by
  rw [realize_argsF]
  constructor
  · rintro ⟨ys, hys, hb⟩
    have hyx : ys = xs := funext fun j => ((hτ j _ _).1 (hys j)).symm
    subst hyx
    exact (hβ a ys).1 hb
  · intro h
    exact ⟨xs, fun j => (hτ j _ _).2 rfl, (hβ a xs).2 h⟩

theorem rel_case (K : Model D.ext) {k m : ℕ} (Δ : Fin k → L.Srt) (dom0 : Fin m → L.Srt)
    (τ : (j : Fin m) → Formula L (Fin.cons (dom0 j) (Fin.cons (dom0 j) Δ) : Fin (k + 2) → L.Srt))
    (β : Formula L dom0) {R : D.sig.Rel m (ExtSrt.old ∘ dom0)}
    (hβ : ∀ ys : (j : Fin m) → (K.str.reduct D.incl).carrier (dom0 j),
      β.Realize (K.str.reduct D.incl) ys ↔ K.str.relMap R ys)
    (xs : (j : Fin m) → K.str.carrier (.old (dom0 j)))
    (w : (j : Fin k) → (K.str.reduct D.incl).carrier (Δ j))
    (hτ : ∀ j (a b : (K.str.reduct D.incl).carrier (dom0 j)),
      (τ j).Realize (K.str.reduct D.incl) (vc2 _ b a w) ↔ xs j = a) :
    (relF Δ dom0 τ β).Realize (K.str.reduct D.incl) w ↔ K.str.relMap R xs := by
  rw [realize_relF]
  constructor
  · rintro ⟨ys, hys, hb⟩
    have hyx : ys = xs := funext fun j => ((hτ j _ _).1 (hys j)).symm
    subst hyx
    exact (hβ ys).1 hb
  · intro h
    exact ⟨xs, fun j => (hτ j _ _).2 rfl, (hβ xs).2 h⟩

theorem ev_unary (K : Str D.sig) {n : ℕ} {Γ : Fin n → D.ExtSrt} {a b : D.ExtSrt}
    (f : D.sig.Func 1 ![a] b) (args : (j : Fin 1) → Term D.sig Γ (![a] j))
    (u : (i : Fin n) → K.carrier (Γ i)) :
    (Term.func f args).realize K u = ap K f ((args 0).realize K u) :=
  funMap_unary _ _ _

end Morita

section Rep
variable {L : Sig} {T : Theory L} (D : MoritaData L T)

theorem term_rep {n k : ℕ} (Γ : Fin n → D.ExtSrt) (c : Fin n → Bool) (Δ : Fin k → L.Srt)
    (pa pb : Fin n → Fin k) (hA : ∀ i, Δ (pa i) = rA D (Γ i)) (hB : ∀ i, Δ (pb i) = rB D (Γ i)) :
    ∀ {e : D.sig.Srt} (t : Term D.sig Γ e), ∃ (s0 : Bool)
      (τ : Formula L (Fin.cons (rB D e) (Fin.cons (rA D e) Δ) : Fin (k + 2) → L.Srt)),
      ∀ (K : Model D.ext) (u : (i : Fin n) → K.str.carrier (Γ i))
        (w : (j : Fin k) → (K.str.reduct D.incl).carrier (Δ j)),
        Linked D K Γ c Δ pa pb hA hB u w →
          (∃ a b, linkP D K.str e s0 (t.realize K.str u) a b) ∧
          ∀ a b, (τ.Realize (K.str.reduct D.incl) (vc2 _ b a w) ↔
            linkP D K.str e s0 (t.realize K.str u) a b) := by
  intro e t
  induction t with
  | var i =>
    refine ⟨c i, fren (E D (Γ i) (c i))
      (![1, 0, (pa i).succ.succ, (pb i).succ.succ] : Fin 4 → Fin (k + 2))
      (fin4_forall rfl rfl (hA i) (hB i)), fun K u w hL => ⟨⟨_, _, hL i⟩, fun a b => ?_⟩⟩
    exact (fren_realize _ _ _ _ _).trans (E_spec D K _ _ _ _ (hL i))
  | func f args ih =>
    cases f with
    | old f =>
      choose s0 τ hτ using ih
      refine ⟨true, argsF Δ _ τ _ (Formula.equal (Term.func f fun j => Term.var j.succ) (Term.var 0)),
        fun K u w hL => ⟨⟨_, Term.realize K.str u (Term.func (ExtFunc.old f) args), rfl⟩,
          fun a b => ?_⟩⟩
      exact func_case D K Δ _ _ τ _ (fun a ys => Iff.rfl) _ w
        (fun j a b => (hτ j K u w hL).2 a b) a b
    | new f =>
      choose s0 τ hτ using ih
      refine ⟨true, argsF Δ _ τ _ (D.funcDef f),
        fun K u w hL => ⟨⟨_, Term.realize K.str u (Term.func (ExtFunc.new f) args), rfl⟩,
          fun a b => ?_⟩⟩
      exact func_case D K Δ _ _ τ _
        (fun a ys => ((sat_func D K.str f).1 (K.isModel _ (mem_func D f)) (Fin.cons a ys)).symm) _ w
        (fun j a b => (hτ j K u w hL).2 a b) a b
    | fst σ =>
      obtain ⟨s', τ', h'⟩ := ih 0
      refine ⟨true, Formula.ex (Γ' := (Fin.cons (D.prodSnd σ) (Fin.cons (D.prodFst σ)
          (Fin.cons (D.prodFst σ) Δ)) : Fin (k + 3) → L.Srt))
        (fren τ' (Fin.cons 0 (Fin.cons 2 fun i => i.succ.succ.succ) : Fin (k + 2) → Fin (k + 3))
          (cons2_forall rfl rfl fun i => rfl)), fun K u w hL => ?_⟩
      obtain ⟨-, hi⟩ := h' K u w hL
      rw [ev_unary]
      refine ⟨⟨_, ap K.str (ExtFunc.fst σ) ((args 0).realize K.str u), rfl⟩,
        fun a b => (r_ex _ _ _).trans ?_⟩
      refine (exists_congr fun y =>
        (fren_realize _ _ _ _ _).trans ((realize_vc2 _ _ _).trans (hi a y))).trans ?_
      exact ⟨fun ⟨_, h1, _⟩ => h1, fun h1 => ⟨_, h1, rfl⟩⟩
    | snd σ =>
      obtain ⟨s', τ', h'⟩ := ih 0
      refine ⟨true, Formula.ex (Γ' := (Fin.cons (D.prodFst σ) (Fin.cons (D.prodSnd σ)
          (Fin.cons (D.prodSnd σ) Δ)) : Fin (k + 3) → L.Srt))
        (fren τ' (Fin.cons 2 (Fin.cons 0 fun i => i.succ.succ.succ) : Fin (k + 2) → Fin (k + 3))
          (cons2_forall rfl rfl fun i => rfl)), fun K u w hL => ?_⟩
      obtain ⟨-, hi⟩ := h' K u w hL
      rw [ev_unary]
      refine ⟨⟨_, ap K.str (ExtFunc.snd σ) ((args 0).realize K.str u), rfl⟩,
        fun a b => (r_ex _ _ _).trans ?_⟩
      refine (exists_congr fun y =>
        (fren_realize _ _ _ _ _).trans ((realize_vc2 _ _ _).trans (hi y a))).trans ?_
      exact ⟨fun ⟨_, _, h2⟩ => h2, fun h2 => ⟨_, rfl, h2⟩⟩
    | incl σ =>
      obtain ⟨s', τ', h'⟩ := ih 0
      refine ⟨true, fren τ' (Fin.cons 1 (Fin.cons 1 fun i => i.succ.succ) : Fin (k + 2) → Fin (k + 2))
          (cons2_forall rfl rfl fun i => rfl), fun K u w hL => ?_⟩
      obtain ⟨-, hi⟩ := h' K u w hL
      rw [ev_unary]
      exact ⟨⟨_, ap K.str (ExtFunc.incl σ) ((args 0).realize K.str u), rfl⟩,
        fun a b => (fren_realize _ _ _ _ _).trans ((realize_vc2 _ _ _).trans (hi a a))⟩
    | inl σ =>
      obtain ⟨s', τ', h'⟩ := ih 0
      refine ⟨true, fren τ' (Fin.cons 1 (Fin.cons 1 fun i => i.succ.succ) : Fin (k + 2) → Fin (k + 2))
          (cons2_forall rfl rfl fun i => rfl), fun K u w hL => ?_⟩
      obtain ⟨-, hi⟩ := h' K u w hL
      rw [ev_unary]
      refine ⟨⟨_, Classical.choice (K.str.nonempty _), rfl⟩,
        fun a b => (fren_realize _ _ _ _ _).trans ((realize_vc2 _ _ _).trans ((hi a a).trans ?_))⟩
      exact ⟨fun h => congrArg _ h.symm, fun h => (inl_inj D K σ h).symm⟩
    | inr σ =>
      obtain ⟨s', τ', h'⟩ := ih 0
      refine ⟨false, fren τ' (Fin.cons 0 (Fin.cons 0 fun i => i.succ.succ) : Fin (k + 2) → Fin (k + 2))
          (cons2_forall rfl rfl fun i => rfl), fun K u w hL => ?_⟩
      obtain ⟨-, hi⟩ := h' K u w hL
      rw [ev_unary]
      refine ⟨⟨Classical.choice (K.str.nonempty _), _, rfl⟩,
        fun a b => (fren_realize _ _ _ _ _).trans ((realize_vc2 _ _ _).trans ((hi b b).trans ?_))⟩
      exact ⟨fun h => congrArg _ h.symm, fun h => (inr_inj D K σ h).symm⟩
    | proj σ =>
      obtain ⟨s', τ', h'⟩ := ih 0
      refine ⟨true, Formula.ex (Γ' := (Fin.cons (D.quotBase σ) (Fin.cons (D.quotBase σ)
          (Fin.cons (D.quotBase σ) Δ)) : Fin (k + 3) → L.Srt))
        (Formula.and
          (fren τ' (Fin.cons 0 (Fin.cons 0 fun i => i.succ.succ.succ) : Fin (k + 2) → Fin (k + 3))
            (cons2_forall rfl rfl fun i => rfl))
          (fren (D.quotDef σ) (![2, 0] : Fin 2 → Fin (k + 3))
            (fun j => Fin.cases rfl (fun j => Fin.cases rfl (fun j => j.elim0) j) j))),
        fun K u w hL => ?_⟩
      obtain ⟨-, hi⟩ := h' K u w hL
      rw [ev_unary]
      refine ⟨⟨_, Classical.choice (K.str.nonempty _), rfl⟩, fun a b => (r_ex _ _ _).trans ?_⟩
      refine (exists_congr fun y => (r_and _ _ _ _).trans (and_congr
        ((fren_realize _ _ _ _ _).trans ((realize_vc2 _ _ _).trans (hi y y)))
        ((fren_realize _ _ _ _ _).trans (realize_fin2 _ _ _)))).trans ?_
      have hq := ((model_ext_newSorts D K).2.2.2 σ).2
      constructor
      · rintro ⟨y, rfl, hy⟩
        exact (hq a _).2 hy
      · intro h
        exact ⟨_, rfl, (hq a _).1 h⟩

theorem form_rep : ∀ {n : ℕ} {Γ : Fin n → D.sig.Srt} (φ : Formula D.sig Γ) {k : ℕ}
    (Δ : Fin k → L.Srt) (c : Fin n → Bool) (pa pb : Fin n → Fin k)
    (hA : ∀ i, Δ (pa i) = rA D (Γ i)) (hB : ∀ i, Δ (pb i) = rB D (Γ i)),
    ∃ ψ : Formula L Δ, ∀ (K : Model D.ext) (u : (i : Fin n) → K.str.carrier (Γ i))
      (w : (j : Fin k) → (K.str.reduct D.incl).carrier (Δ j)),
      Linked D K Γ c Δ pa pb hA hB u w →
        (φ.Realize K.str u ↔ ψ.Realize (K.str.reduct D.incl) w) := by
  intro n Γ φ
  induction φ with
  | falsum => exact fun Δ c pa pb hA hB => ⟨.falsum, fun _ _ _ _ => Iff.rfl⟩
  | @equal n Γ e t₁ t₂ =>
    intro k Δ c pa pb hA hB
    obtain ⟨s1, τ1, h1⟩ := term_rep D Γ c Δ pa pb hA hB t₁
    obtain ⟨s2, τ2, h2⟩ := term_rep D Γ c Δ pa pb hA hB t₂
    by_cases hs : canon D e s1 = canon D e s2
    · have h12 : ∀ K : Str D.sig, linkP D K e s1 = linkP D K e s2 := fun K => by
        rw [← linkP_canon D K e s1, hs, linkP_canon]
      refine ⟨ex2 (Formula.and τ1 τ2), fun K u w hL => ?_⟩
      rw [realize_ex2]
      obtain ⟨⟨a0, b0, hab⟩, i1⟩ := h1 K u w hL
      obtain ⟨-, i2⟩ := h2 K u w hL
      constructor
      · intro heq
        refine ⟨a0, b0, (r_and _ _ _ _).2 ⟨(i1 a0 b0).2 hab, (i2 a0 b0).2 ?_⟩⟩
        rw [← h12 K.str]
        exact heq ▸ hab
      · rintro ⟨a, b, hab'⟩
        obtain ⟨ha, hb⟩ := (r_and _ _ _ _).1 hab'
        have hb' := (i2 a b).1 hb
        rw [← h12 K.str] at hb'
        exact link_unique D K e s1 _ _ a b ((i1 a b).1 ha) hb'
    · refine ⟨Formula.falsum, fun K u w hL => ⟨fun heq => ?_, fun h => h.elim⟩⟩
      obtain ⟨a, b, ha⟩ := (h1 K u w hL).1
      obtain ⟨a', b', hb⟩ := (h2 K u w hL).1
      cases e <;> try exact absurd rfl hs
      cases s1 <;> cases s2 <;> try exact absurd rfl hs
      · exact link_disj D K _ hb ha heq.symm
      · exact link_disj D K _ ha hb heq
  | @rel n Γ m dom r args =>
    intro k Δ c pa pb hA hB
    cases r with
    | old r =>
      choose s0 τ hτ using fun j => term_rep D Γ c Δ pa pb hA hB (args j)
      refine ⟨relF Δ _ τ (Formula.rel r fun j => Term.var j), fun K u w hL => ?_⟩
      exact (rel_case D K Δ _ τ _ (fun ys => Iff.rfl) _ w
        (fun j a b => (hτ j K u w hL).2 a b)).symm
    | new r =>
      choose s0 τ hτ using fun j => term_rep D Γ c Δ pa pb hA hB (args j)
      refine ⟨relF Δ _ τ (D.relDef r), fun K u w hL => ?_⟩
      exact (rel_case D K Δ _ τ _
        (fun ys => ((sat_rel D K.str r).1 (K.isModel _ (mem_rel D r)) ys).symm) _ w
        (fun j a b => (hτ j K u w hL).2 a b)).symm
  | imp φ ψ ih1 ih2 =>
    intro k Δ c pa pb hA hB
    obtain ⟨ψ1, h1⟩ := ih1 Δ c pa pb hA hB
    obtain ⟨ψ2, h2⟩ := ih2 Δ c pa pb hA hB
    exact ⟨.imp ψ1 ψ2, fun K u w hL => imp_congr (h1 K u w hL) (h2 K u w hL)⟩
  | @all n Γ' φ ih =>
    intro k Δ c pa pb hA hB
    have IH := fun b0 => ih (Fin.cons (rB D (Γ' 0)) (Fin.cons (rA D (Γ' 0)) Δ) : Fin (k + 2) → L.Srt)
      (Fin.cons b0 c) (Fin.cons 1 (fun i => (pa i).succ.succ) : Fin (n + 1) → Fin (k + 2))
      (Fin.cons 0 (fun i => (pb i).succ.succ) : Fin (n + 1) → Fin (k + 2))
      (cons1_forall rfl hA) (cons1_forall rfl hB)
    obtain ⟨ψT, hT⟩ := IH true
    obtain ⟨ψF, hF⟩ := IH false
    refine ⟨Formula.and (all2 (Formula.imp (cond D Δ (Γ' 0)) ψT))
      (all2 (Formula.imp (cond D Δ (Γ' 0)) ψF)), fun K u w hL => ?_⟩
    have hL' : ∀ (b0 : Bool) (x : K.str.carrier (Γ' 0)) (a : K.str.carrier (.old (rA D (Γ' 0))))
        (b : K.str.carrier (.old (rB D (Γ' 0)))), linkP D K.str (Γ' 0) b0 x a b →
        Linked D K Γ' (Fin.cons b0 c)
          (Fin.cons (rB D (Γ' 0)) (Fin.cons (rA D (Γ' 0)) Δ) : Fin (k + 2) → L.Srt)
          (Fin.cons 1 (fun i => (pa i).succ.succ) : Fin (n + 1) → Fin (k + 2))
          (Fin.cons 0 (fun i => (pb i).succ.succ) : Fin (n + 1) → Fin (k + 2))
          (cons1_forall rfl hA) (cons1_forall rfl hB)
          (Fin.cons (α := fun i => K.str.carrier (Γ' i)) x u) (vc2 _ b a w) := by
      intro b0 x a b hx i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact hx
      · exact hL i
    rw [r_all, r_and, realize_all2, realize_all2]
    constructor
    · intro hφ
      refine ⟨fun a b hc => ?_, fun a b hc => ?_⟩
      · obtain ⟨x, hx⟩ := (cond_spec D K Δ (Γ' 0) true a b w).1 hc
        exact (hT K _ _ (hL' true x a b hx)).1 (hφ x)
      · obtain ⟨x, hx⟩ := (cond_spec D K Δ (Γ' 0) false a b w).1 hc
        exact (hF K _ _ (hL' false x a b hx)).1 (hφ x)
    · rintro ⟨hTa, hFa⟩ x
      obtain ⟨c0, a, b, hx⟩ := link_exists D K (Γ' 0) x
      cases c0 with
      | true =>
        exact (hT K _ _ (hL' true x a b hx)).2
          (hTa a b ((cond_spec D K Δ (Γ' 0) true a b w).2 ⟨x, hx⟩))
      | false =>
        exact (hF K _ _ (hL' false x a b hx)).2
          (hFa a b ((cond_spec D K Δ (Γ' 0) false a b w).2 ⟨x, hx⟩))

theorem tr_main {n : ℕ} (Γ : Fin n → L.Srt) (φ : Formula D.sig (D.incl.onSrt ∘ Γ)) :
    ∃ ψ : Formula L Γ, ∀ (N : Model D.ext) (v : (i : Fin n) → N.str.carrier (D.incl.onSrt (Γ i))),
      φ.Realize N.str v ↔ (ψ.onFormula D.incl).Realize N.str v := by
  obtain ⟨ψ, hψ⟩ := form_rep D φ Γ (fun _ => true) id id (fun _ => rfl) (fun _ => rfl)
  exact ⟨ψ, fun N v => (hψ N v v (fun _ => rfl)).trans (Formula.realize_onFormula _ _ _ _).symm⟩

end Rep

end TR
end MoritaEquiv

open MoritaEquiv

theorem solution {L : Sig} {T : Theory L} (D : MoritaData L T) {n : ℕ} (Γ : Fin n → L.Srt)
    (φ : Formula D.sig (D.incl.onSrt ∘ Γ)) :
    ∃ ψ : Formula L Γ, ∀ (N : Model D.ext) (v : (i : Fin n) → N.str.carrier (D.incl.onSrt (Γ i))),
      φ.Realize N.str v ↔ (ψ.onFormula D.incl).Realize N.str v :=
  TR.tr_main D Γ φ
