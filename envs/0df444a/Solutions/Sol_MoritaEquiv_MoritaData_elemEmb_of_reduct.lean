-- Prove2me | solution 1 for MoritaEquiv.MoritaData.elemEmb_of_reduct
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-12T20:44:04.127504+00:00
-- url     : https://prove2.me/submissions/4d549fcd-9871-48d6-8269-aa181ef17959

import Mathlib
import Definitions.Def_MoritaEquiv_defs
import Theorems.Thm_MoritaEquiv_MoritaData_model_ext_newSorts
import Theorems.Thm_MoritaEquiv_translation

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

/-- The old-sorted representative context: `rB`-slots first, then `rA`-slots. -/
abbrev RR {n : ℕ} (Γ : Fin n → D.sig.Srt) : Fin (n + n) → L.Srt :=
  ctxApp (fun i => rA D (Γ i)) (fun i => rB D (Γ i))

theorem eZ {n : ℕ} (Γ : Fin n → D.sig.Srt) (i : Fin n) :
    ctxApp (D.incl.onSrt ∘ RR D Γ) Γ (posL i) = Γ i := ctxApp_L _ Γ i

theorem eA {n : ℕ} (Γ : Fin n → D.sig.Srt) (i : Fin n) :
    ctxApp (D.incl.onSrt ∘ RR D Γ) Γ (posR (posR i)) = ExtSrt.old (rA D (Γ i)) :=
  (ctxApp_R _ Γ _).trans (congrArg ExtSrt.old (ctxApp_R _ _ i))

theorem eB {n : ℕ} (Γ : Fin n → D.sig.Srt) (i : Fin n) :
    ctxApp (D.incl.onSrt ∘ RR D Γ) Γ (posR (posL i)) = ExtSrt.old (rB D (Γ i)) :=
  (ctxApp_R _ Γ _).trans (congrArg ExtSrt.old (ctxApp_L _ _ i))

/-- `∃ z̄ (⋀ᵢ link(zᵢ, aᵢ, bᵢ) ∧ φ(z̄))`, a formula in the old-sorted representatives `ā, b̄`. -/
def chi {n : ℕ} (Γ : Fin n → D.sig.Srt) (c : Fin n → Bool) (φ : Formula D.sig Γ) :
    Formula D.sig (D.incl.onSrt ∘ RR D Γ) :=
  exAll Γ (Formula.and
    (andAll fun i => linkF D (Γ i) (c i)
      (cast (congrArg (Term D.sig _) (eZ D Γ i)) (Term.var (posL i)))
      (cast (congrArg (Term D.sig _) (eA D Γ i)) (Term.var (posR (posR i))))
      (cast (congrArg (Term D.sig _) (eB D Γ i)) (Term.var (posR (posL i)))))
    (fren φ posL (eZ D Γ)))

theorem cast_heq' {α β : Type} (e : α = β) (x : α) {γ : Type} (y : γ) (h : HEq x y) :
    HEq (cast e x) y := (cast_heq e x).trans h

theorem realize_chi (K : Str D.sig) {n : ℕ} (Γ : Fin n → D.sig.Srt) (c : Fin n → Bool)
    (φ : Formula D.sig Γ) (ra : (i : Fin n) → K.carrier (.old (rA D (Γ i))))
    (rb : (i : Fin n) → K.carrier (.old (rB D (Γ i)))) :
    (chi D Γ c φ).Realize K (appVal (α := fun s => K.carrier (D.incl.onSrt s)) ra rb) ↔
      ∃ u : (i : Fin n) → K.carrier (Γ i),
        (∀ i, linkP D K (Γ i) (c i) (u i) (ra i) (rb i)) ∧ φ.Realize K u := by
  refine (realize_exAll K _ Γ _).trans (exists_congr fun u => ?_)
  refine (r_and K _ _ _).trans (and_congr ?_ ?_)
  · refine (realize_andAll K _ _).trans (forall_congr' fun i => ?_)
    refine (realize_linkF D K _ _ _ _ _ _).trans (iff_of_eq ?_)
    rw [cast_realize, cast_realize, cast_realize]
    congr 1
    all_goals first
      | exact eZ D Γ i | exact eA D Γ i | exact eB D Γ i
      | exact eq_of_heq (cast_heq' _ _ _ (appVal_L _ u i))
      | exact eq_of_heq (cast_heq' _ _ _ ((appVal_R _ u (posR i)).trans (appVal_R (α := fun s => K.carrier (D.incl.onSrt s)) ra rb i)))
      | exact eq_of_heq (cast_heq' _ _ _ ((appVal_R _ u (posL i)).trans (appVal_L (α := fun s => K.carrier (D.incl.onSrt s)) ra rb i)))
  · refine (fren_realize K φ _ _ _).trans (iff_of_eq (congrArg _ (funext fun i => ?_)))
    exact eq_of_heq (cast_heq' _ _ _ (appVal_L _ u i))

theorem elem_main (N N' : Model D.ext) (g : ∀ s : D.sig.Srt, N.str.carrier s → N'.str.carrier s)
    (hfun : ∀ {m : ℕ} {dom : Fin m → D.sig.Srt} {s : D.sig.Srt} (F : D.sig.Func m dom s)
      (x : (j : Fin m) → N.str.carrier (dom j)),
      g s (N.str.funMap F x) = N'.str.funMap F (fun j => g (dom j) (x j)))
    (hold : ∀ {n : ℕ} {Γ : Fin n → L.Srt} (φ : Formula L Γ)
      (v : (i : Fin n) → (N.str.reduct D.incl).carrier (Γ i)),
      φ.Realize (N'.str.reduct D.incl) (fun i => g (D.incl.onSrt (Γ i)) (v i)) ↔
        φ.Realize (N.str.reduct D.incl) v) :
    ∀ {n : ℕ} {Γ : Fin n → D.sig.Srt} (φ : Formula D.sig Γ) (v : (i : Fin n) → N.str.carrier (Γ i)),
      φ.Realize N'.str (fun i => g (Γ i) (v i)) ↔ φ.Realize N.str v := by
  intro n Γ φ v
  choose c a b hl using fun i => link_exists D N (Γ i) (v i)
  have key : ∀ (K : Model D.ext) (ra : (i : Fin n) → K.str.carrier (.old (rA D (Γ i))))
      (rb : (i : Fin n) → K.str.carrier (.old (rB D (Γ i)))) (u0 : (i : Fin n) → K.str.carrier (Γ i)),
      (∀ i, linkP D K.str (Γ i) (c i) (u0 i) (ra i) (rb i)) →
      ((chi D Γ c φ).Realize K.str (appVal (α := fun s => K.str.carrier (D.incl.onSrt s)) ra rb) ↔
        φ.Realize K.str u0) := by
    intro K ra rb u0 hl0
    refine (realize_chi D K.str Γ c φ ra rb).trans ⟨?_, fun h => ⟨u0, hl0, h⟩⟩
    rintro ⟨u, hu, hφ⟩
    have : u = u0 := funext fun i => link_unique D K _ _ _ _ _ _ (hu i) (hl0 i)
    exact this ▸ hφ
  obtain ⟨ψ, hψ⟩ := translation D (RR D Γ) (chi D Γ c φ)
  have hmap := appVal_map (α := fun s => N.str.carrier (D.incl.onSrt s))
    (β := fun s => N'.str.carrier (D.incl.onSrt s)) (fun s => g (D.incl.onSrt s)) a (Γ := fun i => rB D (Γ i)) b
  calc φ.Realize N'.str (fun i => g (Γ i) (v i))
      ↔ (chi D Γ c φ).Realize N'.str
          (appVal (α := fun s => N'.str.carrier (D.incl.onSrt s))
            (fun i => g _ (a i)) (fun i => g _ (b i))) :=
        (key N' _ _ _ fun i => link_map D g hfun _ _ _ _ _ (hl i)).symm
    _ ↔ ψ.Realize (N'.str.reduct D.incl)
          (appVal (α := fun s => N'.str.carrier (D.incl.onSrt s))
            (fun i => g _ (a i)) (fun i => g _ (b i))) :=
        (hψ N' _).trans (Formula.realize_onFormula _ _ _ _)
    _ ↔ ψ.Realize (N'.str.reduct D.incl)
          (fun p => g (D.incl.onSrt (RR D Γ p))
            (appVal (α := fun s => N.str.carrier (D.incl.onSrt s)) a b p)) := by
        rw [hmap]
    _ ↔ ψ.Realize (N.str.reduct D.incl) (appVal (α := fun s => N.str.carrier (D.incl.onSrt s)) a b) :=
        hold ψ _
    _ ↔ (chi D Γ c φ).Realize N.str (appVal (α := fun s => N.str.carrier (D.incl.onSrt s)) a b) :=
        ((hψ N _).trans (Formula.realize_onFormula _ _ _ _)).symm
    _ ↔ φ.Realize N.str v := key N a b v hl

end Link

end PFU
end MoritaEquiv

open MoritaEquiv

theorem solution {L : Sig} {T : Theory L} (D : MoritaData L T)
    (N N' : Model D.ext) (g : ∀ s : D.sig.Srt, N.str.carrier s → N'.str.carrier s)
    (hfun : ∀ {m : ℕ} {dom : Fin m → D.sig.Srt} {s : D.sig.Srt} (F : D.sig.Func m dom s)
      (x : (j : Fin m) → N.str.carrier (dom j)),
      g s (N.str.funMap F x) = N'.str.funMap F (fun j => g (dom j) (x j)))
    (hold : ∀ {n : ℕ} {Γ : Fin n → L.Srt} (φ : Formula L Γ)
      (v : (i : Fin n) → (N.str.reduct D.incl).carrier (Γ i)),
      φ.Realize (N'.str.reduct D.incl) (fun i => g (D.incl.onSrt (Γ i)) (v i)) ↔
        φ.Realize (N.str.reduct D.incl) v) :
    ∀ {n : ℕ} {Γ : Fin n → D.sig.Srt} (φ : Formula D.sig Γ) (v : (i : Fin n) → N.str.carrier (Γ i)),
      φ.Realize N'.str (fun i => g (Γ i) (v i)) ↔ φ.Realize N.str v :=
  PFU.elem_main D N N' g hfun hold
