-- Prove2me | solution 1 for MoritaEquiv.expansion_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-12T19:14:14.304708+00:00
-- url     : https://prove2.me/submissions/e03d8cd4-cff9-4f57-be8b-0bed962a4177

import Mathlib
import Definitions.Def_MoritaEquiv_defs

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

/-! ### Strong isomorphisms are elementary -/

section StrongIso
variable {L : Sig} {A B : Str L} (E : ∀ s, A.carrier s ≃ B.carrier s)

theorem term_E {n : ℕ} {Γ : Fin n → L.Srt}
    (hf : ∀ {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt} (f : L.Func m dom s) xs,
      E s (A.funMap f xs) = B.funMap f (fun j => E _ (xs j)))
    (v : (i : Fin n) → A.carrier (Γ i)) {s : L.Srt} (t : Term L Γ s) :
    t.realize B (fun i => E _ (v i)) = E s (t.realize A v) := by
  induction t with
  | var i => rfl
  | func f args ih =>
    show B.funMap f _ = E _ (A.funMap f _)
    rw [hf]
    congr 1
    funext j
    exact ih j

theorem cons_E {n : ℕ} {Γ' : Fin (n + 1) → L.Srt} (a : A.carrier (Γ' 0))
    (v : (i : Fin n) → A.carrier (Fin.tail Γ' i)) :
    (Fin.cons (α := fun i => B.carrier (Γ' i)) (E _ a) (fun i => E (Fin.tail Γ' i) (v i)) :
      (i : Fin (n + 1)) → B.carrier (Γ' i)) =
      fun i => E _ (Fin.cons (α := fun i => A.carrier (Γ' i)) a v i) := by
  funext i
  exact Fin.cases rfl (fun j => rfl) i

/-- A sortwise bijection commuting with all function symbols and relation symbols is an
elementary embedding. -/
def strongEmb
    (hf : ∀ {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt} (f : L.Func m dom s) xs,
      E s (A.funMap f xs) = B.funMap f (fun j => E _ (xs j)))
    (hr : ∀ {m : ℕ} {dom : Fin m → L.Srt} (r : L.Rel m dom) xs,
      B.relMap r (fun j => E _ (xs j)) ↔ A.relMap r xs) : ElemEmb A B where
  toFun s := E s
  map_formula := by
    intro n Γ φ
    induction φ with
    | falsum => intro v; exact Iff.rfl
    | equal t₁ t₂ =>
      intro v
      show t₁.realize B _ = t₂.realize B _ ↔ t₁.realize A v = t₂.realize A v
      rw [term_E E hf v t₁, term_E E hf v t₂]
      exact (E _).injective.eq_iff
    | rel r args =>
      intro v
      show B.relMap r (fun j => (args j).realize B _) ↔ A.relMap r (fun j => (args j).realize A v)
      have : (fun j => (args j).realize B (fun i => E _ (v i))) =
          fun j => E _ ((args j).realize A v) := funext fun j => term_E E hf v (args j)
      rw [this]
      exact hr r _
    | imp φ ψ ihφ ihψ => intro v; exact imp_congr (ihφ v) (ihψ v)
    | all φ ih =>
      intro v
      constructor
      · intro h a
        have := h (E _ a)
        rw [cons_E E a v] at this
        exact (ih _).1 this
      · intro h b
        rw [← (E _).apply_symm_apply b, cons_E E _ v]
        exact (ih _).2 (h _)

theorem emb_ext {M N : Str L} {f g : ElemEmb M N} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

/-- Strong isomorphisms of models give isomorphisms in `Mod(T)`. -/
def isoOfE {T : Theory L} (A B : Model T) (E : ∀ s, A.str.carrier s ≃ B.str.carrier s)
    (hf : ∀ {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt} (f : L.Func m dom s) xs,
      E s (A.str.funMap f xs) = B.str.funMap f (fun j => E _ (xs j)))
    (hr : ∀ {m : ℕ} {dom : Fin m → L.Srt} (r : L.Rel m dom) xs,
      B.str.relMap r (fun j => E _ (xs j)) ↔ A.str.relMap r xs) : A ≅ B where
  hom := strongEmb E hf hr
  inv := strongEmb (fun s => (E s).symm)
    (fun f xs => (E _).injective (by
      rw [Equiv.apply_symm_apply, hf]
      congr 1; funext j; exact ((E _).apply_symm_apply _).symm))
    (fun r xs => by
      rw [← hr r]
      have : (fun j => E _ ((E _).symm (xs j))) = xs := funext fun j => (E _).apply_symm_apply _
      rw [this])
  hom_inv_id := emb_ext (funext fun s => funext fun x => (E s).symm_apply_apply x)
  inv_hom_id := emb_ext (funext fun s => funext fun x => (E s).apply_symm_apply x)

/-- Elementary embeddings commute with function symbols. -/
theorem emb_func {M N : Str L} (h : ElemEmb M N) {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt}
    (f : L.Func m dom s) (xs : (j : Fin m) → M.carrier (dom j)) :
    h.toFun s (M.funMap f xs) = N.funMap f (fun j => h.toFun _ (xs j)) := by
  have := (h.map_formula (Formula.equal (Term.func f (fun j => Term.var (Γ := Ctx.cons s dom) j.succ))
    (Term.var 0)) (Fin.cons (α := fun i => M.carrier (Ctx.cons s dom i)) (M.funMap f xs) xs)).2 rfl
  exact this.symm

/-- Elementary embeddings preserve and reflect relation symbols. -/
theorem emb_rel {M N : Str L} (h : ElemEmb M N) {m : ℕ} {dom : Fin m → L.Srt}
    (r : L.Rel m dom) (xs : (j : Fin m) → M.carrier (dom j)) :
    N.relMap r (fun j => h.toFun _ (xs j)) ↔ M.relMap r xs :=
  h.map_formula (Formula.rel r (fun j => Term.var (Γ := dom) j)) xs

end StrongIso

/-! ### Explicit forms of the defining axioms -/

section Axioms
variable {L : Sig} {T : Theory L} (D : MoritaData L T) (S : Str D.sig)

open MoritaData

theorem sat_prod (σ : D.Prod) : S.Satisfies (D.prodAx σ) ↔
    ∀ v : (i : Fin 2) → S.carrier
        ((![ExtSrt.old (D.prodFst σ), ExtSrt.old (D.prodSnd σ)] : Fin 2 → D.sig.Srt) i),
      ∃ z : S.carrier (.prod σ), (ap S (L := D.sig) (ExtFunc.fst σ) z = v 0 ∧
        ap S (L := D.sig) (ExtFunc.snd σ) z = v 1) ∧
        ∀ z' : S.carrier (.prod σ), ap S (L := D.sig) (ExtFunc.fst σ) z' = v 0 ∧
          ap S (L := D.sig) (ExtFunc.snd σ) z' = v 1 → z' = z := by
  simp only [Str.Satisfies, prodAx]
  refine forall_congr' fun v => ?_
  simp only [r_exS, r_and, r_allS, r_imp, r_equal, r_app1]
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

theorem sat_coprod (σ : D.Coprod) : S.Satisfies (D.coprodAx σ) ↔
    ∀ v : (i : Fin 1) → S.carrier ((![ExtSrt.coprod σ] : Fin 1 → D.sig.Srt) i),
      ((∃ a : S.carrier (.old (D.coprodFst σ)), ap S (L := D.sig) (ExtFunc.inl σ) a = v 0 ∧
          ∀ a' : S.carrier (.old (D.coprodFst σ)), ap S (L := D.sig) (ExtFunc.inl σ) a' = v 0 → a' = a) ∨
        (∃ b : S.carrier (.old (D.coprodSnd σ)), ap S (L := D.sig) (ExtFunc.inr σ) b = v 0 ∧
          ∀ b' : S.carrier (.old (D.coprodSnd σ)), ap S (L := D.sig) (ExtFunc.inr σ) b' = v 0 → b' = b)) ∧
      ∀ (a : S.carrier (.old (D.coprodFst σ))) (b : S.carrier (.old (D.coprodSnd σ))),
        ¬ ap S (L := D.sig) (ExtFunc.inl σ) a = ap S (L := D.sig) (ExtFunc.inr σ) b := by
  simp only [Str.Satisfies, coprodAx]
  refine forall_congr' fun v => ?_
  simp only [r_exS, r_and, r_or, r_not, r_allS, r_imp, r_equal, r_app1]
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

theorem sat_sub (σ : D.Sub) : S.Satisfies (D.subAx σ) ↔
    ∀ v : (i : Fin 1) → S.carrier ((D.incl.onSrt ∘ ![D.subBase σ] : Fin 1 → D.sig.Srt) i),
      ((D.subDef σ).Realize (S.reduct D.incl) v ↔
          ∃ z : S.carrier (.sub σ), ap S (L := D.sig) (ExtFunc.incl σ) z = v 0) ∧
        ∀ z₁ z₂ : S.carrier (.sub σ), ap S (L := D.sig) (ExtFunc.incl σ) z₂ =
          ap S (L := D.sig) (ExtFunc.incl σ) z₁ → z₂ = z₁ := by
  simp only [Str.Satisfies, subAx]
  refine forall_congr' fun v => ?_
  simp only [r_exS, r_and, r_iff, r_allS, r_imp, r_equal, r_app1,
    Formula.realize_onFormula]
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

theorem sat_quot (σ : D.Quot) : S.Satisfies (D.quotAx σ) ↔
    ∀ v : (i : Fin 2) → S.carrier
        ((D.incl.onSrt ∘ ![D.quotBase σ, D.quotBase σ] : Fin 2 → D.sig.Srt) i),
      (ap S (L := D.sig) (ExtFunc.proj σ) (v 0) = ap S (L := D.sig) (ExtFunc.proj σ) (v 1) ↔
          (D.quotDef σ).Realize (S.reduct D.incl) v) ∧
        ∀ z : S.carrier (.quot σ), ∃ x : S.carrier (.old (D.quotBase σ)),
          ap S (L := D.sig) (ExtFunc.proj σ) x = z := by
  simp only [Str.Satisfies, quotAx]
  refine forall_congr' fun v => ?_
  simp only [r_exS, r_and, r_iff, r_allS, r_equal, r_app1, Formula.realize_onFormula]
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

theorem sat_rel {m : ℕ} {dom : Fin m → L.Srt} (r : D.NewRel m dom) :
    S.Satisfies (D.relAx r) ↔
    ∀ v : (i : Fin m) → S.carrier ((D.incl.onSrt ∘ dom : Fin m → D.sig.Srt) i),
      (S.relMap (L := D.sig) (ExtRel.new r) (fun j => v j) ↔
        (D.relDef r).Realize (S.reduct D.incl) v) := by
  simp only [Str.Satisfies, relAx]
  refine forall_congr' fun v => ?_
  simp only [r_iff, Formula.realize_onFormula]
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

theorem mem_prod (σ : D.Prod) : D.prodAx σ ∈ D.ext :=
  Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨σ, rfl⟩)))))
theorem mem_coprod (σ : D.Coprod) : D.coprodAx σ ∈ D.ext :=
  Or.inr (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨σ, rfl⟩)))))
theorem mem_sub (σ : D.Sub) : D.subAx σ ∈ D.ext :=
  Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨σ, rfl⟩))))
theorem mem_quot (σ : D.Quot) : D.quotAx σ ∈ D.ext :=
  Or.inr (Or.inl (Or.inl (Or.inr ⟨σ, rfl⟩)))
theorem mem_func {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt} (f : D.NewFunc m dom s) :
    D.funcAx f ∈ D.ext :=
  Or.inr (Or.inl (Or.inr ⟨m, dom, s, f, rfl⟩))
theorem mem_rel {m : ℕ} {dom : Fin m → L.Srt} (r : D.NewRel m dom) : D.relAx r ∈ D.ext :=
  Or.inr (Or.inr ⟨m, dom, r, rfl⟩)

end Axioms

/-! ### The canonical expansion of a model of `T` -/

section Build
variable {L : Sig} {T : Theory L} (D : MoritaData L T) (M : Model T)

open MoritaData

def subP (σ : D.Sub) (a : M.str.carrier (D.subBase σ)) : Prop :=
  (D.subDef σ).Realize M.str (Fin.cons (α := fun j => M.str.carrier (![D.subBase σ] j)) a finZeroElim)

def qrel (σ : D.Quot) (a b : M.str.carrier (D.quotBase σ)) : Prop :=
  (D.quotDef σ).Realize M.str
    (Fin.cons (α := fun j => M.str.carrier (![D.quotBase σ, D.quotBase σ] j)) a
      (Fin.cons (α := fun j => M.str.carrier (![D.quotBase σ, D.quotBase σ] j.succ)) b finZeroElim))

def qsetoid (σ : D.Quot) : Setoid (M.str.carrier (D.quotBase σ)) :=
  ⟨qrel D M σ, D.quot_adm M.str M.isModel σ⟩

def bC : D.ExtSrt → Type
  | .old s => M.str.carrier s
  | .prod σ => M.str.carrier (D.prodFst σ) × M.str.carrier (D.prodSnd σ)
  | .coprod σ => M.str.carrier (D.coprodFst σ) ⊕ M.str.carrier (D.coprodSnd σ)
  | .sub σ => {a // subP D M σ a}
  | .quot σ => Quotient (qsetoid D M σ)

noncomputable def newF {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt} (f : D.NewFunc m dom s)
    (x : (j : Fin m) → M.str.carrier (dom j)) : M.str.carrier s :=
  (D.func_adm M.str M.isModel f x).exists.choose

theorem newF_spec {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt} (f : D.NewFunc m dom s)
    (x : (j : Fin m) → M.str.carrier (dom j)) :
    (D.funcDef f).Realize M.str
      (Fin.cons (α := fun j => M.str.carrier (Ctx.cons s dom j)) (newF D M f x) x) :=
  (D.func_adm M.str M.isModel f x).exists.choose_spec

theorem newF_unique {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt} (f : D.NewFunc m dom s)
    (x : (j : Fin m) → M.str.carrier (dom j)) (y : M.str.carrier s)
    (hy : (D.funcDef f).Realize M.str
      (Fin.cons (α := fun j => M.str.carrier (Ctx.cons s dom j)) y x)) : y = newF D M f x :=
  (D.func_adm M.str M.isModel f x).unique hy (newF_spec D M f x)

noncomputable def bF : ∀ {m : ℕ} {dom : Fin m → D.ExtSrt} {s : D.ExtSrt}, D.ExtFunc m dom s →
    ((j : Fin m) → bC D M (dom j)) → bC D M s
  | _, _, _, .old f, xs => M.str.funMap f xs
  | _, _, _, .new f, xs => newF D M f xs
  | _, _, _, .fst _, xs => (xs 0).1
  | _, _, _, .snd _, xs => (xs 0).2
  | _, _, _, .inl _, xs => Sum.inl (xs 0)
  | _, _, _, .inr _, xs => Sum.inr (xs 0)
  | _, _, _, .incl _, xs => (xs 0).1
  | _, _, _, .proj σ, xs => Quotient.mk (qsetoid D M σ) (xs 0)

def bR : ∀ {m : ℕ} {dom : Fin m → D.ExtSrt}, D.ExtRel m dom → ((j : Fin m) → bC D M (dom j)) → Prop
  | _, _, .old r, xs => M.str.relMap r xs
  | _, _, .new r, xs => (D.relDef r).Realize M.str xs

theorem bNe : ∀ s, Nonempty (bC D M s)
  | .old s => M.str.nonempty s
  | .prod σ => by
    obtain ⟨a⟩ := M.str.nonempty (D.prodFst σ)
    obtain ⟨b⟩ := M.str.nonempty (D.prodSnd σ)
    exact ⟨((a, b) : M.str.carrier (D.prodFst σ) × M.str.carrier (D.prodSnd σ))⟩
  | .coprod σ => by
    obtain ⟨a⟩ := M.str.nonempty (D.coprodFst σ)
    exact ⟨(Sum.inl a : M.str.carrier (D.coprodFst σ) ⊕ M.str.carrier (D.coprodSnd σ))⟩
  | .sub σ => by
    obtain ⟨a, ha⟩ := D.sub_adm M.str M.isModel σ
    exact ⟨(⟨a, ha⟩ : {a // subP D M σ a})⟩
  | .quot σ => by
    obtain ⟨a⟩ := M.str.nonempty (D.quotBase σ)
    exact ⟨(Quotient.mk (qsetoid D M σ) a : Quotient (qsetoid D M σ))⟩

/-- The canonical expansion of `M` to a `Σ⁺`-structure. -/
noncomputable def bS : Str D.sig where
  carrier := bC D M
  funMap f xs := bF D M f xs
  relMap r xs := bR D M r xs
  nonempty := bNe D M

theorem bS_model : (bS D M).IsModel D.ext := by
  rintro A (⟨A₀, hA₀, rfl⟩ | hA)
  · intro v
    exact (Formula.realize_onFormula D.incl (bS D M) A₀.φ v).2 (M.isModel A₀ hA₀ v)
  · rcases hA with (((((⟨σ, rfl⟩ | ⟨σ, rfl⟩) | ⟨σ, rfl⟩) | ⟨σ, rfl⟩) | ⟨m, dom, s, f, rfl⟩) |
      ⟨m, dom, r, rfl⟩)
    · refine (sat_prod D (bS D M) σ).2 fun v => ?_
      refine ⟨((v 0, v 1) : M.str.carrier (D.prodFst σ) × M.str.carrier (D.prodSnd σ)),
        ⟨rfl, rfl⟩, ?_⟩
      rintro z' ⟨h1, h2⟩
      exact Prod.ext h1 h2
    · refine (sat_coprod D (bS D M) σ).2 fun v => ⟨?_, fun a b h => Sum.inl_ne_inr h⟩
      have key : ∀ w : M.str.carrier (D.coprodFst σ) ⊕ M.str.carrier (D.coprodSnd σ),
          ((∃ a : M.str.carrier (D.coprodFst σ), Sum.inl a = w ∧ ∀ a', Sum.inl a' = w → a' = a) ∨
          (∃ b : M.str.carrier (D.coprodSnd σ), Sum.inr b = w ∧ ∀ b', Sum.inr b' = w → b' = b)) := by
        rintro (a | b)
        · exact Or.inl ⟨a, rfl, fun a' h => Sum.inl_injective h⟩
        · exact Or.inr ⟨b, rfl, fun b' h => Sum.inr_injective h⟩
      exact key (v 0)
    · refine (sat_sub D (bS D M) σ).2 fun v => ⟨⟨fun h => ?_, ?_⟩, ?_⟩
      · exact ⟨(⟨v 0, (realize_fin1 M.str (D.subDef σ) v).1 h⟩ : {a // subP D M σ a}), rfl⟩
      · rintro ⟨z, hz⟩
        refine (realize_fin1 M.str (D.subDef σ) v).2 ?_
        have hz' : (z : {a // subP D M σ a}).1 = v 0 := hz
        rw [← hz']
        exact z.2
      · intro z₁ z₂ h
        exact Subtype.ext h
    · refine (sat_quot D (bS D M) σ).2 fun v => ⟨?_, ?_⟩
      · show Quotient.mk (qsetoid D M σ) (v 0) = Quotient.mk (qsetoid D M σ) (v 1) ↔ _
        exact Quotient.eq.trans (realize_fin2 M.str (D.quotDef σ) v).symm
      · intro z
        obtain ⟨a, rfl⟩ := Quotient.exists_rep (z : Quotient (qsetoid D M σ))
        exact ⟨a, rfl⟩
    · refine (sat_func D (bS D M) f).2 fun v => ⟨fun h => ?_, fun h => ?_⟩
      · refine (realize_consEta M.str (D.funcDef f) v).1 ?_
        have h' : newF D M f (fun j => v j.succ) = v 0 := h
        rw [← h']
        exact newF_spec D M f _
      · exact (newF_unique D M f (fun j => v j.succ) (v 0)
          ((realize_consEta M.str (D.funcDef f) v).2 h)).symm
    · exact (sat_rel D (bS D M) r).2 fun v => Iff.rfl

/-- The canonical expansion as a model of `T⁺`. -/
noncomputable def bM : Model D.ext := ⟨bS D M, bS_model D M⟩

theorem bM_proj : D.proj.obj (bM D M) = M := rfl

end Build

/-! ### The expansion is functorial on isomorphisms -/

section Functorial
variable {L : Sig} {T : Theory L} (D : MoritaData L T) {A B : Model T} (i : A ≅ B)

open MoritaData

/-- The sortwise bijections underlying an isomorphism in `Mod(T)`. -/
def eqv (s : L.Srt) : A.str.carrier s ≃ B.str.carrier s where
  toFun := i.hom.toFun s
  invFun := i.inv.toFun s
  left_inv x := congrArg (fun g : A ⟶ A => g.toFun s x) i.hom_inv_id
  right_inv x := congrArg (fun g : B ⟶ B => g.toFun s x) i.inv_hom_id

theorem subP_iff (σ : D.Sub) (a : A.str.carrier (D.subBase σ)) :
    subP D A σ a ↔ subP D B σ (eqv i _ a) :=
  (i.hom.map_formula (D.subDef σ) _).symm.trans (realize_fin1 B.str (D.subDef σ) _)

theorem qrel_iff (σ : D.Quot) (a b : A.str.carrier (D.quotBase σ)) :
    qrel D A σ a b ↔ qrel D B σ (eqv i _ a) (eqv i _ b) :=
  (i.hom.map_formula (D.quotDef σ) _).symm.trans (realize_fin2 B.str (D.quotDef σ) _)

/-- The induced bijections between the canonical expansions. -/
def bE : ∀ s : D.ExtSrt, bC D A s ≃ bC D B s
  | .old s => eqv i s
  | .prod _ => Equiv.prodCongr (eqv i _) (eqv i _)
  | .coprod _ => Equiv.sumCongr (eqv i _) (eqv i _)
  | .sub σ => Equiv.subtypeEquiv (eqv i _) (subP_iff D i σ)
  | .quot σ => Quotient.congr (eqv i _) (qrel_iff D i σ)

theorem newF_map {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt} (f : D.NewFunc m dom s)
    (xs : (j : Fin m) → A.str.carrier (dom j)) :
    eqv i s (newF D A f xs) = newF D B f (fun j => eqv i _ (xs j)) :=
  newF_unique D B f _ _ ((realize_consEta B.str (D.funcDef f) _).2
    ((i.hom.map_formula (D.funcDef f) _).2 (newF_spec D A f xs)))

noncomputable def bIso : bM D A ≅ bM D B :=
  isoOfE (bM D A) (bM D B) (bE D i)
    (by
      intro m dom s f xs
      cases f with
      | old f => exact emb_func i.hom f xs
      | new f => exact newF_map D i f xs
      | fst σ => rfl
      | snd σ => rfl
      | inl σ => rfl
      | inr σ => rfl
      | incl σ => rfl
      | proj σ => rfl)
    (by
      intro m dom r xs
      cases r with
      | old r => exact emb_rel i.hom r xs
      | new r => exact i.hom.map_formula (D.relDef r) xs)

end Functorial

/-! ### Every model of `T⁺` is isomorphic to the canonical expansion of its reduct -/

section Canonical
variable {L : Sig} {T : Theory L} (D : MoritaData L T) (N : Model D.ext)

open MoritaData

theorem ax {A : Axiom D.sig} (h : A ∈ D.ext) : N.str.Satisfies A := N.isModel A h

def pairN (σ : D.Prod) (z : N.str.carrier (.prod σ)) :
    N.str.carrier (.old (D.prodFst σ)) × N.str.carrier (.old (D.prodSnd σ)) :=
  (ap N.str (L := D.sig) (ExtFunc.fst σ) z, ap N.str (L := D.sig) (ExtFunc.snd σ) z)

theorem pairN_bij (σ : D.Prod) : Function.Bijective (pairN D N σ) := by
  have H := (sat_prod D N.str σ).1 (ax D N (mem_prod D σ))
  constructor
  · intro z₁ z₂ h
    obtain ⟨z, -, hu⟩ := H (Fin.cons (ap N.str (L := D.sig) (ExtFunc.fst σ) z₂)
      (Fin.cons (ap N.str (L := D.sig) (ExtFunc.snd σ) z₂) finZeroElim))
    rw [hu z₂ ⟨rfl, rfl⟩]
    exact hu z₁ ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨x, y⟩
    obtain ⟨z, ⟨h1, h2⟩, -⟩ := H (Fin.cons x (Fin.cons y finZeroElim))
    exact ⟨z, Prod.ext h1 h2⟩

def copN (σ : D.Coprod) :
    N.str.carrier (.old (D.coprodFst σ)) ⊕ N.str.carrier (.old (D.coprodSnd σ)) →
      N.str.carrier (.coprod σ) :=
  Sum.elim (ap N.str (L := D.sig) (ExtFunc.inl σ)) (ap N.str (L := D.sig) (ExtFunc.inr σ))

theorem copN_bij (σ : D.Coprod) : Function.Bijective (copN D N σ) := by
  have H := (sat_coprod D N.str σ).1 (ax D N (mem_coprod D σ))
  have H' : ∀ z, _ := fun z => H (Fin.cons z finZeroElim)
  constructor
  · rintro (a | b) (a' | b') h
    · obtain ⟨⟨a₀, -, hu⟩ | ⟨b₀, hb, -⟩, -⟩ := H' (ap N.str (L := D.sig) (ExtFunc.inl σ) a')
      · exact congrArg Sum.inl ((hu a h).trans (hu a' rfl).symm)
      · exact absurd hb.symm ((H' (ap N.str (L := D.sig) (ExtFunc.inl σ) a')).2 a' b₀)
    · exact absurd h ((H' (ap N.str (L := D.sig) (ExtFunc.inl σ) a)).2 a b')
    · exact absurd h.symm ((H' (ap N.str (L := D.sig) (ExtFunc.inl σ) a')).2 a' b)
    · obtain ⟨⟨a₀, ha, -⟩ | ⟨b₀, -, hu⟩, -⟩ := H' (ap N.str (L := D.sig) (ExtFunc.inr σ) b')
      · exact absurd ha ((H' (ap N.str (L := D.sig) (ExtFunc.inr σ) b')).2 a₀ b')
      · exact congrArg Sum.inr ((hu b h).trans (hu b' rfl).symm)
  · intro z
    obtain ⟨⟨a, ha, -⟩ | ⟨b, hb, -⟩, -⟩ := H' z
    · exact ⟨Sum.inl a, ha⟩
    · exact ⟨Sum.inr b, hb⟩

def subN (σ : D.Sub) (z : N.str.carrier (.sub σ)) : {a // subP D (D.proj.obj N) σ a} :=
  ⟨ap N.str (L := D.sig) (ExtFunc.incl σ) z,
    ((sat_sub D N.str σ).1 (ax D N (mem_sub D σ))
      (Fin.cons (ap N.str (L := D.sig) (ExtFunc.incl σ) z) finZeroElim)).1.2 ⟨z, rfl⟩⟩

theorem subN_bij (σ : D.Sub) : Function.Bijective (subN D N σ) := by
  have H := (sat_sub D N.str σ).1 (ax D N (mem_sub D σ))
  constructor
  · intro z₁ z₂ h
    exact ((H (Fin.cons (ap N.str (L := D.sig) (ExtFunc.incl σ) z₁) finZeroElim)).2 z₁ z₂
      (congrArg Subtype.val h).symm).symm
  · rintro ⟨a, ha⟩
    obtain ⟨z, hz⟩ := (H (Fin.cons a finZeroElim)).1.1 ha
    exact ⟨z, Subtype.ext hz⟩

def quotN (σ : D.Quot) : Quotient (qsetoid D (D.proj.obj N) σ) → N.str.carrier (.quot σ) :=
  Quotient.lift (ap N.str (L := D.sig) (ExtFunc.proj σ)) fun a b h =>
    ((sat_quot D N.str σ).1 (ax D N (mem_quot D σ))
      (Fin.cons a (Fin.cons b finZeroElim))).1.2 h

theorem quotN_bij (σ : D.Quot) : Function.Bijective (quotN D N σ) := by
  have H := (sat_quot D N.str σ).1 (ax D N (mem_quot D σ))
  constructor
  · intro q₁ q₂
    induction q₁ using Quotient.inductionOn with
    | h a =>
    induction q₂ using Quotient.inductionOn with
    | h b =>
    intro h
    exact Quotient.sound ((H (Fin.cons a (Fin.cons b finZeroElim))).1.1 h)
  · intro z
    obtain ⟨x, hx⟩ := (H (fun i => Classical.choice (N.str.nonempty _))).2 z
    exact ⟨Quotient.mk _ x, hx⟩

/-- The canonical bijections `bC (Π N) ≃ N`. -/
noncomputable def cE : ∀ s : D.ExtSrt, bC D (D.proj.obj N) s ≃ N.str.carrier s
  | .old _ => Equiv.refl _
  | .prod σ => (Equiv.ofBijective _ (pairN_bij D N σ)).symm
  | .coprod σ => Equiv.ofBijective _ (copN_bij D N σ)
  | .sub σ => (Equiv.ofBijective _ (subN_bij D N σ)).symm
  | .quot σ => Equiv.ofBijective _ (quotN_bij D N σ)

noncomputable def cIso : bM D (D.proj.obj N) ≅ N :=
  isoOfE (bM D (D.proj.obj N)) N (cE D N)
    (by
      intro m dom s f xs
      cases f with
      | old f => rfl
      | new f =>
        show newF D (D.proj.obj N) f xs = N.str.funMap (ExtFunc.new f) xs
        refine (newF_unique D (D.proj.obj N) f xs _ ?_).symm
        exact ((sat_func D N.str f).1 (ax D N (mem_func D f))
          (Fin.cons (N.str.funMap (L := D.sig) (ExtFunc.new f) xs) xs)).1 rfl
      | fst σ =>
        rw [funMap_unary, funMap_unary]
        exact (congrArg Prod.fst ((Equiv.ofBijective _ (pairN_bij D N σ)).apply_symm_apply
          (xs 0))).symm
      | snd σ =>
        rw [funMap_unary, funMap_unary]
        exact (congrArg Prod.snd ((Equiv.ofBijective _ (pairN_bij D N σ)).apply_symm_apply
          (xs 0))).symm
      | inl σ => rw [funMap_unary, funMap_unary]; rfl
      | inr σ => rw [funMap_unary, funMap_unary]; rfl
      | incl σ =>
        rw [funMap_unary, funMap_unary]
        exact (congrArg Subtype.val ((Equiv.ofBijective _ (subN_bij D N σ)).apply_symm_apply
          (xs 0))).symm
      | proj σ => rw [funMap_unary, funMap_unary]; rfl)
    (by
      intro m dom r xs
      cases r with
      | old r => exact Iff.rfl
      | new r => exact (sat_rel D N.str r).1 (ax D N (mem_rel D r)) xs)

end Canonical

end EEU

open EEU

theorem eeu_main {L : Sig} {T : Theory L} (D : MoritaData L T) (M : Model T) :
    (∃ N : Model D.ext, Nonempty (D.proj.obj N ≅ M)) ∧
      ∀ N N' : Model D.ext, (D.proj.obj N ≅ M) → (D.proj.obj N' ≅ M) → Nonempty (N ≅ N') :=
  ⟨⟨bM D M, ⟨Iso.refl _⟩⟩, fun N N' i i' =>
    ⟨(cIso D N).symm ≪≫ bIso D (i ≪≫ i'.symm) ≪≫ cIso D N'⟩⟩

end MoritaEquiv

open MoritaEquiv

theorem solution {L : Sig} {T : Theory L} (D : MoritaData L T) (M : Model T) :
    (∃ N : Model D.ext, Nonempty (D.proj.obj N ≅ M)) ∧
      ∀ N N' : Model D.ext, (D.proj.obj N ≅ M) → (D.proj.obj N' ≅ M) → Nonempty (N ≅ N') :=
  eeu_main D M

