-- Prove2me | solution 1 for MoritaEquiv.MoritaData.exists_extension_of_hom
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-12T20:44:02.841781+00:00
-- url     : https://prove2.me/submissions/236b29d0-88f5-4f93-8cb4-5aae86e56e3b

import Mathlib
import Definitions.Def_MoritaEquiv_defs
import Theorems.Thm_MoritaEquiv_ElemEmb_map_funMap
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

section Ext
variable {L : Sig} {T : Theory L} (D : MoritaData L T) {N N' : Model D.ext}
  (F : ElemEmb (N.str.reduct D.incl) (N'.str.reduct D.incl))

theorem sub_ex (σ : D.Sub) (z : N.str.carrier (.sub σ)) :
    ∃ z' : N'.str.carrier (.sub σ),
      ap N'.str (ExtFunc.incl σ) z' = F.toFun (D.subBase σ) (ap N.str (ExtFunc.incl σ) z) := by
  have h1 := (((model_ext_newSorts D N).2.2.1 σ).2 (ap N.str (ExtFunc.incl σ) z)).1 ⟨z, rfl⟩
  have h2 := (F.map_formula (D.subDef σ) _).2 h1
  exact (((model_ext_newSorts D N').2.2.1 σ).2 _).2 ((realize_fin1 _ _ _).1 h2)

noncomputable def gmap : ∀ s : D.ExtSrt, N.str.carrier s → N'.str.carrier s
  | .old s, x => F.toFun s x
  | .prod σ, z => Function.surjInv ((model_ext_newSorts D N').1 σ).2
      (F.toFun _ (ap N.str (ExtFunc.fst σ) z), F.toFun _ (ap N.str (ExtFunc.snd σ) z))
  | .coprod σ, z => Sum.elim (fun a => ap N'.str (ExtFunc.inl σ) (F.toFun _ a))
      (fun b => ap N'.str (ExtFunc.inr σ) (F.toFun _ b))
      (Function.surjInv ((model_ext_newSorts D N).2.1 σ).2 z)
  | .sub σ, z => Classical.choose (sub_ex D F σ z)
  | .quot σ, z => ap N'.str (ExtFunc.proj σ)
      (F.toFun _ (Function.surjInv ((model_ext_newSorts D N).2.2.2 σ).1 z))

theorem gmap_funMap {m : ℕ} {dom : Fin m → D.sig.Srt} {s : D.sig.Srt} (Fn : D.sig.Func m dom s)
    (x : (j : Fin m) → N.str.carrier (dom j)) :
    gmap D F s (N.str.funMap Fn x) = N'.str.funMap Fn (fun j => gmap D F (dom j) (x j)) := by
  cases Fn with
  | old g => exact ElemEmb.map_funMap F g x
  | new g =>
    have hN := (sat_func D N.str g).1 (N.isModel _ (mem_func D g))
      (Fin.cons (N.str.funMap (L := D.sig) (ExtFunc.new g) x) x)
    have h2 := (F.map_formula (D.funcDef g) _).2 (hN.1 rfl)
    have hN' := (sat_func D N'.str g).1 (N'.isModel _ (mem_func D g))
      (Fin.cons (F.toFun _ (N.str.funMap (L := D.sig) (ExtFunc.new g) x))
        (fun j => F.toFun _ (x j)))
    exact (hN'.2 ((realize_consEta (N'.str.reduct D.incl) (D.funcDef g) _).2 h2)).symm
  | fst σ =>
    rw [funMap_unary N.str, funMap_unary N'.str]
    exact (congrArg Prod.fst (Function.surjInv_eq ((model_ext_newSorts D N').1 σ).2
      (F.toFun _ (ap N.str (ExtFunc.fst σ) (x 0)), F.toFun _ (ap N.str (ExtFunc.snd σ) (x 0))))).symm
  | snd σ =>
    rw [funMap_unary N.str, funMap_unary N'.str]
    exact (congrArg Prod.snd (Function.surjInv_eq ((model_ext_newSorts D N').1 σ).2
      (F.toFun _ (ap N.str (ExtFunc.fst σ) (x 0)), F.toFun _ (ap N.str (ExtFunc.snd σ) (x 0))))).symm
  | inl σ =>
    rw [funMap_unary N.str, funMap_unary N'.str]
    have hb := (model_ext_newSorts D N).2.1 σ
    exact congrArg (Sum.elim (fun a => ap N'.str (ExtFunc.inl σ) (F.toFun _ a))
      (fun b => ap N'.str (ExtFunc.inr σ) (F.toFun _ b)))
      (Function.leftInverse_surjInv hb (Sum.inl (x 0)))
  | inr σ =>
    rw [funMap_unary N.str, funMap_unary N'.str]
    have hb := (model_ext_newSorts D N).2.1 σ
    exact congrArg (Sum.elim (fun a => ap N'.str (ExtFunc.inl σ) (F.toFun _ a))
      (fun b => ap N'.str (ExtFunc.inr σ) (F.toFun _ b)))
      (Function.leftInverse_surjInv hb (Sum.inr (x 0)))
  | incl σ =>
    rw [funMap_unary N.str, funMap_unary N'.str]
    exact (Classical.choose_spec (sub_ex D F σ (x 0))).symm
  | proj σ =>
    rw [funMap_unary N.str, funMap_unary N'.str]
    have hq := (model_ext_newSorts D N).2.2.2 σ
    have e1 : ap N.str (ExtFunc.proj σ) (Function.surjInv hq.1 (ap N.str (ExtFunc.proj σ) (x 0))) =
        ap N.str (ExtFunc.proj σ) (x 0) := Function.surjInv_eq hq.1 _
    have h1 := (hq.2 _ _).1 e1
    have h2 := (F.map_formula (D.quotDef σ) _).2 h1
    exact (((model_ext_newSorts D N').2.2.2 σ).2 _ _).2 ((realize_fin2 _ _ _).1 h2)

end Ext

theorem eoh_main {L : Sig} {T : Theory L} (D : MoritaData L T) {N N' : Model D.ext}
    (f : D.proj.obj N ⟶ D.proj.obj N') :
    ∃ g : ∀ s : D.sig.Srt, N.str.carrier s → N'.str.carrier s,
      (∀ (s : L.Srt) (x : N.str.carrier (D.incl.onSrt s)), g (D.incl.onSrt s) x = ElemEmb.toFun f s x) ∧
      ∀ {m : ℕ} {dom : Fin m → D.sig.Srt} {s : D.sig.Srt} (F : D.sig.Func m dom s)
        (x : (j : Fin m) → N.str.carrier (dom j)),
        g s (N.str.funMap F x) = N'.str.funMap F (fun j => g (dom j) (x j)) :=
  ⟨gmap D f, fun _ _ => rfl, fun Fn x => gmap_funMap D f Fn x⟩


end PFU
end MoritaEquiv

open MoritaEquiv

theorem solution {L : Sig} {T : Theory L} (D : MoritaData L T)
    {N N' : Model D.ext} (f : D.proj.obj N ⟶ D.proj.obj N') :
    ∃ g : ∀ s : D.sig.Srt, N.str.carrier s → N'.str.carrier s,
      (∀ (s : L.Srt) (x : N.str.carrier (D.incl.onSrt s)),
        g (D.incl.onSrt s) x = ElemEmb.toFun f s x) ∧
      ∀ {m : ℕ} {dom : Fin m → D.sig.Srt} {s : D.sig.Srt} (F : D.sig.Func m dom s)
        (x : (j : Fin m) → N.str.carrier (dom j)),
        g s (N.str.funMap F x) = N'.str.funMap F (fun j => g (dom j) (x j)) :=
  PFU.eoh_main D f
