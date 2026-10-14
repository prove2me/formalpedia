-- Prove2me | solution 1 for MoritaEquiv.MoritaData.isModel_ext_iff
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-12T23:48:51.209529+00:00
-- url     : https://prove2.me/submissions/e17d0d98-722c-4b2e-b49f-7448113203a4

import Mathlib
import Definitions.Def_MoritaEquiv_defs

open CategoryTheory

namespace MoritaEquiv
namespace IMX

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


/-! ### Models of a Morita extension and of a translated theory -/

section ExtModel

theorem sat_map {L L' : Sig} (F : L.Hom L') (M : Str L') (A : Axiom L) :
    M.Satisfies (A.map F) ↔ (M.reduct F).Satisfies A :=
  forall_congr' fun v => Formula.realize_onFormula F M A.φ v

theorem isModel_map {L L' : Sig} (F : L.Hom L') (M : Str L') (T : Theory L) :
    M.IsModel (T.map F) ↔ (M.reduct F).IsModel T := by
  constructor
  · intro h A hA; exact (sat_map F M A).1 (h _ ⟨A, hA, rfl⟩)
  · rintro h _ ⟨A, hA, rfl⟩; exact (sat_map F M A).2 (h A hA)

variable {L : Sig} {T : Theory L} (D : MoritaData L T)

theorem isModel_ext_iff (M : Str D.sig) : M.IsModel D.ext ↔
    (M.reduct D.incl).IsModel T ∧ (∀ σ, M.Satisfies (D.prodAx σ)) ∧
      (∀ σ, M.Satisfies (D.coprodAx σ)) ∧ (∀ σ, M.Satisfies (D.subAx σ)) ∧
      (∀ σ, M.Satisfies (D.quotAx σ)) ∧
      (∀ {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt} (f : D.NewFunc m dom s), M.Satisfies (D.funcAx f)) ∧
      (∀ {m : ℕ} {dom : Fin m → L.Srt} (r : D.NewRel m dom), M.Satisfies (D.relAx r)) := by
  constructor
  · intro h
    exact ⟨(isModel_map D.incl M T).1 fun A hA => h A (Or.inl hA),
      fun σ => h _ (mem_prod D σ), fun σ => h _ (mem_coprod D σ), fun σ => h _ (mem_sub D σ),
      fun σ => h _ (mem_quot D σ), fun f => h _ (mem_func D f), fun r => h _ (mem_rel D r)⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩ A (hA | hA)
    · exact (isModel_map D.incl M T).2 h0 A hA
    · rcases hA with (((((⟨σ, rfl⟩ | ⟨σ, rfl⟩) | ⟨σ, rfl⟩) | ⟨σ, rfl⟩) | ⟨m, dom, s, f, rfl⟩) |
        ⟨m, dom, r, rfl⟩)
      exacts [h1 σ, h2 σ, h3 σ, h4 σ, h5 f, h6 r]

end ExtModel

theorem imx_main {L : Sig} {T : Theory L} (D : MoritaData L T) (M : Str D.sig) :
    M.IsModel D.ext ↔
    (M.reduct D.incl).IsModel T ∧
    (∀ σ : D.Prod,
    ∀ v : (i : Fin 2) → M.carrier
        ((![MoritaData.ExtSrt.old (D.prodFst σ), MoritaData.ExtSrt.old (D.prodSnd σ)] : Fin 2 → D.sig.Srt) i),
      ∃ z : M.carrier (.prod σ), (M.funMap (L := D.sig) (MoritaData.ExtFunc.fst σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.prod σ] j)) z finZeroElim) = v 0 ∧
        M.funMap (L := D.sig) (MoritaData.ExtFunc.snd σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.prod σ] j)) z finZeroElim) = v 1) ∧
        ∀ z' : M.carrier (.prod σ), M.funMap (L := D.sig) (MoritaData.ExtFunc.fst σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.prod σ] j)) z' finZeroElim) = v 0 ∧
          M.funMap (L := D.sig) (MoritaData.ExtFunc.snd σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.prod σ] j)) z' finZeroElim) = v 1 → z' = z) ∧
    (∀ σ : D.Coprod,
    ∀ v : (i : Fin 1) → M.carrier ((![MoritaData.ExtSrt.coprod σ] : Fin 1 → D.sig.Srt) i),
      ((∃ a : M.carrier (.old (D.coprodFst σ)), M.funMap (L := D.sig) (MoritaData.ExtFunc.inl σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.coprodFst σ)] j)) a finZeroElim) = v 0 ∧
          ∀ a' : M.carrier (.old (D.coprodFst σ)), M.funMap (L := D.sig) (MoritaData.ExtFunc.inl σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.coprodFst σ)] j)) a' finZeroElim) = v 0 → a' = a) ∨
        (∃ b : M.carrier (.old (D.coprodSnd σ)), M.funMap (L := D.sig) (MoritaData.ExtFunc.inr σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.coprodSnd σ)] j)) b finZeroElim) = v 0 ∧
          ∀ b' : M.carrier (.old (D.coprodSnd σ)), M.funMap (L := D.sig) (MoritaData.ExtFunc.inr σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.coprodSnd σ)] j)) b' finZeroElim) = v 0 → b' = b)) ∧
      ∀ (a : M.carrier (.old (D.coprodFst σ))) (b : M.carrier (.old (D.coprodSnd σ))),
        ¬ M.funMap (L := D.sig) (MoritaData.ExtFunc.inl σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.coprodFst σ)] j)) a finZeroElim) = M.funMap (L := D.sig) (MoritaData.ExtFunc.inr σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.coprodSnd σ)] j)) b finZeroElim)) ∧
    (∀ σ : D.Sub,
    ∀ v : (i : Fin 1) → M.carrier ((D.incl.onSrt ∘ ![D.subBase σ] : Fin 1 → D.sig.Srt) i),
      ((D.subDef σ).Realize (M.reduct D.incl) v ↔
          ∃ z : M.carrier (.sub σ), M.funMap (L := D.sig) (MoritaData.ExtFunc.incl σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.sub σ] j)) z finZeroElim) = v 0) ∧
        ∀ z₁ z₂ : M.carrier (.sub σ), M.funMap (L := D.sig) (MoritaData.ExtFunc.incl σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.sub σ] j)) z₂ finZeroElim) =
          M.funMap (L := D.sig) (MoritaData.ExtFunc.incl σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.sub σ] j)) z₁ finZeroElim) → z₂ = z₁) ∧
    (∀ σ : D.Quot,
    ∀ v : (i : Fin 2) → M.carrier
        ((D.incl.onSrt ∘ ![D.quotBase σ, D.quotBase σ] : Fin 2 → D.sig.Srt) i),
      (M.funMap (L := D.sig) (MoritaData.ExtFunc.proj σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.quotBase σ)] j)) (v 0) finZeroElim) = M.funMap (L := D.sig) (MoritaData.ExtFunc.proj σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.quotBase σ)] j)) (v 1) finZeroElim) ↔
          (D.quotDef σ).Realize (M.reduct D.incl) v) ∧
        ∀ z : M.carrier (.quot σ), ∃ x : M.carrier (.old (D.quotBase σ)),
          M.funMap (L := D.sig) (MoritaData.ExtFunc.proj σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.quotBase σ)] j)) x finZeroElim) = z) ∧
    (∀ {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt} (f : D.NewFunc m dom s),
    ∀ v : (i : Fin (m + 1)) → M.carrier ((D.incl.onSrt ∘ Ctx.cons s dom : Fin (m + 1) → D.sig.Srt) i),
      (M.funMap (L := D.sig) (MoritaData.ExtFunc.new f) (fun j => v j.succ) = v 0 ↔
        (D.funcDef f).Realize (M.reduct D.incl) v)) ∧
    (∀ {m : ℕ} {dom : Fin m → L.Srt} (r : D.NewRel m dom),
    ∀ v : (i : Fin m) → M.carrier ((D.incl.onSrt ∘ dom : Fin m → D.sig.Srt) i),
      (M.relMap (L := D.sig) (MoritaData.ExtRel.new r) (fun j => v j) ↔
        (D.relDef r).Realize (M.reduct D.incl) v)) :=
  (isModel_ext_iff D M).trans <| and_congr Iff.rfl <|
    and_congr (forall_congr' fun σ => sat_prod D M σ) <|
    and_congr (forall_congr' fun σ => sat_coprod D M σ) <|
    and_congr (forall_congr' fun σ => sat_sub D M σ) <|
    and_congr (forall_congr' fun σ => sat_quot D M σ) <|
    and_congr ⟨fun h _ _ _ f => (sat_func D M f).1 (h f), fun h _ _ _ f => (sat_func D M f).2 (h f)⟩
      ⟨fun h _ _ r => (sat_rel D M r).1 (h r), fun h _ _ r => (sat_rel D M r).2 (h r)⟩

end IMX

end MoritaEquiv

open MoritaEquiv

theorem solution {L : Sig} {T : Theory L} (D : MoritaData L T) (M : Str D.sig) :
    M.IsModel D.ext ↔
    (M.reduct D.incl).IsModel T ∧
    (∀ σ : D.Prod,
    ∀ v : (i : Fin 2) → M.carrier
        ((![MoritaData.ExtSrt.old (D.prodFst σ), MoritaData.ExtSrt.old (D.prodSnd σ)] : Fin 2 → D.sig.Srt) i),
      ∃ z : M.carrier (.prod σ), (M.funMap (L := D.sig) (MoritaData.ExtFunc.fst σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.prod σ] j)) z finZeroElim) = v 0 ∧
        M.funMap (L := D.sig) (MoritaData.ExtFunc.snd σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.prod σ] j)) z finZeroElim) = v 1) ∧
        ∀ z' : M.carrier (.prod σ), M.funMap (L := D.sig) (MoritaData.ExtFunc.fst σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.prod σ] j)) z' finZeroElim) = v 0 ∧
          M.funMap (L := D.sig) (MoritaData.ExtFunc.snd σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.prod σ] j)) z' finZeroElim) = v 1 → z' = z) ∧
    (∀ σ : D.Coprod,
    ∀ v : (i : Fin 1) → M.carrier ((![MoritaData.ExtSrt.coprod σ] : Fin 1 → D.sig.Srt) i),
      ((∃ a : M.carrier (.old (D.coprodFst σ)), M.funMap (L := D.sig) (MoritaData.ExtFunc.inl σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.coprodFst σ)] j)) a finZeroElim) = v 0 ∧
          ∀ a' : M.carrier (.old (D.coprodFst σ)), M.funMap (L := D.sig) (MoritaData.ExtFunc.inl σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.coprodFst σ)] j)) a' finZeroElim) = v 0 → a' = a) ∨
        (∃ b : M.carrier (.old (D.coprodSnd σ)), M.funMap (L := D.sig) (MoritaData.ExtFunc.inr σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.coprodSnd σ)] j)) b finZeroElim) = v 0 ∧
          ∀ b' : M.carrier (.old (D.coprodSnd σ)), M.funMap (L := D.sig) (MoritaData.ExtFunc.inr σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.coprodSnd σ)] j)) b' finZeroElim) = v 0 → b' = b)) ∧
      ∀ (a : M.carrier (.old (D.coprodFst σ))) (b : M.carrier (.old (D.coprodSnd σ))),
        ¬ M.funMap (L := D.sig) (MoritaData.ExtFunc.inl σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.coprodFst σ)] j)) a finZeroElim) = M.funMap (L := D.sig) (MoritaData.ExtFunc.inr σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.coprodSnd σ)] j)) b finZeroElim)) ∧
    (∀ σ : D.Sub,
    ∀ v : (i : Fin 1) → M.carrier ((D.incl.onSrt ∘ ![D.subBase σ] : Fin 1 → D.sig.Srt) i),
      ((D.subDef σ).Realize (M.reduct D.incl) v ↔
          ∃ z : M.carrier (.sub σ), M.funMap (L := D.sig) (MoritaData.ExtFunc.incl σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.sub σ] j)) z finZeroElim) = v 0) ∧
        ∀ z₁ z₂ : M.carrier (.sub σ), M.funMap (L := D.sig) (MoritaData.ExtFunc.incl σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.sub σ] j)) z₂ finZeroElim) =
          M.funMap (L := D.sig) (MoritaData.ExtFunc.incl σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.sub σ] j)) z₁ finZeroElim) → z₂ = z₁) ∧
    (∀ σ : D.Quot,
    ∀ v : (i : Fin 2) → M.carrier
        ((D.incl.onSrt ∘ ![D.quotBase σ, D.quotBase σ] : Fin 2 → D.sig.Srt) i),
      (M.funMap (L := D.sig) (MoritaData.ExtFunc.proj σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.quotBase σ)] j)) (v 0) finZeroElim) = M.funMap (L := D.sig) (MoritaData.ExtFunc.proj σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.quotBase σ)] j)) (v 1) finZeroElim) ↔
          (D.quotDef σ).Realize (M.reduct D.incl) v) ∧
        ∀ z : M.carrier (.quot σ), ∃ x : M.carrier (.old (D.quotBase σ)),
          M.funMap (L := D.sig) (MoritaData.ExtFunc.proj σ)
          (Fin.cons (α := fun j => M.carrier (![MoritaData.ExtSrt.old (D.quotBase σ)] j)) x finZeroElim) = z) ∧
    (∀ {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt} (f : D.NewFunc m dom s),
    ∀ v : (i : Fin (m + 1)) → M.carrier ((D.incl.onSrt ∘ Ctx.cons s dom : Fin (m + 1) → D.sig.Srt) i),
      (M.funMap (L := D.sig) (MoritaData.ExtFunc.new f) (fun j => v j.succ) = v 0 ↔
        (D.funcDef f).Realize (M.reduct D.incl) v)) ∧
    (∀ {m : ℕ} {dom : Fin m → L.Srt} (r : D.NewRel m dom),
    ∀ v : (i : Fin m) → M.carrier ((D.incl.onSrt ∘ dom : Fin m → D.sig.Srt) i),
      (M.relMap (L := D.sig) (MoritaData.ExtRel.new r) (fun j => v j) ↔
        (D.relDef r).Realize (M.reduct D.incl) v)) :=
  MoritaEquiv.IMX.imx_main D M
