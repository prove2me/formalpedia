-- Prove2me | solution 1 for MoritaEquiv.MoritaData.model_ext_newSorts
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-12T20:09:26.724683+00:00
-- url     : https://prove2.me/submissions/b319e9b5-e6d2-4ce0-9b10-bc206bef5310

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

variable {L : Sig}

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

end EEU

/-- In every model `N` of a Morita extension `T⁺`, the canonical maps attached to the new sorts are
bijections onto their intended targets: `z ↦ (π₁ z, π₂ z)` for a product sort, `[ρ₁, ρ₂]` for a
coproduct sort, the inclusion `i` onto `{a | φ(a)}` for a subsort, and `ε` with kernel `φ(a, b)`
for a quotient sort. -/
theorem mens_main {L : Sig} {T : Theory L} (D : MoritaData L T)
    (N : Model D.ext) :
    (∀ σ : D.Prod, Function.Bijective fun z : N.str.carrier (.prod σ) =>
      (N.str.funMap (L := D.sig) (MoritaData.ExtFunc.fst σ)
          (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.prod σ] j)) z finZeroElim),
        N.str.funMap (L := D.sig) (MoritaData.ExtFunc.snd σ)
          (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.prod σ] j)) z finZeroElim))) ∧
    (∀ σ : D.Coprod, Function.Bijective (Sum.elim
      (fun a : N.str.carrier (.old (D.coprodFst σ)) =>
        N.str.funMap (L := D.sig) (MoritaData.ExtFunc.inl σ)
          (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.old (D.coprodFst σ)] j)) a
            finZeroElim))
      (fun b : N.str.carrier (.old (D.coprodSnd σ)) =>
        N.str.funMap (L := D.sig) (MoritaData.ExtFunc.inr σ)
          (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.old (D.coprodSnd σ)] j)) b
            finZeroElim)))) ∧
    (∀ σ : D.Sub, Function.Injective (fun z : N.str.carrier (.sub σ) =>
        N.str.funMap (L := D.sig) (MoritaData.ExtFunc.incl σ)
          (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.sub σ] j)) z finZeroElim)) ∧
      ∀ a : N.str.carrier (.old (D.subBase σ)),
        (∃ z : N.str.carrier (.sub σ), N.str.funMap (L := D.sig) (MoritaData.ExtFunc.incl σ)
          (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.sub σ] j)) z finZeroElim) = a) ↔
        (D.subDef σ).Realize (N.str.reduct D.incl)
          (Fin.cons (α := fun j => (N.str.reduct D.incl).carrier (![D.subBase σ] j)) a finZeroElim)) ∧
    (∀ σ : D.Quot, Function.Surjective (fun a : N.str.carrier (.old (D.quotBase σ)) =>
        N.str.funMap (L := D.sig) (MoritaData.ExtFunc.proj σ)
          (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.old (D.quotBase σ)] j)) a
            finZeroElim)) ∧
      ∀ a b : N.str.carrier (.old (D.quotBase σ)),
        N.str.funMap (L := D.sig) (MoritaData.ExtFunc.proj σ)
            (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.old (D.quotBase σ)] j)) a
              finZeroElim) =
          N.str.funMap (L := D.sig) (MoritaData.ExtFunc.proj σ)
            (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.old (D.quotBase σ)] j)) b
              finZeroElim) ↔
        (D.quotDef σ).Realize (N.str.reduct D.incl)
          (Fin.cons (α := fun j => (N.str.reduct D.incl).carrier (![D.quotBase σ, D.quotBase σ] j)) a
            (Fin.cons
              (α := fun j => (N.str.reduct D.incl).carrier (![D.quotBase σ, D.quotBase σ] j.succ)) b
              finZeroElim))) := by
  have hax : ∀ {A : Axiom D.sig}, A ∈ D.ext → N.str.Satisfies A := fun h => N.isModel _ h
  refine ⟨fun σ => ?_, fun σ => ?_, fun σ => ?_, fun σ => ?_⟩
  · have H := (EEU.sat_prod D N.str σ).1 (hax (EEU.mem_prod D σ))
    constructor
    · intro z₁ z₂ h
      obtain ⟨z, -, hu⟩ := H (Fin.cons (EEU.ap N.str (L := D.sig) (MoritaData.ExtFunc.fst σ) z₂)
        (Fin.cons (EEU.ap N.str (L := D.sig) (MoritaData.ExtFunc.snd σ) z₂) finZeroElim))
      rw [hu z₂ ⟨rfl, rfl⟩]
      exact hu z₁ ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · rintro ⟨x, y⟩
      obtain ⟨z, ⟨h1, h2⟩, -⟩ := H (Fin.cons x (Fin.cons y finZeroElim))
      exact ⟨z, Prod.ext h1 h2⟩
  · have H := (EEU.sat_coprod D N.str σ).1 (hax (EEU.mem_coprod D σ))
    have H' : ∀ z, _ := fun z => H (Fin.cons z finZeroElim)
    constructor
    · rintro (a | b) (a' | b') h
      · obtain ⟨⟨a₀, -, hu⟩ | ⟨b₀, hb, -⟩, -⟩ :=
          H' (EEU.ap N.str (L := D.sig) (MoritaData.ExtFunc.inl σ) a')
        · exact congrArg Sum.inl ((hu a h).trans (hu a' rfl).symm)
        · exact absurd hb.symm
            ((H' (EEU.ap N.str (L := D.sig) (MoritaData.ExtFunc.inl σ) a')).2 a' b₀)
      · exact absurd h ((H' (EEU.ap N.str (L := D.sig) (MoritaData.ExtFunc.inl σ) a)).2 a b')
      · exact absurd h.symm ((H' (EEU.ap N.str (L := D.sig) (MoritaData.ExtFunc.inl σ) a')).2 a' b)
      · obtain ⟨⟨a₀, ha, -⟩ | ⟨b₀, -, hu⟩, -⟩ :=
          H' (EEU.ap N.str (L := D.sig) (MoritaData.ExtFunc.inr σ) b')
        · exact absurd ha ((H' (EEU.ap N.str (L := D.sig) (MoritaData.ExtFunc.inr σ) b')).2 a₀ b')
        · exact congrArg Sum.inr ((hu b h).trans (hu b' rfl).symm)
    · intro z
      obtain ⟨⟨a, ha, -⟩ | ⟨b, hb, -⟩, -⟩ := H' z
      · exact ⟨Sum.inl a, ha⟩
      · exact ⟨Sum.inr b, hb⟩
  · have H := (EEU.sat_sub D N.str σ).1 (hax (EEU.mem_sub D σ))
    exact ⟨fun z₁ z₂ h => ((H (Fin.cons (EEU.ap N.str (L := D.sig) (MoritaData.ExtFunc.incl σ) z₁)
      finZeroElim)).2 z₁ z₂ h.symm).symm, fun a => (H (Fin.cons a finZeroElim)).1.symm⟩
  · have H := (EEU.sat_quot D N.str σ).1 (hax (EEU.mem_quot D σ))
    exact ⟨fun z => (H (fun _ => Classical.choice (N.str.nonempty _))).2 z,
      fun a b => (H (Fin.cons a (Fin.cons b finZeroElim))).1⟩

end MoritaEquiv

open MoritaEquiv

theorem solution {L : Sig} {T : Theory L} (D : MoritaData L T)
    (N : Model D.ext) :
    (∀ σ : D.Prod, Function.Bijective fun z : N.str.carrier (.prod σ) =>
      (N.str.funMap (L := D.sig) (MoritaData.ExtFunc.fst σ)
          (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.prod σ] j)) z finZeroElim),
        N.str.funMap (L := D.sig) (MoritaData.ExtFunc.snd σ)
          (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.prod σ] j)) z finZeroElim))) ∧
    (∀ σ : D.Coprod, Function.Bijective (Sum.elim
      (fun a : N.str.carrier (.old (D.coprodFst σ)) =>
        N.str.funMap (L := D.sig) (MoritaData.ExtFunc.inl σ)
          (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.old (D.coprodFst σ)] j)) a
            finZeroElim))
      (fun b : N.str.carrier (.old (D.coprodSnd σ)) =>
        N.str.funMap (L := D.sig) (MoritaData.ExtFunc.inr σ)
          (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.old (D.coprodSnd σ)] j)) b
            finZeroElim)))) ∧
    (∀ σ : D.Sub, Function.Injective (fun z : N.str.carrier (.sub σ) =>
        N.str.funMap (L := D.sig) (MoritaData.ExtFunc.incl σ)
          (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.sub σ] j)) z finZeroElim)) ∧
      ∀ a : N.str.carrier (.old (D.subBase σ)),
        (∃ z : N.str.carrier (.sub σ), N.str.funMap (L := D.sig) (MoritaData.ExtFunc.incl σ)
          (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.sub σ] j)) z finZeroElim) = a) ↔
        (D.subDef σ).Realize (N.str.reduct D.incl)
          (Fin.cons (α := fun j => (N.str.reduct D.incl).carrier (![D.subBase σ] j)) a finZeroElim)) ∧
    (∀ σ : D.Quot, Function.Surjective (fun a : N.str.carrier (.old (D.quotBase σ)) =>
        N.str.funMap (L := D.sig) (MoritaData.ExtFunc.proj σ)
          (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.old (D.quotBase σ)] j)) a
            finZeroElim)) ∧
      ∀ a b : N.str.carrier (.old (D.quotBase σ)),
        N.str.funMap (L := D.sig) (MoritaData.ExtFunc.proj σ)
            (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.old (D.quotBase σ)] j)) a
              finZeroElim) =
          N.str.funMap (L := D.sig) (MoritaData.ExtFunc.proj σ)
            (Fin.cons (α := fun j => N.str.carrier (![MoritaData.ExtSrt.old (D.quotBase σ)] j)) b
              finZeroElim) ↔
        (D.quotDef σ).Realize (N.str.reduct D.incl)
          (Fin.cons (α := fun j => (N.str.reduct D.incl).carrier (![D.quotBase σ, D.quotBase σ] j)) a
            (Fin.cons
              (α := fun j => (N.str.reduct D.incl).carrier (![D.quotBase σ, D.quotBase σ] j.succ)) b
              finZeroElim))) := by
  exact mens_main D N
