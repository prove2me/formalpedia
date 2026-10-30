-- Prove2me | solution 1 for OAI.PureTypeSystem.Labelled.DoubleCode.Formed.access_recovery
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:05:41.953896+00:00
-- url     : https://prove2.me/submissions/829f68c6-2ed0-4fba-be42-9131a5e9e407

import Mathlib
import Definitions.Def_TypeSystemNormalization
import Definitions.Def_OAIQ5T6000

section
-- module Solutions.OAIQ5_T6.TypeSystem_Labelled
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/- Labelled beta reduction retains every annotation.
These are definitions, not an extension of the PTS specification. -/
namespace PureTypeSystem.Labelled

universe u

namespace Expr
variable {S : Type u}

theorem instantiate_rename (b a : Expr S) (ρ : Nat → Nat) :
    (b.rename (liftRen ρ)).instantiate (a.rename ρ) = (b.instantiate a).rename ρ := by
  simp only [instantiate, subst_rename, rename_subst]
  congr 1; funext n; cases n <;> rfl

end Expr

namespace Beta
variable {S : Type u} {M N : Expr S}

theorem rename (h : Beta M N) (ρ : Nat → Nat) : Beta (M.rename ρ) (N.rename ρ) := by
  induction h generalizing ρ with
  | head l A b a =>
      simpa only [Expr.rename, ← Expr.instantiate_rename] using
        (Beta.head l (A.rename ρ) (b.rename (Expr.liftRen ρ)) (a.rename ρ))
  | app_left h ih => exact .app_left (ih ρ)
  | app_right h ih => exact .app_right (ih ρ)
  | lam_domain h ih => exact .lam_domain (ih ρ)
  | lam_body h ih => exact .lam_body (ih _)
  | pi_domain h ih => exact .pi_domain (ih ρ)
  | pi_body h ih => exact .pi_body (ih _)

end Beta

namespace Parallel

variable {S : Type u} {M N : Expr S}

theorem of_beta (h : Beta M N) : Parallel M N := by
  induction h with
  | head l A b a => exact .head A (refl b) (refl a)
  | app_left _ ih => exact .app ih (refl _)
  | app_right _ ih => exact .app (refl _) ih
  | lam_domain _ ih => exact .lam ih (refl _)
  | lam_body _ ih => exact .lam (refl _) ih
  | pi_domain _ ih => exact .pi ih (refl _)
  | pi_body _ ih => exact .pi (refl _) ih

theorem rename (h : Parallel M N) (ρ : Nat → Nat) :
    Parallel (M.rename ρ) (N.rename ρ) := by
  induction h generalizing ρ with
  | var n => exact .var _
  | sort s => exact .sort _
  | app _ _ ihf iha => exact .app (ihf ρ) (iha ρ)
  | lam _ _ ihA ihb => exact .lam (ihA ρ) (ihb (Expr.liftRen ρ))
  | pi _ _ ihA ihB => exact .pi (ihA ρ) (ihB (Expr.liftRen ρ))
  | head A _ _ ihb iha =>
      simpa only [Expr.rename, ← Expr.instantiate_rename] using
        (Parallel.head (A.rename ρ) (ihb (Expr.liftRen ρ)) (iha ρ))

theorem subst (h : Parallel M N) (σ τ : Nat → Expr S)
    (hστ : ∀ n, Parallel (σ n) (τ n)) : Parallel (M.subst σ) (N.subst τ) := by
  have hlift (σ τ : Nat → Expr S) (hστ : ∀ n, Parallel (σ n) (τ n)) :
      ∀ n, Parallel (Expr.liftSub σ n) (Expr.liftSub τ n) := by
    intro n
    cases n with
    | zero => exact .var 0
    | succ n => exact (hστ n).rename Nat.succ
  induction h generalizing σ τ with
  | var n => exact hστ n
  | sort s => exact .sort s
  | app _ _ ihf iha => exact .app (ihf σ τ hστ) (iha σ τ hστ)
  | lam _ _ ihA ihb => exact .lam (ihA σ τ hστ) (ihb _ _ (hlift σ τ hστ))
  | pi _ _ ihA ihB => exact .pi (ihA σ τ hστ) (ihB _ _ (hlift σ τ hστ))
  | head A _ _ ihb iha =>
      simpa only [Expr.subst, ← Expr.instantiate_subst] using
        (Parallel.head (A.subst σ) (ihb _ _ (hlift σ τ hστ)) (iha σ τ hστ))

theorem instantiate {b b' a a' : Expr S} (hb : Parallel b b') (ha : Parallel a a') :
    Parallel (b.instantiate a) (b'.instantiate a') := by
  apply hb.subst
  intro n
  cases n with
  | zero => exact ha
  | succ n => exact .var n

end Parallel

namespace Parallel

variable {S : Type u} {M N : Expr S}

theorem triangle (h : Parallel M N) : Parallel N M.develop := by
  induction h with
  | var n => exact .var n
  | sort s => exact .sort s
  | @app l f f' a a' hf ha ihf iha =>
      cases f with
      | var n => exact .app ihf iha
      | sort s => exact .app ihf iha
      | app k f b => exact .app ihf iha
      | pi k A B => exact .app ihf iha
      | lam k A b =>
          by_cases hl : l = k
          · subst k
            cases hf with
            | lam hA hb =>
                cases ihf with
                | lam ihA ihb => simpa only [Expr.develop, ite_eq_left rfl, ite_true, if_true] using
                    (Parallel.head (l := l) _ ihb iha)
          · simpa only [Expr.develop, ite_eq_right hl] using (Parallel.app (l := l) ihf iha)
  | lam _ _ ihA ihb => exact .lam ihA ihb
  | pi _ _ ihA ihB => exact .pi ihA ihB
  | head A _ _ ihb iha =>
      simpa only [Expr.develop, ite_eq_left rfl, ite_true, if_true] using ihb.instantiate iha

theorem diamond {a b c : Expr S} (hab : Parallel a b) (hac : Parallel a c) :
    ∃ d, Parallel b d ∧ Parallel c d := ⟨a.develop, hab.triangle, hac.triangle⟩

end Parallel

namespace Reduces

variable {S : Type u} {l : Label} {f f' a a' A A' b b' : Expr S}

theorem app (hf : Reduces f f') (ha : Reduces a a') :
    Reduces (.app l f a) (.app l f' a') := by
  exact (hf.lift (fun x => Expr.app l x a) (fun _ _ h => Beta.app_left h)).trans
    (ha.lift (fun x => Expr.app l f' x) (fun _ _ h => Beta.app_right h))

theorem lam (hA : Reduces A A') (hb : Reduces b b') :
    Reduces (.lam l A b) (.lam l A' b') := by
  exact (hA.lift (fun x => Expr.lam l x b) (fun _ _ h => Beta.lam_domain h)).trans
    (hb.lift (fun x => Expr.lam l A' x) (fun _ _ h => Beta.lam_body h))

theorem pi (hA : Reduces A A') (hb : Reduces b b') :
    Reduces (.pi l A b) (.pi l A' b') := by
  exact (hA.lift (fun x => Expr.pi l x b) (fun _ _ h => Beta.pi_domain h)).trans
    (hb.lift (fun x => Expr.pi l A' x) (fun _ _ h => Beta.pi_body h))

end Reduces

namespace Parallel

variable {S : Type u} {M N : Expr S}

theorem reduces (h : Parallel M N) : Reduces M N := by
  induction h with
  | var n => exact .refl
  | sort s => exact .refl
  | app _ _ ihf iha => exact Reduces.app ihf iha
  | lam _ _ ihA ihb => exact Reduces.lam ihA ihb
  | pi _ _ ihA ihB => exact Reduces.pi ihA ihB
  | head A _ _ ihb iha =>
      exact (Reduces.app (Reduces.lam .refl ihb) iha).tail (.head _ _ _ _)

theorem rtc_reduces {M N : Expr S} (h : Relation.ReflTransGen Parallel M N) :
    Reduces M N := Relation.reflTransGen_closed (fun _ _ h => h.reduces) _ _ h

end Parallel

namespace Reduces

variable {S : Type u} {M N : Expr S}

theorem parallel (h : Reduces M N) : Relation.ReflTransGen Parallel M N :=
  Relation.ReflTransGen.mono (fun _ _ h => Parallel.of_beta h) _ _ h

theorem confluent {a b c : Expr S} (hab : Reduces a b) (hac : Reduces a c) :
    Relation.Join Reduces b c := by
  have hd : ∀ a b c : Expr S, Parallel a b → Parallel a c →
      ∃ d, Relation.ReflGen Parallel b d ∧ Relation.ReflTransGen Parallel c d := by
    intro a b c hab hac
    obtain ⟨d, hb, hc⟩ := Parallel.diamond hab hac
    exact ⟨d, .single hb, .single hc⟩
  obtain ⟨d, hb, hc⟩ := Relation.church_rosser hd hab.parallel hac.parallel
  exact ⟨d, Parallel.rtc_reduces hb, Parallel.rtc_reduces hc⟩

end Reduces

namespace Converts

variable {S : Type u} {M N : Expr S}

theorem join (h : Converts M N) : Relation.Join Reduces M N := by
  induction h with
  | rel a b h => exact ⟨b, .single h, .refl⟩
  | refl a => exact ⟨a, .refl, .refl⟩
  | symm a b _ ih =>
      obtain ⟨c, ha, hb⟩ := ih
      exact ⟨c, hb, ha⟩
  | trans a b c _ _ ih₁ ih₂ =>
      obtain ⟨d, ha, hb⟩ := ih₁
      obtain ⟨e, hb', hc⟩ := ih₂
      obtain ⟨f, hd, he⟩ := Reduces.confluent hb hb'
      exact ⟨f, ha.trans hd, hc.trans he⟩

end Converts

namespace Reduces

variable {S : Type u} {l : Label} {A B N : Expr S}

theorem converts {M N : Expr S} (h : Reduces M N) : Converts M N :=
  Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ h

end Reduces

namespace Converts

variable {S : Type u} {M N : Expr S}

theorem rename (h : Converts M N) (ρ : Nat → Nat) :
    Converts (M.rename ρ) (N.rename ρ) := by
  induction h with
  | rel a b h => exact .rel _ _ (h.rename ρ)
  | refl a => exact .refl _
  | symm a b _ ih => exact .symm _ _ ih
  | trans a b c _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

end Converts

namespace TypedSubstitution

variable {S : Type u} {P : Specification S}

theorem weaken {Γ : List (Expr S)} {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) :
    TypedSubstitution P Γ (A :: Γ) (Expr.var ∘ Nat.succ) := by
  intro n B hn
  simpa only [Expr.subst_var_rename, Function.comp_apply, Expr.rename] using
    (HasType.weaken (HasType.lookup hA.valid hn) hA)

theorem single {Γ : List (Expr S)} {a A : Expr S} (ha : HasType P Γ a A) :
    TypedSubstitution P (A :: Γ) Γ (Expr.single a) := by
  intro n B hn
  cases hn with
  | zero => simpa only [Expr.single, Expr.subst_lift_single] using ha
  | succ _ hn =>
      simpa only [Expr.single, Expr.subst_lift_single] using HasType.lookup ha.valid hn

end TypedSubstitution

namespace HasType

variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)}

theorem instantiate {A b B a : Expr S}
    (hb : HasType P (A :: Γ) b B) (ha : HasType P Γ a A) :
    HasType P Γ (b.instantiate a) (B.instantiate a) :=
  hb.subst ha.valid _ (TypedSubstitution.single ha)

theorem weaken_under {A D b B : Expr S} {s t : S}
    (hb : HasType P (A :: Γ) b B) (hA : HasType P Γ A (.sort s))
    (hD : HasType P Γ D (.sort t)) :
    HasType P (A.rename Nat.succ :: D :: Γ)
      (b.rename (Expr.liftRen Nat.succ)) (B.rename (Expr.liftRen Nat.succ)) := by
  have hA' : HasType P (D :: Γ) (A.subst (Expr.var ∘ Nat.succ)) (.sort s) := by
    simpa only [Expr.subst_var_rename, Expr.rename] using HasType.weaken hA hD
  have hσ := (TypedSubstitution.weaken hD).lift hA'
  have h := hb.subst (.cons (.cons hD.valid hD) hA') _ hσ
  have heq : Expr.liftSub (Expr.var ∘ Nat.succ : Nat → Expr S) =
      Expr.var ∘ Expr.liftRen Nat.succ := by
    funext n
    cases n <;> rfl
  simpa only [heq, Expr.subst_var_rename] using h

end HasType

namespace HasType

variable {S : Type u} {P : Specification S}

theorem generation {Γ : List (Expr S)} {M T : Expr S}
    (h : HasType P Γ M T) : Generation P Γ M T := by
  induction h with
  | ax h => exact ⟨_, h, .refl _⟩
  | var h ih => exact ⟨_, .zero _ _, .refl _⟩
  | @weaken Γ M T D s hM hD ihM ihD =>
      cases M with
      | var n =>
          obtain ⟨A, hA, hc⟩ := ihM
          exact ⟨_, .succ D hA, hc.rename Nat.succ⟩
      | sort t =>
          obtain ⟨t', ht, hc⟩ := ihM
          exact ⟨t', ht, hc.rename Nat.succ⟩
      | app l f a =>
          obtain ⟨A, B, hf, ha, hc⟩ := ihM
          refine ⟨_, _, .weaken hf hD, .weaken ha hD, ?_⟩
          simpa only [Expr.instantiate_rename] using hc.rename Nat.succ
      | lam l A b =>
          obtain ⟨B, t, hb, hPi, hc⟩ := ihM
          obtain ⟨r, hA⟩ := hPi.product_domain _ _ _ rfl
          exact ⟨_, t, hb.weaken_under hA hD, .weaken hPi hD,
            hc.rename Nat.succ⟩
      | pi l A B =>
          obtain ⟨t₁, t₂, t₃, hA, hB, hr, hc⟩ := ihM
          exact ⟨t₁, t₂, t₃, .weaken hA hD, hB.weaken_under hA hD,
            hr, hc.rename Nat.succ⟩
  | product hA hB hr ihA ihB => exact ⟨_, _, _, hA, hB, hr, .refl _⟩
  | abstraction hb hPi ihb ihPi => exact ⟨_, _, hb, hPi, .refl _⟩
  | application hf ha ihf iha => exact ⟨_, _, hf, ha, .refl _⟩
  | @conversion Γ M A B s hM hB hc ihM ihB =>
      cases M with
      | var n =>
          obtain ⟨D, hD, hd⟩ := ihM
          exact ⟨D, hD, .trans _ _ _ (.symm _ _ hc) hd⟩
      | sort t =>
          obtain ⟨r, hr, hd⟩ := ihM
          exact ⟨r, hr, .trans _ _ _ (.symm _ _ hc) hd⟩
      | app l f a =>
          obtain ⟨D, E, hf, ha, hd⟩ := ihM
          exact ⟨D, E, hf, ha, .trans _ _ _ (.symm _ _ hc) hd⟩
      | lam l D b =>
          obtain ⟨E, r, hb, hPi, hd⟩ := ihM
          exact ⟨E, r, hb, hPi, .trans _ _ _ (.symm _ _ hc) hd⟩
      | pi l D E =>
          obtain ⟨r₁, r₂, r₃, hD, hE, hr, hd⟩ := ihM
          exact ⟨r₁, r₂, r₃, hD, hE, hr, .trans _ _ _ (.symm _ _ hc) hd⟩

theorem generation_pi {l : Label} {Γ : List (Expr S)} {A B T : Expr S}
    (h : HasType P Γ (.pi l A B) T) :
    ∃ s₁ s₂ s₃, HasType P Γ A (.sort s₁) ∧
      HasType P (A :: Γ) B (.sort s₂) ∧ P.rule s₁ s₂ s₃ ∧
      Converts T (.sort s₃) := h.generation

end HasType

namespace Converts

variable {S : Type u}

theorem pi {l : Label} {A A' B B' : Expr S} (hA : Converts A A') (hB : Converts B B') :
    Converts (.pi l A B) (.pi l A' B') := by
  obtain ⟨D, hD, hD'⟩ := hA.join
  obtain ⟨E, hE, hE'⟩ := hB.join
  exact .trans _ _ _ (hD.pi hE).converts (.symm _ _ (hD'.pi hE').converts)

theorem instantiate_right {a a' : Expr S} (h : Converts a a') (B : Expr S) :
    Converts (B.instantiate a) (B.instantiate a') := by
  induction h with
  | rel a a' h =>
      exact (Parallel.instantiate (Parallel.refl B) (Parallel.of_beta h)).reduces.converts
  | refl a => exact .refl _
  | symm a b h ih => exact .symm _ _ ih
  | trans a b c hab hbc ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

end Converts

namespace WellModed
variable {S : Type u} {γ δ : Nat → Mode} {M : Expr S} {m : Mode}

theorem subst (h : WellModed γ M m) (σ : Nat → Expr S)
    (hσ : ∀ n, WellModed δ (σ n) (γ n)) : WellModed δ (M.subst σ) m := by
  have hlift {γ δ : Nat → Mode} (σ : Nat → Expr S)
      (hσ : ∀ n, WellModed δ (σ n) (γ n)) (i : Mode) :
      ∀ n, WellModed (modeCons i δ) (Expr.liftSub σ n) (modeCons i γ n) := by
    intro n
    cases n with
    | zero => exact .var 0
    | succ n => exact (hσ n).rename Nat.succ (fun _ => rfl)
  induction h generalizing δ σ with
  | var n => exact hσ n
  | sort s => exact .sort s
  | app hf ha ihf iha => exact .app (ihf σ hσ) (iha σ hσ)
  | lam hA hb ihA ihb => exact .lam (ihA σ hσ) (ihb _ (hlift σ hσ _))
  | pi hA hB ihA ihB => exact .pi (ihA σ hσ) (ihB _ (hlift σ hσ _))

theorem instantiate {i : Mode} {b a : Expr S}
    (hb : WellModed (modeCons i γ) b m) (ha : WellModed γ a i) :
    WellModed γ (b.instantiate a) m := by
  apply hb.subst
  intro n
  cases n with
  | zero => exact ha
  | succ n => exact .var n

end WellModed

end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Wrappers
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate _root_.OAI.PureTypeSystem.instCountableExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/- Concrete labelled term operations for wrappers. -/
namespace PureTypeSystem.Labelled
universe u

namespace HasType
variable {S : Type u} {P : Specification S}

variable {Γ : List (Expr S)} {A B M N : Expr S} {s t r : S} {l : Label}
theorem arrow (hA : HasType P Γ A (.sort s)) (hB : HasType P Γ B (.sort t))
    (hr : P.rule s t r) : HasType P Γ (Expr.arrow l A B) (.sort r) :=
  .product hA (.weaken hB hA) hr

theorem constLam (hM : HasType P Γ M B) (hA : HasType P Γ A (.sort s))
    (hPi : HasType P Γ (Expr.arrow l A B) (.sort r)) :
    HasType P Γ (Expr.constLam l A M) (Expr.arrow l A B) :=
  .abstraction (.weaken hM hA) hPi

theorem apply_arrow (hM : HasType P Γ M (Expr.arrow l A B)) (hN : HasType P Γ N A) :
    HasType P Γ (.app l M N) B := by
  simpa only [Expr.instantiate_raise] using HasType.application hM hN
end HasType

namespace WellModed
variable {S : Type u} {γ : Nat → Mode} {A B M : Expr S} {l : Label}

theorem raise {m : Mode} (h : WellModed γ M m) (d : Mode) :
    WellModed (modeCons d γ) (M.rename Nat.succ) m :=
  h.rename _ (fun _ => rfl)

theorem arrow (hA : WellModed γ A .data) (hB : WellModed γ B .data) :
    WellModed γ (Expr.arrow l A B) .data := .pi hA (hB.raise _)

theorem constLam (hA : WellModed γ A .data) (hM : WellModed γ M l.result) :
    WellModed γ (Expr.constLam l A M) l.result := .lam hA (hM.raise _)
end WellModed

namespace SortedAt
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)}
    {A B : Expr S} {I J K : Set S}
theorem mono (h : SortedAt P Γ A I) (hJI : J ⊆ I) : SortedAt P Γ A J :=
  fun _ hs => h _ (hJI hs)

theorem arrow (hA : SortedAt P Γ A I) (hB : SortedAt P Γ B J) (l : Label)
    (hK : K ⊆ OutProfile P I J) : SortedAt P Γ (Expr.arrow l A B) K := by
  intro r hr
  obtain ⟨s, hs, t, ht, hst⟩ := hK hr
  exact (hA s hs).arrow (hB t ht) hst

end SortedAt

/-- The exact positive product-edge lift/projection beta cancellation. -/
theorem positive_cancel {S : Type u} (l : Label) (D e t : Expr S) :
    Beta (.app l (Expr.constLam l D t) e) t := by
  simpa only [Expr.constLam, Expr.instantiate_raise] using Beta.head l D (t.rename Nat.succ) e

end PureTypeSystem.Labelled

/-! Finite simultaneous normal data witnesses.
Feasibility is semantic, so these lemmas do not assume a profile-generation
conjecture. The extra inhabitants are genuine fresh context variables. -/

namespace PureTypeSystem.Labelled

section
universe u
open Classical

namespace Transfer
variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)} {γ δ : Nat → Mode}
    {A B C D : Expr S} {s t r : S}
theorem refl (hA : HasType P Γ A (.sort s)) : Transfer P Γ γ A A :=
  ⟨_,.var hA,.var 0⟩

theorem trans (h : Transfer P Γ γ A B) (h' : Transfer P Γ γ B C)
    (hA : HasType P Γ A (.sort s)) (hB : HasType P Γ B (.sort t)) : Transfer P Γ γ A C := by
  obtain ⟨x,hx,mx⟩ := h
  obtain ⟨y,hy,my⟩ := h'.rename (Embedding.cons hA .proof) hB
  refine ⟨y.instantiate x,?_,my.instantiate mx⟩
  simpa only [Expr.instantiate_raise,Embedding.cons] using hy.instantiate hx

end Transfer

end

section
universe u
variable {S : Type u} {P : Specification S}

namespace Proves
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {A B : Expr S} {s : S}

theorem rename (h : Proves P Γ γ A) (e : Embedding P Γ γ Δ δ) :
    Proves P Δ δ (A.rename e.names) := by
  obtain ⟨p,hp,mp⟩ := h
  exact ⟨_,e.typing hp,e.moded mp⟩

theorem of_var (hA : HasType P Γ A (.sort s)) :
    Proves P (A :: Γ) (modeCons .proof γ) (A.rename Nat.succ) :=
  ⟨_,.var hA,.var 0⟩

theorem apply_arrow (h : Proves P Γ γ (Expr.arrow .pp A B)) (ha : Proves P Γ γ A) :
    Proves P Γ γ B := by
  obtain ⟨p,hp,mp⟩ := h
  obtain ⟨a,ha,ma⟩ := ha
  exact ⟨_,hp.apply_arrow ha,.app mp ma⟩

theorem constLam {D : Expr S} {t : S} (h : Proves P Γ γ A)
    (hD : HasType P Γ D (.sort s)) (mD : WellModed γ D .data)
    (hpi : HasType P Γ (Expr.arrow .dp D A) (.sort t)) :
    Proves P Γ γ (Expr.arrow .dp D A) := by
  obtain ⟨p,hp,mp⟩ := h
  exact ⟨_,hp.constLam hD hpi,mD.constLam mp⟩
end Proves

namespace Transfer
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {A B D : Expr S} {s t : S}

theorem prove (h : Transfer P Γ γ A B) (hp : Proves P Γ γ A) : Proves P Γ γ B := by
  obtain ⟨t,ht,mt⟩ := h
  obtain ⟨p,hp,mp⟩ := hp
  exact ⟨_,by simpa only [Expr.instantiate_raise] using ht.instantiate hp,mt.instantiate mp⟩

theorem abstract (h : Transfer P Γ γ A B) (mA : WellModed γ A .data)
    (hpi : HasType P Γ (Expr.arrow .pp A B) (.sort s)) :
    Proves P Γ γ (Expr.arrow .pp A B) := by
  obtain ⟨p,hp,mp⟩ := h
  exact ⟨_,.abstraction hp hpi,.lam mA mp⟩

/-- An actual argument may be data or proof; its original application label is
retained, and the fresh proof input is inserted before the argument is used. -/
theorem apply_to {l : Label} {a : Expr S} (ha : HasType P Γ a A)
    (ma : WellModed γ a l.domain) (hl : l.result = .proof)
    (hpi : HasType P Γ (Expr.arrow l A B) (.sort s)) :
    Transfer P Γ γ (Expr.arrow l A B) B := by
  refine ⟨.app l (.var 0) (a.rename Nat.succ),?_,?_⟩
  · have hv := HasType.var hpi
    simp only [Expr.arrow_rename] at hv
    exact hv.apply_arrow (.weaken ha hpi)
  · have hv : WellModed (modeCons .proof γ) (.var 0 : Expr S) l.result :=
      hl.symm ▸ WellModed.var 0
    have hh : WellModed (modeCons .proof γ) (.app l (.var 0) (a.rename Nat.succ)) l.result :=
      .app hv (ma.raise .proof)
    simpa only [hl] using hh

 theorem apply_to_proof (ha : Proves P Γ γ A)
    (hpi : HasType P Γ (Expr.arrow .pp A B) (.sort s)) :
    Transfer P Γ γ (Expr.arrow .pp A B) B := by
  obtain ⟨a,ha,ma⟩ := ha
  exact apply_to ha ma rfl hpi
end Transfer
end

universe u
open Classical
variable {S : Type u} {P : Specification S}

namespace ProofParity
variable {Γ : List (Expr S)} {γ : Nat → Mode} {W : WitnessFamily P Γ γ}
    {C : Set (Set S)} {A B D : Expr S} {b : Bool} {s t r : S}

theorem refl : ProofParity W C A A false := by
  intro Δ δ e
  exact ⟨id,fun _ _ => id⟩

/-- Positive paths retain the literal data witness used by projection. -/
theorem positive (h : ProofParity W C A B b)
    (hB : HasType P Γ B (.sort s)) (hD : HasType P Γ D (.sort t))
    (mD : WellModed γ D .data) {d : Expr S}
    (hd : HasType P Γ d D) (md : WellModed γ d .data)
    (hpi : HasType P Γ (Expr.arrow .dp D B) (.sort r)) :
    ProofParity W C A (Expr.arrow .dp D B) b := by
  intro Δ δ e
  have hB' := e.typing hB
  have hD' := e.typing hD
  have hpi' : HasType P Δ (Expr.arrow .dp (D.rename e.names) (B.rename e.names)) (.sort r) := by
    simpa only [Expr.arrow_rename,Expr.rename] using e.typing hpi
  have hp := Transfer.apply_to (e.typing hd) (e.moded md) (l := .dp) rfl hpi'
  cases b with
  | false =>
    obtain ⟨hin,hout⟩ := h Δ δ e
    refine ⟨?_,?_⟩
    · intro ha
      simpa only [Expr.arrow_rename] using (hin ha).constLam hD' (e.moded mD) hpi'
    · intro J hJ ha
      simpa only [Expr.arrow_rename] using hp.trans (hout J hJ ha) hpi' hB'
  | true =>
    obtain ⟨hin,hout⟩ := h Δ δ e
    refine ⟨?_,?_⟩
    · intro J hJ ha
      simpa only [Expr.arrow_rename] using (hin J hJ ha).constLam hD' (e.moded mD) hpi'
    · intro J hJ ha
      simpa only [Expr.arrow_rename] using hp.trans (hout J hJ ha) hpi' hB'

/-- Each negative edge uses its fixed terminal; even/odd callbacks
are composed only with the predeclared terminal terms. -/
theorem negative (h : ProofParity W C A B b)
    (τ : ∀ J J', TerminalProfile P C J → TerminalProfile P C J' →
      Transfer P Γ γ (W.type J) (W.type J'))
    {J₀ : Set S} (hJ₀ : TerminalProfile P C J₀)
    (hB : HasType P Γ B (.sort s)) (mB : WellModed γ B .data)
    (hpi : HasType P Γ (Expr.arrow .pp B (W.type J₀)) (.sort r)) :
    ProofParity W C A (Expr.arrow .pp B (W.type J₀)) (!b) := by
  intro Δ δ e
  have hB' := e.typing hB
  obtain ⟨t₀,ht₀⟩ := hJ₀.feasible.1
  have hF₀ := e.typing (W.sorted J₀ hJ₀.feasible t₀ ht₀)
  have hpi' : HasType P Δ (Expr.arrow .pp (B.rename e.names) ((W.type J₀).rename e.names)) (.sort r) := by
    simpa only [Expr.arrow_rename,Expr.rename] using e.typing hpi
  have conv (J J' : Set S) (hJ : TerminalProfile P C J) (hJ' : TerminalProfile P C J') :
      Transfer P Δ δ ((W.type J).rename e.names) ((W.type J').rename e.names) := by
    obtain ⟨t,ht⟩ := hJ.feasible.1
    exact (τ J J' hJ hJ').rename e (W.sorted J hJ.feasible t ht)
  cases b with
  | false =>
    obtain ⟨hin,hout⟩ := h Δ δ e
    refine ⟨?_,?_⟩
    · intro J hJ ha
      obtain ⟨t,ht⟩ := hJ.feasible.1
      have hF := e.typing (W.sorted J hJ.feasible t ht)
      have hh := (hout J hJ ha).trans (conv J J₀ hJ hJ₀) hB' hF
      simpa only [Expr.arrow_rename] using hh.abstract (e.moded mB) hpi'
    · intro J hJ ha
      have hh := (Transfer.apply_to_proof (hin ha) hpi').trans (conv J₀ J hJ₀ hJ) hpi' hF₀
      simpa only [Expr.arrow_rename] using hh
  | true =>
    obtain ⟨hin,hout⟩ := h Δ δ e
    refine ⟨?_,?_⟩
    · intro ha
      simpa only [Expr.arrow_rename] using (hout J₀ hJ₀ ha).abstract (e.moded mB) hpi'
    · intro J hJ ha
      have hh := (Transfer.apply_to_proof (hin J hJ ha) hpi').trans (conv J₀ J hJ₀ hJ) hpi' hF₀
      simpa only [Expr.arrow_rename] using hh
end ProofParity

namespace Transfer
variable {Γ : List (Expr S)} {γ : Nat → Mode} {A B : Expr S} {s t : S}

/-- Project a dependent product at its newly opened raw argument, retaining the
argument's actual data/proof label. -/
theorem project_pi {l : Label} (hA : HasType P Γ A (.sort s))
    (hpi : HasType P Γ (.pi l A B) (.sort t)) (hl : l.result = .proof) :
    Transfer P (A :: Γ) (modeCons l.domain γ) ((Expr.pi l A B).rename Nat.succ) B := by
  let hpi' := HasType.weaken hpi hA
  have hv := HasType.var hpi'
  have hx := HasType.weaken (HasType.var hA) hpi'
  have hterm := HasType.application hv hx
  have heq : (((B.rename (Expr.liftRen Nat.succ)).rename (Expr.liftRen Nat.succ)).instantiate (.var 1)) =
      B.rename Nat.succ := by
    simp only [Expr.instantiate,Expr.subst_rename,Expr.rename_comp]
    rw [← Expr.subst_var (B.rename Nat.succ),Expr.subst_rename]
    congr 1
    funext n
    cases n <;> rfl
  have hm : WellModed (modeCons .proof (modeCons l.domain γ))
      (.app l (.var 0) (.var 1) : Expr S) l.result :=
    .app (hl.symm ▸ WellModed.var 0) (.var 1)
  exact ⟨_,by simpa only [Expr.rename,heq] using hterm,by simpa only [hl] using hm⟩
end Transfer

namespace StableExtraction
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {W : WitnessFamily P Γ γ}
    {C : Set (Set S)} {Q A B : Expr S} {s t : S}

theorem rename (h : StableExtraction W C Q) (e : Embedding P Γ γ Δ δ) :
    StableExtraction (W.rename e) C (Q.rename e.names) := by
  intro Θ θ f hk
  have hk' : Continuation (W.rename (e.comp f)) C (Q.rename (e.comp f).names) := by
    simpa only [Continuation,Embedding.comp,WitnessFamily.rename,Expr.rename_comp] using hk
  simpa only [Embedding.comp,Expr.rename_comp] using h Θ θ (e.comp f) hk'

theorem terminal {J : Set S} (hJ : TerminalProfile P C J) : StableExtraction W C (W.type J) := by
  intro Δ δ e hk
  obtain ⟨s,hs⟩ := hJ.feasible.1
  have hF := e.typing (W.sorted J hJ.feasible s hs)
  have ht : Transfer P Δ δ ((W.type J).rename e.names) ((W.type J).rename e.names) := .refl hF
  have hr := hk Δ δ (Embedding.refl e.valid δ) J hJ
  simpa only [WitnessFamily.rename,Embedding.refl,Expr.rename_id] using hr (by
    simpa only [WitnessFamily.rename,Embedding.refl,Expr.rename_id] using ht)

/-- Dependent telescope step. The continuation is threaded under the raw binder;
the raw projection supplies the callback at exactly that locally opened value. -/
theorem product {l : Label} (hA : HasType P Γ A (.sort s))
    (mA : WellModed γ A .data) (hpi : HasType P Γ (.pi l A B) (.sort t))
    (hl : l.result = .proof)
    (hB : StableExtraction (W.rename (Embedding.cons hA l.domain)) C B) :
    StableExtraction W C (.pi l A B) := by
  intro Δ δ e hk
  let hA' := e.typing hA
  let d : Embedding P Δ δ (A.rename e.names :: Δ) (modeCons l.domain δ) :=
    Embedding.cons hA' l.domain
  have hpi' : HasType P Δ (.pi l (A.rename e.names) (B.rename (Expr.liftRen e.names))) (.sort t) :=
    e.typing hpi
  have hp := Transfer.project_pi (γ := δ) hA' hpi' hl
  have hb : Proves P (A.rename e.names :: Δ) (modeCons l.domain δ) (B.rename (Expr.liftRen e.names)) := by
    apply hB _ _ (e.lift hA l.domain)
    intro Θ θ f J hJ hc
    have hfpi := HasType.weaken hpi' hA'
    have hp' := hp.rename f hfpi
    obtain ⟨a,bs,c,ha,hbody,hr,_⟩ := hpi'.generation_pi
    have hbody' : HasType P Θ ((B.rename (Expr.liftRen e.names)).rename f.names) (.sort bs) := by
      simpa only [Expr.rename] using f.typing hbody
    have hcb := hp'.trans hc (f.typing hfpi) hbody'
    change Transfer P Θ θ ((((Expr.pi l A B).rename e.names).rename Nat.succ).rename f.names)
      (((((W.rename (Embedding.cons hA l.domain)).rename (e.lift hA l.domain)).type J)).rename f.names) at hcb
    have hres := hk Θ θ (d.comp f) J hJ
    have hcb' : Transfer P Θ θ ((Expr.pi l A B).rename e.names |>.rename (d.comp f).names)
        (((W.rename e).type J).rename (d.comp f).names) := by
      simpa only [Embedding.comp,Embedding.lift,Embedding.cons,d,
        WitnessFamily.rename,Expr.rename_comp,Expr.liftRen,PureTypeSystem.Expr.liftRen,
        Function.comp_def] using hcb
    simpa only [Embedding.comp,Embedding.lift,Embedding.cons,d,
      WitnessFamily.rename,Expr.rename_comp,Expr.liftRen,PureTypeSystem.Expr.liftRen,
      Function.comp_def] using hres hcb' 
  obtain ⟨b,hb,mb⟩ := hb
  have ml : WellModed δ (.lam l (A.rename e.names) b) l.result :=
    .lam (e.moded mA) (by simpa only [hl] using mb)
  exact ⟨_,.abstraction hb hpi',by simpa only [hl] using ml⟩

/-- Constant arrows are the special telescope step used by every path edge. -/
theorem arrow {l : Label} (hA : HasType P Γ A (.sort s))
    (mA : WellModed γ A .data) (hpi : HasType P Γ (Expr.arrow l A B) (.sort t))
    (hl : l.result = .proof) (hB : StableExtraction W C B) :
    StableExtraction W C (Expr.arrow l A B) :=
  product hA mA hpi hl (hB.rename (Embedding.cons hA l.domain))

end StableExtraction

namespace ProofParity
variable {Γ : List (Expr S)} {γ : Nat → Mode} {W : WitnessFamily P Γ γ}
    {C : Set (Set S)} {A B : Expr S} {s t : S}

theorem into (h : ProofParity W C A B false) (hA : HasType P Γ A (.sort s)) :
    Transfer P Γ γ A B := by
  have hp := (h _ _ (Embedding.cons hA .proof)).1 (Proves.of_var hA)
  exact hp

/-- Stable even-path retraction, including dependent stable telescopes. -/
theorem down (h : ProofParity W C A B false) (hs : StableExtraction W C A)
    (hB : HasType P Γ B (.sort t)) : Transfer P Γ γ B A := by
  let d : Embedding P Γ γ (B :: Γ) (modeCons .proof γ) := Embedding.cons hB .proof
  apply hs _ _ d
  intro Δ δ e J hJ hc
  have hout := (h Δ δ (d.comp e)).2 J hJ
  have hc' : Transfer P Δ δ (A.rename (d.comp e).names) ((W.type J).rename (d.comp e).names) := by
    simpa only [Embedding.comp,WitnessFamily.rename,Expr.rename_comp] using hc
  have hp := (Proves.of_var (γ := γ) hB).rename e
  have hp' : Proves P Δ δ (B.rename (d.comp e).names) := by
    simpa only [Embedding.comp,d,Embedding.cons,Expr.rename_comp] using hp
  simpa only [Embedding.comp,WitnessFamily.rename,Expr.rename_comp] using (hout hc').prove hp'
end ProofParity

namespace ProofWrapper

theorem apply_rename (R : ProofWrapper S) (T : Expr S) (ρ : Nat → Nat) :
    (R.apply T).rename ρ = (R.rename ρ).apply (T.rename ρ) := by
  induction R <;> simp_all only [apply,rename,Expr.arrow_rename]

theorem apply_subst (R : ProofWrapper S) (T : Expr S) (σ : Nat → Expr S) :
    (R.apply T).subst σ = (R.subst σ).apply (T.subst σ) := by
  induction R <;> simp_all only [apply,subst,Expr.arrow_subst]

theorem rename_id (R : ProofWrapper S) : R.rename id = R := by
  induction R <;> simp_all only [rename,Expr.rename_id]

theorem rename_comp (R : ProofWrapper S) (ρ σ : Nat → Nat) :
    (R.rename σ).rename ρ = R.rename (ρ ∘ σ) := by
  induction R <;> simp_all only [rename,Expr.rename_comp]

theorem instantiate_raise (R : ProofWrapper S) (a : Expr S) :
    (R.rename Nat.succ).subst (Expr.single a) = R := by
  induction R <;> simp_all only [rename,subst,Expr.subst_lift_single]

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {W : WitnessFamily P Γ γ}
    {C : Set (Set S)} {I J K : Set S} {a b : Bool} {R : ProofWrapper S}

/-- The fixed code has the actual profile sorting, mode, and parity operations. -/
theorem sound (h : Formed W C I J b R)
    (τ : ∀ J J', TerminalProfile P C J → TerminalProfile P C J' →
      Transfer P Γ γ (W.type J) (W.type J'))
    {T : Expr S} (ht : SortedAt P Γ T I) (mt : WellModed γ T .data) :
    SortedAt P Γ (R.apply T) J ∧ WellModed γ (R.apply T) .data ∧
      ProofParity W C T (R.apply T) b := by
  induction h with
  | identity => exact ⟨ht,mt,ProofParity.refl⟩
  | inclusion h hsub ih => exact ⟨ih.1.mono hsub,ih.2⟩
  | @positive A J K b R h htr ih =>
    have hsorted : SortedAt P Γ (Expr.arrow .dp (W.type A) (R.apply T)) K :=
      (W.sorted A htr.domain).arrow ih.1 .dp (by rw [htr.output])
    obtain ⟨r,hr⟩ := htr.product.1
    obtain ⟨s,hs,t,ht,hst⟩ := htr.output ▸ hr
    exact ⟨hsorted,(W.type_mode A htr.domain).arrow ih.2.1,
      ih.2.2.positive (ih.1 t ht) (W.sorted A htr.domain s hs)
        (W.type_mode A htr.domain) (W.typed A htr.domain) (W.value_mode A htr.domain) (hsorted r hr)⟩
  | @negative J B K b R h htr hJ hK ih =>
    have hsorted : SortedAt P Γ (Expr.arrow .pp (R.apply T) (W.type B)) K :=
      ih.1.arrow (W.sorted B htr.codomain) .pp (by rw [htr.output])
    obtain ⟨r,hr⟩ := htr.product.1
    obtain ⟨s,hs,t,ht,hst⟩ := htr.output ▸ hr
    exact ⟨hsorted,ih.2.1.arrow (W.type_mode B htr.codomain),
      ih.2.2.negative τ ⟨J,K,htr,hJ,hK⟩ (ih.1 s hs) ih.2.1 (hsorted r hr)⟩

/-- Every code preserves stable extraction; a negative-containing code creates
it even for an initially arbitrary data type. -/
theorem stable (h : Formed W C I J b R)
    (τ : ∀ J J', TerminalProfile P C J → TerminalProfile P C J' →
      Transfer P Γ γ (W.type J) (W.type J'))
    {T : Expr S} (ht : SortedAt P Γ T I) (mt : WellModed γ T .data) :
    (StableExtraction W C T → StableExtraction W C (R.apply T)) ∧
      (R.containsNegative = true → StableExtraction W C (R.apply T)) := by
  induction h with
  | identity => exact ⟨id,by simp only [containsNegative,Bool.false_eq_true]; tauto⟩
  | inclusion h hsub ih => exact ih
  | @positive A J K b R h htr ih =>
    obtain ⟨htR,mtR,hpar⟩ := h.sound τ ht mt
    have hsorted : SortedAt P Γ (Expr.arrow .dp (W.type A) (R.apply T)) K :=
      (W.sorted A htr.domain).arrow htR .dp (by rw [htr.output])
    obtain ⟨r,hr⟩ := htr.product.1
    obtain ⟨s,hs,t,ht',hst⟩ := htr.output ▸ hr
    have step : StableExtraction W C (R.apply T) →
        StableExtraction W C ((ProofWrapper.positive R (W.type A)).apply T) :=
      StableExtraction.arrow (W.sorted A htr.domain s hs) (W.type_mode A htr.domain) (hsorted r hr) rfl
    exact ⟨fun hp => step (ih.1 hp),fun hn => step (ih.2 hn)⟩
  | @negative J B K b R h htr hJ hK ih =>
    obtain ⟨htR,mtR,hpar⟩ := h.sound τ ht mt
    have hsorted : SortedAt P Γ (Expr.arrow .pp (R.apply T) (W.type B)) K :=
      htR.arrow (W.sorted B htr.codomain) .pp (by rw [htr.output])
    obtain ⟨r,hr⟩ := htr.product.1
    obtain ⟨s,hs,t,ht',hst⟩ := htr.output ▸ hr
    have hx : StableExtraction W C ((ProofWrapper.negative R (W.type B)).apply T) :=
      StableExtraction.arrow (htR s hs) mtR (hsorted r hr) rfl
        (StableExtraction.terminal ⟨J,K,htr,hJ,hK⟩)
    exact ⟨fun _ => hx,fun _ => hx⟩

end Formed
end ProofWrapper
end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Logic
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate _root_.OAI.PureTypeSystem.instCountableExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled

section
universe u
open Classical
variable {S : Type u} {P : Specification S}

namespace LogicSetup

section
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}

theorem terminal_base (L : LogicSetup P Γ γ C) : TerminalProfile P C L.base :=
  ⟨L.domain,L.product,L.triple,L.domain_mem,L.product_mem⟩

theorem Formula.rename {L : LogicSetup P Γ γ C} {A : Expr S} (h : L.Formula A)
    (e : Embedding P Γ γ Δ δ) : (L.rename e).Formula (A.rename e.names) :=
  ⟨fun _ hs => e.typing (h.1 _ hs),e.moded h.2.1,h.2.2.rename e⟩

theorem bottom_formula (L : LogicSetup P Γ γ C) : L.Formula L.bottom :=
  ⟨L.witnesses.sorted L.base L.triple.codomain,L.witnesses.type_mode L.base L.triple.codomain,
    StableExtraction.terminal L.terminal_base⟩

variable (L : LogicSetup P Γ γ C) {A B : Expr S}

theorem imp_rename (e : Embedding P Γ γ Δ δ) (A B : Expr S) :
    (L.imp A B).rename e.names = (L.rename e).imp (A.rename e.names) (B.rename e.names) := by
  simp only [imp,ProofWrapper.apply_rename,Expr.arrow_rename,rename]

theorem bottom_rename (e : Embedding P Γ γ Δ δ) :
    L.bottom.rename e.names = (L.rename e).bottom := rfl

theorem Formula.sorted {A : Expr S} (h : L.Formula A) :
    ∃ s, HasType P Γ A (.sort s) := by
  obtain ⟨s,hs⟩ := L.triple.codomain.1
  exact ⟨s,h.1 s hs⟩

theorem raw_imp (hA : L.Formula A) (hB : L.Formula B) :
    SortedAt P Γ (Expr.arrow .pp (L.inCode.apply A) B) L.product ∧
    WellModed γ (Expr.arrow .pp (L.inCode.apply A) B) .data ∧
    StableExtraction L.witnesses C (Expr.arrow .pp (L.inCode.apply A) B) := by
  obtain ⟨ha,ma,pa⟩ := L.inFormed.sound L.converters hA.1 hA.2.1
  have hs : SortedAt P Γ (Expr.arrow .pp (L.inCode.apply A) B) L.product :=
    ha.arrow hB.1 .pp (by rw [L.triple.output])
  obtain ⟨r,hr⟩ := L.triple.product.1
  obtain ⟨s,hss,t,htt,hst⟩ := L.triple.output ▸ hr
  exact ⟨hs,ma.arrow hB.2.1,StableExtraction.arrow (ha s hss) ma (hs r hr) rfl hB.2.2⟩

theorem imp_formula (hA : L.Formula A) (hB : L.Formula B) : L.Formula (L.imp A B) := by
  obtain ⟨hs,hm,hx⟩ := L.raw_imp hA hB
  obtain ⟨hs',hm',hp⟩ := L.outFormed.sound L.converters hs hm
  exact ⟨hs',hm',(L.outFormed.stable L.converters hs hm).1 hx⟩

theorem imp_intro (hA : L.Formula A) (hB : L.Formula B)
    (ht : Transfer P Γ γ A B) : Proves P Γ γ (L.imp A B) := by
  obtain ⟨ha,ma,pa⟩ := L.inFormed.sound L.converters hA.1 hA.2.1
  obtain ⟨hs,hm,hx⟩ := L.raw_imp hA hB
  obtain ⟨hs',hm',po⟩ := L.outFormed.sound L.converters hs hm
  obtain ⟨r,hr⟩ := L.triple.product.1
  obtain ⟨s,hss,t,htt,hst⟩ := L.triple.output ▸ hr
  have hd := pa.down hA.2.2 (ha s hss)
  have hc := hd.trans ht (ha s hss) (hA.1 t htt)
  exact (po.into (hs r hr)).prove (hc.abstract ma (hs r hr))

theorem imp_elim (hA : L.Formula A) (hB : L.Formula B)
    (hf : Proves P Γ γ (L.imp A B)) (hp : Proves P Γ γ A) : Proves P Γ γ B := by
  obtain ⟨ha,ma,pa⟩ := L.inFormed.sound L.converters hA.1 hA.2.1
  obtain ⟨hs,hm,hx⟩ := L.raw_imp hA hB
  obtain ⟨hs',hm',po⟩ := L.outFormed.sound L.converters hs hm
  obtain ⟨r,hr⟩ := L.triple.product.1
  obtain ⟨s,hss,t,htt,hst⟩ := L.triple.output ▸ hr
  obtain ⟨q,hq⟩ := L.triple.codomain.1
  exact ((po.down hx (hs' q hq)).prove hf).apply_arrow ((pa.into (hA.1 t htt)).prove hp)

/-- Logical abstraction is uniform in every future typing/mode embedding. This
is stronger than a meta-level map on the inhabitants in one context. -/
theorem imp_intro_future (hA : L.Formula A) (hB : L.Formula B)
    (h : ∀ (Δ : List (Expr S)) (δ : Nat → Mode) (e : Embedding P Γ γ Δ δ),
      Proves P Δ δ (A.rename e.names) → Proves P Δ δ (B.rename e.names)) :
    Proves P Γ γ (L.imp A B) := by
  obtain ⟨s,hs⟩ := hA.sorted L
  exact L.imp_intro hA hB (h _ _ (Embedding.cons hs .proof) (Proves.of_var hs))

 theorem imp_future_iff (hA : L.Formula A) (hB : L.Formula B) :
    Proves P Γ γ (L.imp A B) ↔
    ∀ (Δ : List (Expr S)) (δ : Nat → Mode) (e : Embedding P Γ γ Δ δ),
      Proves P Δ δ (A.rename e.names) → Proves P Δ δ (B.rename e.names) := by
  constructor
  · intro hp Δ δ e ha
    exact (L.rename e).imp_elim (hA.rename e) (hB.rename e)
      (by simpa only [L.imp_rename] using hp.rename e) ha
  · exact L.imp_intro_future hA hB

/-- Double negation elimination uses callbacks at each terminal, and therefore
constructs labelled terms for every stable formula, including dependent ones. -/
theorem dne (hA : L.Formula A)
    (hw : Proves P Γ γ (L.imp (L.imp A L.bottom) L.bottom)) : Proves P Γ γ A := by
  have hv := (hA.sorted L).choose_spec.valid
  have hb := L.bottom_formula
  have hn := L.imp_formula hA hb
  have hs := hA.2.2 Γ γ (Embedding.refl hv γ)
  simp only [Embedding.refl,Expr.rename_id] at hs
  apply hs
  intro Δ δ e J hJ ht
  obtain ⟨s,hss⟩ := L.triple.codomain.1
  obtain ⟨t,htt⟩ := hJ.feasible.1
  have hA' := hA.rename e
  have hb' := hb.rename e
  have ht' : Transfer P Δ δ (A.rename e.names) ((L.witnesses.type J).rename e.names) := by
    simpa only [WitnessFamily.rename,Embedding.refl,Expr.rename_id] using ht
  have hjb := (L.converters J L.base hJ L.terminal_base).rename e
    (L.witnesses.sorted J hJ.feasible t htt)
  have hbj := (L.converters L.base J L.terminal_base hJ).rename e
    (L.witnesses.sorted L.base L.triple.codomain s hss)
  obtain ⟨a,ha⟩ := hA'.sorted (L.rename e)
  have negp := (L.rename e).imp_intro hA' hb' (ht'.trans hjb ha
    (e.typing (L.witnesses.sorted J hJ.feasible t htt)))
  have hw' : Proves P Δ δ ((L.rename e).imp ((L.rename e).imp (A.rename e.names) (L.rename e).bottom) (L.rename e).bottom) := by
    simpa only [L.imp_rename,L.bottom_rename] using hw.rename e
  have hbot := (L.rename e).imp_elim ((L.rename e).imp_formula hA' hb') hb' hw' negp
  simpa only [WitnessFamily.rename,Embedding.refl,Expr.rename_id] using hbj.prove hbot

end

end LogicSetup
end

section
universe u
variable {S : Type u} {P : Specification S}
namespace Transfer
variable {Γ : List (Expr S)} {γ : Nat → Mode} {A B : Expr S} {s t : S}
theorem of_conversion (hA : HasType P Γ A (.sort s)) (hB : HasType P Γ B (.sort t))
    (hc : Converts A B) : Transfer P Γ γ A B :=
  ⟨_,.conversion (.var hA) (.weaken hB hA) (hc.rename Nat.succ),.var 0⟩
end Transfer

namespace Equivalent
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {A B D : Expr S} {s t r : S}
theorem refl (hA : HasType P Γ A (.sort s)) : Equivalent P Γ γ A A :=
  ⟨.refl hA,.refl hA⟩
theorem trans (h : Equivalent P Γ γ A B) (k : Equivalent P Γ γ B D)
    (hA : HasType P Γ A (.sort s)) (hB : HasType P Γ B (.sort t)) (hD : HasType P Γ D (.sort r)) :
    Equivalent P Γ γ A D := ⟨h.1.trans k.1 hA hB,k.2.trans h.2 hD hB⟩
theorem of_conversion (hA : HasType P Γ A (.sort s)) (hB : HasType P Γ B (.sort t))
    (hc : Converts A B) : Equivalent P Γ γ A B :=
  ⟨.of_conversion hA hB hc,.of_conversion hB hA (.symm _ _ hc)⟩
end Equivalent

namespace ProofWrapper
variable {T T' : Expr S}
theorem apply_converts (R : ProofWrapper S) (h : Converts T T') : Converts (R.apply T) (R.apply T') := by
  induction R with
  | identity => exact h
  | positive R D ih => exact .pi (.refl _) (ih.rename Nat.succ)
  | negative R F ih => exact .pi ih (.refl _)

end ProofWrapper

namespace PositiveDataWrapper

theorem apply_rename (R : PositiveDataWrapper S) (T : Expr S) (ρ : Nat → Nat) :
    (R.apply T).rename ρ = (R.rename ρ).apply (T.rename ρ) := by
  induction R <;> simp_all only [apply,rename,Expr.arrow_rename]
theorem inject_rename (R : PositiveDataWrapper S) (t : Expr S) (ρ : Nat → Nat) :
    (R.inject t).rename ρ = (R.rename ρ).inject (t.rename ρ) := by
  induction R <;> simp_all only [inject,rename,Expr.constLam_rename]
theorem project_rename (R : PositiveDataWrapper S) (w : Expr S) (ρ : Nat → Nat) :
    (R.project w).rename ρ = (R.rename ρ).project (w.rename ρ) := by
  induction R generalizing w <;> simp_all only [project,rename,Expr.rename]
theorem apply_subst (R : PositiveDataWrapper S) (T : Expr S) (σ : Nat → Expr S) :
    (R.apply T).subst σ = (R.subst σ).apply (T.subst σ) := by
  induction R <;> simp_all only [apply,subst,Expr.arrow_subst]
theorem inject_subst (R : PositiveDataWrapper S) (t : Expr S) (σ : Nat → Expr S) :
    (R.inject t).subst σ = (R.subst σ).inject (t.subst σ) := by
  induction R <;> simp_all only [inject,subst,Expr.constLam_subst]
theorem project_subst (R : PositiveDataWrapper S) (w : Expr S) (σ : Nat → Expr S) :
    (R.project w).subst σ = (R.subst σ).project (w.subst σ) := by
  induction R generalizing w <;> simp_all only [project,subst,Expr.subst]
theorem rename_comp (R : PositiveDataWrapper S) (ρ τ : Nat → Nat) :
    (R.rename τ).rename ρ = R.rename (ρ ∘ τ) := by
  induction R <;> simp_all only [rename,Expr.rename_comp]
theorem rename_id (R : PositiveDataWrapper S) : R.rename id = R := by
  induction R <;> simp_all only [rename,Expr.rename_id]
theorem instantiate_raise (R : PositiveDataWrapper S) (a : Expr S) :
    (R.rename Nat.succ).subst (Expr.single a) = R := by
  induction R <;> simp_all only [rename,subst,Expr.subst_lift_single]

theorem project_reduces (R : PositiveDataWrapper S) {w w' : Expr S}
    (h : Reduces w w') : Reduces (R.project w) (R.project w') := by
  induction R generalizing w w' with
  | identity => exact h
  | step R D e ih => exact ih (h.app .refl)

theorem cancel (R : PositiveDataWrapper S) (t : Expr S) : Reduces (R.project (R.inject t)) t := by
  induction R with
  | identity => exact .refl
  | step R D e ih =>
    exact (R.project_reduces (.single (positive_cancel .dd D e (R.inject t)))).trans ih

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {W : WitnessFamily P Γ γ}
    {I J K : Set S} {R : PositiveDataWrapper S}
theorem rename {Δ : List (Expr S)} {δ : Nat → Mode}
    (h : Formed W I J R) (e : Embedding P Γ γ Δ δ) : Formed (W.rename e) I J (R.rename e.names) := by
  induction h with
  | identity => exact .identity
  | inclusion h hh ih => exact ih.inclusion hh
  | positive h ht ih => exact ih.positive ht

theorem sorted (h : Formed W I J R) {T : Expr S} (ht : SortedAt P Γ T I) :
    SortedAt P Γ (R.apply T) J := by
  induction h with
  | identity => exact ht
  | inclusion h hh ih => exact ih.mono hh
  | positive h ht ih => exact (W.sorted _ ht.domain).arrow ih .dd (by rw [ht.output])

theorem modes (h : Formed W I J R) :
    (∀ T, WellModed γ T .data → WellModed γ (R.apply T) .data) ∧
    (∀ t, WellModed γ t .data → WellModed γ (R.inject t) .data) ∧
    (∀ w, WellModed γ w .data → WellModed γ (R.project w) .data) := by
  induction h with
  | identity => exact ⟨fun _ h => h,fun _ h => h,fun _ h => h⟩
  | inclusion h hh ih => exact ih
  | @positive A J K R h ht ih =>
    exact ⟨fun T hT => (W.type_mode A ht.domain).arrow (ih.1 T hT),
      fun t ht' => (W.type_mode A ht.domain).constLam (ih.2.1 t ht'),
      fun w hw => ih.2.2 _ (.app hw (W.value_mode A ht.domain))⟩

theorem typed (h : Formed W I J R) {T : Expr S} (ht : SortedAt P Γ T I) :
    (∀ t, HasType P Γ t T → HasType P Γ (R.inject t) (R.apply T)) ∧
    (∀ w, HasType P Γ w (R.apply T) → HasType P Γ (R.project w) T) := by
  induction h with
  | identity => exact ⟨fun _ h => h,fun _ h => h⟩
  | inclusion h hh ih => exact ih
  | @positive A J K R h htr ih =>
    have hR := h.sorted ht
    have hpi : SortedAt P Γ (Expr.arrow .dd (W.type A) (R.apply T)) K :=
      (W.sorted A htr.domain).arrow hR .dd (by rw [htr.output])
    obtain ⟨r,hr⟩ := htr.product.1
    obtain ⟨s,hs,t,htt,hst⟩ := htr.output ▸ hr
    exact ⟨fun a ha => (ih.1 a ha).constLam (W.sorted A htr.domain s hs) (hpi r hr),
      fun w hw => ih.2 _ (hw.apply_arrow (W.typed A htr.domain))⟩
end Formed
end PositiveDataWrapper

namespace DataTail

theorem carrier_rename (U : DataTail S) (ρ : Nat → Nat) :
    U.carrier.rename ρ = (U.rename ρ).carrier := U.positive.apply_rename _ _
theorem send_rename (U : DataTail S) (Q : Expr S) (ρ : Nat → Nat) :
    (U.send Q).rename ρ = (U.rename ρ).send (Q.rename ρ) := by
  simp only [send,rename,PositiveDataWrapper.inject_rename,ProofWrapper.apply_rename]
theorem read_rename (U : DataTail S) (w : Expr S) (ρ : Nat → Nat) :
    (U.read w).rename ρ = (U.rename ρ).read (w.rename ρ) := by
  simp only [read,rename,PositiveDataWrapper.project_rename,ProofWrapper.apply_rename]
theorem carrier_subst (U : DataTail S) (σ : Nat → Expr S) :
    U.carrier.subst σ = (U.subst σ).carrier := U.positive.apply_subst _ _
theorem send_subst (U : DataTail S) (Q : Expr S) (σ : Nat → Expr S) :
    (U.send Q).subst σ = (U.subst σ).send (Q.subst σ) := by
  simp only [send,subst,PositiveDataWrapper.inject_subst,ProofWrapper.apply_subst]
theorem read_subst (U : DataTail S) (w : Expr S) (σ : Nat → Expr S) :
    (U.read w).subst σ = (U.subst σ).read (w.subst σ) := by
  simp only [read,subst,PositiveDataWrapper.project_subst,ProofWrapper.apply_subst]
theorem rename_comp (U : DataTail S) (ρ τ : Nat → Nat) :
    (U.rename τ).rename ρ = U.rename (ρ ∘ τ) := by
  cases U; simp only [rename,PositiveDataWrapper.rename_comp,ProofWrapper.rename_comp]
theorem rename_id (U : DataTail S) : U.rename id = U := by
  cases U; simp only [rename,PositiveDataWrapper.rename_id,ProofWrapper.rename_id]
theorem instantiate_raise (U : DataTail S) (a : Expr S) :
    (U.rename Nat.succ).subst (Expr.single a) = U := by
  cases U; simp only [rename,subst,PositiveDataWrapper.instantiate_raise,ProofWrapper.instantiate_raise]

namespace Formed
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {J : Set S} {U : DataTail S}

theorem rename (h : Formed L J U) (e : Embedding P Γ γ Δ δ) :
    Formed (L.rename e) J (U.rename e.names) := by
  refine ⟨h.mem,h.nonempty,h.positive.rename e,h.encode.rename e,h.decode.rename e,?_⟩
  have hn (R : ProofWrapper S) : (R.rename e.names).containsNegative = R.containsNegative := by
    induction R <;> simp_all only [ProofWrapper.rename,ProofWrapper.containsNegative]
  exact (hn U.decode).trans h.negative

theorem sort_sorted (_h : Formed L J U) : SortedAt P Γ (.sort U.sort) (AxProfile P U.sort) := by
  obtain ⟨s,hs⟩ := L.triple.codomain.1
  intro t ht
  exact HasType.sort_of_valid (L.bottom_formula.1 s hs).valid ht

theorem carrier_sorted (h : Formed L J U) : SortedAt P Γ U.carrier J := h.positive.sorted h.sort_sorted

theorem carrier_mode (h : Formed L J U) : WellModed γ U.carrier .data :=
  h.positive.modes.1 _ (.sort _)

theorem send_typed (h : Formed L J U) {Q : Expr S} (hQ : L.Formula Q) :
    HasType P Γ (U.send Q) U.carrier ∧ WellModed γ (U.send Q) .data := by
  obtain ⟨hE,mE,_⟩ := h.encode.sound L.converters hQ.1 hQ.2.1
  exact ⟨h.positive.typed h.sort_sorted |>.1 _ (hE U.sort rfl),h.positive.modes.2.1 _ mE⟩

theorem read_formula (h : Formed L J U) {w : Expr S}
    (hw : HasType P Γ w U.carrier) (mw : WellModed γ w .data) : L.Formula (U.read w) := by
  have ht := h.positive.typed h.sort_sorted |>.2 _ hw
  have mt := h.positive.modes.2.2 _ mw
  have hs : SortedAt P Γ (U.positive.project w) {U.sort} := by intro s hs; cases hs; exact ht
  obtain ⟨hd,md,_⟩ := h.decode.sound L.converters hs mt
  exact ⟨hd,md,(h.decode.stable L.converters hs mt).2 h.negative⟩

theorem read_send (h : Formed L J U) {Q : Expr S} (hQ : L.Formula Q) :
    Equivalent P Γ γ (U.read (U.send Q)) Q := by
  obtain ⟨s,hs⟩ := L.triple.codomain.1
  obtain ⟨hE,mE,pE⟩ := h.encode.sound L.converters hQ.1 hQ.2.1
  have stE := (h.encode.stable L.converters hQ.1 hQ.2.1).1 hQ.2.2
  obtain ⟨hD,mD,pD⟩ := h.decode.sound L.converters hE mE
  have he : Equivalent P Γ γ (U.encode.apply Q) Q :=
    ⟨pE.down hQ.2.2 (hE U.sort rfl),pE.into (hQ.1 s hs)⟩
  have hd : Equivalent P Γ γ (U.decode.apply (U.encode.apply Q)) (U.encode.apply Q) :=
    ⟨pD.down stE (hD s hs),pD.into (hE U.sort rfl)⟩
  have hm := h.send_typed hQ
  have hf := h.read_formula hm.1 hm.2
  have hc : Converts (U.read (U.send Q)) (U.decode.apply (U.encode.apply Q)) :=
    U.decode.apply_converts (U.positive.cancel (U.encode.apply Q)).converts
  exact (Equivalent.of_conversion (hf.1 s hs) (hD s hs) hc).trans
    (hd.trans he (hD s hs) (hE U.sort rfl) (hQ.1 s hs)) (hf.1 s hs) (hD s hs) (hQ.1 s hs)

end Formed
end DataTail
end

section
universe u
variable {S : Type u}

namespace DataWrapper

theorem apply_rename {b} (R : DataWrapper S b) (T : Expr S) (ρ : Nat → Nat) :
    (R.apply T).rename ρ = (R.rename ρ).apply (T.rename ρ) := by
  induction R <;> simp_all only [apply,rename,Expr.arrow_rename,DataTail.carrier_rename]
theorem apply_subst {b} (R : DataWrapper S b) (T : Expr S) (σ : Nat → Expr S) :
    (R.apply T).subst σ = (R.subst σ).apply (T.subst σ) := by
  induction R <;> simp_all only [apply,subst,Expr.arrow_subst,DataTail.carrier_subst]
theorem rename_comp {b} (R : DataWrapper S b) (ρ τ : Nat → Nat) :
    (R.rename τ).rename ρ = R.rename (ρ ∘ τ) := by
  induction R <;> simp_all only [rename,Expr.rename_comp,DataTail.rename_comp]
theorem rename_id {b} (R : DataWrapper S b) : R.rename id = R := by
  induction R <;> simp_all only [rename,Expr.rename_id,DataTail.rename_id]
theorem instantiate_raise {b} (R : DataWrapper S b) (a : Expr S) :
    (R.rename Nat.succ).subst (Expr.single a) = R := by
  induction R <;> simp_all only [rename,subst,Expr.subst_lift_single,DataTail.instantiate_raise]

theorem argRen_comp (b : Bool) (ρ τ : Nat → Nat) :
    argRen b ρ ∘ argRen b τ = argRen b (ρ ∘ τ) := by
  cases b <;> funext n <;> cases n <;> rfl

theorem rename_build_observe {b} (R : DataWrapper S b) :
    (∀ T a ρ, (R.build T a).rename ρ = (R.rename ρ).build (T.rename ρ) (a.rename (argRen b ρ))) ∧
    (∀ T w a ρ, (R.observe T w a).rename ρ =
      (R.rename ρ).observe (T.rename ρ) (w.rename ρ) (a.rename (argRen (!b) ρ))) := by
  generalize he : R.depth = n
  induction n using Nat.strong_induction_on generalizing b R with
  | h n rec =>
   cases R with
   | identity =>
     constructor
     · intro T a ρ; simp only [build,rename,argRen,Bool.false_eq_true,ite_false, if_false]
     · intro T w a ρ
       simpa only [observe,rename,argRen,Bool.not_false,ite_true, if_true] using (Expr.instantiate_rename a w ρ).symm
   | positive R D e =>
     have ih := rec R.depth (by simp only [← he,depth]; omega) R rfl
     exact ⟨fun T a ρ => by simp only [build,rename,Expr.constLam_rename,ih.1],
       fun T w a ρ => by simpa only [observe,rename,Expr.rename] using ih.2 T (.app .dd w e) a ρ⟩
   | @negative b R U =>
     have ih := rec R.depth (by simp only [← he,depth]; omega) R rfl
     constructor
     · intro T a ρ
       simp only [build,Expr.rename,DataTail.send_rename,rename]
       rw [show (((R.rename Nat.succ).observe (T.rename Nat.succ) (.var 0) (a.rename (argRen (!b) Nat.succ))).rename (Expr.liftRen ρ)) =
         ((R.rename Nat.succ).rename (Expr.liftRen ρ)).observe ((T.rename Nat.succ).rename (Expr.liftRen ρ))
           ((Expr.var 0).rename (Expr.liftRen ρ)) ((a.rename (argRen (!b) Nat.succ)).rename (argRen (!b) (Expr.liftRen ρ))) from
         (rec R.depth (by simp only [← he,depth]; omega) (R.rename Nat.succ) (R.depth_rename Nat.succ)).2 _ _ _ _]
       simp only [apply_rename,rename_comp,DataTail.rename_comp,Expr.rename_comp,argRen_comp]
       have e : Expr.liftRen ρ ∘ Nat.succ = Nat.succ ∘ ρ := rfl
       rw [e]
       rfl
     · intro T w a ρ
       simp only [observe,rename,DataTail.read_rename,Expr.rename,ih.1,Bool.not_not]
end DataWrapper
end

universe u
variable {S : Type u} {P : Specification S}

namespace WitnessFamily
variable {Γ Δ Θ : List (Expr S)} {γ δ θ : Nat → Mode}
theorem rename_comp (W : WitnessFamily P Γ γ) (e : Embedding P Γ γ Δ δ)
    (f : Embedding P Δ δ Θ θ) : (W.rename e).rename f = W.rename (e.comp f) := by
  cases W
  simp only [rename,Embedding.comp,Expr.rename_comp]
theorem rename_refl (W : WitnessFamily P Γ γ) (hv : ValidContext P Γ) :
    W.rename (Embedding.refl hv γ) = W := by
  cases W
  simp only [rename,Embedding.refl,Expr.rename_id]
end WitnessFamily

namespace LogicSetup
variable {Γ Δ Θ : List (Expr S)} {γ δ θ : Nat → Mode} {C : Set (Set S)}
theorem Formula.rename_comp_iff (L : LogicSetup P Γ γ C) (e : Embedding P Γ γ Δ δ)
    (f : Embedding P Δ δ Θ θ) (Q : Expr S) :
    ((L.rename e).rename f).Formula Q ↔ (L.rename (e.comp f)).Formula Q := by
  change (SortedAt P Θ Q L.base ∧ WellModed θ Q .data ∧ StableExtraction ((L.witnesses.rename e).rename f) C Q) ↔
    (SortedAt P Θ Q L.base ∧ WellModed θ Q .data ∧ StableExtraction (L.witnesses.rename (e.comp f)) C Q)
  rw [WitnessFamily.rename_comp]

theorem Formula.rename_refl_iff (L : LogicSetup P Γ γ C) (hv : ValidContext P Γ) (Q : Expr S) :
    (L.rename (Embedding.refl hv γ)).Formula Q ↔ L.Formula Q := by
  change (SortedAt P Γ Q L.base ∧ WellModed γ Q .data ∧ StableExtraction (L.witnesses.rename (Embedding.refl hv γ)) C Q) ↔
    (SortedAt P Γ Q L.base ∧ WellModed γ Q .data ∧ StableExtraction L.witnesses C Q)
  rw [WitnessFamily.rename_refl]

namespace Family
variable {L : LogicSetup P Γ γ C} {T Q : Expr S}
theorem rename (h : L.Family T Q) (e : Embedding P Γ γ Δ δ) :
    (L.rename e).Family (T.rename e.names) (Q.rename (Expr.liftRen e.names)) := by
  intro Θ θ f a ha ma
  have hh := h Θ θ (e.comp f) a (by simpa only [Embedding.comp,Expr.rename_comp] using ha) ma
  apply (Formula.rename_comp_iff L e f _).2
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Expr.rename_comp,Embedding.comp]
  have he : Expr.liftRen f.names ∘ Expr.liftRen e.names = Expr.liftRen (f.names ∘ e.names) := by
    funext n; cases n <;> rfl
  rw [he]

theorem instantiate (h : L.Family T Q) {a : Expr S}
    (ha : HasType P Γ a T) (ma : WellModed γ a .data) : L.Formula (Q.instantiate a) := by
  have hh := h Γ γ (Embedding.refl ha.valid γ) a (by simpa only [Embedding.refl,Expr.rename_id] using ha) ma
  have he : Expr.liftRen id = id := by funext n; cases n <;> rfl
  apply (Formula.rename_refl_iff L ha.valid _).1
  simpa only [Embedding.refl,he,Expr.rename_id] using hh

end Family

theorem Family.rename_comp_iff (L : LogicSetup P Γ γ C) (e : Embedding P Γ γ Δ δ)
    (f : Embedding P Δ δ Θ θ) (T Q : Expr S) :
    ((L.rename e).rename f).Family T Q ↔ (L.rename (e.comp f)).Family T Q := by
  constructor <;> intro h Ω ω g a ha ma
  · have hh := h Ω ω g a ha ma
    simpa only [Formula.rename_comp_iff,Embedding.comp,Function.comp_assoc] using hh
  · have hh := h Ω ω g a ha ma
    simpa only [Formula.rename_comp_iff,Embedding.comp,Function.comp_assoc] using hh

namespace DataArg
variable {L : LogicSetup P Γ γ C} {b : Bool} {T a : Expr S}
theorem rename (h : L.DataArg b T a) (e : Embedding P Γ γ Δ δ) :
    (L.rename e).DataArg b (T.rename e.names) (a.rename (DataWrapper.argRen b e.names)) := by
  cases b
  · exact ⟨e.typing h.1,e.moded h.2⟩
  · exact h.rename e

theorem rename_comp_iff (L : LogicSetup P Γ γ C) (e : Embedding P Γ γ Δ δ)
    (f : Embedding P Δ δ Θ θ) (b : Bool) (T a : Expr S) :
    ((L.rename e).rename f).DataArg b T a ↔ (L.rename (e.comp f)).DataArg b T a := by
  cases b
  · rfl
  · exact Family.rename_comp_iff L e f T a
end DataArg
end LogicSetup

namespace DataWrapper
namespace Formed

section
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J K : Set S} {b : Bool} {R : DataWrapper S b}

theorem rename (h : Formed L I J R) (e : Embedding P Γ γ Δ δ) :
    Formed (L.rename e) I J (R.rename e.names) := by
  induction h with
  | identity => exact .identity
  | inclusion h hh ih => exact ih.inclusion hh
  | positive h ht ih => exact ih.positive ht
  | negative h ht hU ih => exact ih.negative ht (hU.rename e)

theorem sorted (h : Formed L I J R) {T : Expr S} (ht : SortedAt P Γ T I) :
    SortedAt P Γ (R.apply T) J := by
  induction h with
  | identity => exact ht
  | inclusion h hh ih => exact ih.mono hh
  | positive h ht ih => exact (L.witnesses.sorted _ ht.domain).arrow ih .dd (by rw [ht.output])
  | negative h ht hU ih => exact ih.arrow hU.carrier_sorted .dd (by rw [ht.output])

theorem mode (h : Formed L I J R) {T : Expr S} (mt : WellModed γ T .data) :
    WellModed γ (R.apply T) .data := by
  induction h with
  | identity => exact mt
  | inclusion h hh ih => exact ih
  | positive h ht ih => exact (L.witnesses.type_mode _ ht.domain).arrow ih
  | negative h ht hU ih => exact ih.arrow hU.carrier_mode

end

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J : Set S} {b : Bool} {R : DataWrapper S b}

/-- Uniform typing includes all future raw input types, so negative-edge
callbacks are checked under their fresh data variable without a closure axiom. -/
theorem sound_rename (h : Formed L I J R) :
    ∀ (Δ : List (Expr S)) (δ : Nat → Mode) (e : Embedding P Γ γ Δ δ)
      (T : Expr S), SortedAt P Δ T I → WellModed δ T .data →
    (∀ a, (L.rename e).DataArg b T a →
      HasType P Δ ((R.rename e.names).build T a) ((R.rename e.names).apply T) ∧
      WellModed δ ((R.rename e.names).build T a) .data) ∧
    (∀ w a, HasType P Δ w ((R.rename e.names).apply T) → WellModed δ w .data →
      (L.rename e).DataArg (!b) T a → (L.rename e).Formula ((R.rename e.names).observe T w a)) := by
  induction h with
  | identity =>
    intro Δ δ e T ht mt
    constructor
    · intro a ha; simpa only [DataWrapper.rename,DataWrapper.build,DataWrapper.apply,LogicSetup.DataArg, Bool.false_eq_true,ite_false, if_false] using ha
    · intro w a hw mw ha
      simpa only [DataWrapper.rename,DataWrapper.observe] using ha.instantiate hw mw
  | inclusion h hh ih => exact ih
  | @positive A J K b R h ht ih =>
    intro Δ δ e T hT mT
    obtain ⟨hb,ho⟩ := ih Δ δ e T hT mT
    have hR := (h.rename e).sorted hT
    have hD := (L.rename e).witnesses.sorted A ht.domain
    have hpi : SortedAt P Δ (Expr.arrow .dd ((L.rename e).witnesses.type A) ((R.rename e.names).apply T)) K :=
      hD.arrow hR .dd (by rw [ht.output])
    obtain ⟨r,hr⟩ := ht.product.1
    obtain ⟨s,hs,t,htt,hst⟩ := ht.output ▸ hr
    constructor
    · intro a ha
      obtain ⟨hba,mba⟩ := hb a ha
      simpa only [DataWrapper.rename,DataWrapper.build,DataWrapper.apply,LogicSetup.rename,WitnessFamily.rename,Label.result] using
        And.intro (hba.constLam (hD s hs) (hpi r hr))
          (((L.rename e).witnesses.type_mode A ht.domain).constLam (l := .dd) mba)
    · intro w a hw mw ha
      simpa only [DataWrapper.rename,DataWrapper.observe,LogicSetup.rename,WitnessFamily.rename] using ho (.app .dd w (((L.rename e).witnesses.value A))) a
        (hw.apply_arrow ((L.rename e).witnesses.typed A ht.domain))
        (.app mw ((L.rename e).witnesses.value_mode A ht.domain)) ha
  | @negative J B K b R U h ht hU ih =>
    intro Δ δ e T hT mT
    have hR := (h.rename e).sorted hT
    have mR := (h.rename e).mode mT
    have hUe := hU.rename e
    have hpi : SortedAt P Δ (Expr.arrow .dd ((R.rename e.names).apply T) ((U.rename e.names).carrier)) K :=
      hR.arrow hUe.carrier_sorted .dd (by rw [ht.output])
    obtain ⟨r,hr⟩ := ht.product.1
    obtain ⟨s,hs,t,htt,hst⟩ := ht.output ▸ hr
    constructor
    · intro a ha
      let d : Embedding P Δ δ ((R.rename e.names).apply T :: Δ) (modeCons .data δ) :=
        Embedding.cons (hR s hs) .data
      have hT' : SortedAt P ((R.rename e.names).apply T :: Δ) (T.rename Nat.succ) I :=
        fun u hu => d.typing (hT u hu)
      have hv : HasType P ((R.rename e.names).apply T :: Δ) (.var 0)
          ((R.rename (e.comp d).names).apply (T.rename Nat.succ)) := by
        simpa only [Embedding.comp,d,Embedding.cons,DataWrapper.apply_rename,DataWrapper.rename_comp]
          using HasType.var (hR s hs)
      have ha' : (L.rename (e.comp d)).DataArg (!b) (T.rename Nat.succ)
          (a.rename (argRen (!b) Nat.succ)) :=
        (LogicSetup.DataArg.rename_comp_iff L e d _ _ _).1 (ha.rename d)
      have hf := (ih _ _ (e.comp d) (T.rename Nat.succ) hT' (d.moded mT)).2
        (.var 0) (a.rename (argRen (!b) Nat.succ)) hv (.var 0) ha'
      have hsnd := (hU.rename (e.comp d)).send_typed hf
      have hbody : HasType P ((R.rename e.names).apply T :: Δ)
          (((U.rename e.names).rename Nat.succ).send
            (((R.rename e.names).rename Nat.succ).observe (T.rename Nat.succ) (.var 0)
              (a.rename (argRen (!b) Nat.succ))))
          (((U.rename e.names).carrier).rename Nat.succ) := by
        simpa only [DataWrapper.rename_comp,DataTail.rename_comp,DataTail.carrier_rename,
          Embedding.comp,d,Embedding.cons] using hsnd.1
      have mbody : WellModed (modeCons .data δ)
          (((U.rename e.names).rename Nat.succ).send
            (((R.rename e.names).rename Nat.succ).observe (T.rename Nat.succ) (.var 0)
              (a.rename (argRen (!b) Nat.succ)))) .data := by
        simpa only [DataWrapper.rename_comp,DataTail.rename_comp,Embedding.comp,d,Embedding.cons] using hsnd.2
      exact ⟨by simpa only [DataWrapper.rename,DataWrapper.build,DataWrapper.apply,Expr.arrow]
          using HasType.abstraction hbody (hpi r hr),
        by simpa only [DataWrapper.rename,DataWrapper.build,Label.result] using WellModed.lam (l := .dd) mR mbody⟩
    · intro w a hw mw ha
      have ha' : (L.rename e).DataArg b T a := by simpa only [Bool.not_not] using ha
      have hba := (ih Δ δ e T hT mT).1 a ha'
      simpa only [DataWrapper.rename,DataWrapper.observe] using hUe.read_formula (hw.apply_arrow hba.1) (.app mw hba.2)

/-- The four displayed operations of the manuscript, on the fixed unrenamed code. -/
theorem sound (h : Formed L I J R) {T : Expr S} (hT : SortedAt P Γ T I)
    (mT : WellModed γ T .data) :
    (∀ a, L.DataArg b T a → HasType P Γ (R.build T a) (R.apply T) ∧ WellModed γ (R.build T a) .data) ∧
    (∀ w a, HasType P Γ w (R.apply T) → WellModed γ w .data →
      L.DataArg (!b) T a → L.Formula (R.observe T w a)) := by
  obtain ⟨s,hs⟩ := L.triple.codomain.1
  let e := Embedding.refl (L.bottom_formula.1 s hs).valid γ
  have hh := h.sound_rename Γ γ e T hT mT
  have harg (c : Bool) (a : Expr S) : L.DataArg c T a ↔ (L.rename e).DataArg c T a := by
    cases c
    · rfl
    · constructor <;> intro ha Δ δ f v hv mv
      · have hh := ha Δ δ f v hv mv
        apply (LogicSetup.Formula.rename_comp_iff L e f _).2
        simpa only [Embedding.comp,e,Embedding.refl,Function.comp_id] using hh
      · have hh := ha Δ δ f v hv mv
        apply (LogicSetup.Formula.rename_comp_iff L e f _).1 at hh
        simpa only [Embedding.comp,e,Embedding.refl,Function.comp_id] using hh
  constructor
  · intro a ha
    simpa only [e,Embedding.refl,DataWrapper.rename_id] using hh.1 a ((harg b a).1 ha)
  · intro w a hw mw ha
    have hf := hh.2 w a (by simpa only [e,Embedding.refl,DataWrapper.rename_id] using hw) mw ((harg (!b) a).1 ha)
    apply (LogicSetup.Formula.rename_refl_iff L (L.bottom_formula.1 s hs).valid _).1
    simpa only [e,Embedding.refl,DataWrapper.rename_id] using hf
end Formed

end DataWrapper
end PureTypeSystem.Labelled

/- A small finite compiler for the propositional term construction.
It has no type-theoretic assumptions. -/
namespace FiniteClassical
universe u
open Formula
variable {α : Type u}

namespace Derives
variable {Γ Δ : Set (Formula α)} {A B R : Formula α}

theorem mono (h : Derives Γ A) (hsub : Γ ⊆ Δ) : Derives Δ A := by
  induction h generalizing Δ with
  | ax h => exact .ax (hsub h)
  | intro h ih => exact .intro (ih (Set.insert_subset_insert hsub))
  | elim h k ih ik => exact .elim (ih hsub) (ik hsub)
  | dne h ih => exact .dne (ih hsub)

theorem weaken (h : Derives Γ A) (B : Formula α) : Derives (insert B Γ) A :=
  h.mono (Set.subset_insert _ _)

theorem cut (h : Derives Γ A) (hs : ∀ B ∈ Γ, Derives Δ B) : Derives Δ A := by
  induction h generalizing Δ with
  | ax h => exact hs _ h
  | @intro Γ A B h ih =>
    apply Derives.intro
    apply ih
    intro Q hQ
    rcases hQ with rfl | hQ
    · exact .ax (Set.mem_insert _ _)
    · exact (hs _ hQ).weaken A
  | elim h k ih ik => exact .elim (ih hs) (ik hs)
  | dne h ih => exact .dne (ih hs)

theorem absurd (h : Derives Γ .bot) : Derives Γ A :=
  .dne (.intro (h.weaken A.neg))

theorem by_cases (h : Derives (insert A Γ) R) (k : Derives (insert A.neg Γ) R) : Derives Γ R := by
  apply Derives.dne
  apply Derives.intro
  have hn : Derives (insert R.neg Γ) A.neg := by
    apply Derives.intro
    have hr : Derives (insert A (insert R.neg Γ)) R := h.mono (by
      intro Q hQ
      rcases hQ with rfl | hQ
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hQ))
    exact .elim (.ax (Set.mem_insert_of_mem _ (Set.mem_insert _ _))) hr
  have hr : Derives (insert R.neg Γ) R := k.cut (by
    intro Q hQ
    rcases hQ with rfl | hQ
    · exact hn
    · exact .ax (Set.mem_insert_of_mem _ hQ))
  exact .elim (.ax (Set.mem_insert _ _)) hr

/-- The signed recursive branch of the source's truth-table compiler. -/
theorem signed [DecidableEq α] (v : α → Bool) (A : Formula α)
    (h : ∀ a ∈ A.support, Derives Γ ((Formula.atom a).sign (v a))) :
    Derives Γ (A.sign (A.eval v)) := by
  induction A with
  | atom a => exact h a (by simp only [support,Finset.mem_singleton])
  | bot => exact .intro (.ax (Set.mem_insert _ _))
  | imp A B ihA ihB =>
    have ha := ihA (fun a ha => h a (Finset.mem_union_left _ ha))
    have hb := ihB (fun a hb => h a (Finset.mem_union_right _ hb))
    cases hA : A.eval v <;> cases hB : B.eval v
    · simp only [sign,eval,hA,hB,Bool.not_false,Bool.true_or,ite_true, if_true] at ha hb ⊢
      exact .intro (.absurd (.elim (ha.weaken A) (.ax (Set.mem_insert _ _))))
    · simp only [sign,eval,hA,hB,Bool.not_false,Bool.true_or,ite_true, if_true] at ha hb ⊢
      exact .intro (hb.weaken A)
    · simp only [sign,eval,hA,hB,Bool.not_true,Bool.false_or,ite_true, if_true,neg] at ha hb ⊢
      exact .intro (.elim (hb.weaken (.imp A B)) (.elim (.ax (Set.mem_insert _ _)) (ha.weaken (.imp A B))))
    · simp only [sign,eval,hA,hB,Bool.not_true,Bool.false_or,ite_true, if_true] at ha hb ⊢
      exact .intro (hb.weaken A)

/-- Exhaustive finite case elimination, with no evaluation reflection axiom. -/
theorem branch [DecidableEq α] (s : Finset α)
    (h : ∀ v : α → Bool, Derives ((fun A => ∃ a ∈ s, A = (Formula.atom a).sign (v a)) ∪ Γ) R) :
    Derives Γ R := by
  induction s using Finset.induction_on generalizing Γ with
  | empty =>
    have hh := h (fun _ => false)
    exact hh.mono (by
      intro X hX
      rcases hX with ⟨a,ha,_⟩ | hX
      · exact False.elim (Finset.notMem_empty a ha)
      · exact hX)
  | @insert a s has ih =>
    apply Derives.by_cases (A := Formula.atom a)
    · apply ih
      intro v
      apply (h (Function.update v a true)).mono
      intro X hX
      rcases hX with ⟨b,hb,rfl⟩ | hX
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · right
          simp only [Function.update_self,sign,ite_true, if_true]
          exact Set.mem_insert _ _
        · left
          refine ⟨b,hb,?_⟩
          rw [Function.update_of_ne (by intro he; subst b; exact has hb)]
      · exact Or.inr (Set.mem_insert_of_mem _ hX)
    · apply ih
      intro v
      apply (h (Function.update v a false)).mono
      intro X hX
      rcases hX with ⟨b,hb,rfl⟩ | hX
      · rcases Finset.mem_insert.mp hb with rfl | hb
        · right
          simp only [Function.update_self,sign]
          exact Set.mem_insert _ _
        · left
          refine ⟨b,hb,?_⟩
          rw [Function.update_of_ne (by intro he; subst b; exact has hb)]
      · exact Or.inr (Set.mem_insert_of_mem _ hX)

/-- Boolean truth-table validity compiles to a finite typed-use derivation. -/
theorem tautology [DecidableEq α] (A : Formula α) (h : ∀ v, A.eval v = true) : Derives Γ A := by
  apply branch A.support
  intro v
  have hh := signed (Γ := (fun X => ∃ a ∈ A.support, X = (Formula.atom a).sign (v a)) ∪ Γ) v A
    (fun a ha => .ax (Or.inl ⟨a,ha,rfl⟩))
  simpa only [h v,sign,ite_true, if_true] using hh
end Derives
end FiniteClassical

namespace PureTypeSystem.Labelled
universe u v
open Classical
variable {S : Type u} {P : Specification S}
namespace LogicSetup
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) {α : Type v}

 theorem interpret_rename (a : α → Expr S) (F : FiniteClassical.Formula α)
    (e : Embedding P Γ γ Δ δ) :
    (L.interpret a F).rename e.names = (L.rename e).interpret (fun i => (a i).rename e.names) F := by
  induction F with
  | atom i => rfl
  | bot => rfl
  | imp A B ihA ihB => simp only [interpret,L.imp_rename,ihA,ihB]

 theorem interpret_formula (a : α → Expr S) (ha : ∀ i, L.Formula (a i))
    (F : FiniteClassical.Formula α) : L.Formula (L.interpret a F) := by
  induction F with
  | atom i => exact ha i
  | bot => exact L.bottom_formula
  | imp A B ihA ihB => exact L.imp_formula ihA ihB

/-- Compilation of every node of the finite classical derivation to actual
labelled typing/proof-mode judgments. -/
 theorem propositional_sound {Ξ : Set (FiniteClassical.Formula α)} {F : FiniteClassical.Formula α}
    (h : FiniteClassical.Derives Ξ F) (a : α → Expr S) (ha : ∀ i, L.Formula (a i))
    (hp : ∀ Q ∈ Ξ, Proves P Γ γ (L.interpret a Q)) : Proves P Γ γ (L.interpret a F) := by
  induction h generalizing Γ γ L a with
  | ax h => exact hp _ h
  | @intro Ξ A B h ih =>
    apply L.imp_intro_future (L.interpret_formula a ha A) (L.interpret_formula a ha B)
    intro Δ δ e hA
    rw [L.interpret_rename]
    apply ih (L := L.rename e) (fun i => (a i).rename e.names) (fun i => (ha i).rename e)
    intro Q hQ
    rcases hQ with rfl | hQ
    · simpa only [L.interpret_rename] using hA
    · simpa only [L.interpret_rename] using (hp _ hQ).rename e
  | @elim Ξ A B h k ih ik =>
    exact L.imp_elim (L.interpret_formula a ha A) (L.interpret_formula a ha B) (ih L a ha hp) (ik L a ha hp)
  | @dne Ξ A h ih => exact L.dne (L.interpret_formula a ha A) (ih L a ha hp)

 theorem propositional_tautology (a : α → Expr S) (ha : ∀ i, L.Formula (a i))
    (F : FiniteClassical.Formula α) (hf : ∀ v, F.eval v = true) :
    Proves P Γ γ (L.interpret a F) :=
  L.propositional_sound (FiniteClassical.Derives.tautology (Γ := ∅) F hf) a ha (by simp)
end LogicSetup
end PureTypeSystem.Labelled

namespace PureTypeSystem.Labelled

section
universe u v
variable {S : Type u} {P : Specification S}
namespace LogicSetup
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C)

theorem top_formula : L.Formula L.top := L.imp_formula L.bottom_formula L.bottom_formula
theorem neg_formula {A : Expr S} (ha : L.Formula A) : L.Formula (L.neg A) := L.imp_formula ha L.bottom_formula
theorem conj_formula {A B : Expr S} (ha : L.Formula A) (hb : L.Formula B) :
    L.Formula (L.conj A B) := L.neg_formula (L.imp_formula ha (L.neg_formula hb))
theorem disj_formula {A B : Expr S} (ha : L.Formula A) (hb : L.Formula B) :
    L.Formula (L.disj A B) := L.neg_formula (L.conj_formula (L.neg_formula ha) (L.neg_formula hb))
theorem iff_formula {A B : Expr S} (ha : L.Formula A) (hb : L.Formula B) :
    L.Formula (L.iff A B) := L.conj_formula (L.imp_formula ha hb) (L.imp_formula hb ha)

/-- Arbitrary finite propositional chaining, compiled to actual open terms. -/
theorem propositional_consequence {α : Type v} (a : α → Expr S) (ha : ∀ i, L.Formula (a i))
    (hs : List (FiniteClassical.Formula α)) (Q : FiniteClassical.Formula α)
    (hv : ∀ v, (FiniteClassical.Formula.chain hs Q).eval v = true)
    (hp : ∀ R ∈ hs, Proves P Γ γ (L.interpret a R)) :
    Proves P Γ γ (L.interpret a Q) := by
  have hf := L.propositional_tautology a ha (FiniteClassical.Formula.chain hs Q) hv
  clear hv
  induction hs with
  | nil => exact hf
  | cons A hs ih =>
    apply ih (fun R hR => hp R (List.mem_cons_of_mem _ hR))
    exact L.imp_elim (L.interpret_formula a ha A) (L.interpret_formula a ha (FiniteClassical.Formula.chain hs Q))
      hf (hp A (List.mem_cons_self))

theorem top_intro : Proves P Γ γ L.top := by
  obtain ⟨s,hs⟩ := L.bottom_formula.sorted L
  exact L.imp_intro L.bottom_formula L.bottom_formula (.refl hs)

theorem conj_intro {A B : Expr S} (hA : L.Formula A) (hB : L.Formula B)
    (ha : Proves P Γ γ A) (hb : Proves P Γ γ B) : Proves P Γ γ (L.conj A B) := by
  apply L.propositional_consequence (fun b : Bool => if b then B else A)
      (fun b => by cases b; exact hA; exact hB)
      [.atom false,.atom true] ((FiniteClassical.Formula.atom false).conj (.atom true))
  · intro v; cases h0 : v false <;> cases h1 : v true <;>
      simp only [FiniteClassical.Formula.chain,List.foldr,FiniteClassical.Formula.conj,
        FiniteClassical.Formula.neg,FiniteClassical.Formula.eval,h0,h1] <;> rfl
  · intro R hR
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hR
    rcases hR with rfl | rfl
    · exact ha
    · exact hb

theorem conj_left {A B : Expr S} (hA : L.Formula A) (hB : L.Formula B)
    (hp : Proves P Γ γ (L.conj A B)) : Proves P Γ γ A := by
  apply L.propositional_consequence (fun b : Bool => if b then B else A)
      (fun b => by cases b; exact hA; exact hB)
      [(FiniteClassical.Formula.atom false).conj (.atom true)] (.atom false)
  · intro v; cases h0 : v false <;> cases h1 : v true <;>
      simp only [FiniteClassical.Formula.chain,List.foldr,FiniteClassical.Formula.conj,
        FiniteClassical.Formula.neg,FiniteClassical.Formula.eval,h0,h1] <;> rfl
  · intro R hR
    have he : R = (FiniteClassical.Formula.atom false).conj (.atom true) := by simpa only [List.mem_singleton] using hR
    subst R; exact hp

theorem conj_right {A B : Expr S} (hA : L.Formula A) (hB : L.Formula B)
    (hp : Proves P Γ γ (L.conj A B)) : Proves P Γ γ B := by
  apply L.propositional_consequence (fun b : Bool => if b then B else A)
      (fun b => by cases b; exact hA; exact hB)
      [(FiniteClassical.Formula.atom false).conj (.atom true)] (.atom true)
  · intro v; cases h0 : v false <;> cases h1 : v true <;>
      simp only [FiniteClassical.Formula.chain,List.foldr,FiniteClassical.Formula.conj,
        FiniteClassical.Formula.neg,FiniteClassical.Formula.eval,h0,h1] <;> rfl
  · intro R hR
    have he : R = (FiniteClassical.Formula.atom false).conj (.atom true) := by simpa only [List.mem_singleton] using hR
    subst R; exact hp

theorem iff_of_equivalent {A B : Expr S} (hA : L.Formula A) (hB : L.Formula B)
    (he : Equivalent P Γ γ A B) : Proves P Γ γ (L.iff A B) :=
  L.conj_intro (L.imp_formula hA hB) (L.imp_formula hB hA)
    (L.imp_intro hA hB he.1) (L.imp_intro hB hA he.2)

theorem equivalent_of_iff {A B : Expr S} (hA : L.Formula A) (hB : L.Formula B)
    (hp : Proves P Γ γ (L.iff A B)) : Equivalent P Γ γ A B := by
  have hab := L.conj_left (L.imp_formula hA hB) (L.imp_formula hB hA) hp
  have hba := L.conj_right (L.imp_formula hA hB) (L.imp_formula hB hA) hp
  obtain ⟨s,hs⟩ := hA.sorted L
  obtain ⟨t,ht⟩ := hB.sorted L
  exact ⟨(L.imp_future_iff hA hB).1 hab _ _ (Embedding.cons hs .proof) (Proves.of_var hs),
    (L.imp_future_iff hB hA).1 hba _ _ (Embedding.cons ht .proof) (Proves.of_var ht)⟩
end LogicSetup
end

section
universe u
variable {S : Type u}
namespace Converts
theorem app {l : Label} {f f' a a' : Expr S} (hf : Converts f f') (ha : Converts a a') :
    Converts (.app l f a) (.app l f' a') := by
  obtain ⟨g,hg,hg'⟩ := hf.join
  obtain ⟨u,hu,hu'⟩ := ha.join
  exact .trans _ _ _ (hg.app hu).converts (.symm _ _ (hg'.app hu').converts)
end Converts
namespace ProofWrapper
theorem subst_rename (R : ProofWrapper S) (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.rename ρ).subst σ = R.subst (σ ∘ ρ) := by
  induction R <;> simp_all only [rename,subst,Expr.subst_rename]
theorem rename_subst (R : ProofWrapper S) (ρ : Nat → Nat) (σ : Nat → Expr S) :
    (R.subst σ).rename ρ = R.subst (fun n => (σ n).rename ρ) := by
  induction R <;> simp_all only [rename,subst,Expr.rename_subst]
end ProofWrapper
namespace PositiveDataWrapper
theorem subst_rename (R : PositiveDataWrapper S) (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.rename ρ).subst σ = R.subst (σ ∘ ρ) := by
  induction R <;> simp_all only [rename,subst,Expr.subst_rename]
theorem rename_subst (R : PositiveDataWrapper S) (ρ : Nat → Nat) (σ : Nat → Expr S) :
    (R.subst σ).rename ρ = R.subst (fun n => (σ n).rename ρ) := by
  induction R <;> simp_all only [rename,subst,Expr.rename_subst]
theorem project_converts (R : PositiveDataWrapper S) {w w' : Expr S} (h : Converts w w') :
    Converts (R.project w) (R.project w') := by
  induction R generalizing w w' with
  | identity => exact h
  | step R D e ih => exact ih (.app h (.refl _))
end PositiveDataWrapper
namespace DataTail
theorem subst_rename (U : DataTail S) (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (U.rename ρ).subst σ = U.subst (σ ∘ ρ) := by
  cases U
  simp only [rename,subst,ProofWrapper.subst_rename,PositiveDataWrapper.subst_rename]
theorem rename_subst (U : DataTail S) (ρ : Nat → Nat) (σ : Nat → Expr S) :
    (U.subst σ).rename ρ = U.subst (fun n => (σ n).rename ρ) := by
  cases U
  simp only [rename,subst,ProofWrapper.rename_subst,PositiveDataWrapper.rename_subst]
theorem read_converts (U : DataTail S) {w w' : Expr S} (h : Converts w w') :
    Converts (U.read w) (U.read w') := U.decode.apply_converts (U.positive.project_converts h)
end DataTail
namespace DataWrapper

theorem subst_rename {b} (R : DataWrapper S b) (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.rename ρ).subst σ = R.subst (σ ∘ ρ) := by
  induction R <;> simp_all only [rename,subst,Expr.subst_rename,DataTail.subst_rename]
theorem rename_subst {b} (R : DataWrapper S b) (ρ : Nat → Nat) (σ : Nat → Expr S) :
    (R.subst σ).rename ρ = R.subst (fun n => (σ n).rename ρ) := by
  induction R <;> simp_all only [rename,subst,Expr.rename_subst,DataTail.rename_subst]

theorem argSub_shift (b : Bool) (σ : Nat → Expr S) :
    argSub b (Expr.liftSub σ) ∘ argRen b Nat.succ =
      fun n => (argSub b σ n).rename (argRen b Nat.succ) := by
  cases b
  · rfl
  · funext n
    cases n with
    | zero => rfl
    | succ n => simp only [argSub,argRen,ite_true, if_true,Function.comp_apply,Expr.liftRen,
        PureTypeSystem.Expr.liftRen,Expr.liftSub,Expr.rename_comp]; rfl

theorem subst_build_observe {b} (R : DataWrapper S b) :
    (∀ T a σ, (R.build T a).subst σ = (R.subst σ).build (T.subst σ) (a.subst (argSub b σ))) ∧
    (∀ T w a σ, (R.observe T w a).subst σ =
      (R.subst σ).observe (T.subst σ) (w.subst σ) (a.subst (argSub (!b) σ))) := by
  generalize he : R.depth = n
  induction n using Nat.strong_induction_on generalizing b R with
  | h n rec =>
   cases R with
   | identity =>
     constructor
     · intro T a σ; simp only [build,subst,argSub,Bool.false_eq_true,ite_false, if_false]
     · intro T w a σ
       simpa only [observe,subst,argSub,Bool.not_false,ite_true, if_true] using (Expr.instantiate_subst a w σ).symm
   | positive R D e =>
     have ih := rec R.depth (by simp only [← he,depth]; omega) R rfl
     exact ⟨fun T a σ => by simp only [build,subst,Expr.constLam_subst,ih.1],
       fun T w a σ => by simpa only [observe,subst,Expr.subst] using ih.2 T (.app .dd w e) a σ⟩
   | @negative b R U =>
     have ih := rec R.depth (by simp only [← he,depth]; omega) R rfl
     constructor
     · intro T a σ
       simp only [build,Expr.subst,DataTail.send_subst,subst]
       rw [(rec R.depth (by simp only [← he,depth]; omega) (R.rename Nat.succ) (R.depth_rename Nat.succ)).2]
       simp only [apply_subst,subst_rename,rename_subst,DataTail.subst_rename,DataTail.rename_subst,
         Expr.subst_rename,Expr.rename_subst,argSub_shift]
       rfl
     · intro T w a σ
       simp only [observe,subst,DataTail.read_subst,Expr.subst,ih.1,Bool.not_not]

theorem observe_converts {b} (R : DataWrapper S b) (T a : Expr S) {w w' : Expr S}
    (h : Converts w w') : Converts (R.observe T w a) (R.observe T w' a) := by
  induction R generalizing w w' with
  | identity => simpa only [observe] using h.instantiate_right a
  | positive R D e ih => simpa only [observe] using ih (.app h (.refl _))
  | negative R U ih => simpa only [observe] using U.read_converts (Converts.app (l := .dd) h (.refl (R.build T a)))

/-- The exact substitution equation exposed by a negative-edge beta step. -/
theorem observe_open {b} (R : DataWrapper S b) (T a v : Expr S) :
    ((R.rename Nat.succ).observe (T.rename Nat.succ) (.var 0)
      (a.rename (argRen (!b) Nat.succ))).instantiate v = R.observe T v a := by
  simp only [Expr.instantiate,(R.rename Nat.succ).subst_build_observe.2,
    instantiate_raise,Expr.subst,Expr.single,Expr.subst_rename]
  have he : argSub (!b) (Expr.single v) ∘ argRen (!b) Nat.succ = Expr.var := by
    cases b <;> funext n <;> cases n <;> rfl
  rw [he,Expr.subst_var]
  rw [show Expr.single v ∘ Nat.succ = Expr.var from rfl,Expr.subst_var]
end DataWrapper
end

universe u
variable {S : Type u} {P : Specification S}
namespace DataWrapper
theorem build_rename {b} (R : DataWrapper S b) (T a : Expr S) (ρ : Nat → Nat) :
    (R.build T a).rename ρ = (R.rename ρ).build (T.rename ρ) (a.rename (argRen b ρ)) :=
  R.rename_build_observe.1 T a ρ
theorem observe_rename {b} (R : DataWrapper S b) (T w a : Expr S) (ρ : Nat → Nat) :
    (R.observe T w a).rename ρ = (R.rename ρ).observe (T.rename ρ) (w.rename ρ) (a.rename (argRen (!b) ρ)) :=
  R.rename_build_observe.2 T w a ρ
theorem build_subst {b} (R : DataWrapper S b) (T a : Expr S) (σ : Nat → Expr S) :
    (R.build T a).subst σ = (R.subst σ).build (T.subst σ) (a.subst (argSub b σ)) :=
  R.subst_build_observe.1 T a σ
theorem observe_subst {b} (R : DataWrapper S b) (T w a : Expr S) (σ : Nat → Expr S) :
    (R.observe T w a).subst σ = (R.subst σ).observe (T.subst σ) (w.subst σ) (a.subst (argSub (!b) σ)) :=
  R.subst_build_observe.2 T w a σ
end DataWrapper
namespace Expr

theorem compose_instantiate (f g a : Expr S) :
    (f.compose g).instantiate a = f.instantiate (g.instantiate a) := by
  simp only [compose,instantiate,subst_subst,subst_rename]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n => rfl

theorem compose_rename (f g : Expr S) (ρ : Nat → Nat) :
    (f.compose g).rename (liftRen ρ) =
      (f.rename (liftRen ρ)).compose (g.rename (liftRen ρ)) := by
  simp only [compose,← instantiate_rename,rename_comp]
  congr 2
  funext n
  cases n <;> rfl
end Expr

namespace DataMap
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {T U f : Expr S} {s : S}
theorem apply (hf : DataMap P Γ γ T U f) {a : Expr S}
    (ha : HasType P Γ a T) (ma : WellModed γ a .data) :
    HasType P Γ (f.instantiate a) U ∧ WellModed γ (f.instantiate a) .data := by
  exact ⟨by simpa only [Expr.instantiate_raise] using hf.1.instantiate ha,
    hf.2.instantiate ma⟩

theorem rename (hf : DataMap P Γ γ T U f) (hT : HasType P Γ T (.sort s))
    (e : Embedding P Γ γ Δ δ) :
    DataMap P Δ δ (T.rename e.names) (U.rename e.names) (f.rename (Expr.liftRen e.names)) := by
  constructor
  · simpa only [Embedding.lift,Expr.rename_comp,show Expr.liftRen e.names ∘ Nat.succ = Nat.succ ∘ e.names from rfl] using (e.lift hT .data).typing hf.1
  · exact (e.lift hT .data).moded hf.2
end DataMap

namespace LogicSetup.Family
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {T U Q f : Expr S} {s : S}
theorem compose (hQ : L.Family U Q) (hf : DataMap P Γ γ T U f)
    (hT : HasType P Γ T (.sort s)) : L.Family T (Q.compose f) := by
  intro Δ δ e a ha ma
  have hd := (hf.rename hT e).apply ha ma
  have hh := hQ Δ δ e ((f.rename (Expr.liftRen e.names)).instantiate a) hd.1 hd.2
  simpa only [Expr.compose_rename,Expr.compose_instantiate] using hh
end LogicSetup.Family

namespace DataWrapper

theorem evalCallback_instantiate (R : DataWrapper S true) (T w a : Expr S) :
    (R.evalCallback T w).instantiate a = R.observe T w a := by
  simp only [evalCallback,Expr.instantiate,observe_subst,instantiate_raise,
    Expr.subst_lift_single,argSub,Bool.not_true,Bool.false_eq_true,ite_false, if_false,Expr.subst,Expr.single]

theorem evalCallback_rename (R : DataWrapper S true) (T w : Expr S) (ρ : Nat → Nat) :
    (R.evalCallback T w).rename (Expr.liftRen ρ) =
      (R.rename ρ).evalCallback (T.rename ρ) (w.rename ρ) := by
  simp only [evalCallback,observe_rename,rename_comp,Expr.rename_comp,
    argRen,Bool.not_true,Bool.false_eq_true,ite_false, if_false,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J : Set S} {R : DataWrapper S true}

theorem evalCallback_family (hR : Formed L I J R) {T w : Expr S}
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hw : HasType P Γ w (R.apply T)) (mw : WellModed γ w .data) :
    L.Family T (R.evalCallback T w) := by
  intro Δ δ e a ha ma
  rw [evalCallback_rename,evalCallback_instantiate]
  exact ((hR.rename e).sound (fun s hs => e.typing (hT s hs)) (e.moded mT)).2
    (w.rename e.names) a (by simpa only [apply_rename] using e.typing hw) (e.moded mw) ⟨ha,ma⟩
end Formed

theorem cancelFormula_swap (b : Bool) (a q : Expr S) :
    cancelFormula (!b) a q = cancelFormula b q a := by cases b <;> rfl

theorem negative_beta {b} (R : DataWrapper S b) (U : DataTail S) (T a q : Expr S) :
    Converts ((R.negative U).observe T ((R.negative U).build T a) q)
      (U.read (U.send (R.observe T (R.build T q) a))) := by
  simp only [observe,build]
  apply U.read_converts
  have hh := Reduces.converts (Relation.ReflTransGen.single (Beta.head .dd (R.apply T)
    ((U.rename Nat.succ).send ((R.rename Nat.succ).observe (T.rename Nat.succ) (.var 0)
      (a.rename (argRen (!b) Nat.succ)))) (R.build T q)))
  have he : ((U.rename Nat.succ).send ((R.rename Nat.succ).observe (T.rename Nat.succ) (.var 0)
      (a.rename (argRen (!b) Nat.succ)))).instantiate (R.build T q) =
        U.send (R.observe T (R.build T q) a) := by
    simp only [Expr.instantiate,DataTail.send_subst,DataTail.instantiate_raise]
    exact congrArg U.send (R.observe_open T a (R.build T q))
  exact he ▸ hh

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J : Set S} {b : Bool} {R : DataWrapper S b}

theorem cancellation (h : Formed L I J R) {T a q : Expr S}
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (ha : L.DataArg b T a) (hq : L.DataArg (!b) T q) :
    Equivalent P Γ γ (R.observe T (R.build T a) q) (cancelFormula b a q) := by
  have htarget : L.Formula (cancelFormula b a q) := by
    cases b
    · exact hq.instantiate ha.1 ha.2
    · exact ha.instantiate hq.1 hq.2
  obtain ⟨s,hs⟩ := L.triple.codomain.1
  induction h generalizing a q with
  | identity => simpa only [observe,build,cancelFormula,Bool.false_eq_true,ite_false, if_false] using Equivalent.refl (γ := γ) (htarget.1 s hs)
  | inclusion h hh ih => exact ih ha hq htarget
  | @positive A J K b R h ht ih =>
    have hb := (h.sound hT mT).1 a ha
    have hf := (h.sound hT mT).2 (R.build T a) q hb.1 hb.2 hq
    have hsnd := (h.positive ht).sound hT mT
    have hb' := hsnd.1 a ha
    have hf' := hsnd.2 _ q hb'.1 hb'.2 hq
    have hc : Converts ((R.positive (L.witnesses.type A) (L.witnesses.value A)).observe T
        ((R.positive (L.witnesses.type A) (L.witnesses.value A)).build T a) q)
        (R.observe T (R.build T a) q) := by
      simpa only [build,observe] using R.observe_converts T q
        (Reduces.converts (Relation.ReflTransGen.single (positive_cancel .dd (L.witnesses.type A) (L.witnesses.value A) (R.build T a))))
    exact (Equivalent.of_conversion (hf'.1 s hs) (hf.1 s hs) hc).trans
      (ih ha hq htarget) (hf'.1 s hs) (hf.1 s hs) (htarget.1 s hs)
  | @negative J B K b R U h ht hU ih =>
    have hq' : L.DataArg b T q := by simpa only [Bool.not_not] using hq
    have hb := (h.sound hT mT).1 q hq'
    have hf := (h.sound hT mT).2 (R.build T q) a hb.1 hb.2 ha
    have hsnd := (h.negative ht hU).sound hT mT
    have hb' := hsnd.1 a ha
    have hf' := hsnd.2 _ q hb'.1 hb'.2 hq
    have hsend := hU.send_typed hf
    have hread := hU.read_formula hsend.1 hsend.2
    have hc := Equivalent.of_conversion (γ := γ) (hf'.1 s hs) (hread.1 s hs) (R.negative_beta U T a q)
    have ih' := ih hq' ha (by simpa only [cancelFormula_swap] using htarget)
    have he := (hU.read_send hf).trans ih' (hread.1 s hs) (hf.1 s hs)
      (by simpa only [cancelFormula_swap] using htarget.1 s hs)
    simpa only [cancelFormula_swap] using hc.trans he (hf'.1 s hs) (hread.1 s hs)
      (by simpa only [cancelFormula_swap] using htarget.1 s hs)
end Formed
end DataWrapper

namespace Expr
theorem compose_subst (f g : Expr S) (σ : Nat → Expr S) :
    (f.compose g).subst (liftSub σ) =
      (f.subst (liftSub σ)).compose (g.subst (liftSub σ)) := by
  simp only [compose,← instantiate_subst,subst_rename,rename_subst]
  congr 2
  funext n
  cases n with
  | zero => rfl
  | succ n => simp only [liftRen,PureTypeSystem.Expr.liftRen,liftSub,Function.comp_apply,rename_comp]; rfl

end Expr
namespace DataWrapper

theorem evalCallback_subst (R : DataWrapper S true) (T w : Expr S) (σ : Nat → Expr S) :
    (R.evalCallback T w).subst (Expr.liftSub σ) =
      (R.subst σ).evalCallback (T.subst σ) (w.subst σ) := by
  simp only [evalCallback,observe_subst,subst_rename,rename_subst,
    Expr.subst_rename,Expr.rename_subst,argSub,Bool.not_true,Bool.false_eq_true,
    ite_false, if_false,Expr.subst,Expr.liftSub]
  rfl

end DataWrapper

namespace LogicCode
variable (L : LogicCode S)

theorem rename_comp (ρ τ : Nat → Nat) : (L.rename τ).rename ρ = L.rename (ρ ∘ τ) := by
  cases L; simp only [rename,Expr.rename_comp,ProofWrapper.rename_comp]
theorem instantiate_raise (a : Expr S) : (L.rename Nat.succ).subst (Expr.single a) = L := by
  cases L; simp only [rename,subst,Expr.subst_lift_single,ProofWrapper.instantiate_raise]
theorem rename_lift_instantiate (ρ : Nat → Nat) (a : Expr S) :
    ((L.rename Nat.succ).rename (Expr.liftRen ρ)).subst (Expr.single a) = L.rename ρ := by
  rw [rename_comp]
  change (L.rename (Nat.succ ∘ ρ)).subst (Expr.single a) = _
  rw [← rename_comp]
  exact instantiate_raise _ a

theorem imp_rename (A B : Expr S) (ρ : Nat → Nat) :
    (L.imp A B).rename ρ = (L.rename ρ).imp (A.rename ρ) (B.rename ρ) := by
  simp only [imp,ProofWrapper.apply_rename,Expr.arrow_rename,rename]
theorem imp_subst (A B : Expr S) (σ : Nat → Expr S) :
    (L.imp A B).subst σ = (L.subst σ).imp (A.subst σ) (B.subst σ) := by
  simp only [imp,ProofWrapper.apply_subst,Expr.arrow_subst,subst]
theorem neg_rename (A : Expr S) (ρ : Nat → Nat) :
    (L.neg A).rename ρ = (L.rename ρ).neg (A.rename ρ) := by
  simp only [neg,imp_rename,rename]
theorem neg_subst (A : Expr S) (σ : Nat → Expr S) :
    (L.neg A).subst σ = (L.subst σ).neg (A.subst σ) := by
  simp only [neg,imp_subst,subst]
theorem top_rename (ρ : Nat → Nat) : L.top.rename ρ = (L.rename ρ).top := by
  simp only [top,imp_rename,rename]
theorem top_subst (σ : Nat → Expr S) : L.top.subst σ = (L.subst σ).top := by
  simp only [top,imp_subst,subst]
theorem conj_rename (A B : Expr S) (ρ : Nat → Nat) :
    (L.conj A B).rename ρ = (L.rename ρ).conj (A.rename ρ) (B.rename ρ) := by
  simp only [conj,neg_rename,imp_rename]
theorem conj_subst (A B : Expr S) (σ : Nat → Expr S) :
    (L.conj A B).subst σ = (L.subst σ).conj (A.subst σ) (B.subst σ) := by
  simp only [conj,neg_subst,imp_subst]
theorem disj_rename (A B : Expr S) (ρ : Nat → Nat) :
    (L.disj A B).rename ρ = (L.rename ρ).disj (A.rename ρ) (B.rename ρ) := by
  simp only [disj,neg_rename,conj_rename]
theorem disj_subst (A B : Expr S) (σ : Nat → Expr S) :
    (L.disj A B).subst σ = (L.subst σ).disj (A.subst σ) (B.subst σ) := by
  simp only [disj,neg_subst,conj_subst]
theorem cond_rename (G A B : Expr S) (ρ : Nat → Nat) :
    (L.cond G A B).rename ρ = (L.rename ρ).cond (G.rename ρ) (A.rename ρ) (B.rename ρ) := by
  simp only [cond,conj_rename,disj_rename,neg_rename]
theorem cond_subst (G A B : Expr S) (σ : Nat → Expr S) :
    (L.cond G A B).subst σ = (L.subst σ).cond (G.subst σ) (A.subst σ) (B.subst σ) := by
  simp only [cond,conj_subst,disj_subst,neg_subst]
theorem sign_subst (b : Bool) (A : Expr S) (σ : Nat → Expr S) :
    (L.sign b A).subst σ = (L.subst σ).sign b (A.subst σ) := by
  cases b <;> simp only [sign,ite_false, if_false,ite_true, if_true,Bool.false_eq_true,neg_subst]
theorem sign_instantiate_raise (b : Bool) (Q a : Expr S) :
    ((L.rename Nat.succ).sign b Q).instantiate a = L.sign b (Q.instantiate a) := by
  simp only [Expr.instantiate,sign_subst,instantiate_raise]
end LogicCode
namespace LogicSetup
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C)
theorem code_rename (e : Embedding P Γ γ Δ δ) : (L.rename e).code = L.code.rename e.names := rfl
theorem cond_formula {G A B : Expr S} (hG : L.Formula G) (hA : L.Formula A) (hB : L.Formula B) :
    L.Formula (L.code.cond G A B) :=
  L.disj_formula (L.conj_formula hG hA) (L.conj_formula (L.neg_formula hG) hB)
theorem sign_formula (b : Bool) {A : Expr S} (hA : L.Formula A) : L.Formula (L.code.sign b A) := by
  cases b
  · exact L.neg_formula hA
  · exact hA

namespace Family
variable {L} {T Q Q' : Expr S} {s : S}
theorem constant (hQ : L.Formula Q) : L.Family T (Q.rename Nat.succ) := by
  intro Δ δ e a ha ma
  rw [Expr.rename_comp]
  rw [show Expr.liftRen e.names ∘ Nat.succ = Nat.succ ∘ e.names from rfl, ← Expr.rename_comp]
  rw [Expr.instantiate_raise]
  exact hQ.rename e

theorem code_imp (ha : L.Family T Q) (hb : L.Family T Q') :
    L.Family T ((L.code.rename Nat.succ).imp Q Q') := by
  intro Δ δ e a hA mA
  simp only [LogicCode.imp_rename,Expr.instantiate,LogicCode.imp_subst,
    LogicCode.rename_lift_instantiate]
  exact (L.rename e).imp_formula (ha _ _ e a hA mA) (hb _ _ e a hA mA)

theorem code_neg (hQ : L.Family T Q) : L.Family T ((L.code.rename Nat.succ).neg Q) :=
  hQ.code_imp (constant L.bottom_formula)

theorem code_sign (hQ : L.Family T Q) (b : Bool) : L.Family T ((L.code.rename Nat.succ).sign b Q) := by
  cases b
  · exact hQ.code_neg
  · exact hQ

theorem code_conj (ha : L.Family T Q) (hb : L.Family T Q') :
    L.Family T ((L.code.rename Nat.succ).conj Q Q') :=
  (ha.code_imp hb.code_neg).code_neg

theorem code_disj (ha : L.Family T Q) (hb : L.Family T Q') :
    L.Family T ((L.code.rename Nat.succ).disj Q Q') :=
  (ha.code_neg.code_conj hb.code_neg).code_neg

theorem code_cond {G : Expr S} (hg : L.Family T G) (ha : L.Family T Q) (hb : L.Family T Q') :
    L.Family T ((L.code.rename Nat.succ).cond G Q Q') :=
  (hg.code_conj ha).code_disj (hg.code_neg.code_conj hb)
end Family
end LogicSetup

namespace DataWrapper

theorem contraCallback_instantiate (R : DataWrapper S true) (T t f : Expr S) :
    (R.contraCallback T t).instantiate f = R.observe T f t := by
  simp only [contraCallback,Expr.instantiate,observe_subst,instantiate_raise,
    Expr.subst_lift_single,argSub,Bool.not_true,Bool.false_eq_true,ite_false, if_false,Expr.subst,Expr.single]

theorem contraCallback_rename (R : DataWrapper S true) (T t : Expr S) (ρ : Nat → Nat) :
    (R.contraCallback T t).rename (Expr.liftRen ρ) =
      (R.rename ρ).contraCallback (T.rename ρ) (t.rename ρ) := by
  simp only [contraCallback,observe_rename,rename_comp,Expr.rename_comp,
    argRen,Bool.not_true,Bool.false_eq_true,ite_false, if_false,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl

theorem contraCallback_subst (R : DataWrapper S true) (T t : Expr S) (σ : Nat → Expr S) :
    (R.contraCallback T t).subst (Expr.liftSub σ) =
      (R.subst σ).contraCallback (T.subst σ) (t.subst σ) := by
  simp only [contraCallback,observe_subst,subst_rename,rename_subst,
    Expr.subst_rename,Expr.rename_subst,argSub,Bool.not_true,Bool.false_eq_true,
    ite_false, if_false,Expr.subst,Expr.liftSub]
  rfl
namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J : Set S} {R : DataWrapper S true}

theorem contraCallback_family (hR : Formed L I J R) {T t : Expr S}
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (ht : HasType P Γ t T) (mt : WellModed γ t .data) :
    L.Family (R.apply T) (R.contraCallback T t) := by
  intro Δ δ e f hf mf
  rw [contraCallback_rename,contraCallback_instantiate]
  exact ((hR.rename e).sound (fun s hs => e.typing (hT s hs)) (e.moded mT)).2
    f (t.rename e.names) (by simpa only [apply_rename] using hf) mf ⟨e.typing ht,e.moded mt⟩
end Formed
end DataWrapper
end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Channels
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate _root_.OAI.PureTypeSystem.instCountableExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled
universe u
variable {S : Type u} {P : Specification S}
namespace LogicSetup
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)} (L : LogicSetup P Γ γ C)
    {A B : Expr S}
theorem neg_equivalent (hA : L.Formula A) (hB : L.Formula B) (he : Equivalent P Γ γ A B) :
    Equivalent P Γ γ (L.neg A) (L.neg B) := by
  apply L.equivalent_of_iff (L.neg_formula hA) (L.neg_formula hB)
  exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (A) else if pl_i = 1 then (B) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.atom 1)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl; exacts [((L).iff_of_equivalent (hA) (hB) he)])

theorem sign_equivalent (b : Bool) (hA : L.Formula A) (hB : L.Formula B) (he : Equivalent P Γ γ A B) :
    Equivalent P Γ γ (L.code.sign b A) (L.code.sign b B) := by
  cases b
  · exact L.neg_equivalent hA hB he
  · exact he
end LogicSetup

namespace DoubleCode
variable (R : DoubleCode S)

variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) (I J K : Set S)
namespace Formed
variable {R L I J K}
theorem rename (h : Formed R L I J K) (e : Embedding P Γ γ Δ δ) :
    Formed (R.rename e.names) (L.rename e) I J K := ⟨h.first.rename e,h.second.rename e⟩
variable (h : Formed R L I J K) {T t v Q : Expr S}
include h
theorem sorted (hT : SortedAt P Γ T I) : SortedAt P Γ (R.carrier T) K := h.second.sorted (h.first.sorted hT)
theorem mode (mT : WellModed γ T .data) : WellModed γ (R.carrier T) .data := h.second.mode (h.first.mode mT)

theorem emb_typed (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (b : Bool) (ht : HasType P Γ t T) (mt : WellModed γ t .data) :
    HasType P Γ (R.emb L.code b T t) (R.carrier T) ∧ WellModed γ (R.emb L.code b T t) .data :=
  (h.second.sound (h.first.sorted hT) (h.first.mode mT)).1 _
    ((h.first.contraCallback_family hT mT ht mt).code_sign b)

theorem eval_formula (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (hv : HasType P Γ v (R.carrier T)) (mv : WellModed γ v .data)
    (hQ : L.Family T Q) : L.Formula (R.eval T v Q) := by
  have hb := (h.first.sound hT mT).1 Q hQ
  exact (h.second.sound (h.first.sorted hT) (h.first.mode mT)).2 v _ hv mv hb

theorem bit_formula (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (hv : HasType P Γ v (R.carrier T)) (mv : WellModed γ v .data) :
    L.Formula (R.bit L.code T v) :=
  h.eval_formula hT mT hv mv (.constant L.top_formula)

theorem rec_formula (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (hv : HasType P Γ v (R.carrier T)) (mv : WellModed γ v .data)
    (hQ : L.Family T Q) : L.Formula (R.recover L.code T v Q) :=
  L.cond_formula (h.bit_formula hT mT hv mv) (h.eval_formula hT mT hv mv hQ)
    (L.neg_formula (h.eval_formula hT mT hv mv hQ))

theorem emb_evaluation (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (b : Bool) (ht : HasType P Γ t T) (mt : WellModed γ t .data)
    (hQ : L.Family T Q) :
    Equivalent P Γ γ (R.eval T (R.emb L.code b T t) Q) (L.code.sign b (Q.instantiate t)) := by
  have hf := (h.first.sound hT mT).1 Q hQ
  have hcb := (h.first.contraCallback_family hT mT ht mt).code_sign b
  have he := h.second.cancellation (h.first.sorted hT) (h.first.mode mT) hcb hf
  have he' : Equivalent P Γ γ (R.eval T (R.emb L.code b T t) Q)
      (L.code.sign b (R.first.observe T (R.first.build T Q) t)) := by
    simpa only [DataWrapper.cancelFormula,ite_true, if_true,LogicCode.sign_instantiate_raise,DataWrapper.contraCallback_instantiate,eval,emb] using he
  have he₁ := h.first.cancellation hT mT hQ ⟨ht,mt⟩
  have ha := (h.first.sound hT mT).2 _ t hf.1 hf.2 ⟨ht,mt⟩
  have hb := hQ.instantiate ht mt
  have he₂ := L.sign_equivalent b ha hb (by simpa only [DataWrapper.cancelFormula,ite_true, if_true] using he₁)
  have hv := h.emb_typed hT mT b ht mt
  have hc := h.eval_formula hT mT hv.1 hv.2 hQ
  obtain ⟨s,hs⟩ := L.triple.codomain.1
  exact he'.trans he₂ (hc.1 s hs) ((L.sign_formula b ha).1 s hs) ((L.sign_formula b hb).1 s hs)

theorem emb_bit (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (b : Bool) (ht : HasType P Γ t T) (mt : WellModed γ t .data) :
    Proves P Γ γ (L.code.sign b (R.bit L.code T (R.emb L.code b T t))) := by
  have hv := h.emb_typed hT mT b ht mt
  have hb := h.bit_formula hT mT hv.1 hv.2
  have he := h.emb_evaluation hT mT b ht mt (.constant L.top_formula)
  simp only [Expr.instantiate_raise] at he
  have hp := L.top_intro
  cases b
  · change Proves P Γ γ (L.neg (R.bit L.code T (R.emb L.code false T t)))
    change Equivalent P Γ γ (R.bit L.code T (R.emb L.code false T t)) (L.neg L.top) at he
    exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (R.bit L.code T (R.emb L.code false T t)) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp FiniteClassical.Formula.bot FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp FiniteClassical.Formula.bot FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot), (FiniteClassical.Formula.imp FiniteClassical.Formula.bot FiniteClassical.Formula.bot)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl; exacts [((L).iff_of_equivalent (hb) (LogicSetup.neg_formula L (LogicSetup.top_formula L)) he), hp])
  · exact he.2.prove hp

theorem emb_recovery (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (b : Bool) (ht : HasType P Γ t T) (mt : WellModed γ t .data)
    (hQ : L.Family T Q) : Equivalent P Γ γ (R.recover L.code T (R.emb L.code b T t) Q) (Q.instantiate t) := by
  have hv := h.emb_typed hT mT b ht mt
  have hb := h.bit_formula hT mT hv.1 hv.2
  have heval := h.eval_formula hT mT hv.1 hv.2 hQ
  have hqt := hQ.instantiate ht mt
  have he := h.emb_evaluation hT mT b ht mt hQ
  have hp := h.emb_bit hT mT b ht mt
  apply L.equivalent_of_iff (h.rec_formula hT mT hv.1 hv.2 hQ) hqt
  change Proves P Γ γ (L.iff (L.code.cond _ _ (L.neg _)) _)
  cases b
  · change Equivalent P Γ γ _ (L.neg (Q.instantiate t)) at he
    change Proves P Γ γ (L.neg _) at hp
    exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (R.eval T (R.emb L.code false T t) Q) else if pl_i = 1 then (Q.instantiate t) else if pl_i = 2 then (R.bit L.code T (R.emb L.code false T t)) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot) (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot), (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.atom 1)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl; exacts [((L).iff_of_equivalent (heval) (LogicSetup.neg_formula L hqt) he), hp])
  · change Equivalent P Γ γ _ (Q.instantiate t) at he
    change Proves P Γ γ (R.bit L.code T (R.emb L.code true T t)) at hp
    exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (R.eval T (R.emb L.code true T t) Q) else if pl_i = 1 then (Q.instantiate t) else if pl_i = 2 then (R.bit L.code T (R.emb L.code true T t)) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.atom 1)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot), (FiniteClassical.Formula.atom 2)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.atom 1)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl; exacts [((L).iff_of_equivalent (heval) (hqt) he), hp])
end Formed
end DoubleCode

namespace LogicCode
variable (L : LogicCode S)
theorem subst_rename (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (L.rename ρ).subst σ = L.subst (σ ∘ ρ) := by
  cases L; simp only [rename,subst,Expr.subst_rename,ProofWrapper.subst_rename]
theorem rename_subst (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (L.subst σ).rename ρ = L.subst (fun i => (σ i).rename ρ) := by
  cases L; simp only [rename,subst,Expr.rename_subst,ProofWrapper.rename_subst]
end LogicCode
namespace DoubleCode
variable (R : DoubleCode S)
theorem rename_comp (ρ τ : Nat → Nat) : (R.rename τ).rename ρ = R.rename (ρ ∘ τ) := by
  cases R; simp only [rename,DataWrapper.rename_comp]
theorem instantiate_raise (a : Expr S) : (R.rename Nat.succ).subst (Expr.single a) = R := by
  cases R; simp only [rename,subst,DataWrapper.instantiate_raise]
theorem subst_rename (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.rename ρ).subst σ = R.subst (σ ∘ ρ) := by
  cases R; simp only [rename,subst,DataWrapper.subst_rename]
theorem rename_subst (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.subst σ).rename ρ = R.subst (fun i => (σ i).rename ρ) := by
  cases R; simp only [rename,subst,DataWrapper.rename_subst]
theorem carrier_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.carrier T).rename ρ = (R.rename ρ).carrier (T.rename ρ) := by
  simp only [carrier,rename,DataWrapper.apply_rename]
theorem carrier_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.carrier T).subst σ = (R.subst σ).carrier (T.subst σ) := by
  simp only [carrier,subst,DataWrapper.apply_subst]
theorem emb_subst (L : LogicCode S) (b : Bool) (T t : Expr S) (σ : Nat → Expr S) :
    (R.emb L b T t).subst σ = (R.subst σ).emb (L.subst σ) b (T.subst σ) (t.subst σ) := by
  simp only [emb,DataWrapper.build_subst,DataWrapper.apply_subst,DataWrapper.argSub,ite_true, if_true,
    LogicCode.sign_subst,LogicCode.subst_rename,LogicCode.rename_subst,
    DataWrapper.contraCallback_subst,subst]
  rfl
theorem eval_rename (T v Q : Expr S) (ρ : Nat → Nat) :
    (R.eval T v Q).rename ρ = (R.rename ρ).eval (T.rename ρ) (v.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [eval,DataWrapper.observe_rename,DataWrapper.build_rename,DataWrapper.apply_rename,
    DataWrapper.argRen,Bool.not_true,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,rename]
theorem eval_subst (T v Q : Expr S) (σ : Nat → Expr S) :
    (R.eval T v Q).subst σ = (R.subst σ).eval (T.subst σ) (v.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [eval,DataWrapper.observe_subst,DataWrapper.build_subst,DataWrapper.apply_subst,
    DataWrapper.argSub,Bool.not_true,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,subst]
theorem bit_rename (L : LogicCode S) (T v : Expr S) (ρ : Nat → Nat) :
    (R.bit L T v).rename ρ = (R.rename ρ).bit (L.rename ρ) (T.rename ρ) (v.rename ρ) := by
  change (R.eval T v (L.top.rename Nat.succ)).rename ρ = _
  rw [eval_rename,Expr.rename_comp]
  change _ = (R.rename ρ).eval _ _ ((L.rename ρ).top.rename Nat.succ)
  rw [← LogicCode.top_rename,Expr.rename_comp]
  rfl
theorem bit_subst (L : LogicCode S) (T v : Expr S) (σ : Nat → Expr S) :
    (R.bit L T v).subst σ = (R.subst σ).bit (L.subst σ) (T.subst σ) (v.subst σ) := by
  change (R.eval T v (L.top.rename Nat.succ)).subst σ = _
  rw [eval_subst,Expr.subst_rename]
  change _ = (R.subst σ).eval _ _ ((L.subst σ).top.rename Nat.succ)
  rw [← LogicCode.top_subst,Expr.rename_subst]
  rfl
theorem rec_rename (L : LogicCode S) (T v Q : Expr S) (ρ : Nat → Nat) :
    (R.recover L T v Q).rename ρ = (R.rename ρ).recover (L.rename ρ) (T.rename ρ) (v.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [recover,LogicCode.cond_rename,LogicCode.neg_rename,bit_rename,eval_rename]
theorem rec_subst (L : LogicCode S) (T v Q : Expr S) (σ : Nat → Expr S) :
    (R.recover L T v Q).subst σ = (R.subst σ).recover (L.subst σ) (T.subst σ) (v.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [recover,LogicCode.cond_subst,LogicCode.neg_subst,bit_subst,eval_subst]

theorem bitBody_instantiate (L : LogicCode S) (T v : Expr S) :
    (R.bitBody L T).instantiate v = R.bit L T v := by
  simp only [bitBody,Expr.instantiate,bit_subst,instantiate_raise,LogicCode.instantiate_raise,
    Expr.subst_lift_single,Expr.subst,Expr.single]
theorem recBody_instantiate (L : LogicCode S) (T Q v : Expr S) :
    (R.recBody L T Q).instantiate v = R.recover L T v Q := by
  simp only [recBody,Expr.instantiate,rec_subst,instantiate_raise,LogicCode.instantiate_raise,
    Expr.subst_lift_single,Expr.subst,Expr.single]
  congr 1
  rw [Expr.subst_rename]
  have he : Expr.liftSub (Expr.single v) ∘ Expr.liftRen Nat.succ = Expr.var := by
    funext n; cases n <;> rfl
  rw [he,Expr.subst_var]
theorem bitBody_rename (L : LogicCode S) (T : Expr S) (ρ : Nat → Nat) :
    (R.bitBody L T).rename (Expr.liftRen ρ) = (R.rename ρ).bitBody (L.rename ρ) (T.rename ρ) := by
  simp only [bitBody,bit_rename,rename_comp,LogicCode.rename_comp,Expr.rename_comp,Expr.rename]
  rfl
theorem recBody_rename (L : LogicCode S) (T Q : Expr S) (ρ : Nat → Nat) :
    (R.recBody L T Q).rename (Expr.liftRen ρ) =
      (R.rename ρ).recBody (L.rename ρ) (T.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [recBody,rec_rename,rename_comp,LogicCode.rename_comp,Expr.rename_comp,Expr.rename]
  congr 1
  congr 1
  funext n; cases n <;> rfl

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J K : Set S} {R : DoubleCode S}
theorem bitBody_family (h : R.Formed L I J K) {T : Expr S}
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) : L.Family (R.carrier T) (R.bitBody L.code T) := by
  intro Δ δ e v hv mv
  rw [bitBody_rename,bitBody_instantiate]
  exact (h.rename e).bit_formula (fun s hs => e.typing (hT s hs)) (e.moded mT)
    (by simpa only [carrier_rename] using hv) mv

theorem recBody_family (h : R.Formed L I J K) {T Q : Expr S}
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (hQ : L.Family T Q) :
    L.Family (R.carrier T) (R.recBody L.code T Q) := by
  intro Δ δ e v hv mv
  rw [recBody_rename,recBody_instantiate]
  exact (h.rename e).rec_formula (fun s hs => e.typing (hT s hs)) (e.moded mT)
    (by simpa only [carrier_rename] using hv) mv (hQ.rename e)
end Formed

theorem tower_rename (n : Nat) (T : Expr S) (ρ : Nat → Nat) :
    (R.tower n T).rename ρ = (R.rename ρ).tower n (T.rename ρ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tower,carrier_rename,ih]
theorem tower_subst (n : Nat) (T : Expr S) (σ : Nat → Expr S) :
    (R.tower n T).subst σ = (R.subst σ).tower n (T.subst σ) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [tower,carrier_subst,ih]
theorem embed_subst (L : LogicCode S) (bs : List Bool) (T t : Expr S) (σ : Nat → Expr S) :
    (R.embed L bs T t).subst σ = (R.subst σ).embed (L.subst σ) bs (T.subst σ) (t.subst σ) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [embed,emb_subst,tower_subst,ih]

namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J : Set S}
    (h : R.Formed L I J I)
include h
theorem tower_sorted {T : Expr S} (hT : SortedAt P Γ T I) (n : Nat) : SortedAt P Γ (R.tower n T) I := by
  induction n with
  | zero => exact hT
  | succ n ih => exact h.sorted ih
theorem tower_mode {T : Expr S} (mT : WellModed γ T .data) (n : Nat) : WellModed γ (R.tower n T) .data := by
  induction n with
  | zero => exact mT
  | succ n ih => exact h.mode ih

theorem embed_typed {T t : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (bs : List Bool) (ht : HasType P Γ t T) (mt : WellModed γ t .data) :
    HasType P Γ (R.embed L.code bs T t) (R.tower bs.length T) ∧ WellModed γ (R.embed L.code bs T t) .data := by
  induction bs with
  | nil => exact ⟨ht,mt⟩
  | cons b bs ih => exact h.emb_typed (h.tower_sorted hT bs.length) (h.tower_mode mT bs.length) b ih.1 ih.2

theorem recoveryBody_family {T Q : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (n : Nat) (hQ : L.Family T Q) : L.Family (R.tower n T) (R.recoveryBody L.code n T Q) := by
  induction n with
  | zero => exact hQ
  | succ n ih => exact h.recBody_family (h.tower_sorted hT n) (h.tower_mode mT n) ih

theorem tagBody_family {T : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (bs : List Bool) : L.Family (R.tower bs.length T) (R.tagBody L.code bs T) := by
  induction bs with
  | nil => exact .constant L.top_formula
  | cons b bs ih =>
    exact ((h.bitBody_family (h.tower_sorted hT bs.length) (h.tower_mode mT bs.length)).code_sign b).code_conj
      (h.recBody_family (h.tower_sorted hT bs.length) (h.tower_mode mT bs.length) ih)

theorem embed_recovery {T t Q : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (bs : List Bool) (ht : HasType P Γ t T) (mt : WellModed γ t .data) (hQ : L.Family T Q) :
    Equivalent P Γ γ ((R.recoveryBody L.code bs.length T Q).instantiate (R.embed L.code bs T t))
      (Q.instantiate t) := by
  induction bs with
  | nil =>
    obtain ⟨s,hs⟩ := L.triple.codomain.1
    exact .refl ((hQ.instantiate ht mt).1 s hs)
  | cons b bs ih =>
    have h₁ := h.embed_typed hT mT bs ht mt
    have h₂ := h.embed_typed hT mT (b::bs) ht mt
    have hc := h.recoveryBody_family hT mT bs.length hQ
    have he := h.emb_recovery (h.tower_sorted hT bs.length) (h.tower_mode mT bs.length) b h₁.1 h₁.2 hc
    have hp : Equivalent P Γ γ
        ((R.recoveryBody L.code (b::bs).length T Q).instantiate (R.embed L.code (b::bs) T t))
        ((R.recoveryBody L.code bs.length T Q).instantiate (R.embed L.code bs T t)) := by
      simpa only [List.length_cons,recoveryBody,recBody_instantiate,embed] using he
    obtain ⟨s,hs⟩ := L.triple.codomain.1
    exact hp.trans ih ((h.recoveryBody_family hT mT (b::bs).length hQ |>.instantiate h₂.1 h₂.2).1 s hs)
      ((hc.instantiate h₁.1 h₁.2).1 s hs) ((hQ.instantiate ht mt).1 s hs)
end Formed
end DoubleCode

theorem LogicCode.conj_instantiate_raise (L : LogicCode S) (A B a : Expr S) :
    ((L.rename Nat.succ).conj A B).instantiate a = L.conj (A.instantiate a) (B.instantiate a) := by
  simp only [Expr.instantiate,LogicCode.conj_subst,LogicCode.instantiate_raise]
namespace LogicSetup
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C)
theorem signed_sign (b c : Bool) {A : Expr S} (hA : L.Formula A)
    (hc : Proves P Γ γ (L.code.sign c A)) :
    Proves P Γ γ (L.code.sign (b == c) (L.code.sign b A)) := by
  cases b <;> cases c <;>
    simp only [Bool.true_beq,Bool.false_beq,Bool.not_false,Bool.not_true,
      LogicCode.sign,ite_true, if_true,ite_false, if_false,Bool.false_eq_true] at hc ⊢ <;>
    first | (exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (A) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) FiniteClassical.Formula.bot)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl; exacts [hc])) | (exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (A) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.atom 0)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl; exacts [hc])) | (exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (A) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.atom 0)] (FiniteClassical.Formula.atom 0) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl; exacts [hc]))
theorem signed_conj (b c : Bool) {A B : Expr S} (hA : L.Formula A) (hB : L.Formula B)
    (ha : Proves P Γ γ (L.code.sign b A)) (hb : Proves P Γ γ (L.code.sign c B)) :
    Proves P Γ γ (L.code.sign (b && c) (L.conj A B)) := by
  cases b <;> cases c <;>
    simp only [Bool.false_and,Bool.true_and,LogicCode.sign,ite_true, if_true,ite_false, if_false,Bool.false_eq_true] at ha hb ⊢ <;>
    first | (exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (A) else if pl_i = 1 then (B) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) FiniteClassical.Formula.bot), (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl; exacts [ha, hb])) | (exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (A) else if pl_i = 1 then (B) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) FiniteClassical.Formula.bot), (FiniteClassical.Formula.atom 1)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl; exacts [ha, hb])) | (exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (A) else if pl_i = 1 then (B) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.atom 0), (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl; exacts [ha, hb])) | (exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (A) else if pl_i = 1 then (B) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.atom 0), (FiniteClassical.Formula.atom 1)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl; exacts [ha, hb]))
end LogicSetup
namespace DoubleCode.Formed
variable {R : DoubleCode S} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J : Set S} (h : R.Formed L I J I)
include h

theorem embed_tag {T t : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (bs cs : List Bool) (hl : bs.length = cs.length) (ht : HasType P Γ t T) (mt : WellModed γ t .data) :
    Proves P Γ γ (L.code.sign (bs == cs)
      ((R.tagBody L.code bs T).instantiate (R.embed L.code cs T t))) := by
  induction bs generalizing cs with
  | nil =>
    cases cs with
    | nil =>
      simp only [beq_self_eq_true,DoubleCode.tagBody,LogicCode.sign,ite_true, if_true,Expr.instantiate_raise]
      change Proves P Γ γ L.top
      exact L.top_intro
    | cons c cs => simp at hl
  | cons b bs ih =>
    cases cs with
    | nil => simp at hl
    | cons c cs =>
      have hlen : bs.length = cs.length := Nat.succ.inj hl
      have hp := ih cs hlen
      have hv := h.embed_typed hT mT cs ht mt
      have hv' : HasType P Γ (R.embed L.code cs T t) (R.tower bs.length T) := by rw [hlen]; exact hv.1
      have hq := h.tagBody_family hT mT bs
      have he := h.emb_recovery (h.tower_sorted hT bs.length) (h.tower_mode mT bs.length) c hv' hv.2 hq
      have hb := h.emb_bit (h.tower_sorted hT bs.length) (h.tower_mode mT bs.length) c hv' hv.2
      have hw := h.emb_typed (h.tower_sorted hT bs.length) (h.tower_mode mT bs.length) c hv' hv.2
      have hf := h.bit_formula (h.tower_sorted hT bs.length) (h.tower_mode mT bs.length) hw.1 hw.2
      have hr := h.rec_formula (h.tower_sorted hT bs.length) (h.tower_mode mT bs.length) hw.1 hw.2 hq
      have hqt := hq.instantiate hv' hv.2
      simp only [DoubleCode.tagBody,DoubleCode.embed,← hlen,
        LogicCode.conj_instantiate_raise,LogicCode.sign_instantiate_raise,
        DoubleCode.bitBody_instantiate,DoubleCode.recBody_instantiate]
      change Proves P Γ γ (L.code.sign ((b::bs) == (c::cs)) (L.conj
        (L.code.sign b (R.bit L.code (R.tower bs.length T)
          (R.emb L.code c (R.tower bs.length T) (R.embed L.code cs T t))))
        (R.recover L.code (R.tower bs.length T)
          (R.emb L.code c (R.tower bs.length T) (R.embed L.code cs T t))
          (R.tagBody L.code bs T))))
      have hbit := L.signed_sign b c hf hb
      have hrec := (L.sign_equivalent (bs == cs) hr hqt he).2.prove hp
      have hh := L.signed_conj (b == c) (bs == cs) (L.sign_formula b hf) hr hbit hrec
      simpa only [List.cons_beq_cons] using hh
end DoubleCode.Formed

theorem queryBits_length (q : Fin 9) : (queryBits q).length = 4 := rfl
theorem queryBits_injective : Function.Injective queryBits := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [queryBits,Nat.testBit]

theorem queryTag_ne_zero (t : Fin 8) : queryTag t ≠ 0 := by
  intro h; have := congrArg Fin.val h; simp only [queryTag,Fin.val_zero] at this; omega

namespace DoubleCode
variable (R : DoubleCode S)
theorem tagged_subst (L : LogicCode S) (q : Fin 9) (T t : Expr S) (σ : Nat → Expr S) :
    (R.tagged L q T t).subst σ = (R.subst σ).tagged (L.subst σ) q (T.subst σ) (t.subst σ) :=
  R.embed_subst L (queryBits q) T t σ

theorem embedBody_instantiate (L : LogicCode S) (q : Fin 9) (T t : Expr S) :
    (R.embedBody L q T).instantiate t = R.tagged L q T t := by
  simp only [embedBody,Expr.instantiate,tagged_subst,instantiate_raise,LogicCode.instantiate_raise,
    Expr.subst_lift_single,Expr.subst,Expr.single]

theorem decoderBody_instantiate (L : LogicCode S) (T bp c : Expr S) :
    (R.decoderBody L T bp).instantiate c = R.first.observe (R.big T) bp (R.tagged L 0 T c) := by
  simp only [decoderBody,Expr.compose_instantiate,embedBody_instantiate,DataWrapper.evalCallback_instantiate]

namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H)
include h

theorem tagged_typed {T c : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (q : Fin 9) (hc : HasType P Γ c T) (mc : WellModed γ c .data) :
    HasType P Γ (R.tagged L.code q T c) (R.big T) ∧ WellModed γ (R.tagged L.code q T c) .data :=
  h.embed_typed hT mT (queryBits q) hc mc

theorem bp_sorted {T : Expr S} (hT : SortedAt P Γ T I) : SortedAt P Γ (R.bpType T) J :=
  h.first.sorted (h.tower_sorted hT 4)
theorem bp_mode {T : Expr S} (mT : WellModed γ T .data) : WellModed γ (R.bpType T) .data :=
  h.first.mode (h.tower_mode mT 4)
theorem param_sorted {T : Expr S} (hT : SortedAt P Γ T I) : SortedAt P Γ (R.paramType T) I :=
  h.second.sorted (h.bp_sorted hT)
theorem param_mode {T : Expr S} (mT : WellModed γ T .data) : WellModed γ (R.paramType T) .data :=
  h.second.mode (h.bp_mode mT)

include hU

theorem encodeBody_family {T p : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (t : Fin 8) (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data) :
    L.Family (R.big T) (R.encodeBody U L.code t T p) :=
  ((h.tagBody_family hT mT (queryBits 0)).code_conj
    (h.recoveryBody_family hT mT 4 (hU.evalCallback_family hT mT hp mp))).code_disj
      (h.tagBody_family hT mT (queryBits (queryTag t)))

theorem encode_typed {T p : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (t : Fin 8) (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data) :
    HasType P Γ (R.encode U L.code t T p) (R.bpType T) ∧ WellModed γ (R.encode U L.code t T p) .data :=
  (h.first.sound (h.tower_sorted hT 4) (h.tower_mode mT 4)).1 _ (h.encodeBody_family hU hT mT t hp mp)

omit hU in
 theorem embedBody_map {T : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (q : Fin 9) {s : S} (hs : HasType P Γ T (.sort s)) :
    DataMap P Γ γ T (R.big T) (R.embedBody L.code q T) := by
  let e : Embedding P Γ γ (T :: Γ) (modeCons .data γ) := Embedding.cons hs Mode.data
  have hh := (h.rename e).tagged_typed (fun s hs => e.typing (hT s hs)) (e.moded mT) q (HasType.var hs) (.var 0)
  simpa only [DataMap,embedBody,LogicSetup.code_rename,big,tower_rename,e,Embedding.cons] using hh

omit hU in
 theorem decoderBody_family {T bp : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hb : HasType P Γ bp (R.bpType T)) (mb : WellModed γ bp .data)
    {s : S} (hs : HasType P Γ T (.sort s)) : L.Family T (R.decoderBody L.code T bp) :=
  (h.first.evalCallback_family (h.tower_sorted hT 4) (h.tower_mode mT 4) hb mb).compose
    (h.embedBody_map hT mT 0 hs) hs

 theorem decode_typed {T bp : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hb : HasType P Γ bp (R.bpType T)) (mb : WellModed γ bp .data)
    {s : S} (hs : HasType P Γ T (.sort s)) :
    HasType P Γ (R.decode U L.code T bp) (U.apply T) ∧ WellModed γ (R.decode U L.code T bp) .data :=
  (hU.sound hT mT).1 _ (h.decoderBody_family hT mT hb mb hs)
end Formed
end DoubleCode

end PureTypeSystem.Labelled

namespace PureTypeSystem.Labelled.LogicSetup
universe u
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {γ : Nat → Mode}
    {C : Set (Set S)} (L : LogicSetup P Γ γ C)
theorem code_bottom : L.code.bottom = L.bottom := rfl
theorem code_top : L.code.top = L.top := rfl
theorem code_conj (A B : Expr S) : L.code.conj A B = L.conj A B := rfl
theorem code_disj (A B : Expr S) : L.code.disj A B = L.disj A B := rfl
end PureTypeSystem.Labelled.LogicSetup

namespace PureTypeSystem.Labelled.LogicSetup
universe u
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {γ : Nat → Mode}
  {C : Set (Set S)} (L : LogicSetup P Γ γ C) {A B D E F : Expr S}

theorem cond_yes (hA : L.Formula A) (hB : L.Formula B) (hD : L.Formula D)
    (hE : L.Formula E) (he : Equivalent P Γ γ E (L.code.cond A B D))
    (ha : Proves P Γ γ A) : Equivalent P Γ γ E B := by
  apply L.equivalent_of_iff hE hB
  exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (E) else if pl_i = 1 then (A) else if pl_i = 2 then (B) else if pl_i = 3 then (D) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 3) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 3) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot), (FiniteClassical.Formula.atom 1)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.atom 2)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl; exacts [((L).iff_of_equivalent (hE) (cond_formula L hA hB hD) he), ha])

theorem cond_no (hA : L.Formula A) (hB : L.Formula B) (hD : L.Formula D)
    (hE : L.Formula E) (he : Equivalent P Γ γ E (L.code.cond A B D))
    (ha : Proves P Γ γ (L.neg A)) : Equivalent P Γ γ E D := by
  apply L.equivalent_of_iff hE hD
  exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (E) else if pl_i = 1 then (A) else if pl_i = 2 then (B) else if pl_i = 3 then (D) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 3) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 3) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot), (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.atom 3)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 3) (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl; exacts [((L).iff_of_equivalent (hE) (cond_formula L hA hB hD) he), ha])

theorem equivalent_bottom_neg (hE : L.Formula E) (he : Equivalent P Γ γ E L.bottom) :
    Proves P Γ γ (L.neg E) := by
  exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (E) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp FiniteClassical.Formula.bot (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl; exacts [((L).iff_of_equivalent (hE) (bottom_formula L) he)])

end PureTypeSystem.Labelled.LogicSetup

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Pairs
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate _root_.OAI.PureTypeSystem.instCountableExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled

section
universe u
variable {S : Type u} {P : Specification S}

theorem queryBits_beq (q r : Fin 9) : (queryBits q == queryBits r) = (q == r) := by
  by_cases he : q = r
  · subst r; simp
  · have hn : queryBits q ≠ queryBits r := fun h => he (queryBits_injective h)
    simp only [beq_eq_false_iff_ne.mpr he,beq_eq_false_iff_ne.mpr hn]
theorem queryTag_injective : Function.Injective queryTag := by
  intro t u h
  apply Fin.ext
  have he := congrArg Fin.val h
  simp only [queryTag] at he
  omega

namespace DoubleCode.Formed
variable {R : DoubleCode S} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H)
include h

theorem tagged_tag {T c : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (q r : Fin 9) (hc : HasType P Γ c T) (mc : WellModed γ c .data) :
    Proves P Γ γ (L.code.sign (q == r)
      ((R.tagBody L.code (queryBits q) T).instantiate (R.tagged L.code r T c))) := by
  simpa only [queryBits_beq,DoubleCode.tagged] using
    h.embed_tag hT mT (queryBits q) (queryBits r) rfl hc mc

include hU

theorem encode_evaluation {T p v : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (t : Fin 8) (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data)
    (hv : HasType P Γ v (R.big T)) (mv : WellModed γ v .data) :
    Equivalent P Γ γ (R.first.observe (R.big T) (R.encode U L.code t T p) v)
      (L.disj (L.conj
        ((R.tagBody L.code (queryBits 0) T).instantiate v)
        ((R.recoveryBody L.code 4 T (U.evalCallback T p)).instantiate v))
        ((R.tagBody L.code (queryBits (queryTag t)) T).instantiate v)) := by
  have he := h.first.cancellation (h.tower_sorted hT 4) (h.tower_mode mT 4)
    (h.encodeBody_family hU hT mT t hp mp) ⟨hv,mv⟩
  simpa only [DoubleCode.encode,DataWrapper.cancelFormula,ite_true, if_true,DoubleCode.encodeBody,
    Expr.instantiate,LogicCode.disj_subst,LogicCode.conj_subst,LogicCode.instantiate_raise,
    LogicSetup.code_disj,LogicSetup.code_conj,DoubleCode.big] using he

theorem encode_mark {T p c₀ : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (t u : Fin 8) (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data)
    (hc : HasType P Γ c₀ T) (mc : WellModed γ c₀ .data) :
    Proves P Γ γ (L.code.sign (t == u) (R.mark L.code u T c₀ (R.encode U L.code t T p))) := by
  have hv := h.tagged_typed hT mT (queryTag u) hc mc
  have he := h.encode_evaluation hU hT mT t hp mp hv.1 hv.2
  have h₀ := h.tagged_tag hT mT 0 (queryTag u) hc mc
  have hq := h.tagged_tag hT mT (queryTag t) (queryTag u) hc mc
  have hd := h.encode_typed hU hT mT t hp mp
  have hf := (h.first.sound (h.tower_sorted hT 4) (h.tower_mode mT 4)).2 _ _ hd.1 hd.2 ⟨hv.1,hv.2⟩
  have f₀ := (h.tagBody_family hT mT (queryBits 0)).instantiate hv.1 hv.2
  have fr := (h.recoveryBody_family hT mT 4 (hU.evalCallback_family hT mT hp mp)).instantiate hv.1 hv.2
  have fq := (h.tagBody_family hT mT (queryBits (queryTag t))).instantiate hv.1 hv.2
  have zne : (0 : Fin 9) ≠ queryTag u := (queryTag_ne_zero u).symm
  simp only [beq_eq_false_iff_ne.mpr zne,LogicCode.sign,Bool.false_eq_true,ite_false, if_false] at h₀
  by_cases htu : t = u
  · subst u
    simp only [beq_self_eq_true,LogicCode.sign,ite_true, if_true] at hq ⊢
    change Proves P Γ γ (R.first.observe _ _ _)
    exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (R.first.observe (R.big T) (R.encode U L.code t T p) (R.tagged L.code (queryTag t) T c₀)) else if pl_i = 1 then ((R.tagBody L.code (queryBits 0) T).instantiate (R.tagged L.code (queryTag t) T c₀)) else if pl_i = 2 then ((R.recoveryBody L.code 4 T (U.evalCallback T p)).instantiate (R.tagged L.code (queryTag t) T c₀)) else if pl_i = 3 then ((R.tagBody L.code (queryBits (queryTag t)) T).instantiate (R.tagged L.code (queryTag t) T c₀)) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 3) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 3) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot), (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot), (FiniteClassical.Formula.atom 3)] (FiniteClassical.Formula.atom 0) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl | rfl; exacts [((L).iff_of_equivalent (hf) (LogicSetup.disj_formula L (LogicSetup.conj_formula L f₀ fr) fq) he), h₀, hq])
  · have qne : queryTag t ≠ queryTag u := fun hh => htu (queryTag_injective hh)
    simp only [beq_eq_false_iff_ne.mpr htu,beq_eq_false_iff_ne.mpr qne,LogicCode.sign,Bool.false_eq_true,ite_false, if_false] at hq ⊢
    change Proves P Γ γ (L.neg (R.first.observe _ _ _))
    exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (R.first.observe (R.big T) (R.encode U L.code t T p) (R.tagged L.code (queryTag u) T c₀)) else if pl_i = 1 then ((R.tagBody L.code (queryBits 0) T).instantiate (R.tagged L.code (queryTag u) T c₀)) else if pl_i = 2 then ((R.recoveryBody L.code 4 T (U.evalCallback T p)).instantiate (R.tagged L.code (queryTag u) T c₀)) else if pl_i = 3 then ((R.tagBody L.code (queryBits (queryTag t)) T).instantiate (R.tagged L.code (queryTag u) T c₀)) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 3) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 3) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot), (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot), (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 3) FiniteClassical.Formula.bot)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl | rfl; exacts [((L).iff_of_equivalent (hf) (LogicSetup.disj_formula L (LogicSetup.conj_formula L f₀ fr) fq) he), h₀, hq])

theorem encode_payload {T p c : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (t : Fin 8) (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data)
    (hc : HasType P Γ c T) (mc : WellModed γ c .data) :
    Equivalent P Γ γ (R.first.observe (R.big T) (R.encode U L.code t T p) (R.tagged L.code 0 T c))
      (U.observe T p c) := by
  have hv := h.tagged_typed hT mT 0 hc mc
  have he := h.encode_evaluation hU hT mT t hp mp hv.1 hv.2
  have h₀ := h.tagged_tag hT mT 0 0 hc mc
  have hq := h.tagged_tag hT mT (queryTag t) 0 hc mc
  have hrec := h.embed_recovery hT mT (queryBits 0) hc mc (hU.evalCallback_family hT mT hp mp)
  simp only [DataWrapper.evalCallback_instantiate,queryBits_length] at hrec
  change Equivalent P Γ γ ((R.recoveryBody L.code 4 T (U.evalCallback T p)).instantiate (R.tagged L.code 0 T c)) (U.observe T p c) at hrec
  have hd := h.encode_typed hU hT mT t hp mp
  have hf := (h.first.sound (h.tower_sorted hT 4) (h.tower_mode mT 4)).2 _ _ hd.1 hd.2 ⟨hv.1,hv.2⟩
  have f₀ := (h.tagBody_family hT mT (queryBits 0)).instantiate hv.1 hv.2
  have fr := (h.recoveryBody_family hT mT 4 (hU.evalCallback_family hT mT hp mp)).instantiate hv.1 hv.2
  have fq := (h.tagBody_family hT mT (queryBits (queryTag t))).instantiate hv.1 hv.2
  have fc := (hU.sound hT mT).2 _ _ hp mp ⟨hc,mc⟩
  simp only [beq_self_eq_true,LogicCode.sign,ite_true, if_true] at h₀
  simp only [beq_eq_false_iff_ne.mpr (queryTag_ne_zero t),LogicCode.sign,Bool.false_eq_true,ite_false, if_false] at hq
  apply L.equivalent_of_iff hf fc
  exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (R.first.observe (R.big T) (R.encode U L.code t T p) (R.tagged L.code 0 T c)) else if pl_i = 1 then ((R.tagBody L.code (queryBits 0) T).instantiate (R.tagged L.code 0 T c)) else if pl_i = 2 then ((R.recoveryBody L.code 4 T (U.evalCallback T p)).instantiate (R.tagged L.code 0 T c)) else if pl_i = 3 then ((R.tagBody L.code (queryBits (queryTag t)) T).instantiate (R.tagged L.code 0 T c)) else if pl_i = 4 then (U.observe T p c) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 3) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 3) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot), (FiniteClassical.Formula.atom 1), (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 3) FiniteClassical.Formula.bot), (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) (FiniteClassical.Formula.atom 4)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 4) (FiniteClassical.Formula.atom 2)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.atom 4)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 4) (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl | rfl | rfl; exacts [((L).iff_of_equivalent (hf) (LogicSetup.disj_formula L (LogicSetup.conj_formula L f₀ fr) fq) he), h₀, hq, ((L).iff_of_equivalent (fr) (fc) hrec)])

theorem decode_encode {T p c : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (t : Fin 8) (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data)
    (hc : HasType P Γ c T) (mc : WellModed γ c .data) {s : S} (hs : HasType P Γ T (.sort s)) :
    Equivalent P Γ γ (U.observe T (R.decode U L.code T (R.encode U L.code t T p)) c) (U.observe T p c) := by
  have hd := h.encode_typed hU hT mT t hp mp
  have hQ := h.decoderBody_family hT mT hd.1 hd.2 hs
  have hdec := h.decode_typed hU hT mT hd.1 hd.2 hs
  have he := hU.cancellation hT mT hQ ⟨hc,mc⟩
  have he' : Equivalent P Γ γ (U.observe T (R.decode U L.code T (R.encode U L.code t T p)) c)
      (R.first.observe (R.big T) (R.encode U L.code t T p) (R.tagged L.code 0 T c)) := by
    simpa only [DataWrapper.cancelFormula,ite_true, if_true,DoubleCode.decoderBody_instantiate,DoubleCode.decode] using he
  have he₂ := h.encode_payload hU hT mT t hp mp hc mc
  have h₁ := (hU.sound hT mT).2 _ _ hdec.1 hdec.2 ⟨hc,mc⟩
  have h₂ := hQ.instantiate hc mc
  have h₃ := (hU.sound hT mT).2 _ _ hp mp ⟨hc,mc⟩
  obtain ⟨r,hr⟩ := L.triple.codomain.1
  exact he'.trans he₂ (h₁.1 r hr) (by simpa only [DoubleCode.decoderBody_instantiate] using h₂.1 r hr) (h₃.1 r hr)
end DoubleCode.Formed

namespace DoubleCode
variable (R : DoubleCode S)
theorem bitBody_subst (L : LogicCode S) (T : Expr S) (σ : Nat → Expr S) :
    (R.bitBody L T).subst (Expr.liftSub σ) =
      (R.subst σ).bitBody (L.subst σ) (T.subst σ) := by
  simp only [bitBody,bit_subst,subst_rename,rename_subst,LogicCode.subst_rename,
    LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl

theorem recBody_subst (L : LogicCode S) (T Q : Expr S) (σ : Nat → Expr S) :
    (R.recBody L T Q).subst (Expr.liftSub σ) =
      (R.subst σ).recBody (L.subst σ) (T.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [recBody,rec_subst,subst_rename,rename_subst,LogicCode.subst_rename,
    LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  congr 1
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Function.comp_apply,Expr.liftSub,Expr.liftRen,PureTypeSystem.Expr.liftRen,Expr.rename_comp]
    congr 1

theorem recoveryBody_subst (L : LogicCode S) (n : Nat) (T Q : Expr S) (σ : Nat → Expr S) :
    (R.recoveryBody L n T Q).subst (Expr.liftSub σ) =
      (R.subst σ).recoveryBody (L.subst σ) n (T.subst σ) (Q.subst (Expr.liftSub σ)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [recoveryBody,recBody_subst,tower_subst,ih]
theorem tagBody_subst (L : LogicCode S) (bs : List Bool) (T : Expr S) (σ : Nat → Expr S) :
    (R.tagBody L bs T).subst (Expr.liftSub σ) =
      (R.subst σ).tagBody (L.subst σ) bs (T.subst σ) := by
  induction bs with
  | nil =>
    simp only [tagBody,Expr.subst_rename,Expr.rename_subst,← LogicCode.top_subst]
    rfl
  | cons b bs ih =>
    simp only [tagBody,LogicCode.conj_subst,LogicCode.sign_subst,LogicCode.subst_rename,
      LogicCode.rename_subst,bitBody_subst,recBody_subst,tower_subst,ih]
    rfl

theorem big_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.big T).rename ρ = (R.rename ρ).big (T.rename ρ) := R.tower_rename 4 T ρ
theorem big_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.big T).subst σ = (R.subst σ).big (T.subst σ) := R.tower_subst 4 T σ
theorem bpType_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.bpType T).rename ρ = (R.rename ρ).bpType (T.rename ρ) := by
  simp only [bpType,DataWrapper.apply_rename,big_rename]; rfl
theorem bpType_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.bpType T).subst σ = (R.subst σ).bpType (T.subst σ) := by
  simp only [bpType,DataWrapper.apply_subst,big_subst]; rfl

theorem embedBody_subst (L : LogicCode S) (q : Fin 9) (T : Expr S) (σ : Nat → Expr S) :
    (R.embedBody L q T).subst (Expr.liftSub σ) =
      (R.subst σ).embedBody (L.subst σ) q (T.subst σ) := by
  simp only [embedBody,tagged_subst,subst_rename,rename_subst,LogicCode.subst_rename,
    LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl

theorem decoderBody_subst (L : LogicCode S) (T bp : Expr S) (σ : Nat → Expr S) :
    (R.decoderBody L T bp).subst (Expr.liftSub σ) =
      (R.subst σ).decoderBody (L.subst σ) (T.subst σ) (bp.subst σ) := by
  simp only [decoderBody,Expr.compose_subst,DataWrapper.evalCallback_subst,embedBody_subst,big_subst]
  rfl

theorem decode_subst (U : DataWrapper S true) (L : LogicCode S) (T bp : Expr S) (σ : Nat → Expr S) :
    (R.decode U L T bp).subst σ =
      (R.subst σ).decode (U.subst σ) (L.subst σ) (T.subst σ) (bp.subst σ) := by
  simp only [decode,DataWrapper.build_subst,DataWrapper.argSub,ite_true, if_true,decoderBody_subst]

theorem decodeMap_instantiate (U : DataWrapper S true) (L : LogicCode S) (T bp : Expr S) :
    (R.decodeMap U L T).instantiate bp = R.decode U L T bp := by
  simp only [decodeMap,Expr.instantiate,decode_subst,instantiate_raise,DataWrapper.instantiate_raise,
    LogicCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]

namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H)
include h hU
 theorem decodeMap_typed {T : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    {s r : S} (hs : HasType P Γ T (.sort s)) (hr : HasType P Γ (R.bpType T) (.sort r)) :
    DataMap P Γ γ (R.bpType T) (U.apply T) (R.decodeMap U L.code T) := by
  let e : Embedding P Γ γ (R.bpType T :: Γ) (modeCons .data γ) := Embedding.cons hr Mode.data
  have hh := (h.rename e).decode_typed (hU.rename e)
    (fun s hs => e.typing (hT s hs)) (e.moded mT)
    (by simpa only [bpType_rename,e,Embedding.cons] using HasType.var hr) (.var 0) (e.typing hs)
  simpa only [DataMap,decodeMap,LogicSetup.code_rename,DataWrapper.apply_rename,e,Embedding.cons] using hh
end Formed

theorem markBody_instantiate (L : LogicCode S) (t : Fin 8) (T c₀ bp : Expr S) :
    (R.markBody L t T c₀).instantiate bp = R.mark L t T c₀ bp := by
  simp only [markBody,DataWrapper.contraCallback_instantiate,mark]
theorem pointBody_instantiate (U : DataWrapper S true) (L : LogicCode S) (T c₀ c bp : Expr S) :
    (R.pointBody U L T c₀ c).instantiate bp =
      L.conj (R.mark L 7 T c₀ bp) (U.observe T (R.decode U L T bp) c) := by
  simp only [pointBody,LogicCode.conj_instantiate_raise,markBody_instantiate,Expr.compose_instantiate,
    decodeMap_instantiate,DataWrapper.contraCallback_instantiate]

namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H)
include h
 theorem bpBottom_typed {T : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) :
    HasType P Γ (R.bpBottom L.code T) (R.bpType T) ∧ WellModed γ (R.bpBottom L.code T) .data :=
  (h.first.sound (h.tower_sorted hT 4) (h.tower_mode mT 4)).1 _ (.constant L.bottom_formula)
 theorem dummy_typed {T : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) :
    HasType P Γ (R.dummy L.code T) (R.paramType T) ∧ WellModed γ (R.dummy L.code T) .data :=
  (h.second.sound (h.bp_sorted hT) (h.bp_mode mT)).1 _ (.constant L.top_formula)
 theorem isDummy_formula {T o : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (ho : HasType P Γ o (R.paramType T)) (mo : WellModed γ o .data) :
    L.Formula (R.isDummy L.code T o) :=
  (h.second.sound (h.bp_sorted hT) (h.bp_mode mT)).2 _ _ ho mo (h.bpBottom_typed hT mT)
 theorem markBody_family {T c₀ : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (t : Fin 8) (hc : HasType P Γ c₀ T) (mc : WellModed γ c₀ .data) :
    L.Family (R.bpType T) (R.markBody L.code t T c₀) := by
  have hv := h.tagged_typed hT mT (queryTag t) hc mc
  exact h.first.contraCallback_family (h.tower_sorted hT 4) (h.tower_mode mT 4) hv.1 hv.2

include hU
 theorem pointBody_family {T c₀ c : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (h₀ : HasType P Γ c₀ T) (m₀ : WellModed γ c₀ .data)
    (hc : HasType P Γ c T) (mc : WellModed γ c .data)
    {s r : S} (hs : HasType P Γ T (.sort s)) (hr : HasType P Γ (R.bpType T) (.sort r)) :
    L.Family (R.bpType T) (R.pointBody U L.code T c₀ c) :=
  (h.markBody_family hT mT 7 h₀ m₀).code_conj
    ((hU.contraCallback_family hT mT hc mc).compose (h.decodeMap_typed hU hT mT hs hr) hr)
 theorem point_typed {T c₀ c : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (h₀ : HasType P Γ c₀ T) (m₀ : WellModed γ c₀ .data)
    (hc : HasType P Γ c T) (mc : WellModed γ c .data)
    {s r : S} (hs : HasType P Γ T (.sort s)) (hr : HasType P Γ (R.bpType T) (.sort r)) :
    HasType P Γ (R.point U L.code T c₀ c) (R.paramType T) ∧
      WellModed γ (R.point U L.code T c₀ c) .data :=
  (h.second.sound (h.bp_sorted hT) (h.bp_mode mT)).1 _ (h.pointBody_family hU hT mT h₀ m₀ hc mc hs hr)
end Formed
end DoubleCode

namespace DoubleCode.Formed
variable {R : DoubleCode S} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H)
include h
 theorem dummy_law {T : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) :
    Proves P Γ γ (R.isDummy L.code T (R.dummy L.code T)) := by
  have ht := h.bpBottom_typed hT mT
  have hh := h.second.cancellation (h.bp_sorted hT) (h.bp_mode mT) (.constant L.top_formula) ht
  have he : Equivalent P Γ γ (R.isDummy L.code T (R.dummy L.code T)) L.top := by
    simpa only [DataWrapper.cancelFormula,ite_true, if_true,Expr.instantiate_raise,
      DoubleCode.isDummy,DoubleCode.dummy,LogicSetup.code_top] using hh
  exact he.2.prove L.top_intro

 theorem bottom_mark {T c₀ : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (t : Fin 8) (hc : HasType P Γ c₀ T) (mc : WellModed γ c₀ .data) :
    Proves P Γ γ (L.neg (R.mark L.code t T c₀ (R.bpBottom L.code T))) := by
  have hv := h.tagged_typed hT mT (queryTag t) hc mc
  have he₀ := h.first.cancellation (h.tower_sorted hT 4) (h.tower_mode mT 4)
    (.constant L.bottom_formula) hv
  have he : Equivalent P Γ γ (R.mark L.code t T c₀ (R.bpBottom L.code T)) L.bottom := by
    simpa only [DataWrapper.cancelFormula,ite_true, if_true,Expr.instantiate_raise,
      DoubleCode.mark,DoubleCode.bpBottom,DoubleCode.big,LogicSetup.code_bottom] using he₀
  have hb := h.bpBottom_typed hT mT
  have hf := (h.first.sound (h.tower_sorted hT 4) (h.tower_mode mT 4)).2 _ _ hb.1 hb.2 hv
  exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (R.mark L.code t T c₀ (R.bpBottom L.code T)) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp FiniteClassical.Formula.bot (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl; exacts [((L).iff_of_equivalent (hf) (LogicSetup.bottom_formula L) he)])

include hU
 theorem point_evaluation {T c₀ c bp : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (h₀ : HasType P Γ c₀ T) (m₀ : WellModed γ c₀ .data)
    (hc : HasType P Γ c T) (mc : WellModed γ c .data)
    {s r : S} (hs : HasType P Γ T (.sort s)) (hr : HasType P Γ (R.bpType T) (.sort r))
    (hb : HasType P Γ bp (R.bpType T)) (mb : WellModed γ bp .data) :
    Equivalent P Γ γ (R.second.observe (R.bpType T) (R.point U L.code T c₀ c) bp)
      (L.conj (R.mark L.code 7 T c₀ bp) (U.observe T (R.decode U L.code T bp) c)) := by
  have hh := h.second.cancellation (h.bp_sorted hT) (h.bp_mode mT)
    (h.pointBody_family hU hT mT h₀ m₀ hc mc hs hr) ⟨hb,mb⟩
  simpa only [DataWrapper.cancelFormula,ite_true, if_true,DoubleCode.pointBody_instantiate,DoubleCode.point,LogicSetup.code_conj] using hh

 theorem point_not_dummy {T c₀ c : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (h₀ : HasType P Γ c₀ T) (m₀ : WellModed γ c₀ .data)
    (hc : HasType P Γ c T) (mc : WellModed γ c .data)
    {s r : S} (hs : HasType P Γ T (.sort s)) (hr : HasType P Γ (R.bpType T) (.sort r)) :
    Proves P Γ γ (L.neg (R.isDummy L.code T (R.point U L.code T c₀ c))) := by
  have hb := h.bpBottom_typed hT mT
  have he := h.point_evaluation hU hT mT h₀ m₀ hc mc hs hr hb.1 hb.2
  have hn := h.bottom_mark hT mT 7 h₀ m₀
  have hp := h.point_typed hU hT mT h₀ m₀ hc mc hs hr
  have hD := h.isDummy_formula hT mT hp.1 hp.2
  have hmark₀ := (h.markBody_family hT mT 7 h₀ m₀).instantiate hb.1 hb.2
  have hmark : L.Formula (R.mark L.code 7 T c₀ (R.bpBottom L.code T)) := by
    simpa only [DoubleCode.markBody_instantiate] using hmark₀
  have hd := h.decode_typed hU hT mT hb.1 hb.2 hs
  have hobs := (hU.sound hT mT).2 _ _ hd.1 hd.2 ⟨hc,mc⟩
  change Proves P Γ γ (L.neg (R.second.observe _ _ _))
  exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (R.second.observe (R.bpType T) (R.point U L.code T c₀ c) (R.bpBottom L.code T)) else if pl_i = 1 then (R.mark L.code 7 T c₀ (R.bpBottom L.code T)) else if pl_i = 2 then (U.observe T (R.decode U L.code T (R.bpBottom L.code T)) c) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot), (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl; exacts [((L).iff_of_equivalent (hD) (LogicSetup.conj_formula L hmark hobs) he), hn])

 theorem point_query {T c₀ c p : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (h₀ : HasType P Γ c₀ T) (m₀ : WellModed γ c₀ .data)
    (hc : HasType P Γ c T) (mc : WellModed γ c .data)
    {s r : S} (hs : HasType P Γ T (.sort s)) (hr : HasType P Γ (R.bpType T) (.sort r))
    (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data) :
    Equivalent P Γ γ (R.query U L.code 7 T (R.point U L.code T c₀ c) p) (U.observe T p c) := by
  have hb := h.encode_typed hU hT mT 7 hp mp
  have he := h.point_evaluation hU hT mT h₀ m₀ hc mc hs hr hb.1 hb.2
  have hm₀ := h.encode_mark hU hT mT 7 7 hp mp h₀ m₀
  have hm : Proves P Γ γ (R.mark L.code 7 T c₀ (R.encode U L.code 7 T p)) := by
    simpa only [beq_self_eq_true,LogicCode.sign,ite_true, if_true] using hm₀
  have hd := h.decode_encode hU hT mT 7 hp mp hc mc hs
  have hpoint := h.point_typed hU hT mT h₀ m₀ hc mc hs hr
  have hH := (h.second.sound (h.bp_sorted hT) (h.bp_mode mT)).2 _ _ hpoint.1 hpoint.2 hb
  have hE := (hU.sound hT mT).2 _ _ hp mp ⟨hc,mc⟩
  have hdc := h.decode_typed hU hT mT hb.1 hb.2 hs
  have hE' := (hU.sound hT mT).2 _ _ hdc.1 hdc.2 ⟨hc,mc⟩
  have hmF₀ := (h.markBody_family hT mT 7 h₀ m₀).instantiate hb.1 hb.2
  have hmF : L.Formula (R.mark L.code 7 T c₀ (R.encode U L.code 7 T p)) := by
    simpa only [DoubleCode.markBody_instantiate] using hmF₀
  apply L.equivalent_of_iff hH hE
  exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (R.second.observe (R.bpType T) (R.point U L.code T c₀ c) (R.encode U L.code 7 T p)) else if pl_i = 1 then (R.mark L.code 7 T c₀ (R.encode U L.code 7 T p)) else if pl_i = 2 then (U.observe T (R.decode U L.code T (R.encode U L.code 7 T p)) c) else if pl_i = 3 then (U.observe T p c) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot), (FiniteClassical.Formula.atom 1), (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) (FiniteClassical.Formula.atom 3)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 3) (FiniteClassical.Formula.atom 2)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.atom 3)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 3) (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl | rfl; exacts [((L).iff_of_equivalent (hH) (LogicSetup.conj_formula L hmF hE') he), hm, ((L).iff_of_equivalent (hE') (hE) hd)])
end DoubleCode.Formed

namespace DoubleCode
variable (R : DoubleCode S)

theorem bundleBody_instantiate (L : LogicCode S) (A d m y f : Expr S) :
    (R.bundleBody L A d m y).instantiate f =
      L.cond (R.first.observe A f d) (R.first.observe A f m) (R.first.observe A f y) := by
  simp only [bundleBody,Expr.instantiate,LogicCode.cond_subst,LogicCode.instantiate_raise,
    DataWrapper.contraCallback,DataWrapper.observe_subst,DataWrapper.instantiate_raise,
    Expr.subst_lift_single,DataWrapper.argSub,Bool.not_true,Bool.false_eq_true,ite_false, if_false,Expr.subst,Expr.single]

theorem accessBody_instantiate (L : LogicCode S) (A guard w fi o : Expr S) :
    (R.accessBody L A guard w fi).instantiate o =
      L.cond (guard.instantiate o) L.top
        (R.second.observe (R.first.apply A) w (fi.instantiate o)) := by
  have he : ((L.rename Nat.succ).cond guard (L.top.rename Nat.succ)
      ((R.second.evalCallback (R.first.apply A) w).compose fi)).instantiate o =
      L.cond (guard.instantiate o) L.top
        (((R.second.evalCallback (R.first.apply A) w).compose fi).instantiate o) := by
    simp only [Expr.instantiate,LogicCode.cond_subst,LogicCode.instantiate_raise,Expr.subst_lift_single]
  exact he.trans (by rw [Expr.compose_instantiate,DataWrapper.evalCallback_instantiate])

namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J : Set S} (h : R.Formed L I J I)
include h
 theorem bundleBody_family {A d m y : Expr S} (hA : SortedAt P Γ A I) (mA : WellModed γ A .data)
    (hd : HasType P Γ d A) (md : WellModed γ d .data)
    (hm : HasType P Γ m A) (mm : WellModed γ m .data)
    (hy : HasType P Γ y A) (my : WellModed γ y .data) :
    L.Family (R.first.apply A) (R.bundleBody L.code A d m y) :=
  (h.first.contraCallback_family hA mA hd md).code_cond
    (h.first.contraCallback_family hA mA hm mm) (h.first.contraCallback_family hA mA hy my)
 theorem bundle_typed {A d m y : Expr S} (hA : SortedAt P Γ A I) (mA : WellModed γ A .data)
    (hd : HasType P Γ d A) (md : WellModed γ d .data)
    (hm : HasType P Γ m A) (mm : WellModed γ m .data)
    (hy : HasType P Γ y A) (my : WellModed γ y .data) :
    HasType P Γ (R.bundle L.code A d m y) (R.carrier A) ∧
      WellModed γ (R.bundle L.code A d m y) .data :=
  (h.second.sound (h.first.sorted hA) (h.first.mode mA)).1 _
    (h.bundleBody_family hA mA hd md hm mm hy my)
 theorem bundle_evaluation {A d m y f : Expr S} (hA : SortedAt P Γ A I) (mA : WellModed γ A .data)
    (hd : HasType P Γ d A) (md : WellModed γ d .data)
    (hm : HasType P Γ m A) (mm : WellModed γ m .data)
    (hy : HasType P Γ y A) (my : WellModed γ y .data)
    (hf : HasType P Γ f (R.first.apply A)) (mf : WellModed γ f .data) :
    Equivalent P Γ γ (R.second.observe (R.first.apply A) (R.bundle L.code A d m y) f)
      (L.code.cond (R.first.observe A f d) (R.first.observe A f m) (R.first.observe A f y)) := by
  have hh := h.second.cancellation (h.first.sorted hA) (h.first.mode mA)
    (h.bundleBody_family hA mA hd md hm mm hy my) ⟨hf,mf⟩
  simpa only [DataWrapper.cancelFormula,ite_true, if_true,DoubleCode.bundleBody_instantiate,DoubleCode.bundle] using hh
 theorem accessBody_family {A guard w fi : Expr S} (hA : SortedAt P Γ A I) (mA : WellModed γ A .data)
    (hg : L.Family A guard) (hw : HasType P Γ w (R.carrier A)) (mw : WellModed γ w .data)
    (hfi : DataMap P Γ γ A (R.first.apply A) fi) {s : S} (hs : HasType P Γ A (.sort s)) :
    L.Family A (R.accessBody L.code A guard w fi) :=
  hg.code_cond (.constant L.top_formula)
    ((h.second.evalCallback_family (h.first.sorted hA) (h.first.mode mA) hw mw).compose hfi hs)
 theorem accessProbe_typed {A guard w fi : Expr S} (hA : SortedAt P Γ A I) (mA : WellModed γ A .data)
    (hg : L.Family A guard) (hw : HasType P Γ w (R.carrier A)) (mw : WellModed γ w .data)
    (hfi : DataMap P Γ γ A (R.first.apply A) fi) {s : S} (hs : HasType P Γ A (.sort s)) :
    HasType P Γ (R.accessProbe L.code A guard w fi) (R.first.apply A) ∧
      WellModed γ (R.accessProbe L.code A guard w fi) .data :=
  (h.first.sound hA mA).1 _ (h.accessBody_family hA mA hg hw mw hfi hs)
 theorem accessProbe_evaluation {A guard w fi o : Expr S} (hA : SortedAt P Γ A I) (mA : WellModed γ A .data)
    (hg : L.Family A guard) (hw : HasType P Γ w (R.carrier A)) (mw : WellModed γ w .data)
    (hfi : DataMap P Γ γ A (R.first.apply A) fi) {s : S} (hs : HasType P Γ A (.sort s))
    (ho : HasType P Γ o A) (mo : WellModed γ o .data) :
    Equivalent P Γ γ (R.first.observe A (R.accessProbe L.code A guard w fi) o)
      (L.code.cond (guard.instantiate o) L.top (R.second.observe (R.first.apply A) w (fi.instantiate o))) := by
  have hh := h.first.cancellation hA mA (h.accessBody_family hA mA hg hw mw hfi hs) ⟨ho,mo⟩
  simpa only [DataWrapper.cancelFormula,ite_true, if_true,DoubleCode.accessBody_instantiate,DoubleCode.accessProbe,LogicSetup.top,LogicCode.top,LogicCode.imp,LogicSetup.imp,LogicSetup.code] using hh
end Formed
end DoubleCode

namespace DoubleCode.Formed
variable {R : DoubleCode S} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J : Set S} (h : R.Formed L I J I)
include h
 theorem bundle_select_true {A d m y f : Expr S} (hA : SortedAt P Γ A I) (mA : WellModed γ A .data)
    (hd : HasType P Γ d A) (md : WellModed γ d .data)
    (hm : HasType P Γ m A) (mm : WellModed γ m .data)
    (hy : HasType P Γ y A) (my : WellModed γ y .data)
    (hf : HasType P Γ f (R.first.apply A)) (mf : WellModed γ f .data)
    (hg : Proves P Γ γ (R.first.observe A f d)) :
    Equivalent P Γ γ (R.second.observe (R.first.apply A) (R.bundle L.code A d m y) f)
      (R.first.observe A f m) := by
  have he := h.bundle_evaluation hA mA hd md hm mm hy my hf mf
  have hw := h.bundle_typed hA mA hd md hm mm hy my
  have hW := (h.second.sound (h.first.sorted hA) (h.first.mode mA)).2 _ _ hw.1 hw.2 ⟨hf,mf⟩
  have hD := (h.first.sound hA mA).2 _ _ hf mf ⟨hd,md⟩
  have hM := (h.first.sound hA mA).2 _ _ hf mf ⟨hm,mm⟩
  have hY := (h.first.sound hA mA).2 _ _ hf mf ⟨hy,my⟩
  apply L.equivalent_of_iff hW hM
  exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (R.second.observe (R.first.apply A) (R.bundle L.code A d m y) f) else if pl_i = 1 then (R.first.observe A f d) else if pl_i = 2 then (R.first.observe A f m) else if pl_i = 3 then (R.first.observe A f y) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 3) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 3) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot), (FiniteClassical.Formula.atom 1)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.atom 2)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl; exacts [((L).iff_of_equivalent (hW) (LogicSetup.cond_formula L hD hM hY) he), hg])
 theorem bundle_select_false {A d m y f : Expr S} (hA : SortedAt P Γ A I) (mA : WellModed γ A .data)
    (hd : HasType P Γ d A) (md : WellModed γ d .data)
    (hm : HasType P Γ m A) (mm : WellModed γ m .data)
    (hy : HasType P Γ y A) (my : WellModed γ y .data)
    (hf : HasType P Γ f (R.first.apply A)) (mf : WellModed γ f .data)
    (hg : Proves P Γ γ (L.neg (R.first.observe A f d))) :
    Equivalent P Γ γ (R.second.observe (R.first.apply A) (R.bundle L.code A d m y) f)
      (R.first.observe A f y) := by
  have he := h.bundle_evaluation hA mA hd md hm mm hy my hf mf
  have hw := h.bundle_typed hA mA hd md hm mm hy my
  have hW := (h.second.sound (h.first.sorted hA) (h.first.mode mA)).2 _ _ hw.1 hw.2 ⟨hf,mf⟩
  have hD := (h.first.sound hA mA).2 _ _ hf mf ⟨hd,md⟩
  have hM := (h.first.sound hA mA).2 _ _ hf mf ⟨hm,mm⟩
  have hY := (h.first.sound hA mA).2 _ _ hf mf ⟨hy,my⟩
  apply L.equivalent_of_iff hW hY
  exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (R.second.observe (R.first.apply A) (R.bundle L.code A d m y) f) else if pl_i = 1 then (R.first.observe A f d) else if pl_i = 2 then (R.first.observe A f m) else if pl_i = 3 then (R.first.observe A f y) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 3) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 3) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot), (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.atom 3)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 3) (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl; exacts [((L).iff_of_equivalent (hW) (LogicSetup.cond_formula L hD hM hY) he), hg])
 theorem accessProbe_true {A guard w fi o : Expr S} (hA : SortedAt P Γ A I) (mA : WellModed γ A .data)
    (hg : L.Family A guard) (hw : HasType P Γ w (R.carrier A)) (mw : WellModed γ w .data)
    (hfi : DataMap P Γ γ A (R.first.apply A) fi) {s : S} (hs : HasType P Γ A (.sort s))
    (ho : HasType P Γ o A) (mo : WellModed γ o .data) (hG : Proves P Γ γ (guard.instantiate o)) :
    Proves P Γ γ (R.first.observe A (R.accessProbe L.code A guard w fi) o) := by
  have he := h.accessProbe_evaluation hA mA hg hw mw hfi hs ho mo
  have ht := h.accessProbe_typed hA mA hg hw mw hfi hs
  have hf := (h.first.sound hA mA).2 _ _ ht.1 ht.2 ⟨ho,mo⟩
  have hgf := hg.instantiate ho mo
  have hpo := hfi.apply ho mo
  have hF := (h.second.sound (h.first.sorted hA) (h.first.mode mA)).2 _ _ hw mw hpo
  exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (R.first.observe A (R.accessProbe L.code A guard w fi) o) else if pl_i = 1 then (guard.instantiate o) else if pl_i = 2 then (R.second.observe (R.first.apply A) w (fi.instantiate o)) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp FiniteClassical.Formula.bot FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp FiniteClassical.Formula.bot FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot), (FiniteClassical.Formula.atom 1)] (FiniteClassical.Formula.atom 0) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl; exacts [((L).iff_of_equivalent (hf) (LogicSetup.cond_formula L hgf (LogicSetup.top_formula L) hF) he), hG])
 theorem accessProbe_false {A guard w fi o : Expr S} (hA : SortedAt P Γ A I) (mA : WellModed γ A .data)
    (hg : L.Family A guard) (hw : HasType P Γ w (R.carrier A)) (mw : WellModed γ w .data)
    (hfi : DataMap P Γ γ A (R.first.apply A) fi) {s : S} (hs : HasType P Γ A (.sort s))
    (ho : HasType P Γ o A) (mo : WellModed γ o .data) (hG : Proves P Γ γ (L.neg (guard.instantiate o))) :
    Equivalent P Γ γ (R.first.observe A (R.accessProbe L.code A guard w fi) o)
      (R.second.observe (R.first.apply A) w (fi.instantiate o)) := by
  have he := h.accessProbe_evaluation hA mA hg hw mw hfi hs ho mo
  have ht := h.accessProbe_typed hA mA hg hw mw hfi hs
  have hf := (h.first.sound hA mA).2 _ _ ht.1 ht.2 ⟨ho,mo⟩
  have hgf := hg.instantiate ho mo
  have hpo := hfi.apply ho mo
  have hF := (h.second.sound (h.first.sorted hA) (h.first.mode mA)).2 _ _ hw mw hpo
  apply L.equivalent_of_iff hf hF
  exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (R.first.observe A (R.accessProbe L.code A guard w fi) o) else if pl_i = 1 then (guard.instantiate o) else if pl_i = 2 then (R.second.observe (R.first.apply A) w (fi.instantiate o)) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp FiniteClassical.Formula.bot FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp FiniteClassical.Formula.bot FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot), (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.atom 2)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl; exacts [((L).iff_of_equivalent (hf) (LogicSetup.cond_formula L hgf (LogicSetup.top_formula L) hF) he), hG])

/-- The exact-parameter access calculation. The inner callback is raw typed data,
    not a selected term depending on the non-dummy proof. -/
 theorem access_bundle {A d m y guard fi : Expr S} (hA : SortedAt P Γ A I) (mA : WellModed γ A .data)
    (hd : HasType P Γ d A) (md : WellModed γ d .data)
    (hm : HasType P Γ m A) (mm : WellModed γ m .data)
    (hy : HasType P Γ y A) (my : WellModed γ y .data)
    (hg : L.Family A guard) (hfi : DataMap P Γ γ A (R.first.apply A) fi)
    {s : S} (hs : HasType P Γ A (.sort s))
    (hgd : Proves P Γ γ (guard.instantiate d))
    (hgm : Proves P Γ γ (L.neg (guard.instantiate m)))
    (hid : Proves P Γ γ (L.neg (R.first.observe A (fi.instantiate m) d))) :
    Equivalent P Γ γ (R.access L.code A guard (R.bundle L.code A d m y) fi)
      (R.first.observe A (fi.instantiate m) y) := by
  have hw := h.bundle_typed hA mA hd md hm mm hy my
  have hf := h.accessProbe_typed hA mA hg hw.1 hw.2 hfi hs
  have ht := h.accessProbe_true hA mA hg hw.1 hw.2 hfi hs hd md hgd
  have he₁ := h.bundle_select_true hA mA hd md hm mm hy my hf.1 hf.2 ht
  have he₂ := h.accessProbe_false hA mA hg hw.1 hw.2 hfi hs hm mm hgm
  have hfm := hfi.apply hm mm
  have he₃ := h.bundle_select_false hA mA hd md hm mm hy my hfm.1 hfm.2 hid
  have h₀ := (h.second.sound (h.first.sorted hA) (h.first.mode mA)).2 _ _ hw.1 hw.2 hf
  have h₁ := (h.first.sound hA mA).2 _ _ hf.1 hf.2 ⟨hm,mm⟩
  have h₂ := (h.second.sound (h.first.sorted hA) (h.first.mode mA)).2 _ _ hw.1 hw.2 hfm
  have h₃ := (h.first.sound hA mA).2 _ _ hfm.1 hfm.2 ⟨hy,my⟩
  obtain ⟨r,hr⟩ := L.triple.codomain.1
  exact (he₁.trans he₂ (h₀.1 r hr) (h₁.1 r hr) (h₂.1 r hr)).trans he₃
    (h₀.1 r hr) (h₂.1 r hr) (h₃.1 r hr)
end DoubleCode.Formed

namespace DoubleCode
variable (R : DoubleCode S)

theorem dummyBody_instantiate (L : LogicCode S) (T o : Expr S) :
    (R.dummyBody L T).instantiate o = R.isDummy L T o :=
  R.second.contraCallback_instantiate _ _ _
theorem queryBody_instantiate (U : DataWrapper S true) (L : LogicCode S) (T p o : Expr S) :
    (R.queryBody U L T p).instantiate o = R.query U L 7 T o p :=
  R.second.contraCallback_instantiate _ _ _
theorem innerBody_instantiate (U : DataWrapper S true) (L : LogicCode S) (T p o : Expr S) :
    (R.innerBody U L T p).instantiate o =
      L.cond (R.isDummy L T o) L.bottom (R.query U L 7 T o p) := by
  simp only [innerBody,Expr.instantiate,LogicCode.cond_subst,LogicCode.instantiate_raise,
    Expr.subst_lift_single]
  change L.cond ((R.dummyBody L T).instantiate o) L.bottom
    ((R.queryBody U L T p).instantiate o) = _
  rw [dummyBody_instantiate,queryBody_instantiate]

namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H)
include h
 theorem dummyBody_family {T : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) :
    L.Family (R.paramType T) (R.dummyBody L.code T) := by
  have hb := h.bpBottom_typed hT mT
  exact h.second.contraCallback_family (h.bp_sorted hT) (h.bp_mode mT) hb.1 hb.2
include hU
 theorem queryBody_family {T p : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data) :
    L.Family (R.paramType T) (R.queryBody U L.code T p) := by
  have he := h.encode_typed hU hT mT 7 hp mp
  exact h.second.contraCallback_family (h.bp_sorted hT) (h.bp_mode mT) he.1 he.2
 theorem innerBody_family {T p : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data) :
    L.Family (R.paramType T) (R.innerBody U L.code T p) :=
  (h.dummyBody_family hT mT).code_cond (.constant L.bottom_formula)
    (h.queryBody_family hU hT mT hp mp)
 theorem innerProbe_typed {T p : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data) :
    HasType P Γ (R.innerProbe U L.code T p) (R.first.apply (R.paramType T)) ∧
      WellModed γ (R.innerProbe U L.code T p) .data :=
  (h.first.sound (h.param_sorted hT) (h.param_mode mT)).1 _ (h.innerBody_family hU hT mT hp mp)
 theorem innerProbe_evaluation {T p o : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data)
    (ho : HasType P Γ o (R.paramType T)) (mo : WellModed γ o .data) :
    Equivalent P Γ γ (R.first.observe (R.paramType T) (R.innerProbe U L.code T p) o)
      (L.code.cond (R.isDummy L.code T o) L.bottom (R.query U L.code 7 T o p)) := by
  have he := h.first.cancellation (h.param_sorted hT) (h.param_mode mT)
    (h.innerBody_family hU hT mT hp mp) ⟨ho,mo⟩
  simpa only [DataWrapper.cancelFormula,ite_true, if_true,innerBody_instantiate,LogicSetup.code_bottom,
    innerProbe] using he
 theorem innerProbe_dummy {T p : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data) :
    Proves P Γ γ (L.neg (R.first.observe (R.paramType T)
      (R.innerProbe U L.code T p) (R.dummy L.code T))) := by
  have hd := h.dummy_typed hT mT
  have he := h.innerProbe_evaluation hU hT mT hp mp hd.1 hd.2
  have hD := h.dummy_law hT mT
  have hi := h.innerProbe_typed hU hT mT hp mp
  have hf := (h.first.sound (h.param_sorted hT) (h.param_mode mT)).2 _ _ hi.1 hi.2 hd
  have hdf := h.isDummy_formula hT mT hd.1 hd.2
  have hq₀ := (h.queryBody_family hU hT mT hp mp).instantiate hd.1 hd.2
  have hq : L.Formula (R.query U L.code 7 T (R.dummy L.code T) p) := by
    simpa only [queryBody_instantiate] using hq₀
  exact L.equivalent_bottom_neg hf (L.cond_yes hdf L.bottom_formula hq hf he hD)
 theorem innerProbe_point {T c₀ c p : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (h₀ : HasType P Γ c₀ T) (m₀ : WellModed γ c₀ .data)
    (hc : HasType P Γ c T) (mc : WellModed γ c .data)
    {s r : S} (hs : HasType P Γ T (.sort s)) (hr : HasType P Γ (R.bpType T) (.sort r))
    (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data) :
    Equivalent P Γ γ (R.first.observe (R.paramType T) (R.innerProbe U L.code T p)
      (R.point U L.code T c₀ c)) (U.observe T p c) := by
  have ht := h.point_typed hU hT mT h₀ m₀ hc mc hs hr
  have he := h.innerProbe_evaluation hU hT mT hp mp ht.1 ht.2
  have hn := h.point_not_dummy hU hT mT h₀ m₀ hc mc hs hr
  have hq := h.point_query hU hT mT h₀ m₀ hc mc hs hr hp mp
  have hi := h.innerProbe_typed hU hT mT hp mp
  have hf := (h.first.sound (h.param_sorted hT) (h.param_mode mT)).2 _ _ hi.1 hi.2 ht
  have ho := (hU.sound hT mT).2 _ _ hp mp ⟨hc,mc⟩
  have hdf := h.isDummy_formula hT mT ht.1 ht.2
  have hqf₀ := (h.queryBody_family hU hT mT hp mp).instantiate ht.1 ht.2
  have hqf : L.Formula (R.query U L.code 7 T (R.point U L.code T c₀ c) p) := by
    simpa only [queryBody_instantiate] using hqf₀
  have he' := L.cond_no hdf L.bottom_formula hqf hf he hn
  obtain ⟨a,ha⟩ := L.triple.codomain.1
  exact he'.trans hq (hf.1 a ha) (hqf.1 a ha) (ho.1 a ha)
end Formed
end DoubleCode

namespace DataMap
variable {Γ : List (Expr S)} {γ : Nat → Mode} {T U V f g : Expr S} {s t : S}
theorem compose (hf : DataMap P Γ γ U V f) (hg : DataMap P Γ γ T U g)
    (hT : HasType P Γ T (.sort s)) (hU : HasType P Γ U (.sort t)) :
    DataMap P Γ γ T V (f.compose g) := by
  have hh := (hf.rename hU (Embedding.cons hT .data)).apply hg.1 hg.2
  exact hh
end DataMap
namespace LogicCode
theorem subst_bottom (L : LogicCode S) (σ : Nat → Expr S) : (L.subst σ).bottom = L.bottom.subst σ := rfl
end LogicCode
namespace DoubleCode

section
variable (R : DoubleCode S)
theorem rename_first (ρ : Nat → Nat) : (R.rename ρ).first = R.first.rename ρ := rfl
theorem subst_first (σ : Nat → Expr S) : (R.subst σ).first = R.first.subst σ := rfl
theorem subst_second (σ : Nat → Expr S) : (R.subst σ).second = R.second.subst σ := rfl
theorem bpBottom_subst (L : LogicCode S) (T : Expr S) (σ : Nat → Expr S) :
    (R.bpBottom L T).subst σ = (R.subst σ).bpBottom (L.subst σ) (T.subst σ) := by
  simp only [bpBottom,DataWrapper.build_subst,big_subst,DataWrapper.argSub,ite_true, if_true,subst_first,LogicCode.subst_bottom,
    Expr.subst_rename,Expr.rename_subst]
  rfl
theorem paramType_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.paramType T).rename ρ = (R.rename ρ).paramType (T.rename ρ) := by
  simp only [paramType,DataWrapper.apply_rename,bpType_rename]; rfl
theorem paramType_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.paramType T).subst σ = (R.subst σ).paramType (T.subst σ) := by
  simp only [paramType,DataWrapper.apply_subst,bpType_subst]; rfl
theorem encodeBody_subst (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T p : Expr S) (σ : Nat → Expr S) :
    (R.encodeBody U L t T p).subst (Expr.liftSub σ) =
      (R.subst σ).encodeBody (U.subst σ) (L.subst σ) t (T.subst σ) (p.subst σ) := by
  simp only [encodeBody,LogicCode.disj_subst,LogicCode.conj_subst,tagBody_subst,
    recoveryBody_subst,DataWrapper.evalCallback_subst,LogicCode.subst_rename,LogicCode.rename_subst]
  rfl
theorem encode_subst (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T p : Expr S) (σ : Nat → Expr S) :
    (R.encode U L t T p).subst σ =
      (R.subst σ).encode (U.subst σ) (L.subst σ) t (T.subst σ) (p.subst σ) := by
  simp only [encode,DataWrapper.build_subst,DataWrapper.argSub,ite_true, if_true,big_subst,encodeBody_subst]
  rfl
theorem dummyBody_subst (L : LogicCode S) (T : Expr S) (σ : Nat → Expr S) :
    (R.dummyBody L T).subst (Expr.liftSub σ) =
      (R.subst σ).dummyBody (L.subst σ) (T.subst σ) := by
  simp only [dummyBody,DataWrapper.contraCallback_subst,bpType_subst,bpBottom_subst]; rfl
theorem innerBody_subst (U : DataWrapper S true) (L : LogicCode S) (T p : Expr S) (σ : Nat → Expr S) :
    (R.innerBody U L T p).subst (Expr.liftSub σ) =
      (R.subst σ).innerBody (U.subst σ) (L.subst σ) (T.subst σ) (p.subst σ) := by
  simp only [innerBody,LogicCode.cond_subst,dummyBody_subst,queryBody,
    DataWrapper.contraCallback_subst,bpType_subst,encode_subst,LogicCode.subst_rename,
    LogicCode.rename_subst,subst_second,LogicCode.subst_bottom,Expr.subst_rename,Expr.rename_subst]
  rfl
theorem innerProbe_subst (U : DataWrapper S true) (L : LogicCode S) (T p : Expr S) (σ : Nat → Expr S) :
    (R.innerProbe U L T p).subst σ =
      (R.subst σ).innerProbe (U.subst σ) (L.subst σ) (T.subst σ) (p.subst σ) := by
  simp only [innerProbe,DataWrapper.build_subst,DataWrapper.argSub,ite_true, if_true,paramType_subst,innerBody_subst]
  rfl

theorem innerMap_instantiate (U : DataWrapper S true) (L : LogicCode S) (T p : Expr S) :
    (R.innerMap U L T).instantiate p = R.innerProbe U L T p := by
  simp only [innerMap,Expr.instantiate,innerProbe_subst,instantiate_raise,
    DataWrapper.instantiate_raise,LogicCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]

namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H)
include h hU
 theorem innerMap_typed {T : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    {s : S} (hs : HasType P Γ (U.apply T) (.sort s)) :
    DataMap P Γ γ (U.apply T) (R.first.apply (R.paramType T)) (R.innerMap U L.code T) := by
  let e : Embedding P Γ γ (U.apply T :: Γ) (modeCons .data γ) := Embedding.cons hs .data
  have hh := (h.rename e).innerProbe_typed (hU.rename e)
    (fun s hs => e.typing (hT s hs)) (e.moded mT)
    (by simpa only [DataWrapper.apply_rename,e,Embedding.cons] using HasType.var hs) (.var 0)
  simpa only [DataMap,innerMap,LogicSetup.code_rename,DataWrapper.apply_rename,
    paramType_rename,rename_first,e,Embedding.cons] using hh
end Formed

theorem accessMap_instantiate (U : DataWrapper S true) (L : LogicCode S) (T pMap m : Expr S) :
    (R.accessMap U L T pMap).instantiate m = R.innerProbe U L T (pMap.instantiate m) := by
  simp only [accessMap,Expr.compose_instantiate,innerMap_instantiate]
namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H) (hI : I.Nonempty) (hH : H.Nonempty)
include h hU hI hH
 theorem accessMap_typed {T pMap : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hp : DataMap P Γ γ (R.paramType T) (U.apply T) pMap) :
    DataMap P Γ γ (R.paramType T) (R.first.apply (R.paramType T)) (R.accessMap U L.code T pMap) := by
  obtain ⟨s,hs⟩ := hI
  obtain ⟨t,ht⟩ := hH
  exact (h.innerMap_typed hU hT mT (hU.sorted hT t ht)).compose hp
    (h.param_sorted hT s hs) (hU.sorted hT t ht)

 theorem access_recovery_oai {T pMap m c₀ c : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hp : DataMap P Γ γ (R.paramType T) (U.apply T) pMap)
    (hm : HasType P Γ m (R.paramType T)) (mm : WellModed γ m .data)
    (h₀ : HasType P Γ c₀ T) (m₀ : WellModed γ c₀ .data)
    (hc : HasType P Γ c T) (mc : WellModed γ c .data)
    {s r : S} (hs : HasType P Γ T (.sort s)) (hr : HasType P Γ (R.bpType T) (.sort r))
    (hnd : Proves P Γ γ (L.neg (R.isDummy L.code T m))) :
    Equivalent P Γ γ
      (R.recoverAccess U L.code T
        (R.bundle L.code (R.paramType T) (R.dummy L.code T) m (R.point U L.code T c₀ c)) pMap)
      (U.observe T (pMap.instantiate m) c) := by
  have hf := h.accessMap_typed hU hI hH hT mT hp
  have hd := h.dummy_typed hT mT
  have hy := h.point_typed hU hT mT h₀ m₀ hc mc hs hr
  have hpm := hp.apply hm mm
  have hid₀ := h.innerProbe_dummy hU hT mT hpm.1 hpm.2
  have hid : Proves P Γ γ (L.neg (R.first.observe (R.paramType T)
      ((R.accessMap U L.code T pMap).instantiate m) (R.dummy L.code T))) := by
    simpa only [accessMap_instantiate] using hid₀
  obtain ⟨a,ha⟩ := hI
  have he₀ := h.access_bundle (h.param_sorted hT) (h.param_mode mT) hd.1 hd.2 hm mm hy.1 hy.2
    (h.dummyBody_family hT mT) hf (h.param_sorted hT a ha)
    (by simpa only [dummyBody_instantiate] using h.dummy_law hT mT)
    (by simpa only [dummyBody_instantiate] using hnd) hid
  have he : Equivalent P Γ γ
      (R.recoverAccess U L.code T
        (R.bundle L.code (R.paramType T) (R.dummy L.code T) m (R.point U L.code T c₀ c)) pMap)
      (R.first.observe (R.paramType T) (R.innerProbe U L.code T (pMap.instantiate m))
        (R.point U L.code T c₀ c)) := by
    simpa only [recoverAccess,accessMap_instantiate] using he₀
  have he' := h.innerProbe_point hU hT mT h₀ m₀ hc mc hs hr hpm.1 hpm.2
  have hw := h.bundle_typed (h.param_sorted hT) (h.param_mode mT) hd.1 hd.2 hm mm hy.1 hy.2
  have hfe := h.accessProbe_typed (h.param_sorted hT) (h.param_mode mT)
    (h.dummyBody_family hT mT) hw.1 hw.2 hf (h.param_sorted hT a ha)
  have hW := (h.second.sound (h.first.sorted (h.param_sorted hT)) (h.first.mode (h.param_mode mT))).2
    _ _ hw.1 hw.2 hfe
  have hfi := h.innerProbe_typed hU hT mT hpm.1 hpm.2
  have hY := (h.first.sound (h.param_sorted hT) (h.param_mode mT)).2 _ _ hfi.1 hfi.2 hy
  have hQ := (hU.sound hT mT).2 _ _ hpm.1 hpm.2 ⟨hc,mc⟩
  obtain ⟨b,hb⟩ := L.triple.codomain.1
  exact he.trans he' (hW.1 b hb) (hY.1 b hb) (hQ.1 b hb)
end Formed
end

end DoubleCode
end

universe u
end PureTypeSystem.Labelled

end OAI
end

theorem solution.{u} : type_of% @OAI.PureTypeSystem.Labelled.DoubleCode.Formed.access_recovery_oai.{u} := @OAI.PureTypeSystem.Labelled.DoubleCode.Formed.access_recovery_oai.{u}
