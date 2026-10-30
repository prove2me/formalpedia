-- Prove2me | solution 1 for OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.parameter_query
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:18:29.516977+00:00
-- url     : https://prove2.me/submissions/7e234d2a-79ad-4098-af89-529ad7eab201

import Mathlib
import Definitions.Def_TypeSystemNormalization
import Definitions.Def_OAIQ5T6000
import Theorems.Thm_OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_propertyBody_family
import Theorems.Thm_OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_property_formula
import Theorems.Thm_OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_property_respect

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

variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I : Set S} {T Q : Expr S} {s : S}

 theorem raw_all (R : QuantifierRoute L.witnesses C L.base I)
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hs : HasType P Γ T (.sort s))
    (hQ : (L.rename (Embedding.cons hs .data)).Formula Q) :
    SortedAt P Γ (.pi .dp T ((R.inCode.rename Nat.succ).apply Q)) R.product ∧
    WellModed γ (.pi .dp T ((R.inCode.rename Nat.succ).apply Q)) .data ∧
    StableExtraction L.witnesses C (.pi .dp T ((R.inCode.rename Nat.succ).apply Q)) := by
  let e : Embedding P Γ γ (T :: Γ) (modeCons .data γ) := Embedding.cons hs .data
  have hr := R.inFormed.rename e
  obtain ⟨hq,mq,pq⟩ := hr.sound (L.rename e).converters hQ.1 hQ.2.1
  have hsrt : SortedAt P Γ (.pi .dp T ((R.inCode.rename Nat.succ).apply Q)) R.product := by
    intro r hr
    obtain ⟨a,ha,b,hb,hab⟩ := R.triple.output ▸ hr
    exact .product (hT a ha) (hq b hb) hab
  obtain ⟨r,hr⟩ := R.triple.product.1
  exact ⟨hsrt,.pi mT mq,StableExtraction.product hs mT (hsrt r hr) rfl
    ((R.inFormed.rename e).stable (L.rename e).converters hQ.1 hQ.2.1 |>.1 hQ.2.2)⟩

 theorem all_intro (R : QuantifierRoute L.witnesses C L.base I)
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hs : HasType P Γ T (.sort s))
    (hQ : (L.rename (Embedding.cons hs .data)).Formula Q)
    (hp : Proves P (T :: Γ) (modeCons .data γ) Q) : Proves P Γ γ (all R T Q) := by
  let e : Embedding P Γ γ (T :: Γ) (modeCons .data γ) := Embedding.cons hs .data
  obtain ⟨ht,mt,st⟩ := raw_all R hT mT hs hQ
  obtain ⟨ha,ma,pa⟩ := R.outFormed.sound L.converters ht mt
  obtain ⟨hb,mb,pb⟩ := (R.inFormed.rename e).sound (L.rename e).converters hQ.1 hQ.2.1
  obtain ⟨a,ha'⟩ := hQ.sorted (L.rename e)
  obtain ⟨q,hq,mq⟩ := (pb.into ha').prove hp
  obtain ⟨r,hr⟩ := R.triple.product.1
  exact (pa.into (ht r hr)).prove ⟨_,.abstraction hq (ht r hr),.lam mT mq⟩

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

theorem opened (h : L.Family T Q) {s : S} (ht : HasType P Γ T (.sort s)) :
    (L.rename (Embedding.cons ht .data)).Formula Q := by
  have hh := h _ _ (Embedding.cons ht .data) (.var 0) (HasType.var ht) (.var 0)
  have heq : (Q.rename (Expr.liftRen Nat.succ)).instantiate (.var 0) = Q := by
    simp only [Expr.instantiate,Expr.subst_rename]
    have he : Expr.single (.var 0 : Expr S) ∘ Expr.liftRen Nat.succ = Expr.var := by
      funext n; cases n <;> rfl
    rw [he,Expr.subst_var]
  exact heq ▸ hh
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

theorem reencode_rename (R R' : DataWrapper S true) (T w : Expr S) (ρ : Nat → Nat) :
    (reencode R R' T w).rename ρ = reencode (R.rename ρ) (R'.rename ρ) (T.rename ρ) (w.rename ρ) := by
  simp only [reencode,build_rename,argRen,ite_true, if_true,evalCallback_rename]

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J K : Set S} {R R' : DataWrapper S true}

theorem reencode_typed (hR : Formed L I J R) (hR' : Formed L I K R') {T w : Expr S}
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hw : HasType P Γ w (R.apply T)) (mw : WellModed γ w .data) :
    HasType P Γ (reencode R R' T w) (R'.apply T) ∧ WellModed γ (reencode R R' T w) .data :=
  (hR'.sound hT mT).1 _ (hR.evalCallback_family hT mT hw mw)
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

theorem reencode_subst (R R' : DataWrapper S true) (T w : Expr S) (σ : Nat → Expr S) :
    (reencode R R' T w).subst σ = reencode (R.subst σ) (R'.subst σ) (T.subst σ) (w.subst σ) := by
  simp only [reencode,build_subst,argSub,ite_true, if_true,evalCallback_subst]

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
theorem iff_rename (A B : Expr S) (ρ : Nat → Nat) :
    (L.iff A B).rename ρ = (L.rename ρ).iff (A.rename ρ) (B.rename ρ) := by
  simp only [iff,imp_rename,conj_rename]
theorem iff_subst (A B : Expr S) (σ : Nat → Expr S) :
    (L.iff A B).subst σ = (L.subst σ).iff (A.subst σ) (B.subst σ) := by
  simp only [iff,imp_subst,conj_subst]
theorem cond_rename (G A B : Expr S) (ρ : Nat → Nat) :
    (L.cond G A B).rename ρ = (L.rename ρ).cond (G.rename ρ) (A.rename ρ) (B.rename ρ) := by
  simp only [cond,conj_rename,disj_rename,neg_rename]
theorem cond_subst (G A B : Expr S) (σ : Nat → Expr S) :
    (L.cond G A B).subst σ = (L.subst σ).cond (G.subst σ) (A.subst σ) (B.subst σ) := by
  simp only [cond,conj_subst,disj_subst,neg_subst]
theorem sign_rename (b : Bool) (A : Expr S) (ρ : Nat → Nat) :
    (L.sign b A).rename ρ = (L.rename ρ).sign b (A.rename ρ) := by
  cases b <;> simp only [sign,ite_false, if_false,ite_true, if_true,Bool.false_eq_true,neg_rename]
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

theorem code_iff (ha : L.Family T Q) (hb : L.Family T Q') :
    L.Family T ((L.code.rename Nat.succ).iff Q Q') :=
  (ha.code_imp hb).code_conj (hb.code_imp ha)

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

namespace ChannelCode
variable (R : ChannelCode S)

variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) (I J K H : Set S)

namespace Formed
variable {R L I J K H}
theorem rename (h : Formed R L I J K H) (e : Embedding P Γ γ Δ δ) :
    Formed (R.rename e.names) (L.rename e) I J K H :=
  ⟨h.logical.rename e,h.raw.rename e,h.predicate.rename e⟩

variable (h : Formed R L I J K H) {T y c p Q : Expr S}
include h

theorem logical_sorted (hT : SortedAt P Γ T I) : SortedAt P Γ (R.logicalType T) J := h.logical.sorted hT
theorem logical_mode (mT : WellModed γ T .data) : WellModed γ (R.logicalType T) .data := h.logical.mode mT

theorem toRaw_typed (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data) :
    HasType P Γ (R.toRaw T y) (R.rawType T) ∧ WellModed γ (R.toRaw T y) .data :=
  h.logical.reencode_typed h.raw hT mT hy my

theorem eval_formula (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data)
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data) :
    L.Formula (R.eval T p y) := by
  have hh := h.toRaw_typed hT mT hy my
  exact (h.predicate.sound (h.raw.sorted hT) (h.raw.mode mT)).2 p _ hp mp hh

end Formed
end ChannelCode

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
theorem emb_rename (L : LogicCode S) (b : Bool) (T t : Expr S) (ρ : Nat → Nat) :
    (R.emb L b T t).rename ρ = (R.rename ρ).emb (L.rename ρ) b (T.rename ρ) (t.rename ρ) := by
  simp only [emb,DataWrapper.build_rename,DataWrapper.apply_rename,DataWrapper.argRen,ite_true, if_true,
    LogicCode.sign_rename,LogicCode.rename_comp,DataWrapper.contraCallback_rename,rename]
  rfl
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
theorem embed_rename (L : LogicCode S) (bs : List Bool) (T t : Expr S) (ρ : Nat → Nat) :
    (R.embed L bs T t).rename ρ = (R.rename ρ).embed (L.rename ρ) bs (T.rename ρ) (t.rename ρ) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [embed,emb_rename,tower_rename,ih]
theorem embed_subst (L : LogicCode S) (bs : List Bool) (T t : Expr S) (σ : Nat → Expr S) :
    (R.embed L bs T t).subst σ = (R.subst σ).embed (L.subst σ) bs (T.subst σ) (t.subst σ) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [embed,emb_subst,tower_subst,ih]
theorem recoveryBody_rename (L : LogicCode S) (n : Nat) (T Q : Expr S) (ρ : Nat → Nat) :
    (R.recoveryBody L n T Q).rename (Expr.liftRen ρ) =
      (R.rename ρ).recoveryBody (L.rename ρ) n (T.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [recoveryBody,recBody_rename,tower_rename,ih]
theorem tagBody_rename (L : LogicCode S) (bs : List Bool) (T : Expr S) (ρ : Nat → Nat) :
    (R.tagBody L bs T).rename (Expr.liftRen ρ) =
      (R.rename ρ).tagBody (L.rename ρ) bs (T.rename ρ) := by
  induction bs with
  | nil =>
    simp only [tagBody,Expr.rename_comp,← LogicCode.top_rename]
    rfl
  | cons b bs ih =>
    simp only [tagBody,LogicCode.conj_rename,LogicCode.sign_rename,LogicCode.rename_comp,
      bitBody_rename,recBody_rename,tower_rename,ih]
    rfl

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

theorem tagged_rename (L : LogicCode S) (q : Fin 9) (T t : Expr S) (ρ : Nat → Nat) :
    (R.tagged L q T t).rename ρ = (R.rename ρ).tagged (L.rename ρ) q (T.rename ρ) (t.rename ρ) :=
  R.embed_rename L (queryBits q) T t ρ
theorem tagged_subst (L : LogicCode S) (q : Fin 9) (T t : Expr S) (σ : Nat → Expr S) :
    (R.tagged L q T t).subst σ = (R.subst σ).tagged (L.subst σ) q (T.subst σ) (t.subst σ) :=
  R.embed_subst L (queryBits q) T t σ

theorem encodeBody_rename (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T p : Expr S) (ρ : Nat → Nat) :
    (R.encodeBody U L t T p).rename (Expr.liftRen ρ) =
      (R.rename ρ).encodeBody (U.rename ρ) (L.rename ρ) t (T.rename ρ) (p.rename ρ) := by
  simp only [encodeBody,LogicCode.disj_rename,LogicCode.conj_rename,tagBody_rename,
    recoveryBody_rename,DataWrapper.evalCallback_rename,LogicCode.rename_comp]
  rfl

theorem embedBody_instantiate (L : LogicCode S) (q : Fin 9) (T t : Expr S) :
    (R.embedBody L q T).instantiate t = R.tagged L q T t := by
  simp only [embedBody,Expr.instantiate,tagged_subst,instantiate_raise,LogicCode.instantiate_raise,
    Expr.subst_lift_single,Expr.subst,Expr.single]
theorem embedBody_rename (L : LogicCode S) (q : Fin 9) (T : Expr S) (ρ : Nat → Nat) :
    (R.embedBody L q T).rename (Expr.liftRen ρ) = (R.rename ρ).embedBody (L.rename ρ) q (T.rename ρ) := by
  simp only [embedBody,tagged_rename,rename_comp,LogicCode.rename_comp,Expr.rename_comp,Expr.rename]
  rfl

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

namespace ProbeCode
variable (R : ProbeCode S)

theorem doubled_rename (ρ : Nat → Nat) : (R.rename ρ).doubled = R.doubled.rename ρ := rfl
theorem doubled_subst (σ : Nat → Expr S) : (R.subst σ).doubled = R.doubled.subst σ := rfl

theorem rawType_rename (A : Expr S) (ρ : Nat → Nat) :
    (R.rawType A).rename ρ = (R.rename ρ).rawType (A.rename ρ) := by
  simp only [rawType,rename,DataWrapper.apply_rename]
theorem rawType_subst (A : Expr S) (σ : Nat → Expr S) :
    (R.rawType A).subst σ = (R.subst σ).rawType (A.subst σ) := by
  simp only [rawType,subst,DataWrapper.apply_subst]
theorem paramType_rename (A : Expr S) (ρ : Nat → Nat) :
    (R.paramType A).rename ρ = (R.rename ρ).paramType (A.rename ρ) := by
  simp only [paramType,DoubleCode.paramType,DoubleCode.bpType,DoubleCode.big,
    DataWrapper.apply_rename,DoubleCode.tower_rename,rawType_rename,doubled,rename,DoubleCode.rename]
theorem paramType_subst (A : Expr S) (σ : Nat → Expr S) :
    (R.paramType A).subst σ = (R.subst σ).paramType (A.subst σ) := by
  simp only [paramType,DoubleCode.paramType,DoubleCode.bpType,DoubleCode.big,
    DataWrapper.apply_subst,DoubleCode.tower_subst,rawType_subst,doubled,subst,DoubleCode.subst]
theorem singleType_rename (A : Expr S) (ρ : Nat → Nat) :
    (R.singleType A).rename ρ = (R.rename ρ).singleType (A.rename ρ) := by
  simp only [singleType,DoubleCode.carrier_rename,paramType_rename,doubled_rename]
theorem singleType_subst (A : Expr S) (σ : Nat → Expr S) :
    (R.singleType A).subst σ = (R.subst σ).singleType (A.subst σ) := by
  simp only [singleType,DoubleCode.carrier_subst,paramType_subst,doubled_subst]
theorem funType_rename (A : Expr S) (ρ : Nat → Nat) :
    (R.funType A).rename ρ = (R.rename ρ).funType (A.rename ρ) := by
  simp only [funType,Expr.arrow_rename,singleType_rename,DataTail.carrier_rename,rename]
theorem funType_subst (A : Expr S) (σ : Nat → Expr S) :
    (R.funType A).subst σ = (R.subst σ).funType (A.subst σ) := by
  simp only [funType,Expr.arrow_subst,singleType_subst,DataTail.carrier_subst,subst]
theorem instantiate_raise (a : Expr S) : (R.rename Nat.succ).subst (Expr.single a) = R := by
  cases R
  simp only [rename,subst,DataWrapper.instantiate_raise,PositiveDataWrapper.instantiate_raise,
    DataTail.instantiate_raise]

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
  (L : LogicSetup P Γ γ C) (I J k p n g : Set S)

namespace Formed
variable {R L I J k p n g} (h : R.Formed L I J k p n g)
include h
theorem rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) :
    (R.rename e.names).Formed (L.rename e) I J k p n g :=
  ⟨h.mainTriple,h.funTriple,h.ax,h.initial.rename e,h.raw.rename e,h.back.rename e,
    h.funPath.rename e,h.lifting.rename e,h.tail.rename e⟩
theorem raw_sorted {A : Expr S} (ha : HasType P Γ A (.sort R.seed)) :
    SortedAt P Γ (R.rawType A) p := h.raw.sorted (h.initial.sorted (fun s hs => by cases hs; exact ha))
theorem raw_mode {A : Expr S} (ma : WellModed γ A .data) : WellModed γ (R.rawType A) .data :=
  h.raw.mode (h.initial.mode ma)
theorem doubled_formed : R.doubled.Formed L p k p := ⟨h.back,h.raw⟩
end Formed
end ProbeCode

end PureTypeSystem.Labelled

namespace PureTypeSystem.Labelled

section
universe u
variable {S : Type u}
namespace ChannelCode
variable (R : ChannelCode S)
theorem rename_comp (ρ τ : Nat → Nat) : (R.rename τ).rename ρ = R.rename (ρ ∘ τ) := by
  cases R; simp only [rename,DataWrapper.rename_comp]
theorem instantiate_raise (a : Expr S) : (R.rename Nat.succ).subst (Expr.single a) = R := by
  cases R; simp only [rename,subst,DataWrapper.instantiate_raise]
theorem logicalType_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.logicalType T).rename ρ = (R.rename ρ).logicalType (T.rename ρ) := by
  simp only [logicalType,rename,DataWrapper.apply_rename]
theorem logicalType_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.logicalType T).subst σ = (R.subst σ).logicalType (T.subst σ) := by
  simp only [logicalType,subst,DataWrapper.apply_subst]
theorem rawType_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.rawType T).rename ρ = (R.rename ρ).rawType (T.rename ρ) := by
  simp only [rawType,rename,DataWrapper.apply_rename]
theorem rawType_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.rawType T).subst σ = (R.subst σ).rawType (T.subst σ) := by
  simp only [rawType,subst,DataWrapper.apply_subst]
theorem predicateType_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.predicateType T).rename ρ = (R.rename ρ).predicateType (T.rename ρ) := by
  simp only [predicateType,rename,DataWrapper.apply_rename]
theorem predicateType_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.predicateType T).subst σ = (R.subst σ).predicateType (T.subst σ) := by
  simp only [predicateType,subst,DataWrapper.apply_subst]
theorem toRaw_rename (T y : Expr S) (ρ : Nat → Nat) :
    (R.toRaw T y).rename ρ = (R.rename ρ).toRaw (T.rename ρ) (y.rename ρ) := by
  simp only [toRaw,DataWrapper.reencode_rename,rename]
theorem toRaw_subst (T y : Expr S) (σ : Nat → Expr S) :
    (R.toRaw T y).subst σ = (R.subst σ).toRaw (T.subst σ) (y.subst σ) := by
  simp only [toRaw,DataWrapper.reencode_subst,subst]
theorem toLog_subst (T c : Expr S) (σ : Nat → Expr S) :
    (R.toLog T c).subst σ = (R.subst σ).toLog (T.subst σ) (c.subst σ) := by
  simp only [toLog,DataWrapper.reencode_subst,subst]
theorem round_subst (T y : Expr S) (σ : Nat → Expr S) :
    (R.round T y).subst σ = (R.subst σ).round (T.subst σ) (y.subst σ) := by
  simp only [round,toRaw_subst,toLog_subst]
theorem eval_rename (T p y : Expr S) (ρ : Nat → Nat) :
    (R.eval T p y).rename ρ = (R.rename ρ).eval (T.rename ρ) (p.rename ρ) (y.rename ρ) := by
  simp only [eval,DataWrapper.observe_rename,rawType_rename,toRaw_rename,rename,
    DataWrapper.argRen,Bool.not_true,Bool.false_eq_true,ite_false, if_false]
theorem eval_subst (T p y : Expr S) (σ : Nat → Expr S) :
    (R.eval T p y).subst σ = (R.subst σ).eval (T.subst σ) (p.subst σ) (y.subst σ) := by
  simp only [eval,DataWrapper.observe_subst,rawType_subst,toRaw_subst,subst,
    DataWrapper.argSub,Bool.not_true,Bool.false_eq_true,ite_false, if_false]
end ChannelCode
end

universe u
variable {S : Type u} {P : Specification S}
namespace LogicSetup
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) {A B : Expr S}

theorem all_intro_future {I : Set S} (R : QuantifierRoute L.witnesses C L.base I)
    {T Q : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    {s : S} (hs : HasType P Γ T (.sort s)) (hQ : L.Family T Q)
    (h : ∀ (Δ : List (Expr S)) (δ : Nat → Mode) (e : Embedding P Γ γ Δ δ)
      (a : Expr S), HasType P Δ a (T.rename e.names) → WellModed δ a .data →
      Proves P Δ δ ((Q.rename (Expr.liftRen e.names)).instantiate a)) :
    Proves P Γ γ (all R T Q) := by
  apply all_intro R hT mT hs (hQ.opened hs)
  have hh := h _ _ (Embedding.cons hs .data) (.var 0) (HasType.var hs) (.var 0)
  have he : (Q.rename (Expr.liftRen Nat.succ)).instantiate (.var 0) = Q := by
    simp only [Expr.instantiate,Expr.subst_rename]
    have he : Expr.single (.var 0 : Expr S) ∘ Expr.liftRen Nat.succ = Expr.var := by
      funext n; cases n <;> rfl
    rw [he,Expr.subst_var]
  exact he ▸ hh

end LogicSetup

namespace QuantifierCode
variable (K : QuantifierCode S)
theorem instantiate_raise (a : Expr S) : (K.rename Nat.succ).subst (Expr.single a) = K := by
  cases K; simp only [rename,subst,ProofWrapper.instantiate_raise]
theorem all_subst (T Q : Expr S) (σ : Nat → Expr S) :
    (K.all T Q).subst σ = (K.subst σ).all (T.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [all,subst,ProofWrapper.apply_subst,Expr.subst,ProofWrapper.subst_rename,ProofWrapper.rename_subst]
  rfl
end QuantifierCode
end PureTypeSystem.Labelled

namespace PureTypeSystem.Labelled.LogicSetup
universe u
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {γ : Nat → Mode}
    {C : Set (Set S)} (L : LogicSetup P Γ γ C)
theorem code_neg (A : Expr S) : L.code.neg A = L.neg A := rfl
theorem code_conj (A B : Expr S) : L.code.conj A B = L.conj A B := rfl
theorem code_disj (A B : Expr S) : L.code.disj A B = L.disj A B := rfl
end PureTypeSystem.Labelled.LogicSetup

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Relations
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate _root_.OAI.PureTypeSystem.instCountableExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled
universe u
variable {S : Type u} {P : Specification S}

namespace ChannelCode
variable (R : ChannelCode S)

theorem roundRespectBody_subst (L : LogicCode S) (T p : Expr S) (σ : Nat → Expr S) :
    (R.roundRespectBody L T p).subst (Expr.liftSub σ) =
      (R.subst σ).roundRespectBody (L.subst σ) (T.subst σ) (p.subst σ) := by
  simp only [roundRespectBody,LogicCode.iff_subst,eval_subst,round_subst,subst,rename,
    LogicCode.subst,LogicCode.rename,DataWrapper.subst_rename,DataWrapper.rename_subst,
    ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,
    Expr.subst,Expr.liftSub]
  rfl

theorem roundRespect_subst (L : LogicCode S) (K : QuantifierCode S) (T p : Expr S) (σ : Nat → Expr S) :
    (R.roundRespect L K T p).subst σ =
      (R.subst σ).roundRespect (L.subst σ) (K.subst σ) (T.subst σ) (p.subst σ) := by
  simp only [roundRespect,QuantifierCode.all_subst,logicalType_subst,roundRespectBody_subst]

end ChannelCode

namespace LogicCode
variable (L : LogicCode S)
theorem guardBody_subst (G Q : Expr S) (σ : Nat → Expr S) :
    (L.guardBody G Q).subst (Expr.liftSub σ) =
      (L.subst σ).guardBody (G.subst (Expr.liftSub σ)) (Q.subst (Expr.liftSub σ)) := by
  simp only [guardBody,imp_subst,subst,rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,
    Expr.subst_rename,Expr.rename_subst]
  rfl
theorem guardAll_subst (K : QuantifierCode S) (T G Q : Expr S) (σ : Nat → Expr S) :
    (L.guardAll K T G Q).subst σ =
      (L.subst σ).guardAll (K.subst σ) (T.subst σ)
        (G.subst (Expr.liftSub σ)) (Q.subst (Expr.liftSub σ)) := by
  simp only [guardAll,QuantifierCode.all_subst,guardBody_subst]
end LogicCode
namespace ChannelCode
variable (R : ChannelCode S)
theorem evalPredBody_subst (T y : Expr S) (σ : Nat → Expr S) :
    (R.evalPredBody T y).subst (Expr.liftSub σ) =
      (R.subst σ).evalPredBody (T.subst σ) (y.subst σ) := by
  simp only [evalPredBody,eval_subst,subst,rename,DataWrapper.subst_rename,DataWrapper.rename_subst,
    Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
theorem compareBody_subst (L : LogicCode S) (T y z : Expr S) (σ : Nat → Expr S) :
    (R.compareBody L T y z).subst (Expr.liftSub σ) =
      (R.subst σ).compareBody (L.subst σ) (T.subst σ) (y.subst σ) (z.subst σ) := by
  simp only [compareBody,LogicCode.iff_subst,evalPredBody_subst,LogicCode.subst,LogicCode.rename,
    ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst]
  rfl
theorem relation_subst (L : LogicCode S) (K : QuantifierCode S) (T G y z : Expr S) (σ : Nat → Expr S) :
    (R.relation L K T G y z).subst σ =
      (R.subst σ).relation (L.subst σ) (K.subst σ) (T.subst σ)
        (G.subst (Expr.liftSub σ)) (y.subst σ) (z.subst σ) := by
  simp only [relation,LogicCode.guardAll_subst,predicateType_subst,compareBody_subst]

end ChannelCode

namespace LogicCode
variable (L : LogicCode S)
theorem negBody_subst (Q : Expr S) (σ : Nat → Expr S) :
    (L.negBody Q).subst (Expr.liftSub σ) = (L.subst σ).negBody (Q.subst (Expr.liftSub σ)) := by
  simp only [negBody,neg_subst,subst,rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,
    Expr.subst_rename,Expr.rename_subst]
  rfl
theorem ex_subst (K : QuantifierCode S) (T Q : Expr S) (σ : Nat → Expr S) :
    (L.ex K T Q).subst σ = (L.subst σ).ex (K.subst σ) (T.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [ex,neg_subst,QuantifierCode.all_subst,negBody_subst]
end LogicCode

namespace ChannelCode
variable (R : ChannelCode S)

theorem evalBody_rename (T p : Expr S) (ρ : Nat → Nat) :
    (R.evalBody T p).rename (Expr.liftRen ρ) =
      (R.rename ρ).evalBody (T.rename ρ) (p.rename ρ) := by
  simp only [evalBody,eval_rename,rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,
    PureTypeSystem.Expr.liftRen]
  rfl
theorem evalBody_instantiate (T p y : Expr S) :
    (R.evalBody T p).instantiate y = R.eval T p y := by
  simp only [evalBody,Expr.instantiate,eval_subst,instantiate_raise,Expr.subst_lift_single,
    Expr.subst,Expr.single]
theorem evalBody_subst (T p : Expr S) (σ : Nat → Expr S) :
    (R.evalBody T p).subst (Expr.liftSub σ) = (R.subst σ).evalBody (T.subst σ) (p.subst σ) := by
  simp only [evalBody,eval_subst,subst,rename,DataWrapper.subst_rename,DataWrapper.rename_subst,
    Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
theorem predCompareBody_rename (L : LogicCode S) (T p q : Expr S) (ρ : Nat → Nat) :
    (R.predCompareBody L T p q).rename (Expr.liftRen ρ) =
      (R.rename ρ).predCompareBody (L.rename ρ) (T.rename ρ) (p.rename ρ) (q.rename ρ) := by
  simp only [predCompareBody,LogicCode.iff_rename,LogicCode.rename_comp,evalBody_rename]
  rfl
theorem predCompareBody_subst (L : LogicCode S) (T p q : Expr S) (σ : Nat → Expr S) :
    (R.predCompareBody L T p q).subst (Expr.liftSub σ) =
      (R.subst σ).predCompareBody (L.subst σ) (T.subst σ) (p.subst σ) (q.subst σ) := by
  simp only [predCompareBody,LogicCode.iff_subst,evalBody_subst,LogicCode.subst,LogicCode.rename,
    ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst]
  rfl
theorem predCompareBody_instantiate (L : LogicCode S) (T p q y : Expr S) :
    (R.predCompareBody L T p q).instantiate y = L.iff (R.eval T p y) (R.eval T q y) := by
  change ((L.rename Nat.succ).iff (R.evalBody T p) (R.evalBody T q)).subst (Expr.single y) = _
  rw [LogicCode.iff_subst,LogicCode.instantiate_raise]
  change L.iff ((R.evalBody T p).instantiate y) ((R.evalBody T q).instantiate y) = _
  rw [evalBody_instantiate,evalBody_instantiate]
theorem predCompare_subst (L : LogicCode S) (K : QuantifierCode S) (T p q : Expr S) (σ : Nat → Expr S) :
    (R.predCompare L K T p q).subst σ =
      (R.subst σ).predCompare (L.subst σ) (K.subst σ) (T.subst σ) (p.subst σ) (q.subst σ) := by
  simp only [predCompare,QuantifierCode.all_subst,logicalType_subst,predCompareBody_subst]
namespace Formed
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H N : Set S} {R : ChannelCode S}
    (h : R.Formed L I J N H) {T p q y : Expr S}
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
include h hT mT
 theorem evalBody_family (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data) :
    L.Family (R.logicalType T) (R.evalBody T p) := by
  intro Δ δ e y hy my
  rw [evalBody_rename,evalBody_instantiate]
  exact (h.rename e).eval_formula (fun s hs => e.typing (hT s hs)) (e.moded mT)
    (by simpa only [predicateType_rename] using e.typing hp) (e.moded mp)
    (by simpa only [logicalType_rename] using hy) my
 theorem predCompareBody_family
    (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data)
    (hq : HasType P Γ q (R.predicateType T)) (mq : WellModed γ q .data) :
    L.Family (R.logicalType T) (R.predCompareBody L.code T p q) :=
  (h.evalBody_family hT mT hp mp).code_iff (h.evalBody_family hT mT hq mq)

 theorem predCompare_intro (K : QuantifierRoute L.witnesses C L.base J)
    (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data)
    (hq : HasType P Γ q (R.predicateType T)) (mq : WellModed γ q .data)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) y,
      HasType P Δ y ((R.rename e.names).logicalType (T.rename e.names)) → WellModed δ y .data →
      Equivalent P Δ δ ((R.rename e.names).eval (T.rename e.names) (p.rename e.names) y)
        ((R.rename e.names).eval (T.rename e.names) (q.rename e.names) y)) :
    Proves P Γ γ (R.predCompare L.code K.code T p q) := by
  obtain ⟨s,hs⟩ := K.triple.domain.1
  apply L.all_intro_future K (h.logical_sorted hT) (h.logical_mode mT) (h.logical_sorted hT s hs)
    (h.predCompareBody_family hT mT hp mp hq mq)
  intro Δ δ e y hy my
  rw [predCompareBody_rename,predCompareBody_instantiate]
  have ht := fun t ht => e.typing (hT t ht)
  have hy' : HasType P Δ y ((R.rename e.names).logicalType (T.rename e.names)) := by
    simpa only [logicalType_rename] using hy
  exact (L.rename e).iff_of_equivalent
    ((h.rename e).eval_formula ht (e.moded mT)
      (by simpa only [predicateType_rename] using e.typing hp) (e.moded mp) hy' my)
    ((h.rename e).eval_formula ht (e.moded mT)
      (by simpa only [predicateType_rename] using e.typing hq) (e.moded mq) hy' my)
    (hh Δ δ e y hy' my)
end Formed
end ChannelCode

end PureTypeSystem.Labelled

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
namespace DataWrapper
theorem reencodeBody_subst (R R' : DataWrapper S true) (T : Expr S) (σ : Nat → Expr S) :
    (reencodeBody R R' T).subst (Expr.liftSub σ) =
      reencodeBody (R.subst σ) (R'.subst σ) (T.subst σ) := by
  simp only [reencodeBody,reencode_subst,subst_rename,rename_subst,
    Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
end DataWrapper
namespace Expr
theorem liftSub_succ_natural (σ : Nat → Expr S) :
    liftSub (liftSub σ) ∘ liftRen Nat.succ =
      (fun n => (liftSub σ n).rename (liftRen Nat.succ)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Function.comp_apply,liftSub,liftRen,PureTypeSystem.Expr.liftRen,rename_comp]
    rfl
end Expr
namespace ChannelCode
variable (R : ChannelCode S)
theorem pred_subst (T Q : Expr S) (σ : Nat → Expr S) :
    (R.pred T Q).subst σ = (R.subst σ).pred (T.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [pred,DataWrapper.build_subst,DataWrapper.argSub,ite_true, if_true,
    Expr.compose_subst,DataWrapper.reencodeBody_subst,rawType_subst,subst]

theorem classBody_subst (L : LogicCode S) (K : QuantifierCode S) (T G y : Expr S) (σ : Nat → Expr S) :
    (R.classBody L K T G y).subst (Expr.liftSub σ) =
      (R.subst σ).classBody (L.subst σ) (K.subst σ) (T.subst σ)
        (G.subst (Expr.liftSub σ)) (y.subst σ) := by
  simp only [classBody,relation_subst,subst,rename,DataWrapper.subst_rename,DataWrapper.rename_subst,
    LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,
    ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,
    Expr.liftSub_succ_natural,Expr.liftSub,Expr.subst]
  rfl

theorem classPred_subst (L : LogicCode S) (K : QuantifierCode S) (T G y : Expr S) (σ : Nat → Expr S) :
    (R.classPred L K T G y).subst σ = (R.subst σ).classPred (L.subst σ) (K.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (y.subst σ) := by
  simp only [classPred,pred_subst,classBody_subst]
theorem unionBody_subst (L : LogicCode S) (K : QuantifierCode S) (T G y z : Expr S) (σ : Nat → Expr S) :
    (R.unionBody L K T G y z).subst (Expr.liftSub σ) = (R.subst σ).unionBody (L.subst σ) (K.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (y.subst σ) (z.subst σ) := by
  simp only [unionBody,LogicCode.disj_subst,classBody_subst,LogicCode.subst_rename,LogicCode.rename_subst]
  rfl
theorem unionPred_subst (L : LogicCode S) (K : QuantifierCode S) (T G y z : Expr S) (σ : Nat → Expr S) :
    (R.unionPred L K T G y z).subst σ = (R.subst σ).unionPred (L.subst σ) (K.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (y.subst σ) (z.subst σ) := by
  simp only [unionPred,pred_subst,unionBody_subst]

theorem isClass_subst (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (t : Fin 3) (y : Expr S) (σ : Nat → Expr S) :
    (R.isClass L KP T G Q t y).subst σ = (R.subst σ).isClass (L.subst σ) (KP.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (fun t => (Q t).subst (Expr.liftSub σ)) t (y.subst σ) := by
  simp only [isClass,← Expr.instantiate_subst,classPred_subst]
theorem edge_subst (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (t : Bool) (y z : Expr S) (σ : Nat → Expr S) :
    (R.edge L KP T G Q t y z).subst σ = (R.subst σ).edge (L.subst σ) (KP.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (fun t => (Q t).subst (Expr.liftSub σ)) t (y.subst σ) (z.subst σ) := by
  simp only [edge,LogicCode.conj_subst,isClass_subst,← Expr.instantiate_subst,unionPred_subst]

theorem formExBody_subst (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p z : Expr S) (σ : Nat → Expr S) :
    (R.formExBody L KP T G Q p z).subst (Expr.liftSub σ) = (R.subst σ).formExBody (L.subst σ) (KP.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (fun t => (Q t).subst (Expr.liftSub σ)) (p.subst σ) (z.subst σ) := by
  simp only [formExBody,LogicCode.conj_subst,edge_subst,eval_subst,subst,rename,
    DataWrapper.subst_rename,DataWrapper.rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,
    QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,
    Expr.subst_rename,Expr.rename_subst,Expr.liftSub_succ_natural,Expr.subst,Expr.liftSub]
  rfl
theorem pairForm_subst (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a z : Expr S) (σ : Nat → Expr S) :
    (R.pairForm L KY KP T G Q p a z).subst σ = (R.subst σ).pairForm (L.subst σ) (KY.subst σ) (KP.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (fun t => (Q t).subst (Expr.liftSub σ))
      (p.subst σ) (a.subst σ) (z.subst σ) := by
  simp only [pairForm,LogicCode.disj_subst,LogicCode.ex_subst,logicalType_subst,formExBody_subst,edge_subst]
theorem pairBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a : Expr S) (σ : Nat → Expr S) :
    (R.pairBody L KY KP T G Q p a).subst (Expr.liftSub σ) = (R.subst σ).pairBody (L.subst σ) (KY.subst σ) (KP.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (fun t => (Q t).subst (Expr.liftSub σ))
      (p.subst σ) (a.subst σ) := by
  simp only [pairBody,pairForm_subst,subst,rename,
    DataWrapper.subst_rename,DataWrapper.rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,
    QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,
    Expr.subst_rename,Expr.rename_subst,Expr.liftSub_succ_natural,Expr.subst,Expr.liftSub]
  rfl
theorem pairPred_subst (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a : Expr S) (σ : Nat → Expr S) :
    (R.pairPred L KY KP T G Q p a).subst σ = (R.subst σ).pairPred (L.subst σ) (KY.subst σ) (KP.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (fun t => (Q t).subst (Expr.liftSub σ))
      (p.subst σ) (a.subst σ) := by
  simp only [pairPred,pred_subst,pairBody_subst]
end ChannelCode

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

theorem decoderBody_rename (L : LogicCode S) (T bp : Expr S) (ρ : Nat → Nat) :
    (R.decoderBody L T bp).rename (Expr.liftRen ρ) =
      (R.rename ρ).decoderBody (L.rename ρ) (T.rename ρ) (bp.rename ρ) := by
  simp only [decoderBody,Expr.compose_rename,DataWrapper.evalCallback_rename,embedBody_rename,big_rename]
  rfl

theorem decode_rename (U : DataWrapper S true) (L : LogicCode S) (T bp : Expr S) (ρ : Nat → Nat) :
    (R.decode U L T bp).rename ρ =
      (R.rename ρ).decode (U.rename ρ) (L.rename ρ) (T.rename ρ) (bp.rename ρ) := by
  simp only [decode,DataWrapper.build_rename,DataWrapper.argRen,ite_true, if_true,decoderBody_rename]

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

namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H)
include h
 theorem markBody_family {T c₀ : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (t : Fin 8) (hc : HasType P Γ c₀ T) (mc : WellModed γ c₀ .data) :
    L.Family (R.bpType T) (R.markBody L.code t T c₀) := by
  have hv := h.tagged_typed hT mT (queryTag t) hc mc
  exact h.first.contraCallback_family (h.tower_sorted hT 4) (h.tower_mode mT 4) hv.1 hv.2

end Formed
end DoubleCode

namespace LogicCode
theorem subst_bottom (L : LogicCode S) (σ : Nat → Expr S) : (L.subst σ).bottom = L.bottom.subst σ := rfl
end LogicCode
namespace DoubleCode

section
variable (R : DoubleCode S)
theorem subst_first (σ : Nat → Expr S) : (R.subst σ).first = R.first.subst σ := rfl
theorem subst_second (σ : Nat → Expr S) : (R.subst σ).second = R.second.subst σ := rfl
theorem bpBottom_subst (L : LogicCode S) (T : Expr S) (σ : Nat → Expr S) :
    (R.bpBottom L T).subst σ = (R.subst σ).bpBottom (L.subst σ) (T.subst σ) := by
  simp only [bpBottom,DataWrapper.build_subst,big_subst,DataWrapper.argSub,ite_true, if_true,subst_first,LogicCode.subst_bottom,
    Expr.subst_rename,Expr.rename_subst]
  rfl
theorem paramType_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.paramType T).subst σ = (R.subst σ).paramType (T.subst σ) := by
  simp only [paramType,DataWrapper.apply_subst,bpType_subst]; rfl
theorem encode_rename (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T p : Expr S) (ρ : Nat → Nat) :
    (R.encode U L t T p).rename ρ =
      (R.rename ρ).encode (U.rename ρ) (L.rename ρ) t (T.rename ρ) (p.rename ρ) := by
  simp only [encode,DataWrapper.build_rename,DataWrapper.argRen,ite_true, if_true,big_rename,encodeBody_rename]
  rfl
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

theorem query_subst (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T m p : Expr S) (σ : Nat → Expr S) :
    (R.query U L t T m p).subst σ =
      (R.subst σ).query (U.subst σ) (L.subst σ) t (T.subst σ) (m.subst σ) (p.subst σ) := by
  simp only [query,DataWrapper.observe_subst,bpType_subst,encode_subst,subst_second,
    DataWrapper.argSub,Bool.not_true,Bool.false_eq_true,ite_false, if_false]
theorem queryPredBody_subst (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T m : Expr S) (σ : Nat → Expr S) :
    (R.queryPredBody U L t T m).subst (Expr.liftSub σ) =
      (R.subst σ).queryPredBody (U.subst σ) (L.subst σ) t (T.subst σ) (m.subst σ) := by
  simp only [queryPredBody,query_subst,subst_rename,rename_subst,DataWrapper.subst_rename,DataWrapper.rename_subst,
    LogicCode.subst_rename,LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H)
include h hU
 theorem query_formula (t : Fin 8) {T m p : Expr S}
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hm : HasType P Γ m (R.paramType T)) (mm : WellModed γ m .data)
    (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data) :
    L.Formula (R.query U L.code t T m p) := by
  have hb := h.encode_typed hU hT mT t hp mp
  exact (h.second.sound (h.bp_sorted hT) (h.bp_mode mT)).2 _ _ hm mm hb
end Formed

end

end DoubleCode
namespace ProbeCode

variable (R : ProbeCode S)

theorem funBuild_subst (A Q : Expr S) (σ : Nat → Expr S) :
    (R.funBuild A Q).subst σ =
      (R.subst σ).funBuild (A.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [funBuild,Expr.subst,singleType_subst,DataTail.send_subst]
  simp only [subst,DataTail.subst_rename,DataTail.rename_subst]
  rfl

theorem wrappedBuild_subst (A Q : Expr S) (σ : Nat → Expr S) :
    (R.wrappedBuild A Q).subst σ =
      (R.subst σ).wrappedBuild (A.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [wrappedBuild,DataWrapper.build_subst,funType_subst,DataWrapper.argSub,
    Bool.false_eq_true,ite_false, if_false,funBuild_subst]
  rfl

end ProbeCode
end

universe u
end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Relational
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled

section
universe u
variable {S : Type u}
namespace ProbeCode
variable (R : ProbeCode S)
theorem subst_rename (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.rename ρ).subst σ = R.subst (σ ∘ ρ) := by
  cases R; simp only [rename,subst,DataWrapper.subst_rename,PositiveDataWrapper.subst_rename,DataTail.subst_rename]
theorem rename_subst (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.subst σ).rename ρ = R.subst (fun n => (σ n).rename ρ) := by
  cases R; simp only [rename,subst,DataWrapper.rename_subst,PositiveDataWrapper.rename_subst,DataTail.rename_subst]
theorem carrier_rename (ρ : Nat → Nat) : R.carrier.rename ρ = (R.rename ρ).carrier := by
  simp only [carrier,body,domain,Expr.rename,DataWrapper.apply_rename,PositiveDataWrapper.apply_rename,
    funType_rename,PositiveDataWrapper.project_rename,DataWrapper.rename_comp,PositiveDataWrapper.rename_comp,
    Expr.liftRen,PureTypeSystem.Expr.liftRen,rename,DataTail.rename_comp]
  rfl
theorem carrier_subst (σ : Nat → Expr S) : R.carrier.subst σ = (R.subst σ).carrier := by
  simp only [carrier,body,domain,Expr.subst,DataWrapper.apply_subst,PositiveDataWrapper.apply_subst,
    funType_subst,PositiveDataWrapper.project_subst,DataWrapper.subst_rename,
    PositiveDataWrapper.subst_rename,
    subst_rename,rename_subst,Expr.liftSub]
  simp only [subst,DataWrapper.rename_subst,PositiveDataWrapper.rename_subst]
  rfl
theorem readBody_subst (w : Expr S) (σ : Nat → Expr S) :
    (R.readBody w).subst (Expr.liftSub σ) = (R.subst σ).readBody (w.subst σ) := by
  simp only [readBody,DataTail.read_subst,DataTail.subst_rename,DataTail.rename_subst,
    Expr.subst,Expr.liftSub,Expr.subst_rename,Expr.rename_subst,subst]
  rfl
theorem observe_subst (A v w : Expr S) (σ : Nat → Expr S) :
    (R.observe A v w).subst σ = (R.subst σ).observe (A.subst σ) (v.subst σ) (w.subst σ) := by
  simp only [observe,DataWrapper.observe_subst,funType_subst,specialize,Expr.subst,
    PositiveDataWrapper.inject_subst,readBody_subst,DataWrapper.argSub,Bool.not_false,ite_true, if_true,subst]
end ProbeCode
namespace DoubleCode
variable (R : DoubleCode S)
theorem decodeMap_subst (U : DataWrapper S true) (L : LogicCode S) (T : Expr S) (σ : Nat → Expr S) :
    (R.decodeMap U L T).subst (Expr.liftSub σ) =
      (R.subst σ).decodeMap (U.subst σ) (L.subst σ) (T.subst σ) := by
  simp only [decodeMap,decode_subst,subst_rename,rename_subst,DataWrapper.subst_rename,DataWrapper.rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
 theorem markBody_subst (L : LogicCode S) (t : Fin 8) (T c : Expr S) (σ : Nat → Expr S) :
    (R.markBody L t T c).subst (Expr.liftSub σ) =
      (R.subst σ).markBody (L.subst σ) t (T.subst σ) (c.subst σ) := by
  simp only [markBody,DataWrapper.contraCallback_subst,big_subst,tagged_subst,subst_first]
 theorem pointBody_subst (U : DataWrapper S true) (L : LogicCode S) (T c₀ c : Expr S) (σ : Nat → Expr S) :
    (R.pointBody U L T c₀ c).subst (Expr.liftSub σ) =
      (R.subst σ).pointBody (U.subst σ) (L.subst σ) (T.subst σ) (c₀.subst σ) (c.subst σ) := by
  simp only [pointBody,LogicCode.conj_subst,markBody_subst,Expr.compose_subst,
    DataWrapper.contraCallback_subst,decodeMap_subst,LogicCode.subst_rename,LogicCode.rename_subst]
  rfl
 theorem point_subst (U : DataWrapper S true) (L : LogicCode S) (T c₀ c : Expr S) (σ : Nat → Expr S) :
    (R.point U L T c₀ c).subst σ =
      (R.subst σ).point (U.subst σ) (L.subst σ) (T.subst σ) (c₀.subst σ) (c.subst σ) := by
  simp only [point,DataWrapper.build_subst,bpType_subst,DataWrapper.argSub,ite_true, if_true,
    pointBody_subst,subst_second]
 theorem dummy_subst (L : LogicCode S) (T : Expr S) (σ : Nat → Expr S) :
    (R.dummy L T).subst σ = (R.subst σ).dummy (L.subst σ) (T.subst σ) := by
  simp only [dummy,DataWrapper.build_subst,bpType_subst,DataWrapper.argSub,ite_true, if_true,
    subst_second,Expr.subst_rename,Expr.rename_subst,← LogicCode.top_subst]
  rfl
 theorem bundle_subst (L : LogicCode S) (A d m y : Expr S) (σ : Nat → Expr S) :
    (R.bundle L A d m y).subst σ =
      (R.subst σ).bundle (L.subst σ) (A.subst σ) (d.subst σ) (m.subst σ) (y.subst σ) := by
  simp only [bundle,bundleBody,DataWrapper.build_subst,DataWrapper.apply_subst,DataWrapper.argSub,ite_true, if_true,
    LogicCode.cond_subst,DataWrapper.contraCallback_subst,subst_first,subst_second,LogicCode.subst_rename,LogicCode.rename_subst]
  rfl
end DoubleCode

namespace ChannelCode
variable (R : ChannelCode S)
theorem subst_rename (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.rename ρ).subst σ = R.subst (σ ∘ ρ) := by
  cases R; simp only [rename,subst,DataWrapper.subst_rename]
theorem rename_subst (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.subst σ).rename ρ = R.subst (fun n => (σ n).rename ρ) := by
  cases R; simp only [rename,subst,DataWrapper.rename_subst]
theorem goodBody_subst (L : LogicCode S) (K : QuantifierCode S) (T Q : Expr S) (σ : Nat → Expr S) :
    (R.goodBody L K T Q).subst (Expr.liftSub σ) =
      (R.subst σ).goodBody (L.subst σ) (K.subst σ) (T.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [goodBody,LogicCode.conj_subst,roundRespect_subst,subst_rename,rename_subst,
    LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,
    ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,
    Expr.subst,Expr.liftSub]
  rfl
end ChannelCode
namespace RelationalCode
variable (R : RelationalCode S)
theorem subst_rename (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.rename ρ).subst σ = R.subst (σ ∘ ρ) := by
  cases R; simp only [rename,subst,ProbeCode.subst_rename,DataWrapper.subst_rename]
theorem rename_subst (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.subst σ).rename ρ = R.subst (fun n => (σ n).rename ρ) := by
  cases R; simp only [rename,subst,ProbeCode.rename_subst,DataWrapper.rename_subst]
theorem instantiate_raise (a : Expr S) : (R.rename Nat.succ).subst (Expr.single a) = R := by
  cases R; simp only [rename,subst,ProbeCode.instantiate_raise,DataWrapper.instantiate_raise]
theorem baseType_rename (A : Expr S) (ρ : Nat → Nat) :
    (R.baseType A).rename ρ = (R.rename ρ).baseType  (A.rename ρ) :=
  R.probe.initial.apply_rename A ρ
theorem channel_subst (σ : Nat → Expr S) : (R.subst σ).channel = R.channel.subst σ := rfl
theorem baseType_subst (A : Expr S) (σ : Nat → Expr S) :
    (R.baseType A).subst σ = (R.subst σ).baseType  (A.subst σ) :=
  R.probe.initial.apply_subst A σ
theorem queryBody_subst (L : LogicCode S) (t : Fin 7) (A m : Expr S) (σ : Nat → Expr S) :
    (R.queryBody L t A m).subst (Expr.liftSub σ) = (R.subst σ).queryBody (L.subst σ) t (A.subst σ) (m.subst σ) := by
  simp only [queryBody,DoubleCode.queryPredBody_subst,ProbeCode.rawType_subst,ProbeCode.doubled,DoubleCode.subst,subst]
  rfl
theorem goodBody_subst (L : LogicCode S) (KY : QuantifierCode S) (A m : Expr S) (σ : Nat → Expr S) :
    (R.goodBody L KY A m).subst (Expr.liftSub σ) = (R.subst σ).goodBody (L.subst σ) (KY.subst σ) (A.subst σ) (m.subst σ) := by
  simp only [goodBody,ChannelCode.goodBody_subst,baseType_subst,queryBody_subst,channel_subst]
theorem pair_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A m p a : Expr S) (σ : Nat → Expr S) :
    (R.pair L KY KP A m p a).subst σ = (R.subst σ).pair (L.subst σ) (KY.subst σ) (KP.subst σ) (A.subst σ) (m.subst σ) (p.subst σ) (a.subst σ) := by
  simp only [pair,ChannelCode.pairPred_subst,baseType_subst,goodBody_subst,queryBody_subst,channel_subst]
theorem rawTop_subst (L : LogicCode S) (A : Expr S) (σ : Nat → Expr S) :
    (R.rawTop L A).subst σ = (R.subst σ).rawTop (L.subst σ) (A.subst σ) := by
  simp only [rawTop,DataWrapper.build_subst,baseType_subst,DataWrapper.argSub,ite_true, if_true,subst,Expr.subst_rename,Expr.rename_subst,← LogicCode.top_subst]
  rfl
theorem point_subst (L : LogicCode S) (A y : Expr S) (σ : Nat → Expr S) :
    (R.point L A y).subst σ = (R.subst σ).point (L.subst σ) (A.subst σ) (y.subst σ) := by
  simp only [point,DoubleCode.point_subst,ProbeCode.rawType_subst,rawTop_subst,ChannelCode.toRaw_subst,baseType_subst,ProbeCode.doubled,DoubleCode.subst,subst]
  rfl
theorem bundle_subst (L : LogicCode S) (A m y : Expr S) (σ : Nat → Expr S) :
    (R.bundle L A m y).subst σ = (R.subst σ).bundle (L.subst σ) (A.subst σ) (m.subst σ) (y.subst σ) := by
  simp only [bundle,DoubleCode.bundle_subst,DoubleCode.dummy_subst,ProbeCode.paramType_subst,ProbeCode.rawType_subst,point_subst,ProbeCode.doubled,DoubleCode.subst,subst]
  rfl
theorem diamond_subst (L : LogicCode S) (A m v y : Expr S) (σ : Nat → Expr S) :
    (R.diamond L A m v y).subst σ = (R.subst σ).diamond (L.subst σ) (A.subst σ) (m.subst σ) (v.subst σ) (y.subst σ) := by
  simp only [diamond,ProbeCode.observe_subst,bundle_subst,subst]
theorem partBody_subst (L : LogicCode S) (A m v : Expr S) (σ : Nat → Expr S) :
    (R.partBody L A m v).subst (Expr.liftSub σ) = (R.subst σ).partBody (L.subst σ) (A.subst σ) (m.subst σ) (v.subst σ) := by
  simp only [partBody,diamond_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
 theorem part_subst (L : LogicCode S) (A m v : Expr S) (σ : Nat → Expr S) :
    (R.part L A m v).subst σ = (R.subst σ).part (L.subst σ) (A.subst σ) (m.subst σ) (v.subst σ) := by
  simp only [part,ChannelCode.pred_subst,baseType_subst,partBody_subst,channel_subst]
 theorem sb_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A m v a : Expr S) (σ : Nat → Expr S) :
    (R.sb L KY KP A m v a).subst σ = (R.subst σ).sb (L.subst σ) (KY.subst σ) (KP.subst σ)
      (A.subst σ) (m.subst σ) (v.subst σ) (a.subst σ) := by
  simp only [sb,DoubleCode.query_subst,ProbeCode.rawType_subst,pair_subst,part_subst,
    ProbeCode.doubled,DoubleCode.subst,subst]
  rfl
 theorem liftBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A m a : Expr S) (σ : Nat → Expr S) :
    (R.liftBody L KY KP A m a).subst (Expr.liftSub σ) = (R.subst σ).liftBody (L.subst σ) (KY.subst σ) (KP.subst σ)
      (A.subst σ) (m.subst σ) (a.subst σ) := by
  simp only [liftBody,sb_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub,QuantifierCode.subst,QuantifierCode.rename,
    ProofWrapper.subst_rename,ProofWrapper.rename_subst]
  rfl
 theorem lift_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A m a : Expr S) (σ : Nat → Expr S) :
    (R.lift L KY KP A m a).subst σ = (R.subst σ).lift (L.subst σ) (KY.subst σ) (KP.subst σ)
      (A.subst σ) (m.subst σ) (a.subst σ) := by
  simp only [lift,DataWrapper.build_subst,ProbeCode.carrier_subst,DataWrapper.argSub,ite_true, if_true,
    liftBody_subst,subst]
end RelationalCode
end

section
universe u
variable {S : Type u} {P : Specification S}
namespace RelationalCode.Formed

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {R : RelationalCode S}
    (H : R.Formed L I J k p n g j h)
include H
theorem rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) :
    (R.rename e.names).Formed (L.rename e) I J k p n g j h :=
  ⟨H.probe.rename e,H.channel.rename e⟩
theorem base_sorted {A : Expr S} (hA : HasType P Γ A (.sort R.probe.seed)) :
    SortedAt P Γ (R.baseType A) k :=
  H.probe.initial.sorted (fun s hs => by cases hs; exact hA)
theorem base_mode {A : Expr S} (mA : WellModed γ A .data) :
    WellModed γ (R.baseType A) .data := H.probe.initial.mode mA
theorem rawTop_typed {A : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data) :
    HasType P Γ (R.rawTop L.code A) (R.probe.rawType A) ∧ WellModed γ (R.rawTop L.code A) .data :=
  (H.probe.raw.sound (H.base_sorted hA) (H.base_mode mA)).1 _ (.constant L.top_formula)
end

end RelationalCode.Formed

namespace DoubleCode
variable (R : DoubleCode S)
theorem accessBody_subst (L : LogicCode S) (A guard w fi : Expr S) (σ : Nat → Expr S) :
    (R.accessBody L A guard w fi).subst (Expr.liftSub σ) =
      (R.subst σ).accessBody (L.subst σ) (A.subst σ) (guard.subst (Expr.liftSub σ)) (w.subst σ) (fi.subst (Expr.liftSub σ)) := by
  simp only [accessBody,LogicCode.cond_subst,Expr.compose_subst,DataWrapper.evalCallback_subst,
    DataWrapper.apply_subst,subst_first,subst_second,LogicCode.subst_rename,LogicCode.rename_subst,
    Expr.subst_rename,Expr.rename_subst,← LogicCode.top_subst]
  rfl
theorem access_subst (L : LogicCode S) (A guard w fi : Expr S) (σ : Nat → Expr S) :
    (R.access L A guard w fi).subst σ = (R.subst σ).access (L.subst σ) (A.subst σ)
      (guard.subst (Expr.liftSub σ)) (w.subst σ) (fi.subst (Expr.liftSub σ)) := by
  simp only [access,accessProbe,DataWrapper.observe_subst,DataWrapper.apply_subst,
    DataWrapper.build_subst,accessBody_subst,subst_first,subst_second,DataWrapper.argSub,
    Bool.not_true,Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
theorem innerMap_subst (U : DataWrapper S true) (L : LogicCode S) (T : Expr S) (σ : Nat → Expr S) :
    (R.innerMap U L T).subst (Expr.liftSub σ) = (R.subst σ).innerMap (U.subst σ) (L.subst σ) (T.subst σ) := by
  simp only [innerMap,innerProbe_subst,subst_rename,rename_subst,DataWrapper.subst_rename,DataWrapper.rename_subst,
    LogicCode.subst_rename,LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
theorem recoverAccess_subst (U : DataWrapper S true) (L : LogicCode S) (T w pMap : Expr S) (σ : Nat → Expr S) :
    (R.recoverAccess U L T w pMap).subst σ = (R.subst σ).recoverAccess (U.subst σ) (L.subst σ)
      (T.subst σ) (w.subst σ) (pMap.subst (Expr.liftSub σ)) := by
  simp only [recoverAccess,access_subst,paramType_subst,dummyBody_subst,accessMap,Expr.compose_subst,innerMap_subst]
end DoubleCode
end

section
universe u
variable {S : Type u}
namespace RelationalCode
variable (R : RelationalCode S)
theorem liftEvalBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A m i : Expr S) (σ : Nat → Expr S) :
    (R.liftEvalBody L KY KP A m i).subst (Expr.liftSub σ) = (R.subst σ).liftEvalBody (L.subst σ) (KY.subst σ) (KP.subst σ) (A.subst σ) (m.subst σ) (i.subst σ) := by
  simp only [liftEvalBody,ChannelCode.eval_subst,lift_subst,channel_subst,ProbeCode.carrier_subst,ChannelCode.subst_rename,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub,ChannelCode.rename_subst]
  simp only [subst,ProbeCode.carrier_rename,ProbeCode.rename_subst]
  rfl
theorem predLift_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A m i : Expr S) (σ : Nat → Expr S) :
    (R.predLift L KY KP A m i).subst σ = (R.subst σ).predLift (L.subst σ) (KY.subst σ) (KP.subst σ) (A.subst σ) (m.subst σ) (i.subst σ) := by
  simp only [predLift,ChannelCode.pred_subst,baseType_subst,liftEvalBody_subst,channel_subst]
theorem predLiftMap_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A i : Expr S) (σ : Nat → Expr S) :
    (R.predLiftMap L KY KP A i).subst (Expr.liftSub σ) = (R.subst σ).predLiftMap (L.subst σ) (KY.subst σ) (KP.subst σ) (A.subst σ) (i.subst σ) := by
  simp only [predLiftMap,predLift_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
theorem recoverLift_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A i w : Expr S) (σ : Nat → Expr S) :
    (R.recoverLift L KY KP A i w).subst σ = (R.subst σ).recoverLift (L.subst σ) (KY.subst σ) (KP.subst σ) (A.subst σ) (i.subst σ) (w.subst σ) := by
  simp only [recoverLift,DoubleCode.recoverAccess_subst,ProbeCode.rawType_subst,predLiftMap_subst,ProbeCode.doubled,DoubleCode.subst,subst]
  rfl
theorem recoverLiftBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (A i : Expr S) (σ : Nat → Expr S) :
    (R.recoverLiftBody L KY KP A i).subst (Expr.liftSub σ) = (R.subst σ).recoverLiftBody (L.subst σ) (KY.subst σ) (KP.subst σ) (A.subst σ) (i.subst σ) := by
  simp only [recoverLiftBody,recoverLift_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
end RelationalCode

namespace ProbeCode
variable (R : ProbeCode S)
theorem uniform_subst (Q : Expr S) (σ : Nat → Expr S) :
    (R.uniform Q).subst σ = (R.subst σ).uniform (Q.subst (Expr.liftSub (Expr.liftSub σ))) := by
  simp only [uniform,Expr.subst,domain,PositiveDataWrapper.apply_subst,wrappedBuild_subst,
    PositiveDataWrapper.project_subst,subst_rename,rename_subst,PositiveDataWrapper.subst_rename,
    Expr.liftSub]
  simp only [subst,PositiveDataWrapper.rename_subst]
  rfl
end ProbeCode
namespace RelationalCode
variable (R : RelationalCode S)
theorem probeFor_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (σ : Nat → Expr S) :
    (R.probeFor L KY KP i).subst σ =
      (R.subst σ).probeFor (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) := by
  simp only [probeFor,ProbeCode.uniform_subst,recoverLiftBody_subst,subst_rename,rename_subst,
    LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,
    ProofWrapper.subst_rename,ProofWrapper.rename_subst,PositiveDataWrapper.project_subst,
    PositiveDataWrapper.subst_rename,Expr.subst_rename,
    Expr.rename_subst,Expr.subst,Expr.liftSub]
  simp only [subst,ProbeCode.subst,PositiveDataWrapper.rename_subst]
  rfl
theorem le_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) (σ : Nat → Expr S) :
    (R.le L KY KP i x).subst σ = (R.subst σ).le (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) (x.subst σ) := by
  simp only [le,DataWrapper.observe_subst,ProbeCode.carrier_subst,probeFor_subst,DataWrapper.argSub,subst]
  rfl
end RelationalCode
end

section
universe u
variable {S : Type u} {P : Specification S}

namespace RelationalCode
variable (R : RelationalCode S)
theorem leBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (σ : Nat → Expr S) :
    (R.leBody L KY KP x).subst (Expr.liftSub σ) =
      (R.subst σ).leBody (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) := by
  simp only [leBody,le_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,
    QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,
    Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
theorem xCompareBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x y : Expr S) (σ : Nat → Expr S) :
    (R.xCompareBody L KY KP x y).subst (Expr.liftSub σ) =
      (R.subst σ).xCompareBody (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) (y.subst σ) := by
  simp only [xCompareBody,LogicCode.iff_subst,leBody_subst,LogicCode.subst_rename,LogicCode.rename_subst]
  rfl
theorem xCompare_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x y : Expr S) (σ : Nat → Expr S) :
    (R.xCompare L KY KP x y).subst σ =
      (R.subst σ).xCompare (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) (y.subst σ) := by
  simp only [xCompare,QuantifierCode.all_subst,ChannelCode.predicateType_subst,ProbeCode.carrier_subst,
    channel_subst,xCompareBody_subst]
  rfl

end RelationalCode
end

section
universe u
namespace RelationalCode
variable {S : Type u} (R : RelationalCode S)

theorem extStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i x y : Expr S) (σ : Nat → Expr S) :
    (R.extStep L KY KP i x y).subst σ =
      (R.subst σ).extStep (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) (x.subst σ) (y.subst σ) := by
  simp only [extStep,LogicCode.imp_subst,LogicCode.iff_subst,xCompare_subst,ChannelCode.eval_subst,ProbeCode.carrier_subst,channel_subst]
  try rfl

theorem extAtBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) (σ : Nat → Expr S) :
    (R.extAtBody L KY KP i x).subst (Expr.liftSub σ) =
      (R.subst σ).extAtBody (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) (x.subst σ) := by
  simp only [extAtBody,extStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl

theorem extAt_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) (σ : Nat → Expr S) :
    (R.extAt L KY KP i x).subst σ =
      (R.subst σ).extAt (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) (x.subst σ) := by
  simp only [extAt,QuantifierCode.all_subst,ChannelCode.logicalType_subst,ProbeCode.carrier_subst,channel_subst,extAtBody_subst]
  try rfl

theorem extBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (σ : Nat → Expr S) :
    (R.extBody L KY KP i).subst (Expr.liftSub σ) =
      (R.subst σ).extBody (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) := by
  simp only [extBody,extAt_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl

theorem extensional_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (σ : Nat → Expr S) :
    (R.extensional L KY KP i).subst σ =
      (R.subst σ).extensional (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) := by
  simp only [extensional,QuantifierCode.all_subst,ChannelCode.logicalType_subst,ProbeCode.carrier_subst,channel_subst,extBody_subst]
  try rfl

theorem validStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x i i' : Expr S) (σ : Nat → Expr S) :
    (R.validStep L KY KP x i i').subst σ =
      (R.subst σ).validStep (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) (i.subst σ) (i'.subst σ) := by
  simp only [validStep,LogicCode.imp_subst,LogicCode.iff_subst,ChannelCode.predCompare_subst,ProbeCode.carrier_subst,channel_subst,le_subst]
  try rfl

theorem validAtBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x i : Expr S) (σ : Nat → Expr S) :
    (R.validAtBody L KY KP x i).subst (Expr.liftSub σ) =
      (R.subst σ).validAtBody (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) (i.subst σ) := by
  simp only [validAtBody,validStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl

theorem validAt_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x i : Expr S) (σ : Nat → Expr S) :
    (R.validAt L KY KP x i).subst σ =
      (R.subst σ).validAt (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) (i.subst σ) := by
  simp only [validAt,QuantifierCode.all_subst,ChannelCode.predicateType_subst,ProbeCode.carrier_subst,channel_subst,validAtBody_subst]
  try rfl

theorem validBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (σ : Nat → Expr S) :
    (R.validBody L KY KP x).subst (Expr.liftSub σ) =
      (R.subst σ).validBody (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) := by
  simp only [validBody,validAt_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl

theorem valid_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (σ : Nat → Expr S) :
    (R.valid L KY KP x).subst σ =
      (R.subst σ).valid (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) := by
  simp only [valid,QuantifierCode.all_subst,ChannelCode.predicateType_subst,ProbeCode.carrier_subst,channel_subst,validBody_subst]
  try rfl
end RelationalCode
end

universe u
variable {S : Type u}
namespace ThreeCopyCode
variable (R : ThreeCopyCode S)
theorem firstType_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.firstType T).rename ρ = (R.rename ρ).firstType (T.rename ρ) := by
  simp only [firstType,DataWrapper.apply_rename,rename]
theorem firstType_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.firstType T).subst σ = (R.subst σ).firstType (T.subst σ) := by
  simp only [firstType,DataWrapper.apply_subst,subst]
theorem middleType_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.middleType T).rename ρ = (R.rename ρ).middleType (T.rename ρ) := by
  simp only [middleType,DoubleCode.carrier_rename,firstType_rename,rename]
theorem middleType_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.middleType T).subst σ = (R.subst σ).middleType (T.subst σ) := by
  simp only [middleType,DoubleCode.carrier_subst,firstType_subst,subst]
theorem carrier_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.carrier T).rename ρ = (R.rename ρ).carrier (T.rename ρ) := by
  simp only [carrier,DoubleCode.carrier_rename,middleType_rename,rename]
theorem carrier_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.carrier T).subst σ = (R.subst σ).carrier (T.subst σ) := by
  simp only [carrier,DoubleCode.carrier_subst,middleType_subst,subst]
theorem bitInner_subst (L : LogicCode S) (T y : Expr S) (σ : Nat → Expr S) :
    (R.bitInner L T y).subst σ = (R.subst σ).bitInner (L.subst σ) (T.subst σ) (y.subst σ) := by
  simp only [bitInner,DoubleCode.rec_subst,DoubleCode.bitBody_subst,middleType_subst,firstType_subst,subst]
theorem bitOuter_subst (L : LogicCode S) (T y : Expr S) (σ : Nat → Expr S) :
    (R.bitOuter L T y).subst σ = (R.subst σ).bitOuter (L.subst σ) (T.subst σ) (y.subst σ) := by
  simp only [bitOuter,DoubleCode.bit_subst,middleType_subst,subst]
theorem observe_subst (L : LogicCode S) (T y a : Expr S) (σ : Nat → Expr S) :
    (R.observe L T y a).subst σ = (R.subst σ).observe (L.subst σ) (T.subst σ) (y.subst σ) (a.subst σ) := by
  simp only [observe,DoubleCode.rec_subst,DoubleCode.recBody_subst,DataWrapper.contraCallback_subst,middleType_subst,firstType_subst,subst]
theorem tagged_subst (L : LogicCode S) (t : Fin 3) (T x : Expr S) (σ : Nat → Expr S) :
    (R.tagged L t T x).subst σ = (R.subst σ).tagged (L.subst σ) t (T.subst σ) (x.subst σ) := by
  simp only [tagged,DoubleCode.emb_subst,DataWrapper.reencode_subst,middleType_subst,firstType_subst,subst]
end ThreeCopyCode
end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Specialization
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate _root_.OAI.PureTypeSystem.instCountableExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled

section
universe u
variable {S : Type u}
namespace ObservationCode
variable (O : ObservationCode S)
theorem subst_rename (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (O.rename ρ).subst σ = O.subst (σ ∘ ρ) := by
  cases O; simp only [rename,subst,RelationalCode.subst_rename,DoubleCode.subst_rename]
theorem rename_subst (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (O.subst σ).rename ρ = O.subst (fun i => (σ i).rename ρ) := by
  cases O; simp only [rename,subst,RelationalCode.rename_subst,DoubleCode.rename_subst]
theorem instantiate_raise (a : Expr S) : (O.rename Nat.succ).subst (Expr.single a) = O := by
  cases O; simp only [rename,subst,RelationalCode.instantiate_raise,DoubleCode.instantiate_raise]
theorem copies_rename (ρ : Nat → Nat) : O.copies.rename ρ = (O.rename ρ).copies := rfl
theorem copies_subst (σ : Nat → Expr S) : O.copies.subst σ = (O.subst σ).copies := rfl
theorem carrier_rename (ρ : Nat → Nat) :
    (O.carrier ).rename ρ = (O.rename ρ).carrier  := by
  simp only [carrier,ThreeCopyCode.carrier_rename,copies_rename,ProbeCode.carrier_rename,rename,RelationalCode.rename,ProbeCode.rename]
  try rfl
theorem carrier_subst (σ : Nat → Expr S) :
    (O.carrier ).subst σ = (O.subst σ).carrier  := by
  simp only [carrier,ThreeCopyCode.carrier_subst,copies_subst,ProbeCode.carrier_subst,subst,RelationalCode.subst,ProbeCode.subst]
  try rfl
theorem tagged_subst (L : LogicCode S) (t : Fin 3) (x : Expr S) (σ : Nat → Expr S) :
    (O.tagged L t x).subst σ = (O.subst σ).tagged (L.subst σ) t (x.subst σ) := by
  simp only [tagged,ThreeCopyCode.tagged_subst,copies_subst,ProbeCode.carrier_subst,subst,RelationalCode.subst,ProbeCode.subst]
  try rfl
theorem bitInner_subst (L : LogicCode S) (y : Expr S) (σ : Nat → Expr S) :
    (O.bitInner L y).subst σ = (O.subst σ).bitInner (L.subst σ) (y.subst σ) := by
  simp only [bitInner,ThreeCopyCode.bitInner_subst,copies_subst,ProbeCode.carrier_subst,subst,RelationalCode.subst,ProbeCode.subst]
  try rfl
theorem bitOuter_subst (L : LogicCode S) (y : Expr S) (σ : Nat → Expr S) :
    (O.bitOuter L y).subst σ = (O.subst σ).bitOuter (L.subst σ) (y.subst σ) := by
  simp only [bitOuter,ThreeCopyCode.bitOuter_subst,copies_subst,ProbeCode.carrier_subst,subst,RelationalCode.subst,ProbeCode.subst]
  try rfl
theorem observe_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i y : Expr S) (σ : Nat → Expr S) :
    (O.observe L KY KP i y).subst σ = (O.subst σ).observe (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) (y.subst σ) := by
  simp only [observe,ThreeCopyCode.observe_subst,copies_subst,ProbeCode.carrier_subst,RelationalCode.probeFor_subst,subst,RelationalCode.subst,ProbeCode.subst]
  try rfl
theorem observeBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (y : Expr S) (σ : Nat → Expr S) :
    (O.observeBody L KY KP y).subst (Expr.liftSub σ) = (O.subst σ).observeBody (L.subst σ) (KY.subst σ) (KP.subst σ) (y.subst σ) := by
  simp only [observeBody,observe_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem compareBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (σ : Nat → Expr S) :
    (O.compareBody L KY KP y z).subst (Expr.liftSub σ) = (O.subst σ).compareBody (L.subst σ) (KY.subst σ) (KP.subst σ) (y.subst σ) (z.subst σ) := by
  simp only [compareBody,LogicCode.iff_subst,observeBody_subst,LogicCode.subst_rename,LogicCode.rename_subst]
  try rfl
theorem compare_subst (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (σ : Nat → Expr S) :
    (O.compare L KY KP y z).subst σ = (O.subst σ).compare (L.subst σ) (KY.subst σ) (KP.subst σ) (y.subst σ) (z.subst σ) := by
  simp only [compare,QuantifierCode.all_subst,ChannelCode.predicateType_subst,ProbeCode.carrier_subst,subst,RelationalCode.subst,ProbeCode.subst,compareBody_subst]
  try rfl
theorem ae_subst (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (σ : Nat → Expr S) :
    (O.ae L KY KP y z).subst σ = (O.subst σ).ae (L.subst σ) (KY.subst σ) (KP.subst σ) (y.subst σ) (z.subst σ) := by
  simp only [ae,LogicCode.conj_subst,LogicCode.iff_subst,bitInner_subst,bitOuter_subst,compare_subst]
  try rfl
end ObservationCode
end

section
universe u v
variable {S : Type u} {P : Specification S} {α : Type v}
namespace LogicCode
variable (L : LogicCode S)
theorem choices_cons (t : α) (ts : List α) (mark property : α → Expr S) :
    L.choices (t::ts) mark property = L.disj (L.conj (mark t) (property t)) (L.choices ts mark property) := rfl

theorem choices_rename (xs : List α) (mark property : α → Expr S) (ρ : Nat → Nat) :
    (L.choices xs mark property).rename ρ =
      (L.rename ρ).choices xs (fun t => (mark t).rename ρ) (fun t => (property t).rename ρ) := by
  induction xs with
  | nil => rfl
  | cons t ts ih => simp only [choices_cons,disj_rename,conj_rename,ih]

theorem choices_subst (xs : List α) (mark property : α → Expr S) (σ : Nat → Expr S) :
    (L.choices xs mark property).subst σ =
      (L.subst σ).choices xs (fun t => (mark t).subst σ) (fun t => (property t).subst σ) := by
  induction xs with
  | nil => rfl
  | cons t ts ih => simp only [choices_cons,disj_subst,conj_subst,ih]
end LogicCode
namespace LogicSetup
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) {mark property : α → Expr S}

theorem choices_formula (xs : List α) (hm : ∀ t ∈ xs, L.Formula (mark t))
    (hp : ∀ t ∈ xs, L.Formula (property t)) : L.Formula (L.code.choices xs mark property) := by
  induction xs with
  | nil => exact L.bottom_formula
  | cons t ts ih =>
    exact L.disj_formula (L.conj_formula (hm t (by simp)) (hp t (by simp)))
      (ih (fun s hs => hm s (by simp [hs])) (fun s hs => hp s (by simp [hs])))

theorem choices_false (xs : List α) (hm : ∀ t ∈ xs, L.Formula (mark t))
    (hp : ∀ t ∈ xs, L.Formula (property t))
    (hn : ∀ t ∈ xs, Proves P Γ γ (L.neg (mark t))) :
    Equivalent P Γ γ (L.code.choices xs mark property) L.bottom := by
  induction xs with
  | nil =>
    obtain ⟨s,hs⟩ := L.bottom_formula.sorted L
    exact .refl hs
  | cons t ts ih =>
    have ht := hm t (by simp)
    have hpt := hp t (by simp)
    have hnt := hn t (by simp)
    have hc := L.choices_formula ts (fun s hs => hm s (by simp [hs])) (fun s hs => hp s (by simp [hs]))
    have hi := ih (fun s hs => hm s (by simp [hs])) (fun s hs => hp s (by simp [hs]))
      (fun s hs => hn s (by simp [hs]))
    apply L.equivalent_of_iff (L.choices_formula (t::ts) hm hp) L.bottom_formula
    change Proves P Γ γ (L.iff (L.disj (L.conj (mark t) (property t)) (L.code.choices ts mark property)) L.bottom)
    exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (mark t) else if pl_i = 1 then (L.code.choices ts mark property) else if pl_i = 2 then (property t) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) FiniteClassical.Formula.bot), (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp FiniteClassical.Formula.bot (FiniteClassical.Formula.atom 1)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp FiniteClassical.Formula.bot (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl; exacts [hnt, ((L).iff_of_equivalent (hc) (bottom_formula L) hi)])

theorem choices_select [DecidableEq α] (xs : List α) (q : α) (hq : q ∈ xs)
    (hnd : xs.Nodup) (hm : ∀ t ∈ xs, L.Formula (mark t))
    (hp : ∀ t ∈ xs, L.Formula (property t))
    (hn : ∀ t ∈ xs, Proves P Γ γ (L.code.sign (decide (q = t)) (mark t))) :
    Equivalent P Γ γ (L.code.choices xs mark property) (property q) := by
  induction xs with
  | nil => simp at hq
  | cons t ts ih =>
    have ht := hm t (by simp)
    have hpt := hp t (by simp)
    have hmt : ∀ s ∈ ts, L.Formula (mark s) := fun s hs => hm s (by simp [hs])
    have hps : ∀ s ∈ ts, L.Formula (property s) := fun s hs => hp s (by simp [hs])
    have hc := L.choices_formula ts hmt hps
    have hnt := hn t (by simp)
    by_cases he : q = t
    · subst q
      have hi := L.choices_false ts hmt hps (fun s hs => by
        have hne : t ≠ s := fun he => (List.nodup_cons.mp hnd).1 (he ▸ hs)
        simpa only [hne,decide_false,LogicCode.sign,Bool.false_eq_true,ite_false, if_false,LogicSetup.code_neg] using hn s (by simp [hs]))
      simp only [decide_true,LogicCode.sign,ite_true, if_true] at hnt
      apply L.equivalent_of_iff (L.choices_formula (t::ts) hm hp) hpt
      change Proves P Γ γ (L.iff (L.disj (L.conj (mark t) (property t)) (L.code.choices ts mark property)) (property t))
      exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (mark t) else if pl_i = 1 then (L.code.choices ts mark property) else if pl_i = 2 then (property t) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.atom 0), (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp FiniteClassical.Formula.bot (FiniteClassical.Formula.atom 1)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.atom 2)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl; exacts [hnt, ((L).iff_of_equivalent (hc) (bottom_formula L) hi)])
    · have hqt : q ∈ ts := (List.mem_cons.mp hq).resolve_left he
      have hi := ih hqt (List.nodup_cons.mp hnd).2 hmt hps (fun s hs => hn s (by simp [hs]))
      have hqp := hp q hq
      simp only [he,decide_false,LogicCode.sign,Bool.false_eq_true,ite_false, if_false] at hnt
      apply L.equivalent_of_iff (L.choices_formula (t::ts) hm hp) hqp
      change Proves P Γ γ (L.iff (L.disj (L.conj (mark t) (property t)) (L.code.choices ts mark property)) (property q))
      exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (mark t) else if pl_i = 1 then (L.code.choices ts mark property) else if pl_i = 2 then (property q) else if pl_i = 3 then (property t) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) FiniteClassical.Formula.bot), (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.atom 2)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) (FiniteClassical.Formula.atom 1)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 3) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.atom 2)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 3) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl; exacts [hnt, ((L).iff_of_equivalent (hc) (hqp) hi)])

namespace Family
variable {L} {T : Expr S} {ms ps : α → Expr S}
theorem choices (xs : List α) (hm : ∀ t ∈ xs, L.Family T (ms t))
    (hp : ∀ t ∈ xs, L.Family T (ps t)) :
    L.Family T ((L.code.rename Nat.succ).choices xs ms ps) := by
  intro Δ δ e a ha ma
  simp only [LogicCode.choices_rename,Expr.instantiate,LogicCode.choices_subst]
  have he : ((L.code.rename Nat.succ).rename (Expr.liftRen e.names)).subst (Expr.single a) = (L.rename e).code := by
    rw [LogicCode.rename_comp]
    have hn : Expr.liftRen e.names ∘ Nat.succ = Nat.succ ∘ e.names := by funext n; rfl
    rw [hn,← LogicCode.rename_comp,LogicCode.instantiate_raise,LogicSetup.code_rename]
  rw [he]
  exact (L.rename e).choices_formula xs (fun t ht => hm t ht Δ δ e a ha ma)
    (fun t ht => hp t ht Δ δ e a ha ma)
end Family
end LogicSetup
end

section
universe u
variable {S : Type u} {P : Specification S}
namespace DoubleCode
variable (R : DoubleCode S)

theorem realizationBody_instantiate (U : DataWrapper S true) (L : LogicCode S)
    (T c bp : Expr S) (Q : Fin 7 → Expr S) :
    (R.realizationBody U L T c Q).instantiate bp = L.choices (List.finRange 7)
      (fun t => R.mark L t.castSucc T c bp) (fun t => (Q t).instantiate (R.decode U L T bp)) := by
  change ((L.rename Nat.succ).choices _ _ _).subst (Expr.single bp) = _
  rw [LogicCode.choices_subst,LogicCode.instantiate_raise]
  congr 1
  · funext t; exact R.markBody_instantiate _ _ _ _ _
  · funext t
    change ((Q t).compose (R.decodeMap U L T)).instantiate bp = _
    rw [Expr.compose_instantiate,decodeMap_instantiate]

namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H)
    {T c : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hc : HasType P Γ c T) (mc : WellModed γ c .data)
    {s r : S} (hs : HasType P Γ T (.sort s)) (hr : HasType P Γ (R.bpType T) (.sort r))
    {Q : Fin 7 → Expr S} (hQ : ∀ t, L.Family (U.apply T) (Q t))
include h hU hT mT hc mc hs hr hQ

theorem realizationBody_family : L.Family (R.bpType T) (R.realizationBody U L.code T c Q) :=
  .choices _ (fun t _ => h.markBody_family hT mT t.castSucc hc mc)
    (fun t _ => (hQ t).compose (h.decodeMap_typed hU hT mT hs hr) hr)

theorem realization_typed :
    HasType P Γ (R.realization U L.code T c Q) (R.paramType T) ∧
      WellModed γ (R.realization U L.code T c Q) .data :=
  (h.second.sound (h.bp_sorted hT) (h.bp_mode mT)).1 _
    (h.realizationBody_family hU hT mT hc mc hs hr hQ)

theorem realization_evaluation {bp : Expr S}
    (hb : HasType P Γ bp (R.bpType T)) (mb : WellModed γ bp .data) :
    Equivalent P Γ γ (R.second.observe (R.bpType T) (R.realization U L.code T c Q) bp)
      (L.code.choices (List.finRange 7) (fun t => R.mark L.code t.castSucc T c bp)
        (fun t => (Q t).instantiate (R.decode U L.code T bp))) := by
  have he := h.second.cancellation (h.bp_sorted hT) (h.bp_mode mT)
    (h.realizationBody_family hU hT mT hc mc hs hr hQ) ⟨hb,mb⟩
  simpa only [DataWrapper.cancelFormula,ite_true, if_true,realization,realizationBody_instantiate] using he

theorem realization_query_decoded (t : Fin 7) {p : Expr S}
    (hp : HasType P Γ p (U.apply T)) (mp : WellModed γ p .data) :
    Equivalent P Γ γ (R.query U L.code t.castSucc T (R.realization U L.code T c Q) p)
      ((Q t).instantiate (R.decode U L.code T (R.encode U L.code t.castSucc T p))) := by
  have hb := h.encode_typed hU hT mT t.castSucc hp mp
  have hd := h.decode_typed hU hT mT hb.1 hb.2 hs
  have he := h.realization_evaluation hU hT mT hc mc hs hr hQ hb.1 hb.2
  have hm : ∀ u, L.Formula (R.mark L.code (u : Fin 7).castSucc T c (R.encode U L.code t.castSucc T p)) := by
    intro u
    simpa only [markBody_instantiate] using (h.markBody_family hT mT u.castSucc hc mc).instantiate hb.1 hb.2
  have hprop := fun u => (hQ u).instantiate hd.1 hd.2
  have hsel := L.choices_select (List.finRange 7) t (by simp) (by decide)
    (fun u _ => hm u) (fun u _ => hprop u) (fun u _ => by
      have hm := h.encode_mark hU hT mT t.castSucc u.castSucc hp mp hc mc
      have heq : (t.castSucc == u.castSucc) = decide (t = u) := by
        by_cases ht : t = u
        · simp [ht]
        · have hn : t.castSucc ≠ u.castSucc := fun h => ht (Fin.castSucc_inj.mp h)
          simp [ht, hn]
      simpa only [heq] using hm)
  have ho := h.realization_typed hU hT mT hc mc hs hr hQ
  have f₀ := (h.second.sound (h.bp_sorted hT) (h.bp_mode mT)).2 _ _ ho.1 ho.2 hb
  have f₁ := L.choices_formula (List.finRange 7) (fun u _ => hm u) (fun u _ => hprop u)
  obtain ⟨a,ha⟩ := f₀.sorted L
  obtain ⟨b,hb⟩ := f₁.sorted L
  obtain ⟨d,hd⟩ := (hprop t).sorted L
  exact he.trans hsel ha hb hd

end Formed
end DoubleCode
end

section
universe u
namespace SpecializedCode
variable {S : Type u} (B : SpecializedCode S)
theorem subst_rename (σ : Nat → Expr S) (ρ : Nat → Nat) : (B.rename ρ).subst σ = B.subst (σ ∘ ρ) := by
  simp only [rename,subst,ObservationCode.subst_rename,Expr.subst_rename]
theorem rename_subst (σ : Nat → Expr S) (ρ : Nat → Nat) : (B.subst σ).rename ρ = B.subst (fun n => (σ n).rename ρ) := by
  simp only [rename,subst,ObservationCode.rename_subst,Expr.rename_subst]
theorem instantiate_raise (a : Expr S) : (B.rename Nat.succ).subst (Expr.single a) = B := by
  simp only [rename,subst,ObservationCode.instantiate_raise,Expr.subst_lift_single]
theorem baseType_rename (ρ : Nat → Nat) : (B.baseType ).rename ρ = (B.rename ρ).baseType  := by
  simp only [baseType,RelationalCode.baseType_rename,rename,relational,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem baseType_subst (σ : Nat → Expr S) : (B.baseType ).subst σ = (B.subst σ).baseType  := by
  simp only [baseType,RelationalCode.baseType_subst,subst,relational,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem xType_subst (σ : Nat → Expr S) : (B.xType ).subst σ = (B.subst σ).xType  := by
  simp only [xType,ChannelCode.logicalType_subst,ProbeCode.carrier_subst,subst,relational,ObservationCode.subst,RelationalCode.channel,RelationalCode.subst]
  try rfl
theorem yType_rename (ρ : Nat → Nat) : (B.yType ).rename ρ = (B.rename ρ).yType  := by
  simp only [yType,ObservationCode.carrier_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem yType_subst (σ : Nat → Expr S) : (B.yType ).subst σ = (B.subst σ).yType  := by
  simp only [yType,ObservationCode.carrier_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem predType_rename (ρ : Nat → Nat) : (B.predType ).rename ρ = (B.rename ρ).predType  := by
  simp only [predType,ChannelCode.predicateType_rename,baseType_rename,rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename]
  try rfl
theorem ev_subst (v y : Expr S) (σ : Nat → Expr S) : (B.ev v y).subst σ = (B.subst σ).ev (v.subst σ) (y.subst σ) := by
  simp only [ev,ChannelCode.eval_subst,baseType_subst,subst,relational,ObservationCode.subst,RelationalCode.channel,RelationalCode.subst]
  try rfl
theorem gStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v y z : Expr S) (σ : Nat → Expr S) :
    (B.gStep L KY KP v y z).subst σ = (B.subst σ).gStep (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (y.subst σ) (z.subst σ) := by
  simp only [gStep,LogicCode.imp_subst,LogicCode.iff_subst,ObservationCode.ae_subst,ev_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem gAtBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (σ : Nat → Expr S) :
    (B.gAtBody L KY KP v y).subst (Expr.liftSub σ) = (B.subst σ).gAtBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (y.subst σ) := by
  simp only [gAtBody,gStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem gAt_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (σ : Nat → Expr S) :
    (B.gAt L KY KP v y).subst σ = (B.subst σ).gAt (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (y.subst σ) := by
  simp only [gAt,QuantifierCode.all_subst,yType_subst,gAtBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem gBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.gBody L KY KP v).subst (Expr.liftSub σ) = (B.subst σ).gBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [gBody,gAt_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem propertyG_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.propertyG L KY KP v).subst σ = (B.subst σ).propertyG (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [propertyG,QuantifierCode.all_subst,yType_subst,gBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem cStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x w : Expr S) (σ : Nat → Expr S) :
    (B.cStep L KY KP t v x w).subst σ = (B.subst σ).cStep (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (x.subst σ) (w.subst σ) := by
  simp only [cStep,LogicCode.iff_subst,ev_subst,ObservationCode.ae_subst,ObservationCode.tagged_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem cAtBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (σ : Nat → Expr S) :
    (B.cAtBody L KY KP t v x).subst (Expr.liftSub σ) = (B.subst σ).cAtBody (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (x.subst σ) := by
  simp only [cAtBody,cStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem cAt_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (σ : Nat → Expr S) :
    (B.cAt L KY KP t v x).subst σ = (B.subst σ).cAt (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (x.subst σ) := by
  simp only [cAt,QuantifierCode.all_subst,yType_subst,cAtBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem cBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (σ : Nat → Expr S) :
    (B.cBody L KY KP t v).subst (Expr.liftSub σ) = (B.subst σ).cBody (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) := by
  simp only [cBody,cAt_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem propertyC_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (σ : Nat → Expr S) :
    (B.propertyC L KY KP t v).subst σ = (B.subst σ).propertyC (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) := by
  simp only [propertyC,LogicCode.ex_subst,xType_subst,cBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem eStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x w : Expr S) (σ : Nat → Expr S) :
    (B.eStep L KY KP t v x w).subst σ = (B.subst σ).eStep (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (x.subst σ) (w.subst σ) := by
  simp only [eStep,LogicCode.iff_subst,LogicCode.disj_subst,ev_subst,ObservationCode.ae_subst,ObservationCode.tagged_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem eAtBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (σ : Nat → Expr S) :
    (B.eAtBody L KY KP t v x).subst (Expr.liftSub σ) = (B.subst σ).eAtBody (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (x.subst σ) := by
  simp only [eAtBody,eStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem eAt_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (σ : Nat → Expr S) :
    (B.eAt L KY KP t v x).subst σ = (B.subst σ).eAt (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (x.subst σ) := by
  simp only [eAt,QuantifierCode.all_subst,yType_subst,eAtBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem eBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (σ : Nat → Expr S) :
    (B.eBody L KY KP t v).subst (Expr.liftSub σ) = (B.subst σ).eBody (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) := by
  simp only [eBody,eAt_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem propertyE_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (σ : Nat → Expr S) :
    (B.propertyE L KY KP t v).subst σ = (B.subst σ).propertyE (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) := by
  simp only [propertyE,LogicCode.ex_subst,xType_subst,eBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem rPredStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (σ : Nat → Expr S) :
    (B.rPredStep L KY KP v x).subst σ = (B.subst σ).rPredStep (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (x.subst σ) := by
  simp only [rPredStep,ev_subst,ObservationCode.tagged_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem rPredBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.rPredBody L KY KP v).subst (Expr.liftSub σ) = (B.subst σ).rPredBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [rPredBody,rPredStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem rPred_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.rPred L KY KP v).subst σ = (B.subst σ).rPred (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [rPred,ChannelCode.pred_subst,ProbeCode.carrier_subst,rPredBody_subst,subst,relational,ObservationCode.subst,RelationalCode.channel,RelationalCode.subst]
  try rfl
theorem rStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (σ : Nat → Expr S) :
    (B.rStep L KY KP v x).subst σ = (B.subst σ).rStep (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (x.subst σ) := by
  simp only [rStep,LogicCode.imp_subst,RelationalCode.valid_subst,ev_subst,ObservationCode.tagged_subst,RelationalCode.le_subst,rPred_subst,subst,relational,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem rBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.rBody L KY KP v).subst (Expr.liftSub σ) = (B.subst σ).rBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [rBody,rStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem rAll_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.rAll L KY KP v).subst σ = (B.subst σ).rAll (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [rAll,QuantifierCode.all_subst,xType_subst,rBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem propertyR_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.propertyR L KY KP v).subst σ = (B.subst σ).propertyR (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [propertyR,LogicCode.imp_subst,RelationalCode.extensional_subst,rPred_subst,rAll_subst,subst,relational,ObservationCode.subst,RelationalCode.subst]
  try rfl
end SpecializedCode
end

universe u
variable {S : Type u} {P : Specification S}
namespace ObservationCode
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (O : ObservationCode S) (L : LogicSetup P Γ γ C) (I J k p n g j h : Set S)
namespace Formed
variable {O L I J k p n g j h} (H : O.Formed L I J k p n g j h)
    (KY : QuantifierRoute L.witnesses C L.base j) (KP : QuantifierRoute L.witnesses C L.base h)
include H
theorem rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) :
    (O.rename e.names).Formed (L.rename e) I J k p n g j h :=
  ⟨H.relational.rename e,H.inner.rename e,H.outer.rename e⟩
end Formed
end ObservationCode

end PureTypeSystem.Labelled

namespace PureTypeSystem.Labelled
universe u
variable {S : Type u} {P : Specification S}

namespace SpecializedCode

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (B : SpecializedCode S) (L : LogicSetup P Γ γ C) (I J k p n g j h : Set S)
namespace Formed
variable {B L I J k p n g j h} (H : B.Formed L I J k p n g j h)
    (KY : QuantifierRoute L.witnesses C L.base j) (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) :
    (B.rename e.names).Formed (L.rename e) I J k p n g j h := by
  refine ⟨H.observation.rename e,e.typing H.type_sorted,e.moded H.type_mode,?_,?_,?_⟩
  · have hh := congrArg (Expr.rename e.names) H.shape
    simpa only [yType_rename,ChannelCode.logicalType_rename,baseType_rename,SpecializedCode.rename,
      relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using hh
  · exact congrArg (DataWrapper.rename e.names) H.outer_second_shape
  · have hh := congrArg (Expr.rename e.names) H.outer_first_shape
    simpa only [DataWrapper.apply_rename,ThreeCopyCode.middleType_rename,ProbeCode.carrier_rename,
      baseType_rename,SpecializedCode.rename,relational,ObservationCode.rename,ObservationCode.copies,
      RelationalCode.rename,DoubleCode.rename,ThreeCopyCode.rename,ProbeCode.rename] using hh

theorem relational_formed : B.relational.Formed L I J k p n g j h := H.observation.relational

theorem base_sorted : SortedAt P Γ B.baseType k := H.relational_formed.base_sorted H.type_sorted
theorem base_mode : WellModed γ B.baseType .data := H.relational_formed.base_mode H.type_mode

end Formed
end

variable (B : SpecializedCode S)
theorem property_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v : Expr S) (σ : Nat → Expr S) :
    (B.property L KY KP t v).subst σ = (B.subst σ).property (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) := by
  fin_cases t <;> simp only [property,propertyG_subst,propertyC_subst,propertyE_subst,propertyR_subst]
theorem propertyBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v : Expr S) :
    (B.propertyBody L KY KP t).instantiate v = B.property L KY KP t v := by
  simp only [propertyBody,Expr.instantiate,property_subst,instantiate_raise,LogicCode.instantiate_raise,
    QuantifierCode.instantiate_raise,Expr.subst,Expr.single]

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem parameter_typed : HasType P Γ (B.parameter L.code KY.code KP.code) (B.relational.probe.paramType B.type) ∧
    WellModed γ (B.parameter L.code KY.code KP.code) .data := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  obtain ⟨r,hr⟩ := H.relational_formed.probe.mainTriple.product.1
  have hc := H.relational_formed.rawTop_typed H.type_sorted H.type_mode
  exact H.relational_formed.probe.doubled_formed.realization_typed H.relational_formed.channel.predicate
    (H.relational_formed.probe.raw_sorted H.type_sorted) (H.relational_formed.probe.raw_mode H.type_mode)
    hc.1 hc.2 (H.relational_formed.probe.raw_sorted H.type_sorted s hs)
    (H.relational_formed.probe.doubled_formed.bp_sorted (H.relational_formed.probe.raw_sorted H.type_sorted) r hr)
    (H.propertyBody_family KY KP)

theorem parameter_query_decoded (t : Fin 7) {v : Expr S} (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) :
    Equivalent P Γ γ
      (B.relational.probe.doubled.query B.relational.predicate L.code t.castSucc (B.relational.probe.rawType B.type)
        (B.parameter L.code KY.code KP.code) v)
      (B.property L.code KY.code KP.code t
        (B.relational.probe.doubled.decode B.relational.predicate L.code (B.relational.probe.rawType B.type)
          (B.relational.probe.doubled.encode B.relational.predicate L.code t.castSucc (B.relational.probe.rawType B.type) v))) := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  obtain ⟨r,hr⟩ := H.relational_formed.probe.mainTriple.product.1
  have hc := H.relational_formed.rawTop_typed H.type_sorted H.type_mode
  have he := H.relational_formed.probe.doubled_formed.realization_query_decoded H.relational_formed.channel.predicate
    (H.relational_formed.probe.raw_sorted H.type_sorted) (H.relational_formed.probe.raw_mode H.type_mode)
    hc.1 hc.2 (H.relational_formed.probe.raw_sorted H.type_sorted s hs)
    (H.relational_formed.probe.doubled_formed.bp_sorted (H.relational_formed.probe.raw_sorted H.type_sorted) r hr)
    (H.propertyBody_family KY KP) t hv mv
  simpa only [propertyBody_instantiate,parameter,RelationalCode.channel] using he
end Formed
end SpecializedCode
end PureTypeSystem.Labelled

namespace PureTypeSystem.Labelled

section
universe u
variable {S : Type u} {P : Specification S}
namespace SpecializedCode.Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

omit H in
theorem v_typed_rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) {v : Expr S}
    (hv : HasType P Γ v B.predType) : HasType P Δ (v.rename e.names) (B.rename e.names).predType := by
  simpa only [predType_rename] using e.typing hv
end SpecializedCode.Formed

namespace SpecializedCode
variable (B : SpecializedCode S)
theorem decoded_rename (L : LogicCode S) (t : Fin 7) (v : Expr S) (ρ : Nat → Nat) :
    (B.decoded L t v).rename ρ = (B.rename ρ).decoded (L.rename ρ) t (v.rename ρ) := by
  simp only [decoded,DoubleCode.decode_rename,DoubleCode.encode_rename,ProbeCode.rawType_rename,
    SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.rename,ProbeCode.rename]
  rfl
namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem decoded_typed (t : Fin 7) {v : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) :
    HasType P Γ (B.decoded L.code t v) B.predType ∧ WellModed γ (B.decoded L.code t v) .data := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  have ht := H.relational_formed.probe.raw_sorted H.type_sorted
  have mT := H.relational_formed.probe.raw_mode H.type_mode
  have he := H.relational_formed.probe.doubled_formed.encode_typed H.relational_formed.channel.predicate ht mT t.castSucc hv mv
  exact H.relational_formed.probe.doubled_formed.decode_typed H.relational_formed.channel.predicate ht mT he.1 he.2 (ht s hs)

theorem decoded_at (t : Fin 7) {v y : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    Equivalent P Γ γ (B.ev (B.decoded L.code t v) y) (B.ev v y) := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  have hy' := H.relational_formed.channel.toRaw_typed H.base_sorted H.base_mode (H.shape ▸ hy) my
  exact H.relational_formed.probe.doubled_formed.decode_encode H.relational_formed.channel.predicate
    (H.relational_formed.probe.raw_sorted H.type_sorted) (H.relational_formed.probe.raw_mode H.type_mode)
    t.castSucc hv mv hy'.1 hy'.2 (H.relational_formed.probe.raw_sorted H.type_sorted s hs)

theorem decoded_compare (t : Fin 7) {v : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) :
    Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.baseType (B.decoded L.code t v) v) := by
  have hd := H.decoded_typed t hv mv
  apply H.relational_formed.channel.predCompare_intro H.base_sorted H.base_mode KY hd.1 hd.2 hv mv
  intro Δ δ e y hy my
  simp only [decoded_rename]
  have hy' : HasType P Δ y (B.rename e.names).yType := by
    rw [(H.rename e).shape]
    simpa only [baseType_rename,SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,
      RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using hy
  simpa only [ev,baseType_rename,LogicSetup.code_rename,SpecializedCode.rename,relational,ObservationCode.rename,
    RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using
    (H.rename e).decoded_at t (v_typed_rename (B := B) e hv) (e.moded mv) hy' my

theorem parameter_query_formula (t : Fin 7) {v : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) :
    L.Formula (B.relational.probe.doubled.query B.relational.predicate L.code t.castSucc (B.relational.probe.rawType B.type)
      (B.parameter L.code KY.code KP.code) v) := by
  have hm := H.parameter_typed KY KP
  exact H.relational_formed.probe.doubled_formed.query_formula H.relational_formed.channel.predicate t.castSucc
    (H.relational_formed.probe.raw_sorted H.type_sorted) (H.relational_formed.probe.raw_mode H.type_mode) hm.1 hm.2 hv mv

/-- Exact source q_t(P), from actual cancellation and the proved respect law. -/
theorem parameter_query_oai (t : Fin 7) {v : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) :
    Equivalent P Γ γ
      (B.relational.probe.doubled.query B.relational.predicate L.code t.castSucc (B.relational.probe.rawType B.type)
        (B.parameter L.code KY.code KP.code) v)
      (B.property L.code KY.code KP.code t v) := by
  have hd := H.decoded_typed t hv mv
  have he := H.parameter_query_decoded KY KP t hv mv
  have hr := H.property_respect KY KP t hd.1 hd.2 hv mv (H.decoded_compare KY t hv mv)
  obtain ⟨s,hs⟩ := L.triple.codomain.1
  exact he.trans hr ((H.parameter_query_formula KY KP t hv mv).1 s hs)
    ((H.property_formula KY KP t hd.1 hd.2).1 s hs) ((H.property_formula KY KP t hv mv).1 s hs)
end Formed
end SpecializedCode
end

universe u
end PureTypeSystem.Labelled

end OAI
end

theorem solution.{u} : type_of% @OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.parameter_query_oai.{u} := @OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.parameter_query_oai.{u}
