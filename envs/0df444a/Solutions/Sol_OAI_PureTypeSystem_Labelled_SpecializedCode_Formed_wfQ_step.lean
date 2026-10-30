-- Prove2me | solution 1 for OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.wfQ_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:32:08.036992+00:00
-- url     : https://prove2.me/submissions/307e5aa4-b2b0-487c-a3a3-aa62fb60cdfe

import Mathlib
import Definitions.Def_TypeSystemNormalization
import Definitions.Def_OAIQ5T6000
import Theorems.Thm_OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_delta_congr
import Theorems.Thm_OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_goodBody_family
import Theorems.Thm_OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_induction_builder
import Theorems.Thm_OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_probe_exact
import Theorems.Thm_OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_probe_respStep
import Theorems.Thm_OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_propertyBody_family
import Theorems.Thm_OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_relation_tagged_same

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

 theorem all_formula (R : QuantifierRoute L.witnesses C L.base I)
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hs : HasType P Γ T (.sort s))
    (hQ : (L.rename (Embedding.cons hs .data)).Formula Q) : L.Formula (all R T Q) := by
  obtain ⟨ht,mt,st⟩ := raw_all R hT mT hs hQ
  obtain ⟨ha,ma,pa⟩ := R.outFormed.sound L.converters ht mt
  exact ⟨ha,ma,(R.outFormed.stable L.converters ht mt).1 st⟩

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

 theorem all_elim (R : QuantifierRoute L.witnesses C L.base I)
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hs : HasType P Γ T (.sort s))
    (hQ : (L.rename (Embedding.cons hs .data)).Formula Q)
    {a : Expr S} (ha : HasType P Γ a T) (ma : WellModed γ a .data)
    (hQa : L.Formula (Q.instantiate a))
    (hp : Proves P Γ γ (all R T Q)) : Proves P Γ γ (Q.instantiate a) := by
  obtain ⟨ht,mt,st⟩ := raw_all R hT mT hs hQ
  obtain ⟨ho,mo,po⟩ := R.outFormed.sound L.converters ht mt
  obtain ⟨r,hr⟩ := L.triple.codomain.1
  obtain ⟨f,hf,mf⟩ := (po.down st (ho r hr)).prove hp
  have heq : ((R.inCode.rename Nat.succ).apply Q).instantiate a = R.inCode.apply (Q.instantiate a) := by
    simp only [Expr.instantiate,ProofWrapper.apply_subst,ProofWrapper.instantiate_raise]
  have hap : Proves P Γ γ (R.inCode.apply (Q.instantiate a)) :=
    ⟨_,by simpa only [heq] using HasType.application hf ha,WellModed.app mf ma⟩
  obtain ⟨hq,mq,pq⟩ := R.inFormed.sound L.converters hQa.1 hQa.2.1
  obtain ⟨t,htt⟩ := R.triple.codomain.1
  exact (pq.down hQa.2.2 (hq t htt)).prove hap

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
theorem symm (h : Equivalent P Γ γ A B) : Equivalent P Γ γ B A := ⟨h.2,h.1⟩
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

theorem neg_rename (A : Expr S) (e : Embedding P Γ γ Δ δ) :
    (L.neg A).rename e.names = (L.rename e).neg (A.rename e.names) := by
  simp only [neg,imp_rename,bottom_rename]
theorem conj_rename (A B : Expr S) (e : Embedding P Γ γ Δ δ) :
    (L.conj A B).rename e.names = (L.rename e).conj (A.rename e.names) (B.rename e.names) := by
  simp only [conj,neg_rename,imp_rename]
theorem iff_rename (A B : Expr S) (e : Embedding P Γ γ Δ δ) :
    (L.iff A B).rename e.names = (L.rename e).iff (A.rename e.names) (B.rename e.names) := by
  simp only [iff,conj_rename,imp_rename]

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

theorem reencodeBody_instantiate (R R' : DataWrapper S true) (T w : Expr S) :
    (reencodeBody R R' T).instantiate w = reencode R R' T w := by
  simp only [reencodeBody,Expr.instantiate,reencode_subst,instantiate_raise,
    Expr.subst_lift_single,Expr.subst,Expr.single]

theorem reencodeBody_rename (R R' : DataWrapper S true) (T : Expr S) (ρ : Nat → Nat) :
    (reencodeBody R R' T).rename (Expr.liftRen ρ) =
      reencodeBody (R.rename ρ) (R'.rename ρ) (T.rename ρ) := by
  simp only [reencodeBody,reencode_rename,rename_comp,Expr.rename_comp,Expr.rename,
    Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J K : Set S} {R R' : DataWrapper S true}

theorem reencode_map (hR : Formed L I J R) (hR' : Formed L I K R') {T : Expr S}
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    {s : S} (hs : HasType P Γ (R.apply T) (.sort s)) :
    DataMap P Γ γ (R.apply T) (R'.apply T) (reencodeBody R R' T) := by
  let e := Embedding.cons (γ := γ) hs Mode.data
  have hh := (hR.rename e).reencode_typed (hR'.rename e)
    (fun t ht => e.typing (hT t ht)) (e.moded mT)
    (by simpa only [e,Embedding.cons,apply_rename] using HasType.var hs)
    (WellModed.var (γ := modeCons .data γ) 0)
  simpa only [DataMap,reencodeBody,e,Embedding.cons,← apply_rename] using hh

theorem reencode_evaluation (hR : Formed L I J R) (hR' : Formed L I K R') {T w a : Expr S}
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hw : HasType P Γ w (R.apply T)) (mw : WellModed γ w .data)
    (ha : HasType P Γ a T) (ma : WellModed γ a .data) :
    Equivalent P Γ γ (R'.observe T (reencode R R' T w) a) (R.observe T w a) := by
  simpa only [reencode,cancelFormula,ite_true, if_true,evalCallback_instantiate] using
    hR'.cancellation hT mT (hR.evalCallback_family hT mT hw mw) ⟨ha,ma⟩
end Formed
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
end LogicCode
namespace LogicSetup
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C)
theorem code_rename (e : Embedding P Γ γ Δ δ) : (L.rename e).code = L.code.rename e.names := rfl
theorem cond_formula {G A B : Expr S} (hG : L.Formula G) (hA : L.Formula A) (hB : L.Formula B) :
    L.Formula (L.code.cond G A B) :=
  L.disj_formula (L.conj_formula hG hA) (L.conj_formula (L.neg_formula hG) hB)

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
theorem predicate_sorted (hT : SortedAt P Γ T I) : SortedAt P Γ (R.predicateType T) H := h.predicate.sorted (h.raw.sorted hT)
theorem logical_mode (mT : WellModed γ T .data) : WellModed γ (R.logicalType T) .data := h.logical.mode mT
theorem predicate_mode (mT : WellModed γ T .data) : WellModed γ (R.predicateType T) .data := h.predicate.mode (h.raw.mode mT)

theorem toRaw_typed (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data) :
    HasType P Γ (R.toRaw T y) (R.rawType T) ∧ WellModed γ (R.toRaw T y) .data :=
  h.logical.reencode_typed h.raw hT mT hy my

theorem toLog_typed (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (hc : HasType P Γ c (R.rawType T)) (mc : WellModed γ c .data) :
    HasType P Γ (R.toLog T c) (R.logicalType T) ∧ WellModed γ (R.toLog T c) .data :=
  h.raw.reencode_typed h.logical hT mT hc mc

theorem round_typed (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data) :
    HasType P Γ (R.round T y) (R.logicalType T) ∧ WellModed γ (R.round T y) .data := by
  have hh := h.toRaw_typed hT mT hy my
  exact h.toLog_typed hT mT hh.1 hh.2

theorem eval_formula (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data)
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data) :
    L.Formula (R.eval T p y) := by
  have hh := h.toRaw_typed hT mT hy my
  exact (h.predicate.sound (h.raw.sorted hT) (h.raw.mode mT)).2 p _ hp mp hh

theorem pred_typed (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (hQ : L.Family (R.logicalType T) Q)
    {s : S} (hs : HasType P Γ (R.rawType T) (.sort s)) :
    HasType P Γ (R.pred T Q) (R.predicateType T) ∧ WellModed γ (R.pred T Q) .data :=
  (h.predicate.sound (h.raw.sorted hT) (h.raw.mode mT)).1 _
    (hQ.compose (h.raw.reencode_map h.logical hT mT hs) hs)

theorem primitive_round (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) {a : Expr S}
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    (ha : HasType P Γ a T) (ma : WellModed γ a .data) :
    Equivalent P Γ γ (R.logical.observe T (R.round T y) a) (R.logical.observe T y a) := by
  have hraw := h.toRaw_typed hT mT hy my
  have hround := h.round_typed hT mT hy my
  have he₁ := h.raw.reencode_evaluation h.logical hT mT hraw.1 hraw.2 ha ma
  have he₂ := h.logical.reencode_evaluation h.raw hT mT hy my ha ma
  have hf₁ := (h.logical.sound hT mT).2 _ a hround.1 hround.2 ⟨ha,ma⟩
  have hf₂ := (h.raw.sound hT mT).2 _ a hraw.1 hraw.2 ⟨ha,ma⟩
  have hf₃ := (h.logical.sound hT mT).2 _ a hy my ⟨ha,ma⟩
  obtain ⟨s,hs⟩ := L.triple.codomain.1
  exact he₁.trans he₂ (hf₁.1 s hs) (hf₂.1 s hs) (hf₃.1 s hs)

theorem pred_evaluation (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (hQ : L.Family (R.logicalType T) Q)
    {s : S} (hs : HasType P Γ (R.rawType T) (.sort s))
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data) :
    Equivalent P Γ γ (R.eval T (R.pred T Q) y) (Q.instantiate (R.round T y)) := by
  have hraw := h.toRaw_typed hT mT hy my
  have hcb := hQ.compose (h.raw.reencode_map h.logical hT mT hs) hs
  simpa only [eval,pred,rawType,DataWrapper.cancelFormula,ite_true, if_true,Expr.compose_instantiate,
    DataWrapper.reencodeBody_instantiate,round,toLog] using
      h.predicate.cancellation (h.raw.sorted hT) (h.raw.mode mT) hcb hraw
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

end Formed
end DoubleCode

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

theorem embedBody_rename (L : LogicCode S) (q : Fin 9) (T : Expr S) (ρ : Nat → Nat) :
    (R.embedBody L q T).rename (Expr.liftRen ρ) = (R.rename ρ).embedBody (L.rename ρ) q (T.rename ρ) := by
  simp only [embedBody,tagged_rename,rename_comp,LogicCode.rename_comp,Expr.rename_comp,Expr.rename]
  rfl

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

namespace DataWrapper
theorem apply_converts {b : Bool} (R : DataWrapper S b) {A B : Expr S}
    (h : Converts A B) : Converts (R.apply A) (R.apply B) := by
  induction R with
  | identity => exact h
  | positive R D e ih => exact .pi (.refl _) (ih.rename Nat.succ)
  | negative R U ih => exact .pi ih (.refl _)
end DataWrapper

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
theorem body_instantiate (a : Expr S) :
    R.body.instantiate a = R.funPath.apply (R.funType (R.lifting.project a)) := by
  simp only [body,Expr.instantiate,DataWrapper.apply_subst,funType_subst,
    PositiveDataWrapper.project_subst,Expr.subst,Expr.single,DataWrapper.instantiate_raise,
    PositiveDataWrapper.instantiate_raise,instantiate_raise]

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
  (L : LogicSetup P Γ γ C) (I J k p n g : Set S)

namespace Formed
variable {R L I J k p n g} (h : R.Formed L I J k p n g)
include h
theorem rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) :
    (R.rename e.names).Formed (L.rename e) I J k p n g :=
  ⟨h.mainTriple,h.funTriple,h.ax,h.initial.rename e,h.raw.rename e,h.back.rename e,
    h.funPath.rename e,h.lifting.rename e,h.tail.rename e⟩
omit h in
theorem seed_sorted (_h : R.Formed L I J k p n g) : SortedAt P Γ (.sort R.seed) (AxProfile P R.seed) := by
  obtain ⟨s,hs⟩ := L.triple.codomain.1
  exact fun t ht => HasType.sort_of_valid (L.bottom_formula.1 s hs).valid ht

theorem domain_sorted : SortedAt P Γ R.domain I := h.lifting.sorted h.seed_sorted
theorem domain_mode : WellModed γ R.domain .data := h.lifting.modes.1 _ (.sort _)
theorem raw_sorted {A : Expr S} (ha : HasType P Γ A (.sort R.seed)) :
    SortedAt P Γ (R.rawType A) p := h.raw.sorted (h.initial.sorted (fun s hs => by cases hs; exact ha))
theorem raw_mode {A : Expr S} (ma : WellModed γ A .data) : WellModed γ (R.rawType A) .data :=
  h.raw.mode (h.initial.mode ma)
theorem doubled_formed : R.doubled.Formed L p k p := ⟨h.back,h.raw⟩
theorem param_sorted {A : Expr S} (ha : HasType P Γ A (.sort R.seed)) :
    SortedAt P Γ (R.paramType A) p := h.doubled_formed.param_sorted (h.raw_sorted ha)
theorem param_mode {A : Expr S} (ma : WellModed γ A .data) : WellModed γ (R.paramType A) .data :=
  h.doubled_formed.param_mode (h.raw_mode ma)
theorem single_sorted {A : Expr S} (ha : HasType P Γ A (.sort R.seed)) :
    SortedAt P Γ (R.singleType A) p := h.doubled_formed.sorted (h.param_sorted ha)
theorem single_mode {A : Expr S} (ma : WellModed γ A .data) : WellModed γ (R.singleType A) .data :=
  h.doubled_formed.mode (h.param_mode ma)
theorem fun_sorted {A : Expr S} (ha : HasType P Γ A (.sort R.seed)) :
    SortedAt P Γ (R.funType A) g :=
  (h.single_sorted ha).arrow h.tail.carrier_sorted .dd (by rw [h.funTriple.output])
theorem fun_mode {A : Expr S} (ma : WellModed γ A .data) : WellModed γ (R.funType A) .data :=
  (h.single_mode ma).arrow h.tail.carrier_mode

theorem body_sorted {s : S} (hs : HasType P Γ R.domain (.sort s)) :
    SortedAt P (R.domain :: Γ) R.body J := by
  let e : Embedding P Γ γ (R.domain :: Γ) (modeCons .data γ) := Embedding.cons hs .data
  have hh := h.rename e
  have hp : HasType P (R.domain :: Γ) ((R.lifting.rename Nat.succ).project (.var 0)) (.sort R.seed) :=
    (hh.lifting.typed hh.seed_sorted).2 _ (by
      simpa only [domain,PositiveDataWrapper.apply_rename,Expr.rename,e,Embedding.cons,ProbeCode.rename] using HasType.var hs)
  exact hh.funPath.sorted (hh.fun_sorted hp)

theorem body_mode {s : S} (hs : HasType P Γ R.domain (.sort s)) :
    WellModed (modeCons .data γ) R.body .data := by
  let e : Embedding P Γ γ (R.domain :: Γ) (modeCons .data γ) := Embedding.cons hs .data
  have hh := h.rename e
  exact hh.funPath.mode (hh.fun_mode (hh.lifting.modes.2.2 _ (.var 0)))

theorem carrier_sorted : SortedAt P Γ R.carrier k := by
  intro r hr
  obtain ⟨s,hs,t,ht,hst⟩ := h.mainTriple.output ▸ hr
  exact HasType.product (h.domain_sorted s hs) (h.body_sorted (h.domain_sorted s hs) t ht) hst

theorem carrier_mode : WellModed γ R.carrier .data := by
  obtain ⟨s,hs⟩ := h.mainTriple.domain.1
  exact .pi h.domain_mode (h.body_mode (h.domain_sorted s hs))
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
theorem toLog_rename (T c : Expr S) (ρ : Nat → Nat) :
    (R.toLog T c).rename ρ = (R.rename ρ).toLog (T.rename ρ) (c.rename ρ) := by
  simp only [toLog,DataWrapper.reencode_rename,rename]
theorem toLog_subst (T c : Expr S) (σ : Nat → Expr S) :
    (R.toLog T c).subst σ = (R.subst σ).toLog (T.subst σ) (c.subst σ) := by
  simp only [toLog,DataWrapper.reencode_subst,subst]
theorem round_rename (T y : Expr S) (ρ : Nat → Nat) :
    (R.round T y).rename ρ = (R.rename ρ).round (T.rename ρ) (y.rename ρ) := by
  simp only [round,toRaw_rename,toLog_rename]
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
/-- Data quantification using a uniform formula callback; the quantified
    annotation is still the original retained direct profile. -/
theorem all_formula_family {I : Set S} (R : QuantifierRoute L.witnesses C L.base I)
    {T Q : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    {s : S} (hs : HasType P Γ T (.sort s)) (hQ : L.Family T Q) :
    L.Formula (all R T Q) := all_formula R hT mT hs (hQ.opened hs)

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

theorem all_elim_family {I : Set S} (R : QuantifierRoute L.witnesses C L.base I)
    {T Q : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    {s : S} (hs : HasType P Γ T (.sort s)) (hQ : L.Family T Q)
    {a : Expr S} (ha : HasType P Γ a T) (ma : WellModed γ a .data)
    (hp : Proves P Γ γ (all R T Q)) : Proves P Γ γ (Q.instantiate a) :=
  all_elim R hT mT hs (hQ.opened hs) ha ma (hQ.instantiate ha ma) hp
end LogicSetup

namespace QuantifierCode
variable (K : QuantifierCode S)
theorem rename_comp (ρ τ : Nat → Nat) : (K.rename τ).rename ρ = K.rename (ρ ∘ τ) := by
  cases K; simp only [rename,ProofWrapper.rename_comp]
theorem instantiate_raise (a : Expr S) : (K.rename Nat.succ).subst (Expr.single a) = K := by
  cases K; simp only [rename,subst,ProofWrapper.instantiate_raise]
theorem all_rename (T Q : Expr S) (ρ : Nat → Nat) :
    (K.all T Q).rename ρ = (K.rename ρ).all (T.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [all,rename,ProofWrapper.apply_rename,Expr.rename,ProofWrapper.rename_comp]
  rfl
theorem all_subst (T Q : Expr S) (σ : Nat → Expr S) :
    (K.all T Q).subst σ = (K.subst σ).all (T.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [all,subst,ProofWrapper.apply_subst,Expr.subst,ProofWrapper.subst_rename,ProofWrapper.rename_subst]
  rfl
end QuantifierCode
namespace QuantifierRoute
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {W : WitnessFamily P Γ γ}
    {C : Set (Set S)} {b I : Set S}
theorem code_rename (R : QuantifierRoute W C b I) (e : Embedding P Γ γ Δ δ) :
    (R.rename e).code = R.code.rename e.names := rfl
end QuantifierRoute
end PureTypeSystem.Labelled

namespace PureTypeSystem.Labelled.LogicSetup
universe u
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {γ : Nat → Mode}
    {C : Set (Set S)} (L : LogicSetup P Γ γ C)
theorem code_iff (A B : Expr S) : L.code.iff A B = L.iff A B := rfl
end PureTypeSystem.Labelled.LogicSetup

namespace PureTypeSystem.Labelled
universe u
variable {S : Type u} {P : Specification S}
namespace Expr
theorem lifted_comp (ρ τ : Nat → Nat) : liftRen ρ ∘ liftRen τ = liftRen (ρ ∘ τ) := by
  funext n; cases n <;> rfl

end Expr
namespace LogicCode
variable (L : LogicCode S)
theorem guardBody_rename (G Q : Expr S) (ρ : Nat → Nat) :
    (L.guardBody G Q).rename (Expr.liftRen ρ) =
      (L.rename ρ).guardBody (G.rename (Expr.liftRen ρ)) (Q.rename (Expr.liftRen ρ)) := by
  simp only [guardBody,imp_rename,rename_comp]
  rfl
theorem guardAll_rename (K : QuantifierCode S) (T G Q : Expr S) (ρ : Nat → Nat) :
    (L.guardAll K T G Q).rename ρ =
      (L.rename ρ).guardAll (K.rename ρ) (T.rename ρ)
        (G.rename (Expr.liftRen ρ)) (Q.rename (Expr.liftRen ρ)) := by
  simp only [guardAll,QuantifierCode.all_rename,guardBody_rename]
end LogicCode
namespace LogicSetup
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) {I : Set S} (K : QuantifierRoute L.witnesses C L.base I)
    {T G Q : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hG : L.Family T G) (hQ : L.Family T Q)
include hT mT hG hQ
 theorem guardAll_formula : L.Formula (L.code.guardAll K.code T G Q) := by
  obtain ⟨s,hs⟩ := K.triple.domain.1
  exact L.all_formula_family K hT mT (hT s hs) (hG.code_imp hQ)

end LogicSetup
end PureTypeSystem.Labelled

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

theorem evalPredBody_rename (T y : Expr S) (ρ : Nat → Nat) :
    (R.evalPredBody T y).rename (Expr.liftRen ρ) =
      (R.rename ρ).evalPredBody (T.rename ρ) (y.rename ρ) := by
  simp only [evalPredBody,eval_rename,rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,
    PureTypeSystem.Expr.liftRen]
  rfl
theorem evalPredBody_instantiate (T y p : Expr S) :
    (R.evalPredBody T y).instantiate p = R.eval T p y := by
  simp only [evalPredBody,Expr.instantiate,eval_subst,instantiate_raise,
    Expr.subst_lift_single,Expr.subst,Expr.single]
theorem compareBody_rename (L : LogicCode S) (T y z : Expr S) (ρ : Nat → Nat) :
    (R.compareBody L T y z).rename (Expr.liftRen ρ) =
      (R.rename ρ).compareBody (L.rename ρ) (T.rename ρ) (y.rename ρ) (z.rename ρ) := by
  simp only [compareBody,LogicCode.iff_rename,LogicCode.rename_comp,evalPredBody_rename]
  rfl

theorem relation_rename (L : LogicCode S) (K : QuantifierCode S) (T G y z : Expr S) (ρ : Nat → Nat) :
    (R.relation L K T G y z).rename ρ =
      (R.rename ρ).relation (L.rename ρ) (K.rename ρ) (T.rename ρ)
        (G.rename (Expr.liftRen ρ)) (y.rename ρ) (z.rename ρ) := by
  simp only [relation,LogicCode.guardAll_rename,predicateType_rename,compareBody_rename]

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H N : Set S} {R : ChannelCode S}
    (h : R.Formed L I J N H) {T y z : Expr S}
include h
 theorem evalPredBody_family (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data) :
    L.Family (R.predicateType T) (R.evalPredBody T y) := by
  intro Δ δ e p hp mp
  rw [evalPredBody_rename,evalPredBody_instantiate]
  apply (h.rename e).eval_formula (fun s hs => e.typing (hT s hs)) (e.moded mT) _ mp _ (e.moded my)
  · simpa only [predicateType_rename] using hp
  · simpa only [logicalType_rename] using e.typing hy
 theorem compareBody_family (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    (hz : HasType P Γ z (R.logicalType T)) (mz : WellModed γ z .data) :
    L.Family (R.predicateType T) (R.compareBody L.code T y z) :=
  (h.evalPredBody_family hT mT hy my).code_iff (h.evalPredBody_family hT mT hz mz)

 theorem relation_formula (K : QuantifierRoute L.witnesses C L.base H)
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    {G : Expr S} (hG : L.Family (R.predicateType T) G)
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    (hz : HasType P Γ z (R.logicalType T)) (mz : WellModed γ z .data) :
    L.Formula (R.relation L.code K.code T G y z) :=
  L.guardAll_formula K (h.predicate_sorted hT) (h.predicate_mode mT) hG
    (h.compareBody_family hT mT hy my hz mz)

end Formed
end ChannelCode

namespace LogicSetup
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {A B D : Expr S}

theorem Formula.equivalent_trans (hA : L.Formula A) (hB : L.Formula B) (hD : L.Formula D)
    (hab : Equivalent P Γ γ A B) (hbd : Equivalent P Γ γ B D) : Equivalent P Γ γ A D := by
  obtain ⟨s,hs⟩ := hA.sorted L
  obtain ⟨t,ht⟩ := hB.sorted L
  obtain ⟨r,hr⟩ := hD.sorted L
  exact hab.trans hbd hs ht hr
end LogicSetup
namespace ThreeCopyCode
variable (R : ThreeCopyCode S)

variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
namespace Formed
variable {R : ThreeCopyCode S} {L : LogicSetup P Γ γ C} {I X J₁ J₂ J₃ J₄ J₅ : Set S}
    (h : R.Formed L I X J₁ J₂ J₃ J₄ J₅)
include h
variable {T y a x : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
include hT mT
theorem tagged_typed (t : Fin 3) (hx : HasType P Γ x (R.source.apply T)) (mx : WellModed γ x .data) :
    HasType P Γ (R.tagged L.code t T x) (R.carrier T) ∧ WellModed γ (R.tagged L.code t T x) .data := by
  have hy := h.source.reencode_typed h.first hT mT hx mx
  have hz := h.inner.emb_typed (h.first.sorted hT) (h.first.mode mT) (t == 1) hy.1 hy.2
  exact h.outer.emb_typed (h.inner.sorted (h.first.sorted hT)) (h.inner.mode (h.first.mode mT)) (t == 2) hz.1 hz.2

end Formed
end ThreeCopyCode

namespace ChannelCode
variable (R : ChannelCode S)

theorem roundRespectBody_rename (L : LogicCode S) (T p : Expr S) (ρ : Nat → Nat) :
    (R.roundRespectBody L T p).rename (Expr.liftRen ρ) =
      (R.rename ρ).roundRespectBody (L.rename ρ) (T.rename ρ) (p.rename ρ) := by
  simp only [roundRespectBody,LogicCode.iff_rename,eval_rename,round_rename,rename_comp,
    LogicCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl

theorem roundRespectBody_instantiate (L : LogicCode S) (T p y : Expr S) :
    (R.roundRespectBody L T p).instantiate y = L.iff (R.eval T p y) (R.eval T p (R.round T y)) := by
  simp only [roundRespectBody,Expr.instantiate,LogicCode.iff_subst,LogicCode.instantiate_raise,
    eval_subst,round_subst,instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]

theorem roundRespect_rename (L : LogicCode S) (K : QuantifierCode S) (T p : Expr S) (ρ : Nat → Nat) :
    (R.roundRespect L K T p).rename ρ =
      (R.rename ρ).roundRespect (L.rename ρ) (K.rename ρ) (T.rename ρ) (p.rename ρ) := by
  simp only [roundRespect,QuantifierCode.all_rename,logicalType_rename,roundRespectBody_rename]

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

theorem goodBody_rename (L : LogicCode S) (K : QuantifierCode S) (T Q : Expr S) (ρ : Nat → Nat) :
    (R.goodBody L K T Q).rename (Expr.liftRen ρ) =
      (R.rename ρ).goodBody (L.rename ρ) (K.rename ρ) (T.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [goodBody,LogicCode.conj_rename,roundRespect_rename,rename_comp,LogicCode.rename_comp,
    QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl

theorem goodBody_instantiate (L : LogicCode S) (K : QuantifierCode S) (T Q p : Expr S) :
    (R.goodBody L K T Q).instantiate p = L.conj (R.roundRespect L K T p) (Q.instantiate p) := by
  simp only [goodBody,Expr.instantiate,LogicCode.conj_subst,roundRespect_subst,
    instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,
    Expr.subst_lift_single,Expr.subst,Expr.single]

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H N : Set S} {R : ChannelCode S}
    (h : R.Formed L I J N H) {T p Q : Expr S}
include h
theorem roundRespectBody_family (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data) :
    L.Family (R.logicalType T) (R.roundRespectBody L.code T p) := by
  intro Δ δ e y hy my
  rw [roundRespectBody_rename,roundRespectBody_instantiate]
  have ht := fun s hs => e.typing (hT s hs)
  have hp' : HasType P Δ (p.rename e.names) ((R.rename e.names).predicateType (T.rename e.names)) := by
    simpa only [predicateType_rename] using e.typing hp
  have hy' : HasType P Δ y ((R.rename e.names).logicalType (T.rename e.names)) := by
    simpa only [logicalType_rename] using hy
  have hr := (h.rename e).round_typed ht (e.moded mT) hy' my
  exact (L.rename e).iff_formula ((h.rename e).eval_formula ht (e.moded mT) hp' (e.moded mp) hy' my)
    ((h.rename e).eval_formula ht (e.moded mT) hp' (e.moded mp) hr.1 hr.2)

theorem roundRespect_formula (K : QuantifierRoute L.witnesses C L.base J)
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data) :
    L.Formula (R.roundRespect L.code K.code T p) := by
  obtain ⟨s,hs⟩ := K.triple.domain.1
  exact L.all_formula_family K (h.logical_sorted hT) (h.logical_mode mT)
    (h.logical_sorted hT s hs) (h.roundRespectBody_family hT mT hp mp)

theorem goodBody_family (K : QuantifierRoute L.witnesses C L.base J)
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hQ : L.Family (R.predicateType T) Q) :
    L.Family (R.predicateType T) (R.goodBody L.code K.code T Q) := by
  intro Δ δ e p hp mp
  rw [goodBody_rename,goodBody_instantiate]
  have hp' : HasType P Δ p ((R.rename e.names).predicateType (T.rename e.names)) := by
    simpa only [predicateType_rename] using hp
  exact (L.rename e).conj_formula ((h.rename e).roundRespect_formula (K.rename e)
    (fun s hs => e.typing (hT s hs)) (e.moded mT) hp' mp) (hQ _ _ e p hp mp)

end Formed
end ChannelCode

namespace LogicSetup.Formula
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {A B : Expr S}
/-- Binder-safe packaging of a pair of uniform proof transformers. -/
theorem equivalent_of_future (hA : L.Formula A) (hB : L.Formula B)
    (hab : ∀ Δ δ (e : Embedding P Γ γ Δ δ),
      Proves P Δ δ (A.rename e.names) → Proves P Δ δ (B.rename e.names))
    (hba : ∀ Δ δ (e : Embedding P Γ γ Δ δ),
      Proves P Δ δ (B.rename e.names) → Proves P Δ δ (A.rename e.names)) : Equivalent P Γ γ A B := by
  obtain ⟨s,hs⟩ := hA.sorted L
  obtain ⟨t,ht⟩ := hB.sorted L
  exact ⟨hab _ _ (Embedding.cons hs .proof) (Proves.of_var hs),
    hba _ _ (Embedding.cons ht .proof) (Proves.of_var ht)⟩
end LogicSetup.Formula

namespace Expr
theorem liftSub_single_liftRen_succ (a : Expr S) :
    liftSub (single a) ∘ liftRen Nat.succ = var := by
  funext n; cases n <;> rfl
end Expr
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

theorem classBody_rename (L : LogicCode S) (K : QuantifierCode S) (T G y : Expr S) (ρ : Nat → Nat) :
    (R.classBody L K T G y).rename (Expr.liftRen ρ) =
      (R.rename ρ).classBody (L.rename ρ) (K.rename ρ) (T.rename ρ)
        (G.rename (Expr.liftRen ρ)) (y.rename ρ) := by
  simp only [classBody,relation_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,
    Expr.rename_comp,Expr.lifted_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl

theorem classBody_instantiate (L : LogicCode S) (K : QuantifierCode S) (T G y w : Expr S) :
    (R.classBody L K T G y).instantiate w = R.relation L K T G w y := by
  simp only [classBody,Expr.instantiate,relation_subst,instantiate_raise,LogicCode.instantiate_raise,
    QuantifierCode.instantiate_raise,Expr.subst_rename,
    Expr.liftSub_single_liftRen_succ,Expr.subst,Expr.single,
    show Expr.single w ∘ Nat.succ = (Expr.var : Nat → Expr S) from rfl,Expr.subst_var]

namespace Formed
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H N : Set S} {R : ChannelCode S}
    (h : R.Formed L I J N H) (K : QuantifierRoute L.witnesses C L.base H)
    {T G Q y z w : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
include h hT mT
 theorem classBody_family (hG : L.Family (R.predicateType T) G)
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data) :
    L.Family (R.logicalType T) (R.classBody L.code K.code T G y) := by
  intro Δ δ e w hw mw
  rw [classBody_rename,classBody_instantiate]
  have hg : (L.rename e).Family ((R.rename e.names).predicateType (T.rename e.names))
      (G.rename (Expr.liftRen e.names)) := by simpa only [predicateType_rename] using hG.rename e
  exact (h.rename e).relation_formula (K.rename e) (fun s hs => e.typing (hT s hs)) (e.moded mT) hg
    (by simpa only [logicalType_rename] using hw) mw
    (by simpa only [logicalType_rename] using e.typing hy) (e.moded my)

 theorem unionBody_family (hG : L.Family (R.predicateType T) G)
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    (hz : HasType P Γ z (R.logicalType T)) (mz : WellModed γ z .data) :
    L.Family (R.logicalType T) (R.unionBody L.code K.code T G y z) :=
  (h.classBody_family K hT mT hG hy my).code_disj (h.classBody_family K hT mT hG hz mz)

 theorem classPred_typed (hG : L.Family (R.predicateType T) G)
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    {s : S} (hs : HasType P Γ (R.rawType T) (.sort s)) :
    HasType P Γ (R.classPred L.code K.code T G y) (R.predicateType T) ∧
      WellModed γ (R.classPred L.code K.code T G y) .data :=
  h.pred_typed hT mT (h.classBody_family K hT mT hG hy my) hs

 theorem unionPred_typed (hG : L.Family (R.predicateType T) G)
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    (hz : HasType P Γ z (R.logicalType T)) (mz : WellModed γ z .data)
    {s : S} (hs : HasType P Γ (R.rawType T) (.sort s)) :
    HasType P Γ (R.unionPred L.code K.code T G y z) (R.predicateType T) ∧
      WellModed γ (R.unionPred L.code K.code T G y z) .data :=
  h.pred_typed hT mT (h.unionBody_family K hT mT hG hy my hz mz) hs

end Formed
end ChannelCode

namespace LogicCode
variable (L : LogicCode S)
theorem negBody_rename (Q : Expr S) (ρ : Nat → Nat) :
    (L.negBody Q).rename (Expr.liftRen ρ) = (L.rename ρ).negBody (Q.rename (Expr.liftRen ρ)) := by
  simp only [negBody,neg_rename,rename_comp]
  rfl
theorem negBody_subst (Q : Expr S) (σ : Nat → Expr S) :
    (L.negBody Q).subst (Expr.liftSub σ) = (L.subst σ).negBody (Q.subst (Expr.liftSub σ)) := by
  simp only [negBody,neg_subst,subst,rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,
    Expr.subst_rename,Expr.rename_subst]
  rfl
theorem ex_rename (K : QuantifierCode S) (T Q : Expr S) (ρ : Nat → Nat) :
    (L.ex K T Q).rename ρ = (L.rename ρ).ex (K.rename ρ) (T.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [ex,neg_rename,QuantifierCode.all_rename,negBody_rename]
theorem ex_subst (K : QuantifierCode S) (T Q : Expr S) (σ : Nat → Expr S) :
    (L.ex K T Q).subst σ = (L.subst σ).ex (K.subst σ) (T.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [ex,neg_subst,QuantifierCode.all_subst,negBody_subst]
end LogicCode
namespace LogicSetup

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) {I : Set S} (K : QuantifierRoute L.witnesses C L.base I)
    {T Q B : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data) (hQ : L.Family T Q)
include hT mT hQ
theorem ex_formula : L.Formula (L.code.ex K.code T Q) := by
  obtain ⟨s,hs⟩ := K.triple.domain.1
  exact L.neg_formula (L.all_formula_family K hT mT (hT s hs) hQ.code_neg)

end

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (L : LogicSetup P Γ γ C) {I : Set S} (K : QuantifierRoute L.witnesses C L.base I)
    {T Q R : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hQ : L.Family T Q) (hR : L.Family T R)
include hT mT hQ hR
/-- Explicit uniform quantifier transport; no fixture of local witnesses leaks. -/
theorem all_map_future
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) a,
      HasType P Δ a (T.rename e.names) → WellModed δ a .data →
      Proves P Δ δ ((Q.rename (Expr.liftRen e.names)).instantiate a) →
      Proves P Δ δ ((R.rename (Expr.liftRen e.names)).instantiate a))
    (hp : Proves P Γ γ (K.code.all T Q)) : Proves P Γ γ (K.code.all T R) := by
  obtain ⟨s,hs⟩ := K.triple.domain.1
  apply L.all_intro_future K hT mT (hT s hs) hR
  intro Δ δ e a ha ma
  have hp' : Proves P Δ δ ((K.rename e).code.all (T.rename e.names) (Q.rename (Expr.liftRen e.names))) := by
    simpa only [QuantifierCode.all_rename,QuantifierRoute.code_rename] using hp.rename e
  exact hh Δ δ e a ha ma ((L.rename e).all_elim_family (K.rename e)
    (fun t ht => e.typing (hT t ht)) (e.moded mT) (e.typing (hT s hs)) (hQ.rename e) ha ma hp')

theorem all_equivalent_future
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) a,
      HasType P Δ a (T.rename e.names) → WellModed δ a .data →
      Equivalent P Δ δ ((Q.rename (Expr.liftRen e.names)).instantiate a)
        ((R.rename (Expr.liftRen e.names)).instantiate a)) :
    Equivalent P Γ γ (K.code.all T Q) (K.code.all T R) := by
  obtain ⟨s,hs⟩ := K.triple.domain.1
  have fq := L.all_formula_family K hT mT (hT s hs) hQ
  have fr := L.all_formula_family K hT mT (hT s hs) hR
  have forward {U V : Expr S} (hU : L.Family T U) (hV : L.Family T V)
      (hx : ∀ Δ δ (e : Embedding P Γ γ Δ δ) a,
        HasType P Δ a (T.rename e.names) → WellModed δ a .data →
        Equivalent P Δ δ ((U.rename (Expr.liftRen e.names)).instantiate a)
          ((V.rename (Expr.liftRen e.names)).instantiate a)) :
      ∀ Δ δ (e : Embedding P Γ γ Δ δ),
      Proves P Δ δ ((K.code.all T U).rename e.names) →
      Proves P Δ δ ((K.code.all T V).rename e.names) := by
    intro Δ δ e hp
    simp only [QuantifierCode.all_rename] at hp ⊢
    apply (L.rename e).all_map_future (K.rename e) (fun t ht => e.typing (hT t ht))
      (e.moded mT) (hU.rename e) (hV.rename e) ?_ hp
    intro Θ θ f a ha ma hu
    have ha' : HasType P Θ a (T.rename (f.names ∘ e.names)) := by
      simpa only [Expr.rename_comp] using ha
    have he := hx Θ θ (e.comp f) a ha' ma
    have hu' : Proves P Θ θ ((U.rename (Expr.liftRen (f.names ∘ e.names))).instantiate a) := by
      simpa only [Expr.rename_comp,Expr.lifted_comp] using hu
    simpa only [Expr.rename_comp,Expr.lifted_comp,Embedding.comp] using he.1.prove hu'
  exact fq.equivalent_of_future fr (forward hQ hR hh)
    (forward hR hQ (fun Δ δ e a ha ma => (hh Δ δ e a ha ma).symm))

end LogicSetup

namespace ChannelCode
variable (R : ChannelCode S)
theorem pred_rename (T Q : Expr S) (ρ : Nat → Nat) :
    (R.pred T Q).rename ρ = (R.rename ρ).pred (T.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [pred,DataWrapper.build_rename,rawType_rename,Expr.compose_rename,
    DataWrapper.reencodeBody_rename,DataWrapper.argRen,ite_true, if_true,rename]

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
theorem predCompare_rename (L : LogicCode S) (K : QuantifierCode S) (T p q : Expr S) (ρ : Nat → Nat) :
    (R.predCompare L K T p q).rename ρ =
      (R.rename ρ).predCompare (L.rename ρ) (K.rename ρ) (T.rename ρ) (p.rename ρ) (q.rename ρ) := by
  simp only [predCompare,QuantifierCode.all_rename,logicalType_rename,predCompareBody_rename]
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

 theorem predCompare_formula (K : QuantifierRoute L.witnesses C L.base J)
    (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data)
    (hq : HasType P Γ q (R.predicateType T)) (mq : WellModed γ q .data) :
    L.Formula (R.predCompare L.code K.code T p q) := by
  obtain ⟨s,hs⟩ := K.triple.domain.1
  exact L.all_formula_family K (h.logical_sorted hT) (h.logical_mode mT) (h.logical_sorted hT s hs)
    (h.predCompareBody_family hT mT hp mp hq mq)

 theorem predCompare_elim (K : QuantifierRoute L.witnesses C L.base J)
    (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data)
    (hq : HasType P Γ q (R.predicateType T)) (mq : WellModed γ q .data)
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    (he : Proves P Γ γ (R.predCompare L.code K.code T p q)) :
    Equivalent P Γ γ (R.eval T p y) (R.eval T q y) := by
  obtain ⟨s,hs⟩ := K.triple.domain.1
  have he' := L.all_elim_family K (h.logical_sorted hT) (h.logical_mode mT) (h.logical_sorted hT s hs)
    (h.predCompareBody_family hT mT hp mp hq mq) hy my he
  rw [predCompareBody_instantiate,LogicSetup.code_iff] at he'
  exact L.equivalent_of_iff (h.eval_formula hT mT hp mp hy my) (h.eval_formula hT mT hq mq hy my) he'

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

namespace ChannelCode
variable (R : ChannelCode S)
theorem classPred_rename (L : LogicCode S) (K : QuantifierCode S) (T G y : Expr S) (ρ : Nat → Nat) :
    (R.classPred L K T G y).rename ρ =
      (R.rename ρ).classPred (L.rename ρ) (K.rename ρ) (T.rename ρ)
        (G.rename (Expr.liftRen ρ)) (y.rename ρ) := by
  simp only [classPred,pred_rename,classBody_rename]
theorem unionBody_rename (L : LogicCode S) (K : QuantifierCode S) (T G y z : Expr S) (ρ : Nat → Nat) :
    (R.unionBody L K T G y z).rename (Expr.liftRen ρ) =
      (R.rename ρ).unionBody (L.rename ρ) (K.rename ρ) (T.rename ρ)
        (G.rename (Expr.liftRen ρ)) (y.rename ρ) (z.rename ρ) := by
  simp only [unionBody,LogicCode.disj_rename,LogicCode.rename_comp,classBody_rename]
  rfl
theorem unionPred_rename (L : LogicCode S) (K : QuantifierCode S) (T G y z : Expr S) (ρ : Nat → Nat) :
    (R.unionPred L K T G y z).rename ρ =
      (R.rename ρ).unionPred (L.rename ρ) (K.rename ρ) (T.rename ρ)
        (G.rename (Expr.liftRen ρ)) (y.rename ρ) (z.rename ρ) := by
  simp only [unionPred,pred_rename,unionBody_rename]
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

theorem isClass_rename (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (t : Fin 3) (y : Expr S) (ρ : Nat → Nat) :
    (R.isClass L KP T G Q t y).rename ρ = (R.rename ρ).isClass (L.rename ρ) (KP.rename ρ)
      (T.rename ρ) (G.rename (Expr.liftRen ρ)) (fun t => (Q t).rename (Expr.liftRen ρ)) t (y.rename ρ) := by
  simp only [isClass,← Expr.instantiate_rename,classPred_rename]
theorem isClass_subst (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (t : Fin 3) (y : Expr S) (σ : Nat → Expr S) :
    (R.isClass L KP T G Q t y).subst σ = (R.subst σ).isClass (L.subst σ) (KP.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (fun t => (Q t).subst (Expr.liftSub σ)) t (y.subst σ) := by
  simp only [isClass,← Expr.instantiate_subst,classPred_subst]
theorem edge_rename (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (t : Bool) (y z : Expr S) (ρ : Nat → Nat) :
    (R.edge L KP T G Q t y z).rename ρ = (R.rename ρ).edge (L.rename ρ) (KP.rename ρ)
      (T.rename ρ) (G.rename (Expr.liftRen ρ)) (fun t => (Q t).rename (Expr.liftRen ρ)) t (y.rename ρ) (z.rename ρ) := by
  simp only [edge,LogicCode.conj_rename,isClass_rename,← Expr.instantiate_rename,unionPred_rename]
theorem edge_subst (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (t : Bool) (y z : Expr S) (σ : Nat → Expr S) :
    (R.edge L KP T G Q t y z).subst σ = (R.subst σ).edge (L.subst σ) (KP.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (fun t => (Q t).subst (Expr.liftSub σ)) t (y.subst σ) (z.subst σ) := by
  simp only [edge,LogicCode.conj_subst,isClass_subst,← Expr.instantiate_subst,unionPred_subst]

theorem formExBody_rename (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p z : Expr S) (ρ : Nat → Nat) :
    (R.formExBody L KP T G Q p z).rename (Expr.liftRen ρ) = (R.rename ρ).formExBody (L.rename ρ) (KP.rename ρ)
      (T.rename ρ) (G.rename (Expr.liftRen ρ)) (fun t => (Q t).rename (Expr.liftRen ρ)) (p.rename ρ) (z.rename ρ) := by
  simp only [formExBody,LogicCode.conj_rename,LogicCode.rename_comp,edge_rename,eval_rename,
    rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.lifted_comp,Expr.rename,Expr.liftRen,
    PureTypeSystem.Expr.liftRen]
  rfl
theorem formExBody_subst (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p z : Expr S) (σ : Nat → Expr S) :
    (R.formExBody L KP T G Q p z).subst (Expr.liftSub σ) = (R.subst σ).formExBody (L.subst σ) (KP.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (fun t => (Q t).subst (Expr.liftSub σ)) (p.subst σ) (z.subst σ) := by
  simp only [formExBody,LogicCode.conj_subst,edge_subst,eval_subst,subst,rename,
    DataWrapper.subst_rename,DataWrapper.rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,
    QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,
    Expr.subst_rename,Expr.rename_subst,Expr.liftSub_succ_natural,Expr.subst,Expr.liftSub]
  rfl
theorem formExBody_instantiate (L : LogicCode S) (KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p z y : Expr S) :
    (R.formExBody L KP T G Q p z).instantiate y =
      L.conj (R.edge L KP T G Q false y z) (R.eval T p y) := by
  simp only [formExBody,Expr.instantiate,LogicCode.conj_subst,edge_subst,eval_subst,instantiate_raise,
    LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_rename,
    Expr.liftSub_single_liftRen_succ,Expr.subst,Expr.single,
    show Expr.single y ∘ Nat.succ = (Expr.var : Nat → Expr S) from rfl,Expr.subst_var]

theorem pairForm_rename (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a z : Expr S) (ρ : Nat → Nat) :
    (R.pairForm L KY KP T G Q p a z).rename ρ = (R.rename ρ).pairForm (L.rename ρ) (KY.rename ρ) (KP.rename ρ)
      (T.rename ρ) (G.rename (Expr.liftRen ρ)) (fun t => (Q t).rename (Expr.liftRen ρ))
      (p.rename ρ) (a.rename ρ) (z.rename ρ) := by
  simp only [pairForm,LogicCode.disj_rename,LogicCode.ex_rename,logicalType_rename,formExBody_rename,edge_rename]
theorem pairForm_subst (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a z : Expr S) (σ : Nat → Expr S) :
    (R.pairForm L KY KP T G Q p a z).subst σ = (R.subst σ).pairForm (L.subst σ) (KY.subst σ) (KP.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (fun t => (Q t).subst (Expr.liftSub σ))
      (p.subst σ) (a.subst σ) (z.subst σ) := by
  simp only [pairForm,LogicCode.disj_subst,LogicCode.ex_subst,logicalType_subst,formExBody_subst,edge_subst]
theorem pairBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a : Expr S) (ρ : Nat → Nat) :
    (R.pairBody L KY KP T G Q p a).rename (Expr.liftRen ρ) = (R.rename ρ).pairBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ)
      (T.rename ρ) (G.rename (Expr.liftRen ρ)) (fun t => (Q t).rename (Expr.liftRen ρ))
      (p.rename ρ) (a.rename ρ) := by
  simp only [pairBody,pairForm_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,
    Expr.rename_comp,Expr.lifted_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl
theorem pairBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a z : Expr S) :
    (R.pairBody L KY KP T G Q p a).instantiate z = R.pairForm L KY KP T G Q p a z := by
  simp only [pairBody,Expr.instantiate,pairForm_subst,instantiate_raise,
    LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_rename,
    Expr.liftSub_single_liftRen_succ,Expr.subst,Expr.single,
    show Expr.single z ∘ Nat.succ = (Expr.var : Nat → Expr S) from rfl,Expr.subst_var]
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
theorem pairPred_rename (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a : Expr S) (ρ : Nat → Nat) :
    (R.pairPred L KY KP T G Q p a).rename ρ = (R.rename ρ).pairPred (L.rename ρ) (KY.rename ρ) (KP.rename ρ)
      (T.rename ρ) (G.rename (Expr.liftRen ρ)) (fun t => (Q t).rename (Expr.liftRen ρ))
      (p.rename ρ) (a.rename ρ) := by
  simp only [pairPred,pred_rename,pairBody_rename]
theorem pairPred_subst (L : LogicCode S) (KY KP : QuantifierCode S) (T G : Expr S)
    (Q : Fin 7 → Expr S) (p a : Expr S) (σ : Nat → Expr S) :
    (R.pairPred L KY KP T G Q p a).subst σ = (R.subst σ).pairPred (L.subst σ) (KY.subst σ) (KP.subst σ)
      (T.subst σ) (G.subst (Expr.liftSub σ)) (fun t => (Q t).subst (Expr.liftSub σ))
      (p.subst σ) (a.subst σ) := by
  simp only [pairPred,pred_subst,pairBody_subst]
end ChannelCode

namespace ChannelCode.Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H N : Set S} {R : ChannelCode S}
    (h : R.Formed L I J N H) (KY : QuantifierRoute L.witnesses C L.base J)
    (KP : QuantifierRoute L.witnesses C L.base H)
    {T G : Expr S} {Q : Fin 7 → Expr S}
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hG : L.Family (R.predicateType T) G) (hQ : ∀ t, L.Family (R.predicateType T) (Q t))
    {s : S} (hs : HasType P Γ (R.rawType T) (.sort s))
include h hT mT hG hQ hs
 theorem isClass_formula (t : Fin 3) {y : Expr S}
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data) :
    L.Formula (R.isClass L.code KP.code T G Q t y) := by
  have hc := h.classPred_typed KP hT mT hG hy my hs
  exact (hQ (classTag t)).instantiate hc.1 hc.2
 theorem edge_formula (t : Bool) {y z : Expr S}
    (hy : HasType P Γ y (R.logicalType T)) (my : WellModed γ y .data)
    (hz : HasType P Γ z (R.logicalType T)) (mz : WellModed γ z .data) :
    L.Formula (R.edge L.code KP.code T G Q t y z) := by
  have hu := h.unionPred_typed KP hT mT hG hy my hz mz hs
  exact L.conj_formula (h.isClass_formula KP hT mT hG hQ hs 0 hy my)
    (L.conj_formula (h.isClass_formula KP hT mT hG hQ hs _ hz mz)
      ((hQ (edgeTag t)).instantiate hu.1 hu.2))
 theorem formExBody_family {p z : Expr S}
    (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data)
    (hz : HasType P Γ z (R.logicalType T)) (mz : WellModed γ z .data) :
    L.Family (R.logicalType T) (R.formExBody L.code KP.code T G Q p z) := by
  intro Δ δ e y hy my
  rw [formExBody_rename,formExBody_instantiate]
  have ht := fun s hs => e.typing (hT s hs)
  have hz' : HasType P Δ (z.rename e.names) ((R.rename e.names).logicalType (T.rename e.names)) := by
    simpa only [logicalType_rename] using e.typing hz
  have hy' : HasType P Δ y ((R.rename e.names).logicalType (T.rename e.names)) := by
    simpa only [logicalType_rename] using hy
  have hg : (L.rename e).Family ((R.rename e.names).predicateType (T.rename e.names)) (G.rename (Expr.liftRen e.names)) := by
    simpa only [predicateType_rename] using hG.rename e
  have hq : ∀ t, (L.rename e).Family ((R.rename e.names).predicateType (T.rename e.names)) ((Q t).rename (Expr.liftRen e.names)) := by
    intro t; simpa only [predicateType_rename] using (hQ t).rename e
  have hs' : HasType P Δ ((R.rename e.names).rawType (T.rename e.names)) (.sort s) := by
    simpa only [rawType_rename,Expr.rename] using e.typing hs
  have hp' : HasType P Δ (p.rename e.names) ((R.rename e.names).predicateType (T.rename e.names)) := by
    simpa only [predicateType_rename] using e.typing hp
  exact (L.rename e).conj_formula ((h.rename e).edge_formula (KP.rename e) ht (e.moded mT) hg hq hs' false hy' my hz' (e.moded mz))
      ((h.rename e).eval_formula ht (e.moded mT) hp' (e.moded mp) hy' my)
 theorem pairForm_formula {p a z : Expr S}
    (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data)
    (ha : HasType P Γ a (R.logicalType T)) (ma : WellModed γ a .data)
    (hz : HasType P Γ z (R.logicalType T)) (mz : WellModed γ z .data) :
    L.Formula (R.pairForm L.code KY.code KP.code T G Q p a z) :=
  L.disj_formula (L.ex_formula KY (h.logical_sorted hT) (h.logical_mode mT)
    (h.formExBody_family KP hT mT hG hQ hs hp mp hz mz))
    (h.edge_formula KP hT mT hG hQ hs true ha ma hz mz)
 theorem pairBody_family {p a : Expr S}
    (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data)
    (ha : HasType P Γ a (R.logicalType T)) (ma : WellModed γ a .data) :
    L.Family (R.logicalType T) (R.pairBody L.code KY.code KP.code T G Q p a) := by
  intro Δ δ e z hz mz
  rw [pairBody_rename,pairBody_instantiate]
  have ht := fun s hs => e.typing (hT s hs)
  have ha' : HasType P Δ (a.rename e.names) ((R.rename e.names).logicalType (T.rename e.names)) := by
    simpa only [logicalType_rename] using e.typing ha
  have hz' : HasType P Δ z ((R.rename e.names).logicalType (T.rename e.names)) := by
    simpa only [logicalType_rename] using hz
  have hg : (L.rename e).Family ((R.rename e.names).predicateType (T.rename e.names)) (G.rename (Expr.liftRen e.names)) := by
    simpa only [predicateType_rename] using hG.rename e
  have hq : ∀ t, (L.rename e).Family ((R.rename e.names).predicateType (T.rename e.names)) ((Q t).rename (Expr.liftRen e.names)) := by
    intro t; simpa only [predicateType_rename] using (hQ t).rename e
  have hs' : HasType P Δ ((R.rename e.names).rawType (T.rename e.names)) (.sort s) := by
    simpa only [rawType_rename,Expr.rename] using e.typing hs
  have hp' : HasType P Δ (p.rename e.names) ((R.rename e.names).predicateType (T.rename e.names)) := by
    simpa only [predicateType_rename] using e.typing hp
  exact (h.rename e).pairForm_formula (KY.rename e) (KP.rename e) ht (e.moded mT) hg hq hs' hp' (e.moded mp) ha' (e.moded ma) hz' mz
 theorem pairPred_typed {p a : Expr S}
    (hp : HasType P Γ p (R.predicateType T)) (mp : WellModed γ p .data)
    (ha : HasType P Γ a (R.logicalType T)) (ma : WellModed γ a .data) :
    HasType P Γ (R.pairPred L.code KY.code KP.code T G Q p a) (R.predicateType T) ∧
      WellModed γ (R.pairPred L.code KY.code KP.code T G Q p a) .data :=
  h.pred_typed hT mT (h.pairBody_family KY KP hT mT hG hQ hs hp mp ha ma) hs
end ChannelCode.Formed

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

namespace DoubleCode
variable (R : DoubleCode S)

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
end Formed
end DoubleCode

namespace DoubleCode
variable (R : DoubleCode S)

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
theorem rename_bottom (L : LogicCode S) (ρ : Nat → Nat) : (L.rename ρ).bottom = L.bottom.rename ρ := rfl
theorem subst_bottom (L : LogicCode S) (σ : Nat → Expr S) : (L.subst σ).bottom = L.bottom.subst σ := rfl
end LogicCode
namespace DoubleCode

section
variable (R : DoubleCode S)
theorem rename_first (ρ : Nat → Nat) : (R.rename ρ).first = R.first.rename ρ := rfl
theorem subst_first (σ : Nat → Expr S) : (R.subst σ).first = R.first.subst σ := rfl
theorem rename_second (ρ : Nat → Nat) : (R.rename ρ).second = R.second.rename ρ := rfl
theorem subst_second (σ : Nat → Expr S) : (R.subst σ).second = R.second.subst σ := rfl
theorem bpBottom_rename (L : LogicCode S) (T : Expr S) (ρ : Nat → Nat) :
    (R.bpBottom L T).rename ρ = (R.rename ρ).bpBottom (L.rename ρ) (T.rename ρ) := by
  simp only [bpBottom,DataWrapper.build_rename,big_rename,DataWrapper.argRen,ite_true, if_true,rename_first,LogicCode.rename_bottom,Expr.rename_comp]
  rfl
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
theorem dummyBody_rename (L : LogicCode S) (T : Expr S) (ρ : Nat → Nat) :
    (R.dummyBody L T).rename (Expr.liftRen ρ) =
      (R.rename ρ).dummyBody (L.rename ρ) (T.rename ρ) := by
  simp only [dummyBody,DataWrapper.contraCallback_rename,bpType_rename,bpBottom_rename]; rfl
theorem dummyBody_subst (L : LogicCode S) (T : Expr S) (σ : Nat → Expr S) :
    (R.dummyBody L T).subst (Expr.liftSub σ) =
      (R.subst σ).dummyBody (L.subst σ) (T.subst σ) := by
  simp only [dummyBody,DataWrapper.contraCallback_subst,bpType_subst,bpBottom_subst]; rfl
theorem innerBody_rename (U : DataWrapper S true) (L : LogicCode S) (T p : Expr S) (ρ : Nat → Nat) :
    (R.innerBody U L T p).rename (Expr.liftRen ρ) =
      (R.rename ρ).innerBody (U.rename ρ) (L.rename ρ) (T.rename ρ) (p.rename ρ) := by
  simp only [innerBody,LogicCode.cond_rename,dummyBody_rename,queryBody,
    DataWrapper.contraCallback_rename,bpType_rename,encode_rename,LogicCode.rename_comp,rename_second,LogicCode.rename_bottom,Expr.rename_comp]
  rfl
theorem innerBody_subst (U : DataWrapper S true) (L : LogicCode S) (T p : Expr S) (σ : Nat → Expr S) :
    (R.innerBody U L T p).subst (Expr.liftSub σ) =
      (R.subst σ).innerBody (U.subst σ) (L.subst σ) (T.subst σ) (p.subst σ) := by
  simp only [innerBody,LogicCode.cond_subst,dummyBody_subst,queryBody,
    DataWrapper.contraCallback_subst,bpType_subst,encode_subst,LogicCode.subst_rename,
    LogicCode.rename_subst,subst_second,LogicCode.subst_bottom,Expr.subst_rename,Expr.rename_subst]
  rfl
theorem innerProbe_rename (U : DataWrapper S true) (L : LogicCode S) (T p : Expr S) (ρ : Nat → Nat) :
    (R.innerProbe U L T p).rename ρ =
      (R.rename ρ).innerProbe (U.rename ρ) (L.rename ρ) (T.rename ρ) (p.rename ρ) := by
  simp only [innerProbe,DataWrapper.build_rename,DataWrapper.argRen,ite_true, if_true,paramType_rename,innerBody_rename]
  rfl
theorem innerProbe_subst (U : DataWrapper S true) (L : LogicCode S) (T p : Expr S) (σ : Nat → Expr S) :
    (R.innerProbe U L T p).subst σ =
      (R.subst σ).innerProbe (U.subst σ) (L.subst σ) (T.subst σ) (p.subst σ) := by
  simp only [innerProbe,DataWrapper.build_subst,DataWrapper.argSub,ite_true, if_true,paramType_subst,innerBody_subst]
  rfl

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

theorem query_rename (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T m p : Expr S) (ρ : Nat → Nat) :
    (R.query U L t T m p).rename ρ =
      (R.rename ρ).query (U.rename ρ) (L.rename ρ) t (T.rename ρ) (m.rename ρ) (p.rename ρ) := by
  simp only [query,DataWrapper.observe_rename,bpType_rename,encode_rename,rename_second,
    DataWrapper.argRen,Bool.not_true,Bool.false_eq_true,ite_false, if_false]
theorem query_subst (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T m p : Expr S) (σ : Nat → Expr S) :
    (R.query U L t T m p).subst σ =
      (R.subst σ).query (U.subst σ) (L.subst σ) t (T.subst σ) (m.subst σ) (p.subst σ) := by
  simp only [query,DataWrapper.observe_subst,bpType_subst,encode_subst,subst_second,
    DataWrapper.argSub,Bool.not_true,Bool.false_eq_true,ite_false, if_false]
theorem queryPredBody_rename (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T m : Expr S) (ρ : Nat → Nat) :
    (R.queryPredBody U L t T m).rename (Expr.liftRen ρ) =
      (R.rename ρ).queryPredBody (U.rename ρ) (L.rename ρ) t (T.rename ρ) (m.rename ρ) := by
  simp only [queryPredBody,query_rename,rename_comp,DataWrapper.rename_comp,LogicCode.rename_comp,
    Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl
theorem queryPredBody_subst (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T m : Expr S) (σ : Nat → Expr S) :
    (R.queryPredBody U L t T m).subst (Expr.liftSub σ) =
      (R.subst σ).queryPredBody (U.subst σ) (L.subst σ) t (T.subst σ) (m.subst σ) := by
  simp only [queryPredBody,query_subst,subst_rename,rename_subst,DataWrapper.subst_rename,DataWrapper.rename_subst,
    LogicCode.subst_rename,LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
theorem queryPredBody_instantiate (U : DataWrapper S true) (L : LogicCode S) (t : Fin 8) (T m p : Expr S) :
    (R.queryPredBody U L t T m).instantiate p = R.query U L t T m p := by
  simp only [queryPredBody,Expr.instantiate,query_subst,instantiate_raise,DataWrapper.instantiate_raise,
    LogicCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
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
 theorem queryPredBody_family (t : Fin 8) {T m : Expr S}
    (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hm : HasType P Γ m (R.paramType T)) (mm : WellModed γ m .data) :
    L.Family (U.apply T) (R.queryPredBody U L.code t T m) := by
  intro Δ δ e p hp mp
  rw [queryPredBody_rename,queryPredBody_instantiate]
  simpa only [← LogicSetup.code_rename] using (h.rename e).query_formula (hU.rename e) t
    (fun s hs => e.typing (hT s hs)) (e.moded mT)
    (by simpa only [paramType_rename] using e.typing hm) (e.moded mm)
    (by simpa only [DataWrapper.apply_rename] using hp) mp
end Formed

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

end Formed
end

variable (R : DoubleCode S) {A B : Expr S}
theorem carrier_converts (h : Converts A B) : Converts (R.carrier A) (R.carrier B) :=
  R.second.apply_converts (R.first.apply_converts h)
theorem tower_converts (n : Nat) (h : Converts A B) : Converts (R.tower n A) (R.tower n B) := by
  induction n with
  | zero => exact h
  | succ n ih => exact R.carrier_converts ih
theorem paramType_converts (h : Converts A B) : Converts (R.paramType A) (R.paramType B) :=
  R.second.apply_converts (R.first.apply_converts (R.tower_converts 4 h))
end DoubleCode
namespace ProbeCode

section
variable (R : ProbeCode S)
theorem funType_converts {A B : Expr S} (h : Converts A B) : Converts (R.funType A) (R.funType B) :=
  .pi (R.doubled.carrier_converts (R.doubled.paramType_converts
    (R.raw.apply_converts (R.initial.apply_converts h)))) (.refl _)
theorem atType_converts {A B : Expr S} (h : Converts A B) : Converts (R.atType A) (R.atType B) :=
  R.funPath.apply_converts (R.funType_converts h)
theorem at_body_convert (A : Expr S) :
    Converts (R.body.instantiate (R.lifting.inject A)) (R.atType A) := by
  rw [body_instantiate]
  exact R.atType_converts (R.lifting.cancel A).converts

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
  {L : LogicSetup P Γ γ C} {I J k p n g : Set S}
namespace Formed
variable {R} (h : R.Formed L I J k p n g)
include h

theorem at_sorted {A : Expr S} (ha : HasType P Γ A (.sort R.seed)) :
    SortedAt P Γ (R.atType A) J := h.funPath.sorted (h.fun_sorted ha)
theorem at_typed {A v : Expr S} (ha : HasType P Γ A (.sort R.seed))
    (hv : HasType P Γ v R.carrier) : HasType P Γ (R.specialize A v) (R.atType A) := by
  obtain ⟨s,hs⟩ := h.mainTriple.codomain.1
  exact (hv.application ((h.lifting.typed h.seed_sorted).1 A ha)).conversion
    (h.at_sorted ha s hs) (R.at_body_convert A)
theorem at_data {A v : Expr S} (ma : WellModed γ A .data) (mv : WellModed γ v .data) :
    WellModed γ (R.specialize A v) .data := .app mv (h.lifting.modes.2.1 A ma)

theorem readBody_family {A w : Expr S} (_ha : HasType P Γ A (.sort R.seed))
    (hw : HasType P Γ w (R.singleType A)) (mw : WellModed γ w .data) :
    L.Family (R.funType A) (R.readBody w) := by
  intro Δ δ e f hf mf
  have hh := h.rename e
  have hF : HasType P Δ f ((R.rename e.names).funType (A.rename e.names)) := by
    simpa only [funType_rename] using hf
  have hW : HasType P Δ (w.rename e.names) ((R.rename e.names).singleType (A.rename e.names)) := by
    simpa only [singleType_rename] using e.typing hw
  have hr := hh.tail.read_formula (hF.apply_arrow hW) (.app mf (e.moded mw))
  convert hr using 1
  all_goals try with_reducible_and_instances rfl
  simp only [readBody,DataTail.read_rename,DataTail.rename_comp,Expr.rename,Expr.rename_comp,
    Expr.liftRen,PureTypeSystem.Expr.liftRen,Function.comp_def,Expr.instantiate,
    DataTail.read_subst,Expr.subst,Expr.single,Expr.subst_rename]
  have he : (fun x => e.names x + 1) = Nat.succ ∘ e.names := rfl
  rw [he,← DataTail.rename_comp,DataTail.instantiate_raise]
  change (R.tail.rename e.names).read (.app .dd f (w.subst (Expr.var ∘ e.names))) = _
  rw [Expr.subst_var_rename]
  rfl

theorem observe_formula {A v w : Expr S} (ha : HasType P Γ A (.sort R.seed))
    (ma : WellModed γ A .data) (hv : HasType P Γ v R.carrier) (mv : WellModed γ v .data)
    (hw : HasType P Γ w (R.singleType A)) (mw : WellModed γ w .data) :
    L.Formula (R.observe A v w) :=
  (h.funPath.sound (h.fun_sorted ha) (h.fun_mode ma)).2 _ _ (h.at_typed ha hv)
    (h.at_data ma mv) (h.readBody_family ha hw mw)
end Formed
end

variable (R : ProbeCode S)

theorem funBuild_rename (A Q : Expr S) (ρ : Nat → Nat) :
    (R.funBuild A Q).rename ρ =
      (R.rename ρ).funBuild (A.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [funBuild,Expr.rename,singleType_rename,DataTail.send_rename,rename,DataTail.rename_comp]
  rfl

theorem funBuild_subst (A Q : Expr S) (σ : Nat → Expr S) :
    (R.funBuild A Q).subst σ =
      (R.subst σ).funBuild (A.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [funBuild,Expr.subst,singleType_subst,DataTail.send_subst]
  simp only [subst,DataTail.subst_rename,DataTail.rename_subst]
  rfl

theorem wrappedBuild_rename (A Q : Expr S) (ρ : Nat → Nat) :
    (R.wrappedBuild A Q).rename ρ =
      (R.rename ρ).wrappedBuild (A.rename ρ) (Q.rename (Expr.liftRen ρ)) := by
  simp only [wrappedBuild,DataWrapper.build_rename,funType_rename,DataWrapper.argRen,
    Bool.false_eq_true,ite_false, if_false,funBuild_rename]
  rfl

theorem wrappedBuild_subst (A Q : Expr S) (σ : Nat → Expr S) :
    (R.wrappedBuild A Q).subst σ =
      (R.subst σ).wrappedBuild (A.subst σ) (Q.subst (Expr.liftSub σ)) := by
  simp only [wrappedBuild,DataWrapper.build_subst,funType_subst,DataWrapper.argSub,
    Bool.false_eq_true,ite_false, if_false,funBuild_subst]
  rfl

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
  {L : LogicSetup P Γ γ C} {I J k p n g : Set S}
namespace Formed
variable {R} (h : R.Formed L I J k p n g)
include h
 theorem funBuild_typed {A Q : Expr S} (ha : HasType P Γ A (.sort R.seed))
    (ma : WellModed γ A .data) (hQ : L.Family (R.singleType A) Q) :
    HasType P Γ (R.funBuild A Q) (R.funType A) ∧ WellModed γ (R.funBuild A Q) .data := by
  obtain ⟨r,hr⟩ := h.funTriple.product.1
  obtain ⟨s,hs,t,ht,hst⟩ := h.funTriple.output ▸ hr
  let e : Embedding P Γ γ (R.singleType A :: Γ) (modeCons .data γ) :=
    Embedding.cons (h.single_sorted ha s hs) .data
  have hsend := (h.tail.rename e).send_typed (hQ.opened (h.single_sorted ha s hs))
  refine ⟨HasType.abstraction ?_ (h.fun_sorted ha r hr), .lam (h.single_mode ma) ?_⟩
  · simpa only [DataTail.carrier_rename,e,Embedding.cons,funType,Expr.arrow] using hsend.1
  · exact hsend.2

 theorem wrappedBuild_typed {A Q : Expr S} (ha : HasType P Γ A (.sort R.seed))
    (ma : WellModed γ A .data) (hQ : L.Family (R.singleType A) Q) :
    HasType P Γ (R.wrappedBuild A Q) (R.atType A) ∧
      WellModed γ (R.wrappedBuild A Q) .data :=
  (h.funPath.sound (h.fun_sorted ha) (h.fun_mode ma)).1 _ (h.funBuild_typed ha ma hQ)

end Formed
end ProbeCode
end

universe u
variable {S : Type u} {P : Specification S}
namespace ProbeCode
variable (R : ProbeCode S)

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
  {L : LogicSetup P Γ γ C} {I J k p n g : Set S}
namespace Formed
variable {R} (h : R.Formed L I J k p n g)
include h
 theorem project_typed {z : Expr S} (hz : HasType P Γ z R.domain) :
    HasType P Γ (R.lifting.project z) (.sort R.seed) := (h.lifting.typed h.seed_sorted).2 _ hz
 theorem project_mode {z : Expr S} (mz : WellModed γ z .data) :
    WellModed γ (R.lifting.project z) .data := h.lifting.modes.2.2 _ mz
 theorem raised_project {s : S} (hs : HasType P Γ R.domain (.sort s)) :
    HasType P (R.domain :: Γ) ((R.lifting.rename Nat.succ).project (.var 0)) (.sort R.seed) := by
  let e : Embedding P Γ γ (R.domain :: Γ) (modeCons .data γ) := Embedding.cons hs .data
  apply (h.rename e).project_typed
  simpa only [domain,PositiveDataWrapper.apply_rename,Expr.rename,ProbeCode.rename,e,Embedding.cons] using HasType.var hs
 theorem uniform_typed {Q : Expr S} {s : S} (hs : HasType P Γ R.domain (.sort s))
    (hQ : (L.rename (Embedding.cons hs .data)).Family
      ((R.rename Nat.succ).singleType ((R.lifting.rename Nat.succ).project (.var 0))) Q) :
    HasType P Γ (R.uniform Q) R.carrier ∧ WellModed γ (R.uniform Q) .data := by
  let e : Embedding P Γ γ (R.domain :: Γ) (modeCons .data γ) := Embedding.cons hs .data
  have hh := h.rename e
  have hb := hh.wrappedBuild_typed (h.raised_project hs)
    (hh.project_mode (WellModed.var 0)) hQ
  obtain ⟨r,hr⟩ := h.mainTriple.product.1
  exact ⟨HasType.abstraction hb.1 (h.carrier_sorted r hr),.lam h.domain_mode hb.2⟩

end Formed
end ProbeCode
end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Relational
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
namespace ProbeCode
variable (R : ProbeCode S)
theorem rename_comp (ρ τ : Nat → Nat) : (R.rename τ).rename ρ = R.rename (ρ ∘ τ) := by
  cases R; simp only [rename,DataWrapper.rename_comp,PositiveDataWrapper.rename_comp,DataTail.rename_comp]
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
theorem readBody_rename (w : Expr S) (ρ : Nat → Nat) :
    (R.readBody w).rename (Expr.liftRen ρ) = (R.rename ρ).readBody (w.rename ρ) := by
  simp only [readBody,DataTail.read_rename,DataTail.rename_comp,Expr.rename,Expr.rename_comp,
    Expr.liftRen,PureTypeSystem.Expr.liftRen,rename]
  rfl
theorem readBody_subst (w : Expr S) (σ : Nat → Expr S) :
    (R.readBody w).subst (Expr.liftSub σ) = (R.subst σ).readBody (w.subst σ) := by
  simp only [readBody,DataTail.read_subst,DataTail.subst_rename,DataTail.rename_subst,
    Expr.subst,Expr.liftSub,Expr.subst_rename,Expr.rename_subst,subst]
  rfl
theorem observe_rename (A v w : Expr S) (ρ : Nat → Nat) :
    (R.observe A v w).rename ρ = (R.rename ρ).observe (A.rename ρ) (v.rename ρ) (w.rename ρ) := by
  simp only [observe,DataWrapper.observe_rename,funType_rename,specialize,Expr.rename,
    PositiveDataWrapper.inject_rename,readBody_rename,DataWrapper.argRen,Bool.not_false,ite_true, if_true,rename]
theorem observe_subst (A v w : Expr S) (σ : Nat → Expr S) :
    (R.observe A v w).subst σ = (R.subst σ).observe (A.subst σ) (v.subst σ) (w.subst σ) := by
  simp only [observe,DataWrapper.observe_subst,funType_subst,specialize,Expr.subst,
    PositiveDataWrapper.inject_subst,readBody_subst,DataWrapper.argSub,Bool.not_false,ite_true, if_true,subst]
end ProbeCode
namespace DoubleCode
variable (R : DoubleCode S)
theorem decodeMap_rename (U : DataWrapper S true) (L : LogicCode S) (T : Expr S) (ρ : Nat → Nat) :
    (R.decodeMap U L T).rename (Expr.liftRen ρ) =
      (R.rename ρ).decodeMap (U.rename ρ) (L.rename ρ) (T.rename ρ) := by
  simp only [decodeMap,decode_rename,rename_comp,DataWrapper.rename_comp,LogicCode.rename_comp,Expr.rename_comp,Expr.liftRen,PureTypeSystem.Expr.liftRen,Expr.rename]
  rfl
 theorem markBody_rename (L : LogicCode S) (t : Fin 8) (T c : Expr S) (ρ : Nat → Nat) :
    (R.markBody L t T c).rename (Expr.liftRen ρ) =
      (R.rename ρ).markBody (L.rename ρ) t (T.rename ρ) (c.rename ρ) := by
  simp only [markBody,DataWrapper.contraCallback_rename,big_rename,tagged_rename,rename_first]
 theorem pointBody_rename (U : DataWrapper S true) (L : LogicCode S) (T c₀ c : Expr S) (ρ : Nat → Nat) :
    (R.pointBody U L T c₀ c).rename (Expr.liftRen ρ) =
      (R.rename ρ).pointBody (U.rename ρ) (L.rename ρ) (T.rename ρ) (c₀.rename ρ) (c.rename ρ) := by
  simp only [pointBody,LogicCode.conj_rename,markBody_rename,Expr.compose_rename,
    DataWrapper.contraCallback_rename,decodeMap_rename,LogicCode.rename_comp]
  rfl
 theorem point_rename (U : DataWrapper S true) (L : LogicCode S) (T c₀ c : Expr S) (ρ : Nat → Nat) :
    (R.point U L T c₀ c).rename ρ =
      (R.rename ρ).point (U.rename ρ) (L.rename ρ) (T.rename ρ) (c₀.rename ρ) (c.rename ρ) := by
  simp only [point,DataWrapper.build_rename,bpType_rename,DataWrapper.argRen,ite_true, if_true,
    pointBody_rename,rename_second]
 theorem dummy_rename (L : LogicCode S) (T : Expr S) (ρ : Nat → Nat) :
    (R.dummy L T).rename ρ = (R.rename ρ).dummy (L.rename ρ) (T.rename ρ) := by
  simp only [dummy,DataWrapper.build_rename,bpType_rename,DataWrapper.argRen,ite_true, if_true,
    rename_second,Expr.rename_comp,← LogicCode.top_rename]
  rfl
 theorem bundle_rename (L : LogicCode S) (A d m y : Expr S) (ρ : Nat → Nat) :
    (R.bundle L A d m y).rename ρ =
      (R.rename ρ).bundle (L.rename ρ) (A.rename ρ) (d.rename ρ) (m.rename ρ) (y.rename ρ) := by
  simp only [bundle,bundleBody,DataWrapper.build_rename,DataWrapper.apply_rename,DataWrapper.argRen,ite_true, if_true,
    LogicCode.cond_rename,DataWrapper.contraCallback_rename,rename_first,rename_second,LogicCode.rename_comp]
  rfl
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
theorem rename_comp (ρ τ : Nat → Nat) : (R.rename τ).rename ρ = R.rename (ρ ∘ τ) := by
  cases R; simp only [rename,ProbeCode.rename_comp,DataWrapper.rename_comp]
theorem subst_rename (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.rename ρ).subst σ = R.subst (σ ∘ ρ) := by
  cases R; simp only [rename,subst,ProbeCode.subst_rename,DataWrapper.subst_rename]
theorem rename_subst (σ : Nat → Expr S) (ρ : Nat → Nat) :
    (R.subst σ).rename ρ = R.subst (fun n => (σ n).rename ρ) := by
  cases R; simp only [rename,subst,ProbeCode.rename_subst,DataWrapper.rename_subst]
theorem instantiate_raise (a : Expr S) : (R.rename Nat.succ).subst (Expr.single a) = R := by
  cases R; simp only [rename,subst,ProbeCode.instantiate_raise,DataWrapper.instantiate_raise]
theorem channel_rename (ρ : Nat → Nat) : (R.rename ρ).channel = R.channel.rename ρ := rfl
theorem baseType_rename (A : Expr S) (ρ : Nat → Nat) :
    (R.baseType A).rename ρ = (R.rename ρ).baseType  (A.rename ρ) :=
  R.probe.initial.apply_rename A ρ
theorem queryBody_rename (L : LogicCode S) (t : Fin 7) (A m : Expr S) (ρ : Nat → Nat) :
    (R.queryBody L t A m).rename (Expr.liftRen ρ) = (R.rename ρ).queryBody (L.rename ρ) t (A.rename ρ) (m.rename ρ) := by
  simp only [queryBody,DoubleCode.queryPredBody_rename,ProbeCode.rawType_rename,ProbeCode.doubled,DoubleCode.rename,rename]
  rfl
theorem goodBody_rename (L : LogicCode S) (KY : QuantifierCode S) (A m : Expr S) (ρ : Nat → Nat) :
    (R.goodBody L KY A m).rename (Expr.liftRen ρ) = (R.rename ρ).goodBody (L.rename ρ) (KY.rename ρ) (A.rename ρ) (m.rename ρ) := by
  simp only [goodBody,ChannelCode.goodBody_rename,baseType_rename,queryBody_rename,channel_rename]
theorem pair_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A m p a : Expr S) (ρ : Nat → Nat) :
    (R.pair L KY KP A m p a).rename ρ = (R.rename ρ).pair (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (A.rename ρ) (m.rename ρ) (p.rename ρ) (a.rename ρ) := by
  simp only [pair,ChannelCode.pairPred_rename,baseType_rename,goodBody_rename,queryBody_rename,channel_rename]
theorem rawTop_rename (L : LogicCode S) (A : Expr S) (ρ : Nat → Nat) :
    (R.rawTop L A).rename ρ = (R.rename ρ).rawTop (L.rename ρ) (A.rename ρ) := by
  simp only [rawTop,DataWrapper.build_rename,baseType_rename,DataWrapper.argRen,ite_true, if_true,rename,Expr.rename_comp,← LogicCode.top_rename]
  rfl
theorem point_rename (L : LogicCode S) (A y : Expr S) (ρ : Nat → Nat) :
    (R.point L A y).rename ρ = (R.rename ρ).point (L.rename ρ) (A.rename ρ) (y.rename ρ) := by
  simp only [point,DoubleCode.point_rename,ProbeCode.rawType_rename,rawTop_rename,ChannelCode.toRaw_rename,baseType_rename,ProbeCode.doubled,DoubleCode.rename,rename]
  rfl
theorem bundle_rename (L : LogicCode S) (A m y : Expr S) (ρ : Nat → Nat) :
    (R.bundle L A m y).rename ρ = (R.rename ρ).bundle (L.rename ρ) (A.rename ρ) (m.rename ρ) (y.rename ρ) := by
  simp only [bundle,DoubleCode.bundle_rename,DoubleCode.dummy_rename,ProbeCode.paramType_rename,ProbeCode.rawType_rename,point_rename,ProbeCode.doubled,DoubleCode.rename,rename]
  rfl
theorem diamond_rename (L : LogicCode S) (A m v y : Expr S) (ρ : Nat → Nat) :
    (R.diamond L A m v y).rename ρ = (R.rename ρ).diamond (L.rename ρ) (A.rename ρ) (m.rename ρ) (v.rename ρ) (y.rename ρ) := by
  simp only [diamond,ProbeCode.observe_rename,bundle_rename,rename]
theorem partBody_rename (L : LogicCode S) (A m v : Expr S) (ρ : Nat → Nat) :
    (R.partBody L A m v).rename (Expr.liftRen ρ) = (R.rename ρ).partBody (L.rename ρ) (A.rename ρ) (m.rename ρ) (v.rename ρ) := by
  simp only [partBody,diamond_rename,rename_comp,LogicCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl
 theorem part_rename (L : LogicCode S) (A m v : Expr S) (ρ : Nat → Nat) :
    (R.part L A m v).rename ρ = (R.rename ρ).part (L.rename ρ) (A.rename ρ) (m.rename ρ) (v.rename ρ) := by
  simp only [part,ChannelCode.pred_rename,baseType_rename,partBody_rename,channel_rename]
 theorem sb_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A m v a : Expr S) (ρ : Nat → Nat) :
    (R.sb L KY KP A m v a).rename ρ = (R.rename ρ).sb (L.rename ρ) (KY.rename ρ) (KP.rename ρ)
      (A.rename ρ) (m.rename ρ) (v.rename ρ) (a.rename ρ) := by
  simp only [sb,DoubleCode.query_rename,ProbeCode.rawType_rename,pair_rename,part_rename,
    ProbeCode.doubled,DoubleCode.rename,rename]
  rfl
 theorem liftBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A m a : Expr S) (ρ : Nat → Nat) :
    (R.liftBody L KY KP A m a).rename (Expr.liftRen ρ) = (R.rename ρ).liftBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ)
      (A.rename ρ) (m.rename ρ) (a.rename ρ) := by
  simp only [liftBody,sb_rename,rename_comp,LogicCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen,QuantifierCode.rename,
    ProofWrapper.rename_comp]
  rfl
 theorem lift_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A m a : Expr S) (ρ : Nat → Nat) :
    (R.lift L KY KP A m a).rename ρ = (R.rename ρ).lift (L.rename ρ) (KY.rename ρ) (KP.rename ρ)
      (A.rename ρ) (m.rename ρ) (a.rename ρ) := by
  simp only [lift,DataWrapper.build_rename,ProbeCode.carrier_rename,DataWrapper.argRen,ite_true, if_true,
    liftBody_rename,rename]
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
theorem partBody_instantiate (L : LogicCode S) (A m v y : Expr S) :
    (R.partBody L A m v).instantiate y = R.diamond L A m v y := by
  simp only [partBody,Expr.instantiate,diamond_subst,instantiate_raise,LogicCode.instantiate_raise,
    Expr.subst_lift_single,Expr.subst,Expr.single]
theorem liftBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (A m a v : Expr S) :
    (R.liftBody L KY KP A m a).instantiate v = R.sb L KY KP A m v a := by
  simp only [liftBody,Expr.instantiate,sb_subst,instantiate_raise,LogicCode.instantiate_raise,
    QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
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
theorem queryBody_family (t : Fin 7) {A m : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data) :
    L.Family (R.channel.predicateType (R.baseType A)) (R.queryBody L.code t A m) :=
  H.probe.doubled_formed.queryPredBody_family H.channel.predicate t.castSucc
    (H.probe.raw_sorted hA) (H.probe.raw_mode mA) hm mm
theorem goodBody_family (KY : QuantifierRoute L.witnesses C L.base j) {A m : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data) :
    L.Family (R.channel.predicateType (R.baseType A)) (R.goodBody L.code KY.code A m) :=
  H.channel.goodBody_family KY (H.base_sorted hA) (H.base_mode mA) (H.queryBody_family 0 hA mA hm mm)
theorem pair_typed (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h) {A m q a : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data)
    (hq : HasType P Γ q (R.channel.predicateType (R.baseType A))) (mq : WellModed γ q .data)
    (ha : HasType P Γ a (R.channel.logicalType (R.baseType A))) (ma : WellModed γ a .data) :
    HasType P Γ (R.pair L.code KY.code KP.code A m q a) (R.channel.predicateType (R.baseType A)) ∧
      WellModed γ (R.pair L.code KY.code KP.code A m q a) .data := by
  obtain ⟨s,hs⟩ := H.probe.funTriple.domain.1
  exact H.channel.pairPred_typed KY KP (H.base_sorted hA) (H.base_mode mA)
    (H.goodBody_family KY hA mA hm mm) (fun t => H.queryBody_family t hA mA hm mm)
    (H.probe.raw_sorted hA s hs) hq mq ha ma
theorem rawTop_typed {A : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data) :
    HasType P Γ (R.rawTop L.code A) (R.probe.rawType A) ∧ WellModed γ (R.rawTop L.code A) .data :=
  (H.probe.raw.sound (H.base_sorted hA) (H.base_mode mA)).1 _ (.constant L.top_formula)
theorem point_typed {A y : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hy : HasType P Γ y (R.channel.logicalType (R.baseType A))) (my : WellModed γ y .data) :
    HasType P Γ (R.point L.code A y) (R.probe.paramType A) ∧ WellModed γ (R.point L.code A y) .data := by
  obtain ⟨s,hs⟩ := H.probe.funTriple.domain.1
  obtain ⟨r,hr⟩ := H.probe.mainTriple.product.1
  have ht := H.rawTop_typed hA mA
  have hc := H.channel.toRaw_typed (H.base_sorted hA) (H.base_mode mA) hy my
  exact H.probe.doubled_formed.point_typed H.channel.predicate (H.probe.raw_sorted hA)
    (H.probe.raw_mode mA) ht.1 ht.2 hc.1 hc.2 (H.probe.raw_sorted hA s hs)
    (H.probe.doubled_formed.bp_sorted (H.probe.raw_sorted hA) r hr)
theorem bundle_typed {A m y : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data)
    (hy : HasType P Γ y (R.channel.logicalType (R.baseType A))) (my : WellModed γ y .data) :
    HasType P Γ (R.bundle L.code A m y) (R.probe.singleType A) ∧ WellModed γ (R.bundle L.code A m y) .data := by
  have hd := H.probe.doubled_formed.dummy_typed (H.probe.raw_sorted hA) (H.probe.raw_mode mA)
  have hp := H.point_typed hA mA hy my
  exact H.probe.doubled_formed.bundle_typed (H.probe.param_sorted hA) (H.probe.param_mode mA)
    hd.1 hd.2 hm mm hp.1 hp.2
theorem diamond_formula {A m v y : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data)
    (hv : HasType P Γ v R.probe.carrier) (mv : WellModed γ v .data)
    (hy : HasType P Γ y (R.channel.logicalType (R.baseType A))) (my : WellModed γ y .data) :
    L.Formula (R.diamond L.code A m v y) := by
  have hb := H.bundle_typed hA mA hm mm hy my
  exact H.probe.observe_formula hA mA hv mv hb.1 hb.2
end

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {R : RelationalCode S}
    (H : R.Formed L I J k p n g j h)
include H
theorem partBody_family {A m v : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data)
    (hv : HasType P Γ v R.probe.carrier) (mv : WellModed γ v .data) :
    L.Family (R.channel.logicalType (R.baseType A)) (R.partBody L.code A m v) := by
  intro Δ δ e y hy my
  rw [partBody_rename,partBody_instantiate]
  have hA' : HasType P Δ (A.rename e.names) (.sort (R.rename e.names).probe.seed) := by
    simpa only [Expr.rename,RelationalCode.rename,ProbeCode.rename] using e.typing hA
  have hm' : HasType P Δ (m.rename e.names) ((R.rename e.names).probe.paramType (A.rename e.names)) := by
    simpa only [ProbeCode.paramType_rename,RelationalCode.rename] using e.typing hm
  have hv' : HasType P Δ (v.rename e.names) (R.rename e.names).probe.carrier := by
    simpa only [ProbeCode.carrier_rename,RelationalCode.rename] using e.typing hv
  have hy' : HasType P Δ y ((R.rename e.names).channel.logicalType ((R.rename e.names).baseType (A.rename e.names))) := by
    simpa only [ChannelCode.logicalType_rename,baseType_rename,channel_rename] using hy
  exact (H.rename e).diamond_formula hA' (e.moded mA) hm' (e.moded mm) hv' (e.moded mv) hy' my
theorem part_typed {A m v : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data)
    (hv : HasType P Γ v R.probe.carrier) (mv : WellModed γ v .data) :
    HasType P Γ (R.part L.code A m v) (R.channel.predicateType (R.baseType A)) ∧
      WellModed γ (R.part L.code A m v) .data := by
  obtain ⟨s,hs⟩ := H.probe.funTriple.domain.1
  exact H.channel.pred_typed (H.base_sorted hA) (H.base_mode mA)
    (H.partBody_family hA mA hm mm hv mv) (H.probe.raw_sorted hA s hs)
theorem sb_formula (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h) {A m v a : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data)
    (hv : HasType P Γ v R.probe.carrier) (mv : WellModed γ v .data)
    (ha : HasType P Γ a (R.channel.logicalType (R.baseType A))) (ma : WellModed γ a .data) :
    L.Formula (R.sb L.code KY.code KP.code A m v a) := by
  have hp := H.part_typed hA mA hm mm hv mv
  have hq := H.pair_typed KY KP hA mA hm mm hp.1 hp.2 ha ma
  exact H.probe.doubled_formed.query_formula H.channel.predicate 6 (H.probe.raw_sorted hA)
    (H.probe.raw_mode mA) hm mm hq.1 hq.2
theorem liftBody_family (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h) {A m a : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data)
    (ha : HasType P Γ a (R.channel.logicalType (R.baseType A))) (ma : WellModed γ a .data) :
    L.Family R.probe.carrier (R.liftBody L.code KY.code KP.code A m a) := by
  intro Δ δ e v hv mv
  rw [liftBody_rename,liftBody_instantiate]
  have hA' : HasType P Δ (A.rename e.names) (.sort (R.rename e.names).probe.seed) := by
    simpa only [Expr.rename,RelationalCode.rename,ProbeCode.rename] using e.typing hA
  have hm' : HasType P Δ (m.rename e.names) ((R.rename e.names).probe.paramType (A.rename e.names)) := by
    simpa only [ProbeCode.paramType_rename,RelationalCode.rename] using e.typing hm
  have hv' : HasType P Δ v (R.rename e.names).probe.carrier := by
    simpa only [ProbeCode.carrier_rename,RelationalCode.rename] using hv
  have ha' : HasType P Δ (a.rename e.names) ((R.rename e.names).channel.logicalType ((R.rename e.names).baseType (A.rename e.names))) := by
    simpa only [ChannelCode.logicalType_rename,baseType_rename,channel_rename] using e.typing ha
  exact (H.rename e).sb_formula (KY.rename e) (KP.rename e) hA' (e.moded mA) hm' (e.moded mm) hv' mv ha' (e.moded ma)
theorem lift_typed (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h) {A m a : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data)
    (ha : HasType P Γ a (R.channel.logicalType (R.baseType A))) (ma : WellModed γ a .data) :
    HasType P Γ (R.lift L.code KY.code KP.code A m a) (R.channel.logicalType R.probe.carrier) ∧
      WellModed γ (R.lift L.code KY.code KP.code A m a) .data :=
  (H.channel.logical.sound H.probe.carrier_sorted H.probe.carrier_mode).1 _ (H.liftBody_family KY KP hA mA hm mm ha ma)
end RelationalCode.Formed

namespace DoubleCode
variable (R : DoubleCode S)
theorem accessBody_rename (L : LogicCode S) (A guard w fi : Expr S) (ρ : Nat → Nat) :
    (R.accessBody L A guard w fi).rename (Expr.liftRen ρ) =
      (R.rename ρ).accessBody (L.rename ρ) (A.rename ρ) (guard.rename (Expr.liftRen ρ)) (w.rename ρ) (fi.rename (Expr.liftRen ρ)) := by
  simp only [accessBody,LogicCode.cond_rename,Expr.compose_rename,DataWrapper.evalCallback_rename,
    DataWrapper.apply_rename,rename_first,rename_second,LogicCode.rename_comp,Expr.rename_comp,← LogicCode.top_rename]
  rfl
theorem accessBody_subst (L : LogicCode S) (A guard w fi : Expr S) (σ : Nat → Expr S) :
    (R.accessBody L A guard w fi).subst (Expr.liftSub σ) =
      (R.subst σ).accessBody (L.subst σ) (A.subst σ) (guard.subst (Expr.liftSub σ)) (w.subst σ) (fi.subst (Expr.liftSub σ)) := by
  simp only [accessBody,LogicCode.cond_subst,Expr.compose_subst,DataWrapper.evalCallback_subst,
    DataWrapper.apply_subst,subst_first,subst_second,LogicCode.subst_rename,LogicCode.rename_subst,
    Expr.subst_rename,Expr.rename_subst,← LogicCode.top_subst]
  rfl
theorem access_rename (L : LogicCode S) (A guard w fi : Expr S) (ρ : Nat → Nat) :
    (R.access L A guard w fi).rename ρ = (R.rename ρ).access (L.rename ρ) (A.rename ρ)
      (guard.rename (Expr.liftRen ρ)) (w.rename ρ) (fi.rename (Expr.liftRen ρ)) := by
  simp only [access,accessProbe,DataWrapper.observe_rename,DataWrapper.apply_rename,
    DataWrapper.build_rename,accessBody_rename,rename_first,rename_second,DataWrapper.argRen,
    Bool.not_true,Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
theorem access_subst (L : LogicCode S) (A guard w fi : Expr S) (σ : Nat → Expr S) :
    (R.access L A guard w fi).subst σ = (R.subst σ).access (L.subst σ) (A.subst σ)
      (guard.subst (Expr.liftSub σ)) (w.subst σ) (fi.subst (Expr.liftSub σ)) := by
  simp only [access,accessProbe,DataWrapper.observe_subst,DataWrapper.apply_subst,
    DataWrapper.build_subst,accessBody_subst,subst_first,subst_second,DataWrapper.argSub,
    Bool.not_true,Bool.false_eq_true,ite_false, if_false,ite_true, if_true]
theorem innerMap_rename (U : DataWrapper S true) (L : LogicCode S) (T : Expr S) (ρ : Nat → Nat) :
    (R.innerMap U L T).rename (Expr.liftRen ρ) = (R.rename ρ).innerMap (U.rename ρ) (L.rename ρ) (T.rename ρ) := by
  simp only [innerMap,innerProbe_rename,rename_comp,DataWrapper.rename_comp,LogicCode.rename_comp,
    Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl
theorem innerMap_subst (U : DataWrapper S true) (L : LogicCode S) (T : Expr S) (σ : Nat → Expr S) :
    (R.innerMap U L T).subst (Expr.liftSub σ) = (R.subst σ).innerMap (U.subst σ) (L.subst σ) (T.subst σ) := by
  simp only [innerMap,innerProbe_subst,subst_rename,rename_subst,DataWrapper.subst_rename,DataWrapper.rename_subst,
    LogicCode.subst_rename,LogicCode.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
theorem recoverAccess_rename (U : DataWrapper S true) (L : LogicCode S) (T w pMap : Expr S) (ρ : Nat → Nat) :
    (R.recoverAccess U L T w pMap).rename ρ = (R.rename ρ).recoverAccess (U.rename ρ) (L.rename ρ)
      (T.rename ρ) (w.rename ρ) (pMap.rename (Expr.liftRen ρ)) := by
  simp only [recoverAccess,access_rename,paramType_rename,dummyBody_rename,accessMap,Expr.compose_rename,innerMap_rename]
theorem recoverAccess_subst (U : DataWrapper S true) (L : LogicCode S) (T w pMap : Expr S) (σ : Nat → Expr S) :
    (R.recoverAccess U L T w pMap).subst σ = (R.subst σ).recoverAccess (U.subst σ) (L.subst σ)
      (T.subst σ) (w.subst σ) (pMap.subst (Expr.liftSub σ)) := by
  simp only [recoverAccess,access_subst,paramType_subst,dummyBody_subst,accessMap,Expr.compose_subst,innerMap_subst]
namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H) (hI : I.Nonempty) (hH : H.Nonempty)
include h hU hI hH
theorem recoverAccess_formula {T w pMap : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (hp : DataMap P Γ γ (R.paramType T) (U.apply T) pMap)
    (hw : HasType P Γ w (R.carrier (R.paramType T))) (mw : WellModed γ w .data) :
    L.Formula (R.recoverAccess U L.code T w pMap) := by
  have hf := h.accessMap_typed hU hI hH hT mT hp
  obtain ⟨s,hs⟩ := hI
  have ha := h.accessProbe_typed (h.param_sorted hT) (h.param_mode mT)
    (h.dummyBody_family hT mT) hw mw hf (h.param_sorted hT s hs)
  exact (h.second.sound (h.first.sorted (h.param_sorted hT)) (h.first.mode (h.param_mode mT))).2 _ _ hw mw ha
end Formed
end DoubleCode
end

section
universe u
variable {S : Type u}
namespace RelationalCode
variable (R : RelationalCode S)
theorem liftEvalBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A m i : Expr S) (ρ : Nat → Nat) :
    (R.liftEvalBody L KY KP A m i).rename (Expr.liftRen ρ) = (R.rename ρ).liftEvalBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (A.rename ρ) (m.rename ρ) (i.rename ρ) := by
  simp only [liftEvalBody,ChannelCode.eval_rename,lift_rename,channel_rename,ProbeCode.carrier_rename,ChannelCode.rename_comp,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  simp only [rename,ProbeCode.rename_comp]
  rfl
theorem predLift_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A m i : Expr S) (ρ : Nat → Nat) :
    (R.predLift L KY KP A m i).rename ρ = (R.rename ρ).predLift (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (A.rename ρ) (m.rename ρ) (i.rename ρ) := by
  simp only [predLift,ChannelCode.pred_rename,baseType_rename,liftEvalBody_rename,channel_rename]
theorem predLiftMap_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A i : Expr S) (ρ : Nat → Nat) :
    (R.predLiftMap L KY KP A i).rename (Expr.liftRen ρ) = (R.rename ρ).predLiftMap (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (A.rename ρ) (i.rename ρ) := by
  simp only [predLiftMap,predLift_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl
theorem recoverLift_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A i w : Expr S) (ρ : Nat → Nat) :
    (R.recoverLift L KY KP A i w).rename ρ = (R.rename ρ).recoverLift (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (A.rename ρ) (i.rename ρ) (w.rename ρ) := by
  simp only [recoverLift,DoubleCode.recoverAccess_rename,ProbeCode.rawType_rename,predLiftMap_rename,ProbeCode.doubled,DoubleCode.rename,rename]
  rfl
theorem recoverLiftBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (A i : Expr S) (ρ : Nat → Nat) :
    (R.recoverLiftBody L KY KP A i).rename (Expr.liftRen ρ) = (R.rename ρ).recoverLiftBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (A.rename ρ) (i.rename ρ) := by
  simp only [recoverLiftBody,recoverLift_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl
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
theorem liftEvalBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (A m i y : Expr S) :
    (R.liftEvalBody L KY KP A m i).instantiate y = R.channel.eval R.probe.carrier i (R.lift L KY KP A m y) := by
  simp only [liftEvalBody,Expr.instantiate,ChannelCode.eval_subst,lift_subst,
    instantiate_raise,ChannelCode.instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,
    Expr.subst_lift_single,Expr.subst,Expr.single]
theorem recoverLiftBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (A i w : Expr S) :
    (R.recoverLiftBody L KY KP A i).instantiate w = R.recoverLift L KY KP A i w := by
  simp only [recoverLiftBody,Expr.instantiate,recoverLift_subst,
    instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,
    Expr.subst_lift_single,Expr.subst,Expr.single]
end RelationalCode

namespace ProbeCode
variable (R : ProbeCode S)
theorem uniform_rename (Q : Expr S) (ρ : Nat → Nat) :
    (R.uniform Q).rename ρ = (R.rename ρ).uniform (Q.rename (Expr.liftRen (Expr.liftRen ρ))) := by
  simp only [uniform,Expr.rename,domain,PositiveDataWrapper.apply_rename,wrappedBuild_rename,
    PositiveDataWrapper.project_rename,PositiveDataWrapper.rename_comp,
    Expr.liftRen,PureTypeSystem.Expr.liftRen,rename]
  simp only [DataWrapper.rename_comp,DataTail.rename_comp]
  rfl
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
theorem probeFor_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (ρ : Nat → Nat) :
    (R.probeFor L KY KP i).rename ρ =
      (R.rename ρ).probeFor (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) := by
  simp only [probeFor,ProbeCode.uniform_rename,recoverLiftBody_rename,
    LogicCode.rename_comp,QuantifierCode.rename_comp,PositiveDataWrapper.project_rename,
    PositiveDataWrapper.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen,rename,ProbeCode.rename]
  simp only [DataWrapper.rename_comp,DataTail.rename_comp]
  rfl
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
theorem le_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) (ρ : Nat → Nat) :
    (R.le L KY KP i x).rename ρ = (R.rename ρ).le (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) (x.rename ρ) := by
  simp only [le,DataWrapper.observe_rename,ProbeCode.carrier_rename,probeFor_rename,DataWrapper.argRen,rename]
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
namespace RelationalCode.Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {R : RelationalCode S}
    (H : R.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H
theorem liftEvalBody_family {A m i : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data) :
    L.Family (R.channel.logicalType (R.baseType A)) (R.liftEvalBody L.code KY.code KP.code A m i) := by
  intro Δ δ e y hy my
  rw [liftEvalBody_rename,liftEvalBody_instantiate]
  have hA' : HasType P Δ (A.rename e.names) (.sort (R.rename e.names).probe.seed) := by
    simpa only [Expr.rename,RelationalCode.rename,ProbeCode.rename] using e.typing hA
  have hm' : HasType P Δ (m.rename e.names) ((R.rename e.names).probe.paramType (A.rename e.names)) := by
    simpa only [ProbeCode.paramType_rename,RelationalCode.rename] using e.typing hm
  have hi' : HasType P Δ (i.rename e.names) ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) := by
    simpa only [ChannelCode.predicateType_rename,ProbeCode.carrier_rename,channel_rename,RelationalCode.rename,RelationalCode.channel,ChannelCode.rename,ProbeCode.rename] using e.typing hi
  have hy' : HasType P Δ y ((R.rename e.names).channel.logicalType ((R.rename e.names).baseType (A.rename e.names))) := by
    simpa only [ChannelCode.logicalType_rename,baseType_rename,channel_rename] using hy
  have hl := (H.rename e).lift_typed (KY.rename e) (KP.rename e) hA' (e.moded mA) hm' (e.moded mm) hy' my
  exact (H.rename e).channel.eval_formula (H.rename e).probe.carrier_sorted (H.rename e).probe.carrier_mode hi' (e.moded mi) hl.1 hl.2
theorem predLift_typed {A m i : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hm : HasType P Γ m (R.probe.paramType A)) (mm : WellModed γ m .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data) :
    HasType P Γ (R.predLift L.code KY.code KP.code A m i) (R.channel.predicateType (R.baseType A)) ∧
      WellModed γ (R.predLift L.code KY.code KP.code A m i) .data := by
  obtain ⟨s,hs⟩ := H.probe.funTriple.domain.1
  exact H.channel.pred_typed (H.base_sorted hA) (H.base_mode mA)
    (H.liftEvalBody_family KY KP hA mA hm mm hi mi) (H.probe.raw_sorted hA s hs)
theorem predLiftMap_typed {A i : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data) :
    DataMap P Γ γ (R.probe.paramType A) (R.channel.predicateType (R.baseType A)) (R.predLiftMap L.code KY.code KP.code A i) := by
  obtain ⟨s,hs⟩ := H.probe.funTriple.domain.1
  let e : Embedding P Γ γ (R.probe.paramType A :: Γ) (modeCons .data γ) := Embedding.cons (H.probe.param_sorted hA s hs) .data
  have hA' : HasType P (R.probe.paramType A :: Γ) (A.rename e.names) (.sort (R.rename e.names).probe.seed) := by
    simpa only [Expr.rename,RelationalCode.rename,ProbeCode.rename] using e.typing hA
  have hm' : HasType P (R.probe.paramType A :: Γ) (.var 0) ((R.rename e.names).probe.paramType (A.rename e.names)) := by
    simpa only [ProbeCode.paramType_rename,RelationalCode.rename,e,Embedding.cons] using HasType.var (H.probe.param_sorted hA s hs)
  have hi' : HasType P (R.probe.paramType A :: Γ) (i.rename e.names) ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) := by
    simpa only [ChannelCode.predicateType_rename,ProbeCode.carrier_rename,channel_rename,RelationalCode.rename,RelationalCode.channel,ChannelCode.rename,ProbeCode.rename] using e.typing hi
  have ht := (H.rename e).predLift_typed (KY.rename e) (KP.rename e) hA' (e.moded mA) hm' (.var 0) hi' (e.moded mi)
  simpa only [DataMap,predLiftMap,LogicSetup.code_rename,QuantifierRoute.code_rename,
    ChannelCode.predicateType_rename,baseType_rename,channel_rename,e,Embedding.cons,
    QuantifierRoute.code,QuantifierRoute.rename,QuantifierCode.rename] using ht
theorem recoverLift_formula {A i w : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hw : HasType P Γ w (R.probe.singleType A)) (mw : WellModed γ w .data) :
    L.Formula (R.recoverLift L.code KY.code KP.code A i w) := by
  exact H.probe.doubled_formed.recoverAccess_formula H.channel.predicate H.probe.funTriple.domain.1 KP.triple.domain.1
    (H.probe.raw_sorted hA) (H.probe.raw_mode mA) (H.predLiftMap_typed KY KP hA mA hi mi) hw mw
theorem recoverLiftBody_family {A i : Expr S}
    (hA : HasType P Γ A (.sort R.probe.seed)) (mA : WellModed γ A .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data) :
    L.Family (R.probe.singleType A) (R.recoverLiftBody L.code KY.code KP.code A i) := by
  intro Δ δ e w hw mw
  rw [recoverLiftBody_rename,recoverLiftBody_instantiate]
  have hA' : HasType P Δ (A.rename e.names) (.sort (R.rename e.names).probe.seed) := by
    simpa only [Expr.rename,RelationalCode.rename,ProbeCode.rename] using e.typing hA
  have hi' : HasType P Δ (i.rename e.names) ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) := by
    simpa only [ChannelCode.predicateType_rename,ProbeCode.carrier_rename,channel_rename,RelationalCode.rename,RelationalCode.channel,ChannelCode.rename,ProbeCode.rename] using e.typing hi
  have hw' : HasType P Δ w ((R.rename e.names).probe.singleType (A.rename e.names)) := by
    simpa only [ProbeCode.singleType_rename,RelationalCode.rename] using hw
  exact (H.rename e).recoverLift_formula (KY.rename e) (KP.rename e) hA' (e.moded mA) hi' (e.moded mi) hw' mw
theorem probeFor_typed {i : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data) :
    HasType P Γ (R.probeFor L.code KY.code KP.code i) R.probe.carrier ∧
      WellModed γ (R.probeFor L.code KY.code KP.code i) .data := by
  obtain ⟨s,hs⟩ := H.probe.mainTriple.domain.1
  let e : Embedding P Γ γ (R.probe.domain :: Γ) (modeCons .data γ) := Embedding.cons (H.probe.domain_sorted s hs) .data
  have hi' : HasType P (R.probe.domain :: Γ) (i.rename e.names) ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) := by
    simpa only [ChannelCode.predicateType_rename,ProbeCode.carrier_rename,channel_rename,RelationalCode.rename,RelationalCode.channel,ChannelCode.rename,ProbeCode.rename] using e.typing hi
  have hf := (H.rename e).recoverLiftBody_family (KY.rename e) (KP.rename e)
    (H.probe.raised_project (H.probe.domain_sorted s hs))
    ((H.probe.rename e).project_mode (.var 0)) hi' (e.moded mi)
  exact H.probe.uniform_typed (H.probe.domain_sorted s hs) hf
theorem le_formula {i x : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data) :
    L.Formula (R.le L.code KY.code KP.code i x) := by
  have ht := H.probeFor_typed KY KP hi mi
  exact (H.channel.logical.sound H.probe.carrier_sorted H.probe.carrier_mode).2 _ _ hx mx ht
end RelationalCode.Formed

namespace RelationalCode
variable (R : RelationalCode S)

theorem leBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (ρ : Nat → Nat) :
    (R.leBody L KY KP x).rename (Expr.liftRen ρ) =
      (R.rename ρ).leBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) := by
  simp only [leBody,le_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,
    Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl
theorem leBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (σ : Nat → Expr S) :
    (R.leBody L KY KP x).subst (Expr.liftSub σ) =
      (R.subst σ).leBody (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) := by
  simp only [leBody,le_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,
    QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,
    Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  rfl
theorem leBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (x i : Expr S) :
    (R.leBody L KY KP x).instantiate i = R.le L KY KP i x := by
  simp only [leBody,Expr.instantiate,le_subst,instantiate_raise,LogicCode.instantiate_raise,
    QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
theorem xCompareBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x y : Expr S) (ρ : Nat → Nat) :
    (R.xCompareBody L KY KP x y).rename (Expr.liftRen ρ) =
      (R.rename ρ).xCompareBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) (y.rename ρ) := by
  simp only [xCompareBody,LogicCode.iff_rename,leBody_rename,LogicCode.rename_comp]
  rfl
theorem xCompareBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x y : Expr S) (σ : Nat → Expr S) :
    (R.xCompareBody L KY KP x y).subst (Expr.liftSub σ) =
      (R.subst σ).xCompareBody (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) (y.subst σ) := by
  simp only [xCompareBody,LogicCode.iff_subst,leBody_subst,LogicCode.subst_rename,LogicCode.rename_subst]
  rfl
theorem xCompareBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (x y i : Expr S) :
    (R.xCompareBody L KY KP x y).instantiate i = L.iff (R.le L KY KP i x) (R.le L KY KP i y) := by
  change ((L.rename Nat.succ).iff (R.leBody L KY KP x) (R.leBody L KY KP y)).subst (Expr.single i) = _
  rw [LogicCode.iff_subst,LogicCode.instantiate_raise]
  change L.iff ((R.leBody L KY KP x).instantiate i) ((R.leBody L KY KP y).instantiate i) = _
  rw [leBody_instantiate,leBody_instantiate]
theorem xCompare_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x y : Expr S) (ρ : Nat → Nat) :
    (R.xCompare L KY KP x y).rename ρ =
      (R.rename ρ).xCompare (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) (y.rename ρ) := by
  simp only [xCompare,QuantifierCode.all_rename,ChannelCode.predicateType_rename,ProbeCode.carrier_rename,
    channel_rename,xCompareBody_rename]
  rfl
theorem xCompare_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x y : Expr S) (σ : Nat → Expr S) :
    (R.xCompare L KY KP x y).subst σ =
      (R.subst σ).xCompare (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) (y.subst σ) := by
  simp only [xCompare,QuantifierCode.all_subst,ChannelCode.predicateType_subst,ProbeCode.carrier_subst,
    channel_subst,xCompareBody_subst]
  rfl

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {R : RelationalCode S}
    (H : R.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H
theorem leBody_family {x : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data) :
    L.Family (R.channel.predicateType R.probe.carrier) (R.leBody L.code KY.code KP.code x) := by
  intro Δ δ e i hi mi
  rw [leBody_rename,leBody_instantiate]
  have hi' : HasType P Δ i ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) := by
    simpa only [ChannelCode.predicateType_rename,ProbeCode.carrier_rename,channel_rename,
      RelationalCode.rename,RelationalCode.channel,ChannelCode.rename,ProbeCode.rename] using hi
  have hx' : HasType P Δ (x.rename e.names) ((R.rename e.names).channel.logicalType (R.rename e.names).probe.carrier) := by
    simpa only [ChannelCode.logicalType_rename,ProbeCode.carrier_rename,channel_rename,
      RelationalCode.rename,RelationalCode.channel,ChannelCode.rename,ProbeCode.rename] using e.typing hx
  exact (H.rename e).le_formula (KY.rename e) (KP.rename e) hi' mi hx' (e.moded mx)
theorem xCompareBody_family {x y : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hy : HasType P Γ y (R.channel.logicalType R.probe.carrier)) (my : WellModed γ y .data) :
    L.Family (R.channel.predicateType R.probe.carrier) (R.xCompareBody L.code KY.code KP.code x y) :=
  (H.leBody_family KY KP hx mx).code_iff (H.leBody_family KY KP hy my)
theorem xCompare_formula {x y : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hy : HasType P Γ y (R.channel.logicalType R.probe.carrier)) (my : WellModed γ y .data) :
    L.Formula (R.xCompare L.code KY.code KP.code x y) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  exact L.all_formula_family KP (H.channel.predicate_sorted H.probe.carrier_sorted)
    (H.channel.predicate_mode H.probe.carrier_mode) (H.channel.predicate_sorted H.probe.carrier_sorted s hs)
    (H.xCompareBody_family KY KP hx mx hy my)
theorem xCompare_intro {x y : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hy : HasType P Γ y (R.channel.logicalType R.probe.carrier)) (my : WellModed γ y .data)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) i,
      HasType P Δ i ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) → WellModed δ i .data →
      Equivalent P Δ δ ((R.rename e.names).le (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names) i (x.rename e.names))
        ((R.rename e.names).le (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names) i (y.rename e.names))) :
    Proves P Γ γ (R.xCompare L.code KY.code KP.code x y) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  apply L.all_intro_future KP (H.channel.predicate_sorted H.probe.carrier_sorted)
    (H.channel.predicate_mode H.probe.carrier_mode) (H.channel.predicate_sorted H.probe.carrier_sorted s hs)
    (H.xCompareBody_family KY KP hx mx hy my)
  intro Δ δ e i hi mi
  rw [xCompareBody_rename,xCompareBody_instantiate]
  have hi' : HasType P Δ i ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) := by
    simpa only [ChannelCode.predicateType_rename,ProbeCode.carrier_rename,channel_rename,
      RelationalCode.rename,RelationalCode.channel,ChannelCode.rename,ProbeCode.rename] using hi
  have hx' : HasType P Δ (x.rename e.names) ((R.rename e.names).channel.logicalType (R.rename e.names).probe.carrier) := by
    simpa only [ChannelCode.logicalType_rename,ProbeCode.carrier_rename,channel_rename,
      RelationalCode.rename,RelationalCode.channel,ChannelCode.rename,ProbeCode.rename] using e.typing hx
  have hy' : HasType P Δ (y.rename e.names) ((R.rename e.names).channel.logicalType (R.rename e.names).probe.carrier) := by
    simpa only [ChannelCode.logicalType_rename,ProbeCode.carrier_rename,channel_rename,
      RelationalCode.rename,RelationalCode.channel,ChannelCode.rename,ProbeCode.rename] using e.typing hy
  exact (L.rename e).iff_of_equivalent ((H.rename e).le_formula (KY.rename e) (KP.rename e) hi' mi hx' (e.moded mx))
    ((H.rename e).le_formula (KY.rename e) (KP.rename e) hi' mi hy' (e.moded my)) (hh Δ δ e i hi' mi)
end Formed
end RelationalCode
end

section
universe u
namespace RelationalCode
variable {S : Type u} (R : RelationalCode S)

theorem extStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i x y : Expr S) (ρ : Nat → Nat) :
    (R.extStep L KY KP i x y).rename ρ =
      (R.rename ρ).extStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) (x.rename ρ) (y.rename ρ) := by
  simp only [extStep,LogicCode.imp_rename,LogicCode.iff_rename,xCompare_rename,ChannelCode.eval_rename,ProbeCode.carrier_rename,channel_rename]
  try rfl

theorem extStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i x y : Expr S) (σ : Nat → Expr S) :
    (R.extStep L KY KP i x y).subst σ =
      (R.subst σ).extStep (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) (x.subst σ) (y.subst σ) := by
  simp only [extStep,LogicCode.imp_subst,LogicCode.iff_subst,xCompare_subst,ChannelCode.eval_subst,ProbeCode.carrier_subst,channel_subst]
  try rfl

theorem extAtBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) (ρ : Nat → Nat) :
    (R.extAtBody L KY KP i x).rename (Expr.liftRen ρ) =
      (R.rename ρ).extAtBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) (x.rename ρ) := by
  simp only [extAtBody,extStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl

theorem extAtBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) (σ : Nat → Expr S) :
    (R.extAtBody L KY KP i x).subst (Expr.liftSub σ) =
      (R.subst σ).extAtBody (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) (x.subst σ) := by
  simp only [extAtBody,extStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl

theorem extAtBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (i x a : Expr S) :
    (R.extAtBody L KY KP i x).instantiate a = R.extStep L KY KP i x a := by
  simp only [extAtBody,Expr.instantiate,extStep_subst,instantiate_raise,LogicCode.instantiate_raise,
    QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]

theorem extAt_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) (ρ : Nat → Nat) :
    (R.extAt L KY KP i x).rename ρ =
      (R.rename ρ).extAt (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) (x.rename ρ) := by
  simp only [extAt,QuantifierCode.all_rename,ChannelCode.logicalType_rename,ProbeCode.carrier_rename,channel_rename,extAtBody_rename]
  try rfl

theorem extAt_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i x : Expr S) (σ : Nat → Expr S) :
    (R.extAt L KY KP i x).subst σ =
      (R.subst σ).extAt (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) (x.subst σ) := by
  simp only [extAt,QuantifierCode.all_subst,ChannelCode.logicalType_subst,ProbeCode.carrier_subst,channel_subst,extAtBody_subst]
  try rfl

theorem extBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (ρ : Nat → Nat) :
    (R.extBody L KY KP i).rename (Expr.liftRen ρ) =
      (R.rename ρ).extBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) := by
  simp only [extBody,extAt_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl

theorem extBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (σ : Nat → Expr S) :
    (R.extBody L KY KP i).subst (Expr.liftSub σ) =
      (R.subst σ).extBody (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) := by
  simp only [extBody,extAt_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl

theorem extBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (i a : Expr S) :
    (R.extBody L KY KP i).instantiate a = R.extAt L KY KP i a := by
  simp only [extBody,Expr.instantiate,extAt_subst,instantiate_raise,LogicCode.instantiate_raise,
    QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]

theorem extensional_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (ρ : Nat → Nat) :
    (R.extensional L KY KP i).rename ρ =
      (R.rename ρ).extensional (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) := by
  simp only [extensional,QuantifierCode.all_rename,ChannelCode.logicalType_rename,ProbeCode.carrier_rename,channel_rename,extBody_rename]
  try rfl

theorem extensional_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (σ : Nat → Expr S) :
    (R.extensional L KY KP i).subst σ =
      (R.subst σ).extensional (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) := by
  simp only [extensional,QuantifierCode.all_subst,ChannelCode.logicalType_subst,ProbeCode.carrier_subst,channel_subst,extBody_subst]
  try rfl

theorem validStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x i i' : Expr S) (ρ : Nat → Nat) :
    (R.validStep L KY KP x i i').rename ρ =
      (R.rename ρ).validStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) (i.rename ρ) (i'.rename ρ) := by
  simp only [validStep,LogicCode.imp_rename,LogicCode.iff_rename,ChannelCode.predCompare_rename,ProbeCode.carrier_rename,channel_rename,le_rename]
  try rfl

theorem validStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x i i' : Expr S) (σ : Nat → Expr S) :
    (R.validStep L KY KP x i i').subst σ =
      (R.subst σ).validStep (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) (i.subst σ) (i'.subst σ) := by
  simp only [validStep,LogicCode.imp_subst,LogicCode.iff_subst,ChannelCode.predCompare_subst,ProbeCode.carrier_subst,channel_subst,le_subst]
  try rfl

theorem validAtBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x i : Expr S) (ρ : Nat → Nat) :
    (R.validAtBody L KY KP x i).rename (Expr.liftRen ρ) =
      (R.rename ρ).validAtBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) (i.rename ρ) := by
  simp only [validAtBody,validStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl

theorem validAtBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x i : Expr S) (σ : Nat → Expr S) :
    (R.validAtBody L KY KP x i).subst (Expr.liftSub σ) =
      (R.subst σ).validAtBody (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) (i.subst σ) := by
  simp only [validAtBody,validStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl

theorem validAtBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (x i a : Expr S) :
    (R.validAtBody L KY KP x i).instantiate a = R.validStep L KY KP x i a := by
  simp only [validAtBody,Expr.instantiate,validStep_subst,instantiate_raise,LogicCode.instantiate_raise,
    QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]

theorem validAt_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x i : Expr S) (ρ : Nat → Nat) :
    (R.validAt L KY KP x i).rename ρ =
      (R.rename ρ).validAt (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) (i.rename ρ) := by
  simp only [validAt,QuantifierCode.all_rename,ChannelCode.predicateType_rename,ProbeCode.carrier_rename,channel_rename,validAtBody_rename]
  try rfl

theorem validAt_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x i : Expr S) (σ : Nat → Expr S) :
    (R.validAt L KY KP x i).subst σ =
      (R.subst σ).validAt (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) (i.subst σ) := by
  simp only [validAt,QuantifierCode.all_subst,ChannelCode.predicateType_subst,ProbeCode.carrier_subst,channel_subst,validAtBody_subst]
  try rfl

theorem validBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (ρ : Nat → Nat) :
    (R.validBody L KY KP x).rename (Expr.liftRen ρ) =
      (R.rename ρ).validBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) := by
  simp only [validBody,validAt_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl

theorem validBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (σ : Nat → Expr S) :
    (R.validBody L KY KP x).subst (Expr.liftSub σ) =
      (R.subst σ).validBody (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) := by
  simp only [validBody,validAt_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl

theorem validBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (x a : Expr S) :
    (R.validBody L KY KP x).instantiate a = R.validAt L KY KP x a := by
  simp only [validBody,Expr.instantiate,validAt_subst,instantiate_raise,LogicCode.instantiate_raise,
    QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]

theorem valid_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (ρ : Nat → Nat) :
    (R.valid L KY KP x).rename ρ =
      (R.rename ρ).valid (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) := by
  simp only [valid,QuantifierCode.all_rename,ChannelCode.predicateType_rename,ProbeCode.carrier_rename,channel_rename,validBody_rename]
  try rfl

theorem valid_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (σ : Nat → Expr S) :
    (R.valid L KY KP x).subst σ =
      (R.subst σ).valid (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) := by
  simp only [valid,QuantifierCode.all_subst,ChannelCode.predicateType_subst,ProbeCode.carrier_subst,channel_subst,validBody_subst]
  try rfl
end RelationalCode
end

section
universe u
variable {S : Type u} {P : Specification S}
namespace RelationalCode.Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {R : RelationalCode S}
    (H : R.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

omit H in
theorem x_typed_rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) {x : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) :
    HasType P Δ (x.rename e.names) ((R.rename e.names).channel.logicalType (R.rename e.names).probe.carrier) := by
  simpa only [ChannelCode.logicalType_rename,ProbeCode.carrier_rename,channel_rename,
    RelationalCode.rename,RelationalCode.channel,ChannelCode.rename,ProbeCode.rename] using e.typing hx

theorem xCompare_round {x : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data) :
    Proves P Γ γ (R.xCompare L.code KY.code KP.code x (R.channel.round R.probe.carrier x)) := by
  have hr := H.channel.round_typed H.probe.carrier_sorted H.probe.carrier_mode hx mx
  apply H.xCompare_intro KY KP hx mx hr.1 hr.2
  intro Δ δ e i hi mi
  have hv := (H.rename e).probeFor_typed (KY.rename e) (KP.rename e) hi mi
  have hh := (H.rename e).channel.primitive_round (H.rename e).probe.carrier_sorted
    (H.rename e).probe.carrier_mode (x_typed_rename (R := R) e hx) (e.moded mx) hv.1 hv.2
  simpa only [le,ChannelCode.round_rename,ProbeCode.carrier_rename,channel_rename,
    LogicSetup.code_rename,QuantifierRoute.code,QuantifierRoute.rename,QuantifierCode.rename,
    RelationalCode.rename,RelationalCode.channel, ChannelCode.rename, ProbeCode.rename] using hh.symm
end RelationalCode.Formed

namespace RelationalCode
variable (R : RelationalCode S)
theorem x_type_rename (ρ : Nat → Nat) :
    (R.channel.logicalType R.probe.carrier).rename ρ =
      (R.rename ρ).channel.logicalType (R.rename ρ).probe.carrier := by
  simp only [ChannelCode.logicalType_rename,ProbeCode.carrier_rename,channel_rename]
  rfl
theorem p_type_rename (ρ : Nat → Nat) :
    (R.channel.predicateType R.probe.carrier).rename ρ =
      (R.rename ρ).channel.predicateType (R.rename ρ).probe.carrier := by
  simp only [ChannelCode.predicateType_rename,ProbeCode.carrier_rename,channel_rename]
  rfl
namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {R : RelationalCode S}
    (H : R.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem extStep_formula {i x y : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hy : HasType P Γ y (R.channel.logicalType R.probe.carrier)) (my : WellModed γ y .data) :
    L.Formula (R.extStep L.code KY.code KP.code i x y) :=
  L.imp_formula (H.xCompare_formula KY KP hx mx hy my)
    (L.iff_formula (H.channel.eval_formula H.probe.carrier_sorted H.probe.carrier_mode hi mi hx mx)
      (H.channel.eval_formula H.probe.carrier_sorted H.probe.carrier_mode hi mi hy my))

theorem validStep_formula {x i c : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hc : HasType P Γ c (R.channel.predicateType R.probe.carrier)) (mc : WellModed γ c .data) :
    L.Formula (R.validStep L.code KY.code KP.code x i c) :=
  L.imp_formula (H.channel.predCompare_formula H.probe.carrier_sorted H.probe.carrier_mode KY hi mi hc mc)
    (L.iff_formula (H.le_formula KY KP hi mi hx mx) (H.le_formula KY KP hc mc hx mx))

theorem extAtBody_family {i x : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data) :
    L.Family (R.channel.logicalType R.probe.carrier) (R.extAtBody L.code KY.code KP.code i x) := by
  intro Δ δ e y hy my
  rw [extAtBody_rename,extAtBody_instantiate]
  have hi' : HasType P Δ (i.rename e.names) ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) := by
    simpa only [p_type_rename] using e.typing hi
  have hx' : HasType P Δ (x.rename e.names) ((R.rename e.names).channel.logicalType (R.rename e.names).probe.carrier) := by
    simpa only [x_type_rename] using e.typing hx
  have hy' : HasType P Δ y ((R.rename e.names).channel.logicalType (R.rename e.names).probe.carrier) := by
    simpa only [x_type_rename] using hy
  exact (H.rename e).extStep_formula (KY.rename e) (KP.rename e) hi' (e.moded mi) hx' (e.moded mx) hy' my

theorem extAt_formula {i x : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data) :
    L.Formula (R.extAt L.code KY.code KP.code i x) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  exact L.all_formula_family KY (H.channel.logical_sorted H.probe.carrier_sorted)
    (H.channel.logical_mode H.probe.carrier_mode) (H.channel.logical_sorted H.probe.carrier_sorted s hs)
    (H.extAtBody_family KY KP hi mi hx mx)

theorem extBody_family {i : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data) :
    L.Family (R.channel.logicalType R.probe.carrier) (R.extBody L.code KY.code KP.code i) := by
  intro Δ δ e x hx mx
  rw [extBody_rename,extBody_instantiate]
  have hi' : HasType P Δ (i.rename e.names) ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) := by
    simpa only [p_type_rename] using e.typing hi
  have hx' : HasType P Δ x ((R.rename e.names).channel.logicalType (R.rename e.names).probe.carrier) := by
    simpa only [x_type_rename] using hx
  exact (H.rename e).extAt_formula (KY.rename e) (KP.rename e) hi' (e.moded mi) hx' mx

theorem extensional_formula {i : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data) :
    L.Formula (R.extensional L.code KY.code KP.code i) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  exact L.all_formula_family KY (H.channel.logical_sorted H.probe.carrier_sorted)
    (H.channel.logical_mode H.probe.carrier_mode) (H.channel.logical_sorted H.probe.carrier_sorted s hs)
    (H.extBody_family KY KP hi mi)

theorem validAtBody_family {x i : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data) :
    L.Family (R.channel.predicateType R.probe.carrier) (R.validAtBody L.code KY.code KP.code x i) := by
  intro Δ δ e c hc mc
  rw [validAtBody_rename,validAtBody_instantiate]
  have hx' : HasType P Δ (x.rename e.names) ((R.rename e.names).channel.logicalType (R.rename e.names).probe.carrier) := by
    simpa only [x_type_rename] using e.typing hx
  have hi' : HasType P Δ (i.rename e.names) ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) := by
    simpa only [p_type_rename] using e.typing hi
  have hc' : HasType P Δ c ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) := by
    simpa only [p_type_rename] using hc
  exact (H.rename e).validStep_formula (KY.rename e) (KP.rename e) hx' (e.moded mx) hi' (e.moded mi) hc' mc

theorem validAt_formula {x i : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data) :
    L.Formula (R.validAt L.code KY.code KP.code x i) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  exact L.all_formula_family KP (H.channel.predicate_sorted H.probe.carrier_sorted)
    (H.channel.predicate_mode H.probe.carrier_mode) (H.channel.predicate_sorted H.probe.carrier_sorted s hs)
    (H.validAtBody_family KY KP hx mx hi mi)

theorem validBody_family {x : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data) :
    L.Family (R.channel.predicateType R.probe.carrier) (R.validBody L.code KY.code KP.code x) := by
  intro Δ δ e i hi mi
  rw [validBody_rename,validBody_instantiate]
  have hx' : HasType P Δ (x.rename e.names) ((R.rename e.names).channel.logicalType (R.rename e.names).probe.carrier) := by
    simpa only [x_type_rename] using e.typing hx
  have hi' : HasType P Δ i ((R.rename e.names).channel.predicateType (R.rename e.names).probe.carrier) := by
    simpa only [p_type_rename] using hi
  exact (H.rename e).validAt_formula (KY.rename e) (KP.rename e) hx' (e.moded mx) hi' mi

theorem valid_formula {x : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data) :
    L.Formula (R.valid L.code KY.code KP.code x) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  exact L.all_formula_family KP (H.channel.predicate_sorted H.probe.carrier_sorted)
    (H.channel.predicate_mode H.probe.carrier_mode) (H.channel.predicate_sorted H.probe.carrier_sorted s hs)
    (H.validBody_family KY KP hx mx)
end Formed
end RelationalCode

namespace RelationalCode.Formed

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {R : RelationalCode S}
    (H : R.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem extAt_intro {i x : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) y,
      HasType P Δ y ((R.rename e.names).channel.logicalType (R.rename e.names).probe.carrier) → WellModed δ y .data →
      Proves P Δ δ ((R.rename e.names).extStep (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names) (i.rename e.names) (x.rename e.names) y)) :
    Proves P Γ γ (R.extAt L.code KY.code KP.code i x) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  apply L.all_intro_future KY (H.channel.logical_sorted H.probe.carrier_sorted)
    (H.channel.logical_mode H.probe.carrier_mode) (H.channel.logical_sorted H.probe.carrier_sorted s hs)
    (H.extAtBody_family KY KP hi mi hx mx)
  intro Δ δ e y hy my
  rw [extAtBody_rename,extAtBody_instantiate]
  exact hh Δ δ e y (by simpa only [x_type_rename] using hy) my

theorem extAt_elim_one {i x y : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hy : HasType P Γ y (R.channel.logicalType R.probe.carrier)) (my : WellModed γ y .data)
    (hp : Proves P Γ γ (R.extAt L.code KY.code KP.code i x)) :
    Proves P Γ γ (R.extStep L.code KY.code KP.code i x y) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  have hh := L.all_elim_family KY (H.channel.logical_sorted H.probe.carrier_sorted)
    (H.channel.logical_mode H.probe.carrier_mode) (H.channel.logical_sorted H.probe.carrier_sorted s hs)
    (H.extAtBody_family KY KP hi mi hx mx) hy my hp
  simpa only [extAtBody_instantiate] using hh

theorem extensional_intro {i : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) x,
      HasType P Δ x ((R.rename e.names).channel.logicalType (R.rename e.names).probe.carrier) → WellModed δ x .data →
      Proves P Δ δ ((R.rename e.names).extAt (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names) (i.rename e.names) x)) :
    Proves P Γ γ (R.extensional L.code KY.code KP.code i) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  apply L.all_intro_future KY (H.channel.logical_sorted H.probe.carrier_sorted)
    (H.channel.logical_mode H.probe.carrier_mode) (H.channel.logical_sorted H.probe.carrier_sorted s hs)
    (H.extBody_family KY KP hi mi)
  intro Δ δ e x hx mx
  rw [extBody_rename,extBody_instantiate]
  exact hh Δ δ e x (by simpa only [x_type_rename] using hx) mx

theorem extensional_elim_one {i x : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hp : Proves P Γ γ (R.extensional L.code KY.code KP.code i)) :
    Proves P Γ γ (R.extAt L.code KY.code KP.code i x) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  have hh := L.all_elim_family KY (H.channel.logical_sorted H.probe.carrier_sorted)
    (H.channel.logical_mode H.probe.carrier_mode) (H.channel.logical_sorted H.probe.carrier_sorted s hs)
    (H.extBody_family KY KP hi mi) hx mx hp
  simpa only [extBody_instantiate] using hh

theorem validAt_elim_one {x i c : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hc : HasType P Γ c (R.channel.predicateType R.probe.carrier)) (mc : WellModed γ c .data)
    (hp : Proves P Γ γ (R.validAt L.code KY.code KP.code x i)) :
    Proves P Γ γ (R.validStep L.code KY.code KP.code x i c) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  have hh := L.all_elim_family KP (H.channel.predicate_sorted H.probe.carrier_sorted)
    (H.channel.predicate_mode H.probe.carrier_mode) (H.channel.predicate_sorted H.probe.carrier_sorted s hs)
    (H.validAtBody_family KY KP hx mx hi mi) hc mc hp
  simpa only [validAtBody_instantiate] using hh

theorem valid_elim_one {x i : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hp : Proves P Γ γ (R.valid L.code KY.code KP.code x)) :
    Proves P Γ γ (R.validAt L.code KY.code KP.code x i) := by
  obtain ⟨s,hs⟩ := KP.triple.domain.1
  have hh := L.all_elim_family KP (H.channel.predicate_sorted H.probe.carrier_sorted)
    (H.channel.predicate_mode H.probe.carrier_mode) (H.channel.predicate_sorted H.probe.carrier_sorted s hs)
    (H.validBody_family KY KP hx mx) hi mi hp
  simpa only [validBody_instantiate] using hh

theorem extensional_elim {i x y : Expr S}
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hy : HasType P Γ y (R.channel.logicalType R.probe.carrier)) (my : WellModed γ y .data)
    (he : Proves P Γ γ (R.extensional L.code KY.code KP.code i))
    (hr : Proves P Γ γ (R.xCompare L.code KY.code KP.code x y)) :
    Equivalent P Γ γ (R.channel.eval R.probe.carrier i x) (R.channel.eval R.probe.carrier i y) := by
  have hh := H.extAt_elim_one KY KP hi mi hx mx hy my (H.extensional_elim_one KY KP hi mi hx mx he)
  have fx := H.channel.eval_formula H.probe.carrier_sorted H.probe.carrier_mode hi mi hx mx
  have fy := H.channel.eval_formula H.probe.carrier_sorted H.probe.carrier_mode hi mi hy my
  exact L.equivalent_of_iff fx fy (L.imp_elim (H.xCompare_formula KY KP hx mx hy my) (L.iff_formula fx fy) hh hr)

theorem valid_elim {x i c : Expr S}
    (hx : HasType P Γ x (R.channel.logicalType R.probe.carrier)) (mx : WellModed γ x .data)
    (hi : HasType P Γ i (R.channel.predicateType R.probe.carrier)) (mi : WellModed γ i .data)
    (hc : HasType P Γ c (R.channel.predicateType R.probe.carrier)) (mc : WellModed γ c .data)
    (hv : Proves P Γ γ (R.valid L.code KY.code KP.code x))
    (he : Proves P Γ γ (R.channel.predCompare L.code KY.code R.probe.carrier i c)) :
    Equivalent P Γ γ (R.le L.code KY.code KP.code i x) (R.le L.code KY.code KP.code c x) := by
  have hh := H.validAt_elim_one KY KP hx mx hi mi hc mc (H.valid_elim_one KY KP hx mx hi mi hv)
  have fi := H.le_formula KY KP hi mi hx mx
  have fc := H.le_formula KY KP hc mc hx mx
  exact L.equivalent_of_iff fi fc (L.imp_elim
    (H.channel.predCompare_formula H.probe.carrier_sorted H.probe.carrier_mode KY hi mi hc mc)
    (L.iff_formula fi fc) hh he)
end

end RelationalCode.Formed
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
theorem bitInner_rename (L : LogicCode S) (T y : Expr S) (ρ : Nat → Nat) :
    (R.bitInner L T y).rename ρ = (R.rename ρ).bitInner (L.rename ρ) (T.rename ρ) (y.rename ρ) := by
  simp only [bitInner,DoubleCode.rec_rename,DoubleCode.bitBody_rename,middleType_rename,firstType_rename,rename]
theorem bitInner_subst (L : LogicCode S) (T y : Expr S) (σ : Nat → Expr S) :
    (R.bitInner L T y).subst σ = (R.subst σ).bitInner (L.subst σ) (T.subst σ) (y.subst σ) := by
  simp only [bitInner,DoubleCode.rec_subst,DoubleCode.bitBody_subst,middleType_subst,firstType_subst,subst]
theorem bitOuter_rename (L : LogicCode S) (T y : Expr S) (ρ : Nat → Nat) :
    (R.bitOuter L T y).rename ρ = (R.rename ρ).bitOuter (L.rename ρ) (T.rename ρ) (y.rename ρ) := by
  simp only [bitOuter,DoubleCode.bit_rename,middleType_rename,rename]
theorem bitOuter_subst (L : LogicCode S) (T y : Expr S) (σ : Nat → Expr S) :
    (R.bitOuter L T y).subst σ = (R.subst σ).bitOuter (L.subst σ) (T.subst σ) (y.subst σ) := by
  simp only [bitOuter,DoubleCode.bit_subst,middleType_subst,subst]
theorem observe_rename (L : LogicCode S) (T y a : Expr S) (ρ : Nat → Nat) :
    (R.observe L T y a).rename ρ = (R.rename ρ).observe (L.rename ρ) (T.rename ρ) (y.rename ρ) (a.rename ρ) := by
  simp only [observe,DoubleCode.rec_rename,DoubleCode.recBody_rename,DataWrapper.contraCallback_rename,middleType_rename,firstType_rename,rename]
theorem observe_subst (L : LogicCode S) (T y a : Expr S) (σ : Nat → Expr S) :
    (R.observe L T y a).subst σ = (R.subst σ).observe (L.subst σ) (T.subst σ) (y.subst σ) (a.subst σ) := by
  simp only [observe,DoubleCode.rec_subst,DoubleCode.recBody_subst,DataWrapper.contraCallback_subst,middleType_subst,firstType_subst,subst]
theorem tagged_rename (L : LogicCode S) (t : Fin 3) (T x : Expr S) (ρ : Nat → Nat) :
    (R.tagged L t T x).rename ρ = (R.rename ρ).tagged (L.rename ρ) t (T.rename ρ) (x.rename ρ) := by
  simp only [tagged,DoubleCode.emb_rename,DataWrapper.reencode_rename,middleType_rename,firstType_rename,rename]
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

theorem rename_comp (ρ τ : Nat → Nat) : (O.rename τ).rename ρ = O.rename (ρ ∘ τ) := by
  cases O; simp only [rename,RelationalCode.rename_comp,DoubleCode.rename_comp]
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
theorem tagged_rename (L : LogicCode S) (t : Fin 3) (x : Expr S) (ρ : Nat → Nat) :
    (O.tagged L t x).rename ρ = (O.rename ρ).tagged (L.rename ρ) t (x.rename ρ) := by
  simp only [tagged,ThreeCopyCode.tagged_rename,copies_rename,ProbeCode.carrier_rename,rename,RelationalCode.rename,ProbeCode.rename]
  try rfl
theorem tagged_subst (L : LogicCode S) (t : Fin 3) (x : Expr S) (σ : Nat → Expr S) :
    (O.tagged L t x).subst σ = (O.subst σ).tagged (L.subst σ) t (x.subst σ) := by
  simp only [tagged,ThreeCopyCode.tagged_subst,copies_subst,ProbeCode.carrier_subst,subst,RelationalCode.subst,ProbeCode.subst]
  try rfl
theorem bitInner_rename (L : LogicCode S) (y : Expr S) (ρ : Nat → Nat) :
    (O.bitInner L y).rename ρ = (O.rename ρ).bitInner (L.rename ρ) (y.rename ρ) := by
  simp only [bitInner,ThreeCopyCode.bitInner_rename,copies_rename,ProbeCode.carrier_rename,rename,RelationalCode.rename,ProbeCode.rename]
  try rfl
theorem bitInner_subst (L : LogicCode S) (y : Expr S) (σ : Nat → Expr S) :
    (O.bitInner L y).subst σ = (O.subst σ).bitInner (L.subst σ) (y.subst σ) := by
  simp only [bitInner,ThreeCopyCode.bitInner_subst,copies_subst,ProbeCode.carrier_subst,subst,RelationalCode.subst,ProbeCode.subst]
  try rfl
theorem bitOuter_rename (L : LogicCode S) (y : Expr S) (ρ : Nat → Nat) :
    (O.bitOuter L y).rename ρ = (O.rename ρ).bitOuter (L.rename ρ) (y.rename ρ) := by
  simp only [bitOuter,ThreeCopyCode.bitOuter_rename,copies_rename,ProbeCode.carrier_rename,rename,RelationalCode.rename,ProbeCode.rename]
  try rfl
theorem bitOuter_subst (L : LogicCode S) (y : Expr S) (σ : Nat → Expr S) :
    (O.bitOuter L y).subst σ = (O.subst σ).bitOuter (L.subst σ) (y.subst σ) := by
  simp only [bitOuter,ThreeCopyCode.bitOuter_subst,copies_subst,ProbeCode.carrier_subst,subst,RelationalCode.subst,ProbeCode.subst]
  try rfl
theorem observe_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i y : Expr S) (ρ : Nat → Nat) :
    (O.observe L KY KP i y).rename ρ = (O.rename ρ).observe (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) (y.rename ρ) := by
  simp only [observe,ThreeCopyCode.observe_rename,copies_rename,ProbeCode.carrier_rename,RelationalCode.probeFor_rename,rename,RelationalCode.rename,ProbeCode.rename]
  try rfl
theorem observe_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i y : Expr S) (σ : Nat → Expr S) :
    (O.observe L KY KP i y).subst σ = (O.subst σ).observe (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) (y.subst σ) := by
  simp only [observe,ThreeCopyCode.observe_subst,copies_subst,ProbeCode.carrier_subst,RelationalCode.probeFor_subst,subst,RelationalCode.subst,ProbeCode.subst]
  try rfl
theorem observeBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (y : Expr S) (ρ : Nat → Nat) :
    (O.observeBody L KY KP y).rename (Expr.liftRen ρ) = (O.rename ρ).observeBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (y.rename ρ) := by
  simp only [observeBody,observe_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem observeBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (y : Expr S) (σ : Nat → Expr S) :
    (O.observeBody L KY KP y).subst (Expr.liftSub σ) = (O.subst σ).observeBody (L.subst σ) (KY.subst σ) (KP.subst σ) (y.subst σ) := by
  simp only [observeBody,observe_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem compareBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (ρ : Nat → Nat) :
    (O.compareBody L KY KP y z).rename (Expr.liftRen ρ) = (O.rename ρ).compareBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (y.rename ρ) (z.rename ρ) := by
  simp only [compareBody,LogicCode.iff_rename,observeBody_rename,LogicCode.rename_comp]
  try rfl
theorem compareBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (σ : Nat → Expr S) :
    (O.compareBody L KY KP y z).subst (Expr.liftSub σ) = (O.subst σ).compareBody (L.subst σ) (KY.subst σ) (KP.subst σ) (y.subst σ) (z.subst σ) := by
  simp only [compareBody,LogicCode.iff_subst,observeBody_subst,LogicCode.subst_rename,LogicCode.rename_subst]
  try rfl
theorem compare_rename (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (ρ : Nat → Nat) :
    (O.compare L KY KP y z).rename ρ = (O.rename ρ).compare (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (y.rename ρ) (z.rename ρ) := by
  simp only [compare,QuantifierCode.all_rename,RelationalCode.p_type_rename,compareBody_rename]
  try rfl
theorem compare_subst (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (σ : Nat → Expr S) :
    (O.compare L KY KP y z).subst σ = (O.subst σ).compare (L.subst σ) (KY.subst σ) (KP.subst σ) (y.subst σ) (z.subst σ) := by
  simp only [compare,QuantifierCode.all_subst,ChannelCode.predicateType_subst,ProbeCode.carrier_subst,subst,RelationalCode.subst,ProbeCode.subst,compareBody_subst]
  try rfl
theorem ae_rename (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (ρ : Nat → Nat) :
    (O.ae L KY KP y z).rename ρ = (O.rename ρ).ae (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (y.rename ρ) (z.rename ρ) := by
  simp only [ae,LogicCode.conj_rename,LogicCode.iff_rename,bitInner_rename,bitOuter_rename,compare_rename]
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

end Formed
end DoubleCode
end

section
universe u
namespace SpecializedCode
variable {S : Type u} (B : SpecializedCode S)
theorem rename_comp (ρ τ : Nat → Nat) : (B.rename ρ).rename τ = B.rename (τ ∘ ρ) := by
  simp only [rename,ObservationCode.rename_comp,Expr.rename_comp]
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
theorem xType_rename (ρ : Nat → Nat) : (B.xType ).rename ρ = (B.rename ρ).xType  := by
  simp only [xType,ChannelCode.logicalType_rename,ProbeCode.carrier_rename,rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename]
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
theorem xPredType_rename (ρ : Nat → Nat) : (B.xPredType ).rename ρ = (B.rename ρ).xPredType  := by
  simp only [xPredType,ChannelCode.predicateType_rename,ProbeCode.carrier_rename,rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename]
  try rfl
theorem ev_rename (v y : Expr S) (ρ : Nat → Nat) : (B.ev v y).rename ρ = (B.rename ρ).ev (v.rename ρ) (y.rename ρ) := by
  simp only [ev,ChannelCode.eval_rename,baseType_rename,rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename]
  try rfl
theorem ev_subst (v y : Expr S) (σ : Nat → Expr S) : (B.ev v y).subst σ = (B.subst σ).ev (v.subst σ) (y.subst σ) := by
  simp only [ev,ChannelCode.eval_subst,baseType_subst,subst,relational,ObservationCode.subst,RelationalCode.channel,RelationalCode.subst]
  try rfl
theorem gStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v y z : Expr S) (ρ : Nat → Nat) :
    (B.gStep L KY KP v y z).rename ρ = (B.rename ρ).gStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (y.rename ρ) (z.rename ρ) := by
  simp only [gStep,LogicCode.imp_rename,LogicCode.iff_rename,ObservationCode.ae_rename,ev_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem gStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v y z : Expr S) (σ : Nat → Expr S) :
    (B.gStep L KY KP v y z).subst σ = (B.subst σ).gStep (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (y.subst σ) (z.subst σ) := by
  simp only [gStep,LogicCode.imp_subst,LogicCode.iff_subst,ObservationCode.ae_subst,ev_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem gAtBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (ρ : Nat → Nat) :
    (B.gAtBody L KY KP v y).rename (Expr.liftRen ρ) = (B.rename ρ).gAtBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (y.rename ρ) := by
  simp only [gAtBody,gStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem gAtBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (σ : Nat → Expr S) :
    (B.gAtBody L KY KP v y).subst (Expr.liftSub σ) = (B.subst σ).gAtBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (y.subst σ) := by
  simp only [gAtBody,gStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem gAt_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (ρ : Nat → Nat) :
    (B.gAt L KY KP v y).rename ρ = (B.rename ρ).gAt (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (y.rename ρ) := by
  simp only [gAt,QuantifierCode.all_rename,yType_rename,gAtBody_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem gAt_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (σ : Nat → Expr S) :
    (B.gAt L KY KP v y).subst σ = (B.subst σ).gAt (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (y.subst σ) := by
  simp only [gAt,QuantifierCode.all_subst,yType_subst,gAtBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem gBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.gBody L KY KP v).rename (Expr.liftRen ρ) = (B.rename ρ).gBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [gBody,gAt_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem gBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.gBody L KY KP v).subst (Expr.liftSub σ) = (B.subst σ).gBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [gBody,gAt_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem propertyG_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.propertyG L KY KP v).rename ρ = (B.rename ρ).propertyG (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [propertyG,QuantifierCode.all_rename,yType_rename,gBody_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem propertyG_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.propertyG L KY KP v).subst σ = (B.subst σ).propertyG (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [propertyG,QuantifierCode.all_subst,yType_subst,gBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem cStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x w : Expr S) (ρ : Nat → Nat) :
    (B.cStep L KY KP t v x w).rename ρ = (B.rename ρ).cStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) (x.rename ρ) (w.rename ρ) := by
  simp only [cStep,LogicCode.iff_rename,ev_rename,ObservationCode.ae_rename,ObservationCode.tagged_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem cStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x w : Expr S) (σ : Nat → Expr S) :
    (B.cStep L KY KP t v x w).subst σ = (B.subst σ).cStep (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (x.subst σ) (w.subst σ) := by
  simp only [cStep,LogicCode.iff_subst,ev_subst,ObservationCode.ae_subst,ObservationCode.tagged_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem cAtBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (ρ : Nat → Nat) :
    (B.cAtBody L KY KP t v x).rename (Expr.liftRen ρ) = (B.rename ρ).cAtBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) (x.rename ρ) := by
  simp only [cAtBody,cStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem cAtBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (σ : Nat → Expr S) :
    (B.cAtBody L KY KP t v x).subst (Expr.liftSub σ) = (B.subst σ).cAtBody (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (x.subst σ) := by
  simp only [cAtBody,cStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem cAt_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (ρ : Nat → Nat) :
    (B.cAt L KY KP t v x).rename ρ = (B.rename ρ).cAt (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) (x.rename ρ) := by
  simp only [cAt,QuantifierCode.all_rename,yType_rename,cAtBody_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem cAt_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (σ : Nat → Expr S) :
    (B.cAt L KY KP t v x).subst σ = (B.subst σ).cAt (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (x.subst σ) := by
  simp only [cAt,QuantifierCode.all_subst,yType_subst,cAtBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem cBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (ρ : Nat → Nat) :
    (B.cBody L KY KP t v).rename (Expr.liftRen ρ) = (B.rename ρ).cBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) := by
  simp only [cBody,cAt_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem cBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (σ : Nat → Expr S) :
    (B.cBody L KY KP t v).subst (Expr.liftSub σ) = (B.subst σ).cBody (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) := by
  simp only [cBody,cAt_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem propertyC_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (ρ : Nat → Nat) :
    (B.propertyC L KY KP t v).rename ρ = (B.rename ρ).propertyC (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) := by
  simp only [propertyC,LogicCode.ex_rename,xType_rename,cBody_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem propertyC_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (σ : Nat → Expr S) :
    (B.propertyC L KY KP t v).subst σ = (B.subst σ).propertyC (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) := by
  simp only [propertyC,LogicCode.ex_subst,xType_subst,cBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem eStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x w : Expr S) (ρ : Nat → Nat) :
    (B.eStep L KY KP t v x w).rename ρ = (B.rename ρ).eStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) (x.rename ρ) (w.rename ρ) := by
  simp only [eStep,LogicCode.iff_rename,LogicCode.disj_rename,ev_rename,ObservationCode.ae_rename,ObservationCode.tagged_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem eStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x w : Expr S) (σ : Nat → Expr S) :
    (B.eStep L KY KP t v x w).subst σ = (B.subst σ).eStep (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (x.subst σ) (w.subst σ) := by
  simp only [eStep,LogicCode.iff_subst,LogicCode.disj_subst,ev_subst,ObservationCode.ae_subst,ObservationCode.tagged_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem eAtBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (ρ : Nat → Nat) :
    (B.eAtBody L KY KP t v x).rename (Expr.liftRen ρ) = (B.rename ρ).eAtBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) (x.rename ρ) := by
  simp only [eAtBody,eStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem eAtBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (σ : Nat → Expr S) :
    (B.eAtBody L KY KP t v x).subst (Expr.liftSub σ) = (B.subst σ).eAtBody (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (x.subst σ) := by
  simp only [eAtBody,eStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem eAt_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (ρ : Nat → Nat) :
    (B.eAt L KY KP t v x).rename ρ = (B.rename ρ).eAt (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) (x.rename ρ) := by
  simp only [eAt,QuantifierCode.all_rename,yType_rename,eAtBody_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem eAt_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v x : Expr S) (σ : Nat → Expr S) :
    (B.eAt L KY KP t v x).subst σ = (B.subst σ).eAt (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) (x.subst σ) := by
  simp only [eAt,QuantifierCode.all_subst,yType_subst,eAtBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem eBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (ρ : Nat → Nat) :
    (B.eBody L KY KP t v).rename (Expr.liftRen ρ) = (B.rename ρ).eBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) := by
  simp only [eBody,eAt_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem eBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (σ : Nat → Expr S) :
    (B.eBody L KY KP t v).subst (Expr.liftSub σ) = (B.subst σ).eBody (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) := by
  simp only [eBody,eAt_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem propertyE_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (ρ : Nat → Nat) :
    (B.propertyE L KY KP t v).rename ρ = (B.rename ρ).propertyE (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) := by
  simp only [propertyE,LogicCode.ex_rename,xType_rename,eBody_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem propertyE_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 3) (v : Expr S) (σ : Nat → Expr S) :
    (B.propertyE L KY KP t v).subst σ = (B.subst σ).propertyE (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) := by
  simp only [propertyE,LogicCode.ex_subst,xType_subst,eBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem rPredStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (ρ : Nat → Nat) :
    (B.rPredStep L KY KP v x).rename ρ = (B.rename ρ).rPredStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (x.rename ρ) := by
  simp only [rPredStep,ev_rename,ObservationCode.tagged_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem rPredStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (σ : Nat → Expr S) :
    (B.rPredStep L KY KP v x).subst σ = (B.subst σ).rPredStep (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (x.subst σ) := by
  simp only [rPredStep,ev_subst,ObservationCode.tagged_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem rPredBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.rPredBody L KY KP v).rename (Expr.liftRen ρ) = (B.rename ρ).rPredBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [rPredBody,rPredStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem rPredBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.rPredBody L KY KP v).subst (Expr.liftSub σ) = (B.subst σ).rPredBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [rPredBody,rPredStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem rPred_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.rPred L KY KP v).rename ρ = (B.rename ρ).rPred (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [rPred,ChannelCode.pred_rename,ProbeCode.carrier_rename,rPredBody_rename,rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename]
  try rfl
theorem rPred_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.rPred L KY KP v).subst σ = (B.subst σ).rPred (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [rPred,ChannelCode.pred_subst,ProbeCode.carrier_subst,rPredBody_subst,subst,relational,ObservationCode.subst,RelationalCode.channel,RelationalCode.subst]
  try rfl
theorem rStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (ρ : Nat → Nat) :
    (B.rStep L KY KP v x).rename ρ = (B.rename ρ).rStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (x.rename ρ) := by
  simp only [rStep,LogicCode.imp_rename,RelationalCode.valid_rename,ev_rename,ObservationCode.tagged_rename,RelationalCode.le_rename,rPred_rename,rename,relational,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem rStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (σ : Nat → Expr S) :
    (B.rStep L KY KP v x).subst σ = (B.subst σ).rStep (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (x.subst σ) := by
  simp only [rStep,LogicCode.imp_subst,RelationalCode.valid_subst,ev_subst,ObservationCode.tagged_subst,RelationalCode.le_subst,rPred_subst,subst,relational,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem rBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.rBody L KY KP v).rename (Expr.liftRen ρ) = (B.rename ρ).rBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [rBody,rStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem rBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.rBody L KY KP v).subst (Expr.liftSub σ) = (B.subst σ).rBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [rBody,rStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem rAll_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.rAll L KY KP v).rename ρ = (B.rename ρ).rAll (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [rAll,QuantifierCode.all_rename,xType_rename,rBody_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem rAll_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.rAll L KY KP v).subst σ = (B.subst σ).rAll (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [rAll,QuantifierCode.all_subst,xType_subst,rBody_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem propertyR_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.propertyR L KY KP v).rename ρ = (B.rename ρ).propertyR (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [propertyR,LogicCode.imp_rename,RelationalCode.extensional_rename,rPred_rename,rAll_rename,rename,relational,ObservationCode.rename,RelationalCode.rename]
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
theorem copies_formed : O.copies.Formed L k j p k p k j :=
  ⟨H.relational.channel.logical,H.relational.probe.raw,H.inner,H.outer⟩
theorem carrier_sorted : SortedAt P Γ O.carrier j :=
  H.outer.sorted (H.inner.sorted (H.relational.probe.raw.sorted H.relational.probe.carrier_sorted))
theorem carrier_mode : WellModed γ O.carrier .data :=
  H.outer.mode (H.inner.mode (H.relational.probe.raw.mode H.relational.probe.carrier_mode))
theorem tagged_typed {x : Expr S} (t : Fin 3)
    (hx : HasType P Γ x (O.relational.channel.logicalType O.relational.probe.carrier)) (mx : WellModed γ x .data) :
    HasType P Γ (O.tagged L.code t x) O.carrier ∧ WellModed γ (O.tagged L.code t x) .data :=
  H.copies_formed.tagged_typed H.relational.probe.carrier_sorted H.relational.probe.carrier_mode t hx mx
end Formed
end ObservationCode

end PureTypeSystem.Labelled

namespace PureTypeSystem.Labelled.LogicSetup
universe u
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {γ : Nat → Mode}
  {C : Set (Set S)} (L : LogicSetup P Γ γ C) {A A' B B' : Expr S}

theorem imp_equivalent (hA : L.Formula A) (hA' : L.Formula A')
    (hB : L.Formula B) (hB' : L.Formula B')
    (eA : Equivalent P Γ γ A A') (eB : Equivalent P Γ γ B B') :
    Equivalent P Γ γ (L.imp A B) (L.imp A' B') := by
  apply L.equivalent_of_iff (L.imp_formula hA hB) (L.imp_formula hA' hB')
  exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (A) else if pl_i = 1 then (A') else if pl_i = 2 then (B) else if pl_i = 3 then (B') else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.atom 1)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.atom 0)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot), (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) (FiniteClassical.Formula.atom 3)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 3) (FiniteClassical.Formula.atom 2)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot)] (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.atom 2)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.atom 3))) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.atom 3)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.atom 2))) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl | rfl; exacts [((L).iff_of_equivalent (hA) (hA') eA), ((L).iff_of_equivalent (hB) (hB') eB)])

end PureTypeSystem.Labelled.LogicSetup

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
theorem y_sorted : SortedAt P Γ B.yType j := H.observation.carrier_sorted
theorem y_mode : WellModed γ B.yType .data := H.observation.carrier_mode
theorem x_sorted : SortedAt P Γ B.xType j := H.relational_formed.channel.logical_sorted H.relational_formed.probe.carrier_sorted
theorem x_mode : WellModed γ B.xType .data := H.relational_formed.channel.logical_mode H.relational_formed.probe.carrier_mode

theorem tagged_typed {x : Expr S} (t : Fin 3) (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data) :
    HasType P Γ (B.observation.tagged L.code t x) B.yType ∧ WellModed γ (B.observation.tagged L.code t x) .data :=
  H.observation.tagged_typed t hx mx

end Formed
end

variable (B : SpecializedCode S)

theorem property_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v : Expr S) (ρ : Nat → Nat) :
    (B.property L KY KP t v).rename ρ = (B.rename ρ).property (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t (v.rename ρ) := by
  fin_cases t <;> simp only [property,propertyG_rename,propertyC_rename,propertyE_rename,propertyR_rename]
theorem property_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (v : Expr S) (σ : Nat → Expr S) :
    (B.property L KY KP t v).subst σ = (B.subst σ).property (L.subst σ) (KY.subst σ) (KP.subst σ) t (v.subst σ) := by
  fin_cases t <;> simp only [property,propertyG_subst,propertyC_subst,propertyE_subst,propertyR_subst]
theorem propertyBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (ρ : Nat → Nat) :
    (B.propertyBody L KY KP t).rename (Expr.liftRen ρ) =
      (B.rename ρ).propertyBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) t := by
  simp only [propertyBody,property_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  rfl

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

end Formed
end SpecializedCode
end PureTypeSystem.Labelled

namespace PureTypeSystem.Labelled.LogicSetup
universe u
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {γ : Nat → Mode}
  {C : Set (Set S)} (L : LogicSetup P Γ γ C) {A B D : Expr S}
/-- The source's guarded comparison builder, with a genuine proof binder. -/
theorem guarded_equivalent_future (hA : L.Formula A) (hB : L.Formula B) (hD : L.Formula D)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ), Proves P Δ δ (A.rename e.names) →
      Equivalent P Δ δ (B.rename e.names) (D.rename e.names)) :
    Equivalent P Γ γ (L.imp A B) (L.imp A D) := by
  have hp : Proves P Γ γ (L.imp A (L.iff B D)) := by
    apply L.imp_intro_future hA (L.iff_formula hB hD)
    intro Δ δ e ha
    rw [L.iff_rename]
    exact (L.rename e).iff_of_equivalent (hB.rename e) (hD.rename e) (hh Δ δ e ha)
  apply L.equivalent_of_iff (L.imp_formula hA hB) (L.imp_formula hA hD)
  exact (L).propositional_consequence (fun pl_i : Nat => if pl_i = 0 then (A) else if pl_i = 1 then (B) else if pl_i = 2 then (D) else (L).bottom) (by have hb := (L).bottom_formula; intro i; (try dsimp only); split_ifs <;> solve_by_elim [(L).imp_formula,(L).neg_formula,(L).conj_formula,(L).disj_formula,(L).iff_formula,(L).cond_formula,(L).bottom_formula,(L).top_formula]) [(FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 1) (FiniteClassical.Formula.atom 2)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 2) (FiniteClassical.Formula.atom 1)) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot))] (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.atom 1)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.atom 2))) (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.atom 2)) (FiniteClassical.Formula.imp (FiniteClassical.Formula.atom 0) (FiniteClassical.Formula.atom 1))) FiniteClassical.Formula.bot)) FiniteClassical.Formula.bot) (by intro v; simp only [FiniteClassical.Formula.chain, List.foldr, FiniteClassical.Formula.eval, Bool.or_eq_true_eq_eq_true_or_eq_true, Bool.or_eq_false_eq_eq_false_and_eq_false, Bool.not_eq_true_eq_eq_false, Bool.not_eq_false_eq_eq_true, Bool.true_eq_false_eq_False, Bool.false_eq_true_eq_False, eq_self_iff_true, ← Bool.eq_false_eq_not_eq_true]; tauto) (by intro R hR; simp only [List.mem_cons, List.not_mem_nil, or_false] at hR; rcases hR with rfl; exacts [hp])
end PureTypeSystem.Labelled.LogicSetup

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
theorem y_typed_rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) {v : Expr S}
    (hv : HasType P Γ v B.yType) : HasType P Δ (v.rename e.names) (B.rename e.names).yType := by
  simpa only [yType_rename] using e.typing hv
omit H in
theorem x_typed_rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) {v : Expr S}
    (hv : HasType P Γ v B.xType) : HasType P Δ (v.rename e.names) (B.rename e.names).xType := by
  simpa only [xType_rename] using e.typing hv
end SpecializedCode.Formed

namespace SpecializedCode
variable (B : SpecializedCode S)
theorem relational_rename (ρ : Nat → Nat) : (B.relational.rename ρ) = (B.rename ρ).relational := rfl
theorem observation_rename (ρ : Nat → Nat) : (B.observation.rename ρ) = (B.rename ρ).observation := rfl
end SpecializedCode
end

universe u
variable {S : Type u}
namespace DoubleCode
variable (R : DoubleCode S)
theorem realizationBody_rename (U : DataWrapper S true) (L : LogicCode S) (T c : Expr S) (Q : Fin 7 → Expr S) (ρ : Nat → Nat) :
    (R.realizationBody U L T c Q).rename (Expr.liftRen ρ) =
      (R.rename ρ).realizationBody (U.rename ρ) (L.rename ρ) (T.rename ρ) (c.rename ρ) (fun t => (Q t).rename (Expr.liftRen ρ)) := by
  simp only [realizationBody,LogicCode.choices_rename,LogicCode.rename_comp,Expr.compose_rename,markBody_rename,decodeMap_rename]
  rfl
theorem realizationBody_subst (U : DataWrapper S true) (L : LogicCode S) (T c : Expr S) (Q : Fin 7 → Expr S) (σ : Nat → Expr S) :
    (R.realizationBody U L T c Q).subst (Expr.liftSub σ) =
      (R.subst σ).realizationBody (U.subst σ) (L.subst σ) (T.subst σ) (c.subst σ) (fun t => (Q t).subst (Expr.liftSub σ)) := by
  simp only [realizationBody,LogicCode.choices_subst,LogicCode.subst_rename,LogicCode.rename_subst,Expr.compose_subst,markBody_subst,decodeMap_subst]
  rfl
theorem realization_rename (U : DataWrapper S true) (L : LogicCode S) (T c : Expr S) (Q : Fin 7 → Expr S) (ρ : Nat → Nat) :
    (R.realization U L T c Q).rename ρ =
      (R.rename ρ).realization (U.rename ρ) (L.rename ρ) (T.rename ρ) (c.rename ρ) (fun t => (Q t).rename (Expr.liftRen ρ)) := by
  simp only [realization,DataWrapper.build_rename,bpType_rename,realizationBody_rename,rename_second,
    DataWrapper.argRen,ite_true, if_true]
theorem realization_subst (U : DataWrapper S true) (L : LogicCode S) (T c : Expr S) (Q : Fin 7 → Expr S) (σ : Nat → Expr S) :
    (R.realization U L T c Q).subst σ =
      (R.subst σ).realization (U.subst σ) (L.subst σ) (T.subst σ) (c.subst σ) (fun t => (Q t).subst (Expr.liftSub σ)) := by
  simp only [realization,DataWrapper.build_subst,bpType_subst,realizationBody_subst,subst_second,
    DataWrapper.argSub,ite_true, if_true]
end DoubleCode
namespace SpecializedCode
variable (B : SpecializedCode S)
theorem propertyBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (t : Fin 7) (σ : Nat → Expr S) :
    (B.propertyBody L KY KP t).subst (Expr.liftSub σ) =
      (B.subst σ).propertyBody (L.subst σ) (KY.subst σ) (KP.subst σ) t := by
  simp only [propertyBody,property_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,
    QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,
    Expr.subst,Expr.liftSub]
  rfl
theorem parameter_rename (L : LogicCode S) (KY KP : QuantifierCode S) (ρ : Nat → Nat) :
    (B.parameter L KY KP).rename ρ = (B.rename ρ).parameter (L.rename ρ) (KY.rename ρ) (KP.rename ρ) := by
  simp only [parameter,DoubleCode.realization_rename,ProbeCode.rawType_rename,RelationalCode.rawTop_rename,propertyBody_rename,
    SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.rename,ProbeCode.rename,ProbeCode.doubled,DoubleCode.rename]
theorem parameter_subst (L : LogicCode S) (KY KP : QuantifierCode S) (σ : Nat → Expr S) :
    (B.parameter L KY KP).subst σ = (B.subst σ).parameter (L.subst σ) (KY.subst σ) (KP.subst σ) := by
  simp only [parameter,DoubleCode.realization_subst,ProbeCode.rawType_subst,RelationalCode.rawTop_subst,propertyBody_subst,
    SpecializedCode.subst,relational,ObservationCode.subst,RelationalCode.subst,ProbeCode.subst,ProbeCode.doubled,DoubleCode.subst]
end SpecializedCode
end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Equivalence
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled

section
universe u
variable {S : Type u} {P : Specification S}

namespace SpecializedCode
variable (B : SpecializedCode S)
theorem goodBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (ρ : Nat → Nat) :
    (B.goodBody L KY KP).rename (Expr.liftRen ρ) = (B.rename ρ).goodBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) := by
  simp only [goodBody,RelationalCode.goodBody_rename,parameter_rename,
    SpecializedCode.rename,relational,ObservationCode.rename]
theorem relation_rename (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (ρ : Nat → Nat) :
    (B.relation L KY KP y z).rename ρ = (B.rename ρ).relation (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (y.rename ρ) (z.rename ρ) := by
  simp only [relation,ChannelCode.relation_rename,baseType_rename,goodBody_rename,
    SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.rename,RelationalCode.channel,ChannelCode.rename,ProbeCode.rename]

end SpecializedCode
end

universe u
variable {S : Type u} {P : Specification S}

namespace SpecializedCode.Formed

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem relation_formula {y z : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data) :
    L.Formula (B.relation L.code KY.code KP.code y z) :=
  H.relational_formed.channel.relation_formula KP H.base_sorted H.base_mode (H.goodBody_family KY KP)
    (H.shape ▸ hy) my (H.shape ▸ hz) mz

end

end SpecializedCode.Formed

end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Response
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate _root_.OAI.PureTypeSystem.instCountableExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled
universe u
variable {S : Type u} {P : Specification S}

namespace SpecializedCode
variable (B : SpecializedCode S)

theorem diamond_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (ρ : Nat → Nat) :
    (B.diamond L KY KP v y).rename ρ = (B.rename ρ).diamond (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (y.rename ρ) := by
  simp only [diamond,RelationalCode.diamond_rename,parameter_rename,relational_rename]
  rfl
theorem lift_rename (L : LogicCode S) (KY KP : QuantifierCode S) (y : Expr S) (ρ : Nat → Nat) :
    (B.lift L KY KP y).rename ρ = (B.rename ρ).lift (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (y.rename ρ) := by
  simp only [lift,RelationalCode.lift_rename,parameter_rename,relational_rename]
  rfl
end SpecializedCode
namespace SpecializedCode.Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

omit H in
theorem carrier_typed_rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) {v : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) :
    HasType P Δ (v.rename e.names) (B.rename e.names).relational.probe.carrier := by
  simpa only [ProbeCode.carrier_rename,SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.rename,ProbeCode.rename] using e.typing hv

omit H in
theorem xPred_typed_rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) {v : Expr S}
    (hv : HasType P Γ v B.xPredType) : HasType P Δ (v.rename e.names) (B.rename e.names).xPredType := by
  simpa only [xPredType_rename] using e.typing hv

theorem diamond_formula {v y : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    L.Formula (B.diamond L.code KY.code KP.code v y) :=
  H.relational_formed.diamond_formula H.type_sorted H.type_mode (H.parameter_typed KY KP).1 (H.parameter_typed KY KP).2 hv mv (H.shape ▸ hy) my

theorem lift_typed {y : Expr S}
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data) :
    HasType P Γ (B.lift L.code KY.code KP.code y) B.xType ∧ WellModed γ (B.lift L.code KY.code KP.code y) .data :=
  H.relational_formed.lift_typed KY KP H.type_sorted H.type_mode (H.parameter_typed KY KP).1 (H.parameter_typed KY KP).2 (H.shape ▸ hy) my

end SpecializedCode.Formed

namespace SpecializedCode
variable (B : SpecializedCode S)
theorem goodBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (σ : Nat → Expr S) :
    (B.goodBody L KY KP).subst (Expr.liftSub σ) = (B.subst σ).goodBody (L.subst σ) (KY.subst σ) (KP.subst σ) := by
  simp only [goodBody,RelationalCode.goodBody_subst,parameter_subst,
    SpecializedCode.subst,relational,ObservationCode.subst]
theorem relation_subst (L : LogicCode S) (KY KP : QuantifierCode S) (y z : Expr S) (σ : Nat → Expr S) :
    (B.relation L KY KP y z).subst σ = (B.subst σ).relation (L.subst σ) (KY.subst σ) (KP.subst σ) (y.subst σ) (z.subst σ) := by
  simp only [relation,ChannelCode.relation_subst,baseType_subst,goodBody_subst,
    SpecializedCode.subst,relational,ObservationCode.subst,RelationalCode.subst,RelationalCode.channel,ChannelCode.subst,ProbeCode.subst]

theorem relational_subst (σ : Nat → Expr S) : B.relational.subst σ = (B.subst σ).relational := rfl
theorem diamond_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (σ : Nat → Expr S) :
    (B.diamond L KY KP v y).subst σ = (B.subst σ).diamond (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (y.subst σ) := by
  simp only [diamond,RelationalCode.diamond_subst,parameter_subst,relational_subst]
  rfl
theorem respStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v y z : Expr S) (ρ : Nat → Nat) :
    (B.respStep L KY KP v y z).rename ρ = (B.rename ρ).respStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (y.rename ρ) (z.rename ρ) := by
  simp only [respStep,LogicCode.imp_rename,LogicCode.iff_rename,relation_rename,diamond_rename]
theorem respStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v y z : Expr S) (σ : Nat → Expr S) :
    (B.respStep L KY KP v y z).subst σ = (B.subst σ).respStep (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (y.subst σ) (z.subst σ) := by
  simp only [respStep,LogicCode.imp_subst,LogicCode.iff_subst,relation_subst,diamond_subst]
theorem respAtBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (ρ : Nat → Nat) :
    (B.respAtBody L KY KP v y).rename (Expr.liftRen ρ) = (B.rename ρ).respAtBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (y.rename ρ) := by
  simp only [respAtBody,respStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem respAtBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (σ : Nat → Expr S) :
    (B.respAtBody L KY KP v y).subst (Expr.liftSub σ) = (B.subst σ).respAtBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (y.subst σ) := by
  simp only [respAtBody,respStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem respAtBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (v y z : Expr S) :
    (B.respAtBody L KY KP v y).instantiate z = B.respStep L KY KP v y z := by
  simp only [respAtBody,Expr.instantiate,respStep_subst,instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
theorem respAt_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (ρ : Nat → Nat) :
    (B.respAt L KY KP v y).rename ρ = (B.rename ρ).respAt (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (y.rename ρ) := by
  simp only [respAt,QuantifierCode.all_rename,yType_rename,respAtBody_rename]
theorem respAt_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) (σ : Nat → Expr S) :
    (B.respAt L KY KP v y).subst σ = (B.subst σ).respAt (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (y.subst σ) := by
  simp only [respAt,QuantifierCode.all_subst,yType_subst,respAtBody_subst]
theorem respBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.respBody L KY KP v).rename (Expr.liftRen ρ) = (B.rename ρ).respBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [respBody,respAt_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem respBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (v y : Expr S) :
    (B.respBody L KY KP v).instantiate y = B.respAt L KY KP v y := by
  simp only [respBody,Expr.instantiate,respAt_subst,instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
end SpecializedCode

namespace SpecializedCode.Formed

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem respStep_formula {v y z : Expr S} 
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    : L.Formula (B.respStep L.code KY.code KP.code v y z) := 
  L.imp_formula (H.relation_formula KY KP hy my hz mz) (L.iff_formula (H.diamond_formula KY KP hv mv hy my) (H.diamond_formula KY KP hv mv hz mz))

theorem respAtBody_family {v y : Expr S} 
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    : L.Family B.yType (B.respAtBody L.code KY.code KP.code v y) := by
  intro Δ δ e z hz mz
  rw [respAtBody_rename,respAtBody_instantiate]
  have hv' : HasType P Δ (v.rename e.names) (B.rename e.names).relational.probe.carrier := by
    exact carrier_typed_rename e hv
  have hy' : HasType P Δ (y.rename e.names) (B.rename e.names).yType := by
    simpa only [yType_rename] using e.typing hy
  have hz' : HasType P Δ z (B.rename e.names).yType := by
    simpa only [yType_rename] using hz
  exact (H.rename e).respStep_formula (KY.rename e) (KP.rename e) hv' (e.moded mv) hy' (e.moded my) hz' mz

theorem respAt_formula {v y : Expr S} 
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    : L.Formula (B.respAt L.code KY.code KP.code v y) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  exact L.all_formula_family KY H.y_sorted H.y_mode (H.y_sorted s hs) (H.respAtBody_family KY KP hv mv hy my)

theorem respBody_family {v : Expr S} 
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    : L.Family B.yType (B.respBody L.code KY.code KP.code v) := by
  intro Δ δ e y hy my
  rw [respBody_rename,respBody_instantiate]
  have hv' : HasType P Δ (v.rename e.names) (B.rename e.names).relational.probe.carrier := by
    exact carrier_typed_rename e hv
  have hy' : HasType P Δ y (B.rename e.names).yType := by
    simpa only [yType_rename] using hy
  exact (H.rename e).respAt_formula (KY.rename e) (KP.rename e) hv' (e.moded mv) hy' my

end

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem respAt_intro {v y : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) z,
      HasType P Δ z (B.rename e.names).yType → WellModed δ z .data →
      Proves P Δ δ ((B.rename e.names).respStep (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names)
        (v.rename e.names) (y.rename e.names) z)) : Proves P Γ γ (B.respAt L.code KY.code KP.code v y) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  apply L.all_intro_future KY H.y_sorted H.y_mode (H.y_sorted s hs) (H.respAtBody_family KY KP hv mv hy my)
  intro Δ δ e z hz mz
  rw [respAtBody_rename,respAtBody_instantiate]
  exact hh Δ δ e z (by simpa only [yType_rename] using hz) mz

theorem respAt_elim {v y z : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (hp : Proves P Γ γ (B.respAt L.code KY.code KP.code v y)) :
    Proves P Γ γ (B.respStep L.code KY.code KP.code v y z) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  have hh := L.all_elim_family KY H.y_sorted H.y_mode (H.y_sorted s hs) (H.respAtBody_family KY KP hv mv hy my) hz mz hp
  simpa only [respAtBody_instantiate] using hh

theorem response_intro {v : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hh : ∀ Δ δ (e : Embedding P Γ γ Δ δ) y,
      HasType P Δ y (B.rename e.names).yType → WellModed δ y .data →
      Proves P Δ δ ((B.rename e.names).respAt (L.code.rename e.names) (KY.code.rename e.names) (KP.code.rename e.names)
        (v.rename e.names) y)) : Proves P Γ γ (B.response L.code KY.code KP.code v) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  apply L.all_intro_future KY H.y_sorted H.y_mode (H.y_sorted s hs) (H.respBody_family KY KP hv mv)
  intro Δ δ e y hy my
  rw [respBody_rename,respBody_instantiate]
  exact hh Δ δ e y (by simpa only [yType_rename] using hy) my

theorem response_elim_one {v y : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hp : Proves P Γ γ (B.response L.code KY.code KP.code v)) :
    Proves P Γ γ (B.respAt L.code KY.code KP.code v y) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  have hh := L.all_elim_family KY H.y_sorted H.y_mode (H.y_sorted s hs) (H.respBody_family KY KP hv mv) hy my hp
  simpa only [respBody_instantiate] using hh

theorem response_elim {v y z : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hz : HasType P Γ z B.yType) (mz : WellModed γ z .data)
    (hp : Proves P Γ γ (B.response L.code KY.code KP.code v))
    (he : Proves P Γ γ (B.relation L.code KY.code KP.code y z)) :
    Equivalent P Γ γ (B.diamond L.code KY.code KP.code v y) (B.diamond L.code KY.code KP.code v z) := by
  have hh := H.respAt_elim KY KP hv mv hy my hz mz (H.response_elim_one KY KP hv mv hy my hp)
  have hc := L.imp_elim (H.relation_formula KY KP hy my hz mz)
    (L.iff_formula (H.diamond_formula KY KP hv mv hy my) (H.diamond_formula KY KP hv mv hz mz)) hh he
  exact L.equivalent_of_iff (H.diamond_formula KY KP hv mv hy my) (H.diamond_formula KY KP hv mv hz mz) hc

end SpecializedCode.Formed

namespace SpecializedCode
variable (B : SpecializedCode S)
theorem responsePredStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (ρ : Nat → Nat) :
    (B.responsePredStep L KY KP v x).rename ρ = (B.rename ρ).responsePredStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (x.rename ρ) := by
  simp only [responsePredStep,diamond_rename,ObservationCode.tagged_rename,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem responsePredStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (σ : Nat → Expr S) :
    (B.responsePredStep L KY KP v x).subst σ = (B.subst σ).responsePredStep (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (x.subst σ) := by
  simp only [responsePredStep,diamond_subst,ObservationCode.tagged_subst,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem responsePredBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.responsePredBody L KY KP v).rename (Expr.liftRen ρ) = (B.rename ρ).responsePredBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [responsePredBody,responsePredStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem responsePredBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.responsePredBody L KY KP v).subst (Expr.liftSub σ) = (B.subst σ).responsePredBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [responsePredBody,responsePredStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem responsePredBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) :
    (B.responsePredBody L KY KP v).instantiate x = B.responsePredStep L KY KP v x := by
  simp only [responsePredBody,Expr.instantiate,responsePredStep_subst,instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
theorem responsePred_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.responsePred L KY KP v).rename ρ = (B.rename ρ).responsePred (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [responsePred,ChannelCode.pred_rename,ProbeCode.carrier_rename,responsePredBody_rename,rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename]
  try rfl
theorem responsePred_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.responsePred L KY KP v).subst σ = (B.subst σ).responsePred (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [responsePred,ChannelCode.pred_subst,ProbeCode.carrier_subst,responsePredBody_subst,subst,relational,ObservationCode.subst,RelationalCode.channel,RelationalCode.subst]
  try rfl
end SpecializedCode

namespace SpecializedCode.Formed

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem responsePredStep_formula {v x : Expr S} 
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    : L.Formula (B.responsePredStep L.code KY.code KP.code v x) := by
  have ht := H.tagged_typed 0 hx mx
  exact H.diamond_formula KY KP hv mv ht.1 ht.2

theorem responsePredBody_family {v : Expr S} 
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    : L.Family B.xType (B.responsePredBody L.code KY.code KP.code v) := by
  intro Δ δ e x hx mx
  rw [responsePredBody_rename,responsePredBody_instantiate]
  have hv' : HasType P Δ (v.rename e.names) (B.rename e.names).relational.probe.carrier := by
    exact carrier_typed_rename e hv
  have hx' : HasType P Δ x (B.rename e.names).xType := by
    simpa only [xType_rename] using hx
  exact (H.rename e).responsePredStep_formula (KY.rename e) (KP.rename e) hv' (e.moded mv) hx' mx

theorem responsePred_typed {v : Expr S} (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data) :
    HasType P Γ (B.responsePred L.code KY.code KP.code v) B.xPredType ∧ WellModed γ (B.responsePred L.code KY.code KP.code v) .data := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  exact H.relational_formed.channel.pred_typed H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode
    (H.responsePredBody_family KY KP hv mv) (H.relational_formed.probe.raw.sorted H.relational_formed.probe.carrier_sorted s hs)

theorem responsePred_evaluation {v x : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data) :
    Equivalent P Γ γ (B.relational.channel.eval B.relational.probe.carrier (B.responsePred L.code KY.code KP.code v) x)
      (B.responsePredStep L.code KY.code KP.code v (B.relational.channel.round B.relational.probe.carrier x)) := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  have he := H.relational_formed.channel.pred_evaluation H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode
    (H.responsePredBody_family KY KP hv mv) (H.relational_formed.probe.raw.sorted H.relational_formed.probe.carrier_sorted s hs) hx mx
  simpa only [responsePredBody_instantiate,responsePred] using he

end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem probe_respAt {i y : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hy : HasType P Γ y B.yType) (my : WellModed γ y .data)
    (hex : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i)) :
    Proves P Γ γ (B.respAt L.code KY.code KP.code (B.relational.probeFor L.code KY.code KP.code i) y) := by
  have hp := H.relational_formed.probeFor_typed KY KP hi mi
  apply H.respAt_intro KY KP hp.1 hp.2 hy my
  intro Δ δ e z hz mz
  simp only [RelationalCode.probeFor_rename]
  have hex' := hex.rename e
  simp only [RelationalCode.extensional_rename] at hex'
  exact (H.rename e).probe_respStep (KY.rename e) (KP.rename e) (xPred_typed_rename e hi) (e.moded mi)
    (y_typed_rename (B := B) e hy) (e.moded my) hz mz hex'

theorem probe_response {i : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hex : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i)) :
    Proves P Γ γ (B.response L.code KY.code KP.code (B.relational.probeFor L.code KY.code KP.code i)) := by
  have hp := H.relational_formed.probeFor_typed KY KP hi mi
  apply H.response_intro KY KP hp.1 hp.2
  intro Δ δ e y hy my
  simp only [RelationalCode.probeFor_rename]
  have hex' := hex.rename e
  simp only [RelationalCode.extensional_rename] at hex'
  exact (H.rename e).probe_respAt (KY.rename e) (KP.rename e) (xPred_typed_rename e hi) (e.moded mi) hy my hex'
end

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem responsePred_exact {v x : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hr : Proves P Γ γ (B.response L.code KY.code KP.code v)) :
    Equivalent P Γ γ (B.relational.channel.eval B.relational.probe.carrier (B.responsePred L.code KY.code KP.code v) x)
      (B.diamond L.code KY.code KP.code v (B.observation.tagged L.code 0 x)) := by
  have rx := H.relational_formed.channel.round_typed H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hx mx
  have tx := H.tagged_typed 0 hx mx
  have tr := H.tagged_typed 0 rx.1 rx.2
  have iv := H.responsePred_typed KY KP hv mv
  have ee := H.response_elim KY KP hv mv tx.1 tx.2 tr.1 tr.2 hr
    ((H.relation_tagged_same KY KP 0 hx mx rx.1 rx.2).2.prove (H.relational_formed.xCompare_round KY KP hx mx))
  exact (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hx mx).equivalent_trans
    (H.diamond_formula KY KP hv mv tr.1 tr.2) (H.diamond_formula KY KP hv mv tx.1 tx.2)
    (H.responsePred_evaluation KY KP hv mv hx mx) ee.symm

end SpecializedCode.Formed
end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Diagonal
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate _root_.OAI.PureTypeSystem.instCountableExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled
universe u
variable {S : Type u} {P : Specification S}
namespace SpecializedCode
variable (B : SpecializedCode S)
theorem lift_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (σ : Nat → Expr S) :
    (B.lift L KY KP x).subst σ = (B.subst σ).lift (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) := by
  simp only [lift,RelationalCode.lift_subst,parameter_subst,relational_subst]
  rfl

theorem delta_rename (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (ρ : Nat → Nat) :
    (B.delta L KY KP x).rename ρ = (B.rename ρ).delta (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (x.rename ρ) := by
  simp only [delta,lift_rename,ObservationCode.tagged_rename,observation_rename]
theorem delta_subst (L : LogicCode S) (KY KP : QuantifierCode S) (x : Expr S) (σ : Nat → Expr S) :
    (B.delta L KY KP x).subst σ = (B.subst σ).delta (L.subst σ) (KY.subst σ) (KP.subst σ) (x.subst σ) := by
  simp only [delta,lift_subst,ObservationCode.tagged_subst,SpecializedCode.subst,ObservationCode.subst]
theorem shiftPredStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (ρ : Nat → Nat) :
    (B.shiftPredStep L KY KP v x).rename ρ = (B.rename ρ).shiftPredStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (x.rename ρ) := by
  simp only [shiftPredStep,ChannelCode.eval_rename,ProbeCode.carrier_rename,delta_rename,relational,RelationalCode.channel,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem shiftPredStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (σ : Nat → Expr S) :
    (B.shiftPredStep L KY KP v x).subst σ = (B.subst σ).shiftPredStep (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (x.subst σ) := by
  simp only [shiftPredStep,ChannelCode.eval_subst,ProbeCode.carrier_subst,delta_subst,relational,RelationalCode.channel,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem shiftPredBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.shiftPredBody L KY KP v).rename (Expr.liftRen ρ) = (B.rename ρ).shiftPredBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [shiftPredBody,shiftPredStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem shiftPredBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) :
    (B.shiftPredBody L KY KP v).instantiate x = B.shiftPredStep L KY KP v x := by
  simp only [shiftPredBody,Expr.instantiate,shiftPredStep_subst,instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
theorem shiftPred_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.shiftPred L KY KP v).rename ρ = (B.rename ρ).shiftPred (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [shiftPred,ChannelCode.pred_rename,ProbeCode.carrier_rename,shiftPredBody_rename,rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename]
  try rfl
end SpecializedCode

namespace SpecializedCode.Formed

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem delta_typed {x : Expr S} (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data) :
    HasType P Γ (B.delta L.code KY.code KP.code x) B.xType ∧ WellModed γ (B.delta L.code KY.code KP.code x) .data := by
  have ht := H.tagged_typed 0 hx mx
  exact H.lift_typed KY KP ht.1 ht.2

theorem shiftPredStep_formula {v x : Expr S} 
    (hv : HasType P Γ v B.xPredType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    : L.Formula (B.shiftPredStep L.code KY.code KP.code v x) := by
  have ht := H.delta_typed KY KP hx mx
  exact H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hv mv ht.1 ht.2

theorem shiftPredBody_family {v : Expr S} 
    (hv : HasType P Γ v B.xPredType) (mv : WellModed γ v .data)
    : L.Family B.xType (B.shiftPredBody L.code KY.code KP.code v) := by
  intro Δ δ e x hx mx
  rw [shiftPredBody_rename,shiftPredBody_instantiate]
  have hv' : HasType P Δ (v.rename e.names) (B.rename e.names).xPredType := by
    exact xPred_typed_rename e hv
  have hx' : HasType P Δ x (B.rename e.names).xType := by
    simpa only [xType_rename] using hx
  exact (H.rename e).shiftPredStep_formula (KY.rename e) (KP.rename e) hv' (e.moded mv) hx' mx

theorem shiftPred_typed {v : Expr S} (hv : HasType P Γ v B.xPredType) (mv : WellModed γ v .data) :
    HasType P Γ (B.shiftPred L.code KY.code KP.code v) B.xPredType ∧ WellModed γ (B.shiftPred L.code KY.code KP.code v) .data := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  exact H.relational_formed.channel.pred_typed H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode
    (H.shiftPredBody_family KY KP hv mv) (H.relational_formed.probe.raw.sorted H.relational_formed.probe.carrier_sorted s hs)

theorem shiftPred_evaluation {v x : Expr S}
    (hv : HasType P Γ v B.xPredType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data) :
    Equivalent P Γ γ (B.relational.channel.eval B.relational.probe.carrier (B.shiftPred L.code KY.code KP.code v) x)
      (B.shiftPredStep L.code KY.code KP.code v (B.relational.channel.round B.relational.probe.carrier x)) := by
  obtain ⟨s,hs⟩ := H.relational_formed.probe.funTriple.domain.1
  have he := H.relational_formed.channel.pred_evaluation H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode
    (H.shiftPredBody_family KY KP hv mv) (H.relational_formed.probe.raw.sorted H.relational_formed.probe.carrier_sorted s hs) hx mx
  simpa only [shiftPredBody_instantiate,shiftPred] using he

end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem shiftPred_exact {v x : Expr S}
    (hv : HasType P Γ v B.xPredType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hr : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code v)) :
    Equivalent P Γ γ (B.relational.channel.eval B.relational.probe.carrier (B.shiftPred L.code KY.code KP.code v) x)
      (B.relational.channel.eval B.relational.probe.carrier v (B.delta L.code KY.code KP.code x)) := by
  have rx := H.relational_formed.channel.round_typed H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hx mx
  have dx := H.delta_typed KY KP hx mx
  have dr := H.delta_typed KY KP rx.1 rx.2
  have iv := H.shiftPred_typed KY KP hv mv
  have ee := H.relational_formed.extensional_elim KY KP hv mv dx.1 dx.2 dr.1 dr.2 hr
    (H.delta_congr KY KP hx mx rx.1 rx.2 (H.relational_formed.xCompare_round KY KP hx mx))
  exact (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hx mx).equivalent_trans
    (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hv mv dr.1 dr.2)
    (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hv mv dx.1 dx.2)
    (H.shiftPred_evaluation KY KP hv mv hx mx) ee.symm

theorem shiftPred_respect {v x y : Expr S}
    (hv : HasType P Γ v B.xPredType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hy : HasType P Γ y B.xType) (my : WellModed γ y .data)
    (hr : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code v))
    (he : Proves P Γ γ (B.relational.xCompare L.code KY.code KP.code x y)) :
    Equivalent P Γ γ (B.relational.channel.eval B.relational.probe.carrier (B.shiftPred L.code KY.code KP.code v) x)
      (B.relational.channel.eval B.relational.probe.carrier (B.shiftPred L.code KY.code KP.code v) y) := by
  have dx := H.delta_typed KY KP hx mx
  have dy := H.delta_typed KY KP hy my
  have iv := H.shiftPred_typed KY KP hv mv
  have f1 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hx mx
  have f4 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hy my
  have f2 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hv mv dx.1 dx.2
  have f3 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hv mv dy.1 dy.2
  have e1 := H.shiftPred_exact KY KP hv mv hx mx hr
  have e3 := H.shiftPred_exact KY KP hv mv hy my hr
  have e2 := H.relational_formed.extensional_elim KY KP hv mv dx.1 dx.2 dy.1 dy.2 hr (H.delta_congr KY KP hx mx hy my he)
  exact f1.equivalent_trans f3 f4 (f1.equivalent_trans f2 f3 e1 e2) e3.symm

theorem shiftPred_extStep {v x y : Expr S}
    (hv : HasType P Γ v B.xPredType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hy : HasType P Γ y B.xType) (my : WellModed γ y .data)
    (hr : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code v)) :
    Proves P Γ γ (B.relational.extStep L.code KY.code KP.code (B.shiftPred L.code KY.code KP.code v) x y) := by
  have iv := H.shiftPred_typed KY KP hv mv
  apply L.imp_intro_future (H.relational_formed.xCompare_formula KY KP hx mx hy my)
    (L.iff_formula (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hx mx)
      (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode iv.1 iv.2 hy my))
  intro Δ δ e he
  simp only [RelationalCode.xCompare_rename] at he
  simp only [LogicSetup.iff_rename,ChannelCode.eval_rename,ProbeCode.carrier_rename,shiftPred_rename]
  have hr' := hr.rename e
  simp only [RelationalCode.extensional_rename] at hr'
  have hv' := xPred_typed_rename e hv
  have hx' := x_typed_rename (B := B) e hx
  have hy' := x_typed_rename (B := B) e hy
  have iv' := (H.rename e).shiftPred_typed (KY.rename e) (KP.rename e) hv' (e.moded mv)
  have ee := (H.rename e).shiftPred_respect (KY.rename e) (KP.rename e) hv' (e.moded mv) hx' (e.moded mx) hy' (e.moded my) hr' he
  exact (L.rename e).iff_of_equivalent
    ((H.rename e).relational_formed.channel.eval_formula (H.rename e).relational_formed.probe.carrier_sorted (H.rename e).relational_formed.probe.carrier_mode iv'.1 iv'.2 hx' (e.moded mx))
    ((H.rename e).relational_formed.channel.eval_formula (H.rename e).relational_formed.probe.carrier_sorted (H.rename e).relational_formed.probe.carrier_mode iv'.1 iv'.2 hy' (e.moded my)) ee

theorem shiftPred_extAt {v x : Expr S}
    (hv : HasType P Γ v B.xPredType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (hr : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code v)) :
    Proves P Γ γ (B.relational.extAt L.code KY.code KP.code (B.shiftPred L.code KY.code KP.code v) x) := by
  have iv := H.shiftPred_typed KY KP hv mv
  apply H.relational_formed.extAt_intro KY KP iv.1 iv.2 hx mx
  intro Δ δ e y hy my
  simp only [shiftPred_rename]
  have hr' := hr.rename e
  simp only [RelationalCode.extensional_rename] at hr'
  exact (H.rename e).shiftPred_extStep (KY.rename e) (KP.rename e) (xPred_typed_rename e hv) (e.moded mv)
    (x_typed_rename (B := B) e hx) (e.moded mx) hy my hr'

theorem shiftPred_extensional {v : Expr S}
    (hv : HasType P Γ v B.xPredType) (mv : WellModed γ v .data)
    (hr : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code v)) :
    Proves P Γ γ (B.relational.extensional L.code KY.code KP.code (B.shiftPred L.code KY.code KP.code v)) := by
  have iv := H.shiftPred_typed KY KP hv mv
  apply H.relational_formed.extensional_intro KY KP iv.1 iv.2
  intro Δ δ e x hx mx
  simp only [shiftPred_rename]
  have hr' := hr.rename e
  simp only [RelationalCode.extensional_rename] at hr'
  exact (H.rename e).shiftPred_extAt (KY.rename e) (KP.rename e) (xPred_typed_rename e hv) (e.moded mv) hx mx hr'
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H
theorem shift_compare_at {i x : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (he : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i)) :
    Equivalent P Γ γ
      (B.relational.channel.eval B.relational.probe.carrier (B.responsePred L.code KY.code KP.code (B.relational.probeFor L.code KY.code KP.code i)) x)
      (B.relational.channel.eval B.relational.probe.carrier (B.shiftPred L.code KY.code KP.code i) x) := by
  have zi := H.relational_formed.probeFor_typed KY KP hi mi
  have ri := H.responsePred_typed KY KP zi.1 zi.2
  have si := H.shiftPred_typed KY KP hi mi
  have tx := H.tagged_typed 0 hx mx
  have dx := H.delta_typed KY KP hx mx
  have f1 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode ri.1 ri.2 hx mx
  have f4 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode si.1 si.2 hx mx
  have f2 := H.diamond_formula KY KP zi.1 zi.2 tx.1 tx.2
  have f3 := H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hi mi dx.1 dx.2
  exact f1.equivalent_trans f3 f4
    (f1.equivalent_trans f2 f3 (H.responsePred_exact KY KP zi.1 zi.2 hx mx (H.probe_response KY KP hi mi he))
      (H.probe_exact KY KP hi mi tx.1 tx.2 he)) (H.shiftPred_exact KY KP hi mi hx mx he).symm

theorem shift_compare {i : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (he : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i)) :
    Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.relational.probe.carrier
      (B.responsePred L.code KY.code KP.code (B.relational.probeFor L.code KY.code KP.code i))
      (B.shiftPred L.code KY.code KP.code i)) := by
  have zi := H.relational_formed.probeFor_typed KY KP hi mi
  have ri := H.responsePred_typed KY KP zi.1 zi.2
  have si := H.shiftPred_typed KY KP hi mi
  apply H.relational_formed.channel.predCompare_intro H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode KY ri.1 ri.2 si.1 si.2
  intro Δ δ e x hx mx
  simp only [responsePred_rename,RelationalCode.probeFor_rename,shiftPred_rename]
  have he' := he.rename e
  simp only [RelationalCode.extensional_rename] at he'
  simpa only [LogicSetup.code_rename,QuantifierRoute.code,QuantifierRoute.rename,QuantifierCode.rename,ProbeCode.carrier_rename,SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using
    (H.rename e).shift_compare_at (KY.rename e) (KP.rename e) (xPred_typed_rename e hi) (e.moded mi)
      (by simpa only [ProbeCode.carrier_rename,xType,SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using hx) mx he'

end

end SpecializedCode.Formed

namespace SpecializedCode
variable (B : SpecializedCode S)
theorem indStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (ρ : Nat → Nat) :
    (B.indStep L KY KP v x).rename ρ = (B.rename ρ).indStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) (x.rename ρ) := by
  simp only [indStep,LogicCode.imp_rename,RelationalCode.valid_rename,RelationalCode.le_rename,ChannelCode.eval_rename,ProbeCode.carrier_rename,relational,RelationalCode.channel,rename,ObservationCode.rename,RelationalCode.rename]
  try rfl
theorem indStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) (σ : Nat → Expr S) :
    (B.indStep L KY KP v x).subst σ = (B.subst σ).indStep (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) (x.subst σ) := by
  simp only [indStep,LogicCode.imp_subst,RelationalCode.valid_subst,RelationalCode.le_subst,ChannelCode.eval_subst,ProbeCode.carrier_subst,relational,RelationalCode.channel,subst,ObservationCode.subst,RelationalCode.subst]
  try rfl
theorem indBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.indBody L KY KP v).rename (Expr.liftRen ρ) = (B.rename ρ).indBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [indBody,indStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem indBody_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.indBody L KY KP v).subst (Expr.liftSub σ) = (B.subst σ).indBody (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [indBody,indStep_subst,subst_rename,rename_subst,LogicCode.subst_rename,LogicCode.rename_subst,QuantifierCode.subst,QuantifierCode.rename,ProofWrapper.subst_rename,ProofWrapper.rename_subst,Expr.subst_rename,Expr.rename_subst,Expr.subst,Expr.liftSub]
  try rfl
theorem indBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (v x : Expr S) :
    (B.indBody L KY KP v).instantiate x = B.indStep L KY KP v x := by
  simp only [indBody,Expr.instantiate,indStep_subst,instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst_lift_single,Expr.subst,Expr.single]
theorem induction_rename (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (ρ : Nat → Nat) :
    (B.induction L KY KP i).rename ρ = (B.rename ρ).induction (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (i.rename ρ) := by
  simp only [induction,QuantifierCode.all_rename,xType_rename,indBody_rename]
theorem induction_subst (L : LogicCode S) (KY KP : QuantifierCode S) (i : Expr S) (σ : Nat → Expr S) :
    (B.induction L KY KP i).subst σ = (B.subst σ).induction (L.subst σ) (KY.subst σ) (KP.subst σ) (i.subst σ) := by
  simp only [induction,QuantifierCode.all_subst,xType_subst,indBody_subst]

theorem wfStep_rename (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (ρ : Nat → Nat) :
    (B.wfStep L KY KP v).rename ρ = (B.rename ρ).wfStep (L.rename ρ) (KY.rename ρ) (KP.rename ρ) (v.rename ρ) := by
  simp only [wfStep,induction_rename,responsePred_rename]
theorem wfBody_rename (L : LogicCode S) (KY KP : QuantifierCode S) (ρ : Nat → Nat) :
    (B.wfBody L KY KP).rename (Expr.liftRen ρ) = (B.rename ρ).wfBody (L.rename ρ) (KY.rename ρ) (KP.rename ρ) := by
  simp only [wfBody,wfStep_rename,rename_comp,LogicCode.rename_comp,QuantifierCode.rename_comp,Expr.rename,Expr.liftRen,PureTypeSystem.Expr.liftRen]
  try rfl
theorem wfStep_subst (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) (σ : Nat → Expr S) :
    (B.wfStep L KY KP v).subst σ = (B.subst σ).wfStep (L.subst σ) (KY.subst σ) (KP.subst σ) (v.subst σ) := by
  simp only [wfStep,induction_subst,responsePred_subst]
theorem wfBody_instantiate (L : LogicCode S) (KY KP : QuantifierCode S) (v : Expr S) :
    (B.wfBody L KY KP).instantiate v = B.wfStep L KY KP v := by
  simp only [wfBody,Expr.instantiate,wfStep_subst,instantiate_raise,LogicCode.instantiate_raise,QuantifierCode.instantiate_raise,Expr.subst,Expr.single]
theorem wf_rename (L : LogicCode S) (KY KP : QuantifierCode S) (ρ : Nat → Nat) :
    (B.wf L KY KP).rename ρ = (B.rename ρ).wf (L.rename ρ) (KY.rename ρ) (KP.rename ρ) := by
  simp only [wf,DataWrapper.build_rename,DataWrapper.argRen,ite_true, if_true,wfBody_rename,ProbeCode.carrier_rename,relational,rename,ObservationCode.rename,RelationalCode.rename]
end SpecializedCode

namespace SpecializedCode.Formed

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem indStep_formula {i x : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data) :
    L.Formula (B.indStep L.code KY.code KP.code i x) := by
  exact L.imp_formula (H.relational_formed.valid_formula KY KP hx mx)
    (L.imp_formula (H.relational_formed.le_formula KY KP hi mi hx mx)
      (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hi mi hx mx))

theorem indBody_family {i : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data) :
    L.Family B.xType (B.indBody L.code KY.code KP.code i) := by
  intro Δ δ e x hx mx
  rw [indBody_rename,indBody_instantiate]
  exact (H.rename e).indStep_formula (KY.rename e) (KP.rename e) (xPred_typed_rename e hi) (e.moded mi)
    (by simpa only [xType_rename] using hx) mx

theorem induction_formula {i : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data) :
    L.Formula (B.induction L.code KY.code KP.code i) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  exact L.all_formula_family KY H.x_sorted H.x_mode (H.x_sorted s hs) (H.indBody_family KY KP hi mi)

end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem wfStep_formula {v : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data) :
    L.Formula (B.wfStep L.code KY.code KP.code v) := by
  have hi := H.responsePred_typed KY KP hv mv
  exact H.induction_formula KY KP hi.1 hi.2

theorem wfBody_family : L.Family B.relational.probe.carrier (B.wfBody L.code KY.code KP.code) := by
  intro Δ δ e v hv mv
  rw [wfBody_rename,wfBody_instantiate]
  exact (H.rename e).wfStep_formula (KY.rename e) (KP.rename e)
    (by simpa only [ProbeCode.carrier_rename,SpecializedCode.rename,relational,ObservationCode.rename,RelationalCode.rename] using hv) mv

theorem wf_typed : HasType P Γ (B.wf L.code KY.code KP.code) B.xType ∧ WellModed γ (B.wf L.code KY.code KP.code) .data :=
  (H.relational_formed.channel.logical.sound H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode).1 _ (H.wfBody_family KY KP)

theorem wf_primitive_evaluation {v : Expr S}
    (hv : HasType P Γ v B.relational.probe.carrier) (mv : WellModed γ v .data) :
    Equivalent P Γ γ (B.relational.logical.observe B.relational.probe.carrier (B.wf L.code KY.code KP.code) v)
      (B.induction L.code KY.code KP.code (B.responsePred L.code KY.code KP.code v)) := by
  simpa only [wf,RelationalCode.channel,DataWrapper.cancelFormula,ite_true, if_true,wfBody_instantiate,wfStep] using
    H.relational_formed.channel.logical.cancellation H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode (H.wfBody_family KY KP) ⟨hv,mv⟩

theorem wf_evaluation {i : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data) :
    Equivalent P Γ γ (B.relational.le L.code KY.code KP.code i (B.wf L.code KY.code KP.code))
      (B.induction L.code KY.code KP.code (B.responsePred L.code KY.code KP.code (B.relational.probeFor L.code KY.code KP.code i))) := by
  have hz := H.relational_formed.probeFor_typed KY KP hi mi
  exact H.wf_primitive_evaluation KY KP hz.1 hz.2
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem indConsequence_respect {v c x : Expr S}
    (hv : HasType P Γ v B.xPredType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.xPredType) (mc : WellModed γ c .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.relational.probe.carrier v c))
    (hu : Proves P Γ γ (B.relational.valid L.code KY.code KP.code x)) :
    Equivalent P Γ γ
      (L.imp (B.relational.le L.code KY.code KP.code v x) (B.relational.channel.eval B.relational.probe.carrier v x))
      (L.imp (B.relational.le L.code KY.code KP.code c x) (B.relational.channel.eval B.relational.probe.carrier c x)) := by
  have evc := H.relational_formed.channel.predCompare_elim H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode KY hv mv hc mc hx mx he
  have el := H.relational_formed.valid_elim KY KP hx mx hv mv hc mc hu he
  exact L.imp_equivalent (H.relational_formed.le_formula KY KP hv mv hx mx) (H.relational_formed.le_formula KY KP hc mc hx mx)
    (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hv mv hx mx)
    (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hc mc hx mx) el evc

omit H in
theorem xComparison_rename {Δ : List (Expr S)} {δ : Nat → Mode} (e : Embedding P Γ γ Δ δ) {v c : Expr S}
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.relational.probe.carrier v c)) :
    Proves P Δ δ ((B.rename e.names).relational.channel.predCompare (L.rename e).code (KY.rename e).code
      (B.rename e.names).relational.probe.carrier (v.rename e.names) (c.rename e.names)) := by
  simpa only [ChannelCode.predCompare_rename,ProbeCode.carrier_rename,relational_rename,LogicSetup.code_rename,QuantifierRoute.code_rename,relational,SpecializedCode.rename,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using he.rename e

theorem indStep_respect {v c x : Expr S}
    (hv : HasType P Γ v B.xPredType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.xPredType) (mc : WellModed γ c .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.relational.probe.carrier v c)) :
    Equivalent P Γ γ (B.indStep L.code KY.code KP.code v x) (B.indStep L.code KY.code KP.code c x) := by
  apply L.guarded_equivalent_future (H.relational_formed.valid_formula KY KP hx mx)
    (L.imp_formula (H.relational_formed.le_formula KY KP hv mv hx mx)
      (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hv mv hx mx))
    (L.imp_formula (H.relational_formed.le_formula KY KP hc mc hx mx)
      (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hc mc hx mx))
  intro Δ δ e hu
  have hu' : Proves P Δ δ ((B.rename e.names).relational.valid (L.rename e).code (KY.rename e).code (KP.rename e).code (x.rename e.names)) := by
    simpa only [RelationalCode.valid_rename,relational_rename,LogicSetup.code_rename,QuantifierRoute.code_rename] using hu
  simpa only [LogicSetup.imp_rename,ChannelCode.eval_rename,ProbeCode.carrier_rename,RelationalCode.le_rename,
    relational_rename,LogicSetup.code_rename,QuantifierRoute.code,QuantifierRoute.rename,QuantifierCode.rename,relational,SpecializedCode.rename,ObservationCode.rename,RelationalCode.channel,RelationalCode.rename,ChannelCode.rename,ProbeCode.rename] using
    (H.rename e).indConsequence_respect (KY.rename e) (KP.rename e)
      (xPred_typed_rename e hv) (e.moded mv) (xPred_typed_rename e hc) (e.moded mc)
      (x_typed_rename (B := B) e hx) (e.moded mx) (xComparison_rename KY e he) hu'

theorem induction_respect {v c : Expr S}
    (hv : HasType P Γ v B.xPredType) (mv : WellModed γ v .data)
    (hc : HasType P Γ c B.xPredType) (mc : WellModed γ c .data)
    (he : Proves P Γ γ (B.relational.channel.predCompare L.code KY.code B.relational.probe.carrier v c)) :
    Equivalent P Γ γ (B.induction L.code KY.code KP.code v) (B.induction L.code KY.code KP.code c) := by
  apply L.all_equivalent_future KY H.x_sorted H.x_mode (H.indBody_family KY KP hv mv)
    (H.indBody_family KY KP hc mc)
  intro Δ δ e x hx mx
  rw [indBody_rename,indBody_rename,indBody_instantiate,indBody_instantiate]
  exact (H.rename e).indStep_respect (KY.rename e) (KP.rename e)
    (xPred_typed_rename e hv) (e.moded mv) (xPred_typed_rename e hc) (e.moded mc)
    (by simpa only [xType_rename] using hx) mx (xComparison_rename KY e he)
end

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem wf_shift_evaluation {i : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (he : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i)) :
    Equivalent P Γ γ (B.relational.le L.code KY.code KP.code i (B.wf L.code KY.code KP.code))
      (B.induction L.code KY.code KP.code (B.shiftPred L.code KY.code KP.code i)) := by
  have zi := H.relational_formed.probeFor_typed KY KP hi mi
  have pi := H.responsePred_typed KY KP zi.1 zi.2
  have si := H.shiftPred_typed KY KP hi mi
  exact (H.relational_formed.le_formula KY KP hi mi (H.wf_typed KY KP).1 (H.wf_typed KY KP).2).equivalent_trans
    (H.induction_formula KY KP pi.1 pi.2) (H.induction_formula KY KP si.1 si.2) (H.wf_evaluation KY KP hi mi)
    (H.induction_respect KY KP pi.1 pi.2 si.1 si.2 (H.shift_compare KY KP hi mi he))
end

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem wfQ_member {i : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (he : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i))
    (ht : Proves P Γ γ (B.relational.le L.code KY.code KP.code i (B.wf L.code KY.code KP.code))) :
    Proves P Γ γ (B.relational.channel.eval B.relational.probe.carrier i (B.delta L.code KY.code KP.code (B.wf L.code KY.code KP.code))) := by
  have si := H.shiftPred_typed KY KP hi mi
  have wf := H.wf_typed KY KP
  exact (H.shiftPred_exact KY KP hi mi wf.1 wf.2 he).1.prove
    (H.induction_builder KY KP si.1 si.2 (H.shiftPred_extensional KY KP hi mi he)
      ((H.wf_shift_evaluation KY KP hi mi he).1.prove ht))

theorem wfQ_imp {i : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data)
    (he : Proves P Γ γ (B.relational.extensional L.code KY.code KP.code i)) :
    Proves P Γ γ (L.imp (B.relational.le L.code KY.code KP.code i (B.wf L.code KY.code KP.code))
      (B.relational.channel.eval B.relational.probe.carrier i (B.delta L.code KY.code KP.code (B.wf L.code KY.code KP.code)))) := by
  have wf := H.wf_typed KY KP
  have dx := H.delta_typed KY KP wf.1 wf.2
  apply L.imp_intro_future (H.relational_formed.le_formula KY KP hi mi wf.1 wf.2)
    (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hi mi dx.1 dx.2)
  intro Δ δ e ht
  simp only [RelationalCode.le_rename,wf_rename] at ht
  simp only [ChannelCode.eval_rename,ProbeCode.carrier_rename,delta_rename,wf_rename]
  have he' := he.rename e
  simp only [RelationalCode.extensional_rename] at he'
  exact (H.rename e).wfQ_member (KY.rename e) (KP.rename e) (xPred_typed_rename e hi) (e.moded mi) he' ht

theorem wfQ_step_oai {i : Expr S}
    (hi : HasType P Γ i B.xPredType) (mi : WellModed γ i .data) :
    Proves P Γ γ (B.qStep L.code KY.code KP.code (B.wf L.code KY.code KP.code) i) := by
  have wf := H.wf_typed KY KP
  have dx := H.delta_typed KY KP wf.1 wf.2
  apply L.imp_intro_future (H.relational_formed.extensional_formula KY KP hi mi)
    (L.imp_formula (H.relational_formed.le_formula KY KP hi mi wf.1 wf.2)
      (H.relational_formed.channel.eval_formula H.relational_formed.probe.carrier_sorted H.relational_formed.probe.carrier_mode hi mi dx.1 dx.2))
  intro Δ δ e he
  simp only [RelationalCode.extensional_rename] at he
  simp only [LogicSetup.imp_rename,RelationalCode.le_rename,ChannelCode.eval_rename,ProbeCode.carrier_rename,delta_rename,wf_rename]
  exact (H.rename e).wfQ_imp (KY.rename e) (KP.rename e) (xPred_typed_rename e hi) (e.moded mi) he

end SpecializedCode.Formed
end PureTypeSystem.Labelled

end OAI
end

theorem solution.{u} : type_of% @OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.wfQ_step_oai.{u} := @OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.wfQ_step_oai.{u}
