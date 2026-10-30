-- Prove2me | solution 1 for OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.good_backward
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:12:41.829699+00:00
-- url     : https://prove2.me/submissions/589f39bb-6414-44e8-bf17-4967ac2aefe5

import Mathlib
import Definitions.Def_TypeSystemNormalization
import Definitions.Def_OAIQ5T6000
import Theorems.Thm_OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_parameter_query
import Theorems.Thm_OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_propertyBody_family
import Theorems.Thm_OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_propertyG_roundRespect

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

end LogicSetup
end

section
universe u
variable {S : Type u} {P : Specification S}
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

end LogicSetup
end

section
universe u
variable {S : Type u}
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

end DataWrapper

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
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate
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
theorem logical_mode (mT : WellModed γ T .data) : WellModed γ (R.logicalType T) .data := h.logical.mode mT

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

end Formed
end ChannelCode

namespace DoubleCode
variable (R : DoubleCode S)
theorem rename_comp (ρ τ : Nat → Nat) : (R.rename τ).rename ρ = R.rename (ρ ∘ τ) := by
  cases R; simp only [rename,DataWrapper.rename_comp]
theorem instantiate_raise (a : Expr S) : (R.rename Nat.succ).subst (Expr.single a) = R := by
  cases R; simp only [rename,subst,DataWrapper.instantiate_raise]
theorem carrier_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.carrier T).rename ρ = (R.rename ρ).carrier (T.rename ρ) := by
  simp only [carrier,rename,DataWrapper.apply_rename]
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

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
  (L : LogicSetup P Γ γ C) (I J k p n g : Set S)

namespace Formed
variable {R L I J k p n g} (h : R.Formed L I J k p n g)
include h
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
theorem rawType_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.rawType T).rename ρ = (R.rename ρ).rawType (T.rename ρ) := by
  simp only [rawType,rename,DataWrapper.apply_rename]
theorem rawType_subst (T : Expr S) (σ : Nat → Expr S) :
    (R.rawType T).subst σ = (R.subst σ).rawType (T.subst σ) := by
  simp only [rawType,subst,DataWrapper.apply_subst]
theorem predicateType_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.predicateType T).rename ρ = (R.rename ρ).predicateType (T.rename ρ) := by
  simp only [predicateType,rename,DataWrapper.apply_rename]
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

end Formed
end ChannelCode

end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Pairs
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

namespace DoubleCode
variable (R : DoubleCode S)

theorem big_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.big T).rename ρ = (R.rename ρ).big (T.rename ρ) := R.tower_rename 4 T ρ
theorem bpType_rename (T : Expr S) (ρ : Nat → Nat) :
    (R.bpType T).rename ρ = (R.rename ρ).bpType (T.rename ρ) := by
  simp only [bpType,DataWrapper.apply_rename,big_rename]; rfl

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
 theorem markBody_family {T c₀ : Expr S} (hT : SortedAt P Γ T I) (mT : WellModed γ T .data)
    (t : Fin 8) (hc : HasType P Γ c₀ T) (mc : WellModed γ c₀ .data) :
    L.Family (R.bpType T) (R.markBody L.code t T c₀) := by
  have hv := h.tagged_typed hT mT (queryTag t) hc mc
  exact h.first.contraCallback_family (h.tower_sorted hT 4) (h.tower_mode mT 4) hv.1 hv.2

end Formed
end DoubleCode

namespace DoubleCode

section
variable (R : DoubleCode S)
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
variable {S : Type u} {P : Specification S}
namespace RelationalCode.Formed

section
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {R : RelationalCode S}
    (H : R.Formed L I J k p n g j h)
include H
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

end

universe u
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

universe u
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

theorem relational_formed : B.relational.Formed L I J k p n g j h := H.observation.relational

theorem base_sorted : SortedAt P Γ B.baseType k := H.relational_formed.base_sorted H.type_sorted
theorem base_mode : WellModed γ B.baseType .data := H.relational_formed.base_mode H.type_mode

end Formed
end

variable (B : SpecializedCode S)

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

namespace PureTypeSystem.Labelled

section
universe u
variable {S : Type u} {P : Specification S}

namespace SpecializedCode
variable (B : SpecializedCode S)
namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem parameter_query_formula (t : Fin 7) {v : Expr S}
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data) :
    L.Formula (B.relational.probe.doubled.query B.relational.predicate L.code t.castSucc (B.relational.probe.rawType B.type)
      (B.parameter L.code KY.code KP.code) v) := by
  have hm := H.parameter_typed KY KP
  exact H.relational_formed.probe.doubled_formed.query_formula H.relational_formed.channel.predicate t.castSucc
    (H.relational_formed.probe.raw_sorted H.type_sorted) (H.relational_formed.probe.raw_mode H.type_mode) hm.1 hm.2 hv mv

end Formed
end SpecializedCode
end

universe u
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

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J k p n g j h : Set S} {B : SpecializedCode S}
    (H : B.Formed L I J k p n g j h) (KY : QuantifierRoute L.witnesses C L.base j)
    (KP : QuantifierRoute L.witnesses C L.base h)
include H

theorem good_backward_oai {v : Expr S} (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hg : Proves P Γ γ (B.propertyG L.code KY.code KP.code v)) :
    Proves P Γ γ (B.good L.code KY.code KP.code v) := by
  exact L.conj_intro (H.relational_formed.channel.roundRespect_formula KY H.base_sorted H.base_mode hv mv)
    (H.parameter_query_formula KY KP 0 hv mv) (H.propertyG_roundRespect KY KP hv mv hg)
    ((H.parameter_query KY KP 0 hv mv).2.prove hg)

end Formed
end SpecializedCode
end

universe u
end PureTypeSystem.Labelled

end OAI
end

theorem solution.{u} : type_of% @OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.good_backward_oai.{u} := @OAI.PureTypeSystem.Labelled.SpecializedCode.Formed.good_backward_oai.{u}
