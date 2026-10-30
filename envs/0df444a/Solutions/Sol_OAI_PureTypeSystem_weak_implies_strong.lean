-- Prove2me | solution 1 for OAI.PureTypeSystem.weak_implies_strong
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:33:13.143968+00:00
-- url     : https://prove2.me/submissions/d1d2cb45-1590-47bc-81e7-3088ea46fa60

import Mathlib
import Definitions.Def_TypeSystemNormalization
import Definitions.Def_OAIQ5T6000
import Theorems.Thm_OAI_PureTypeSystem_Labelled_SpecializedCode_Formed_relational_bottom

section
-- module Solutions.OAIQ5_T6.TypeSystem_Reduction
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate _root_.OAI.PureTypeSystem.instCountableExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem

universe u

namespace Normal

variable {S : Type u}

theorem stronglyNormalizing {M : Expr S} (h : Normal M) : StronglyNormalizing M :=
  .intro M (fun N hN => False.elim (h N hN))

end Normal

namespace StronglyNormalizing

variable {S : Type u} {M N : Expr S}

/-- SN of an image reflects along any map preserving individual reduction steps. -/
theorem of_map {f : Expr S → Expr S}
    (hf : ∀ {M N}, Beta M N → Beta (f M) (f N)) {M : Expr S}
    (h : StronglyNormalizing (f M)) : StronglyNormalizing M := by
  have aux : ∀ N, StronglyNormalizing N → ∀ M, f M = N → StronglyNormalizing M := by
    intro N hN
    induction hN with
    | intro N _ ih =>
        intro M heq
        apply Acc.intro
        intro M' hM
        exact ih (f M') (heq ▸ hf hM) M' rfl
  exact aux _ h M rfl

theorem app_left {f a : Expr S} (h : StronglyNormalizing (.app f a)) :
    StronglyNormalizing f := of_map (fun h => Beta.app_left h) h

theorem app_right {f a : Expr S} (h : StronglyNormalizing (.app f a)) :
    StronglyNormalizing a := of_map (fun h => Beta.app_right h) h

theorem lam_domain {A b : Expr S} (h : StronglyNormalizing (.lam A b)) :
    StronglyNormalizing A := of_map (fun h => Beta.lam_domain h) h

theorem lam_body {A b : Expr S} (h : StronglyNormalizing (.lam A b)) :
    StronglyNormalizing b := of_map (fun h => Beta.lam_body h) h

theorem pi_domain {A B : Expr S} (h : StronglyNormalizing (.pi A B)) :
    StronglyNormalizing A := of_map (fun h => Beta.pi_domain h) h

theorem pi_body {A B : Expr S} (h : StronglyNormalizing (.pi A B)) :
    StronglyNormalizing B := of_map (fun h => Beta.pi_body h) h

theorem of_subst (σ : Nat → Expr S) (h : StronglyNormalizing (M.subst σ)) :
    StronglyNormalizing M := of_map (fun h => h.subst σ) h

theorem of_rename (ρ : Nat → Nat) (h : StronglyNormalizing (M.rename ρ)) :
    StronglyNormalizing M := of_map (fun h => h.rename ρ) h

theorem lam {A b : Expr S} (hA : StronglyNormalizing A) (hb : StronglyNormalizing b) :
    StronglyNormalizing (.lam A b) := by
  induction hA generalizing b with
  | intro A hA ihA =>
      induction hb with
      | intro b hb ihb =>
          apply Acc.intro
          intro N hN
          cases hN with
          | lam_domain h => exact ihA _ h (Acc.intro _ hb)
          | lam_body h => exact ihb _ h

theorem pi {A B : Expr S} (hA : StronglyNormalizing A) (hB : StronglyNormalizing B) :
    StronglyNormalizing (.pi A B) := by
  induction hA generalizing B with
  | intro A hA ihA =>
      induction hB with
      | intro B hB ihB =>
          apply Acc.intro
          intro N hN
          cases hN with
          | pi_domain h => exact ihA _ h (Acc.intro _ hB)
          | pi_body h => exact ihB _ h

end StronglyNormalizing

namespace StronglyNormalizing

variable {S : Type u}

theorem var_apps (n : Nat) {as : List (Expr S)} (has : StronglyNormalizingArgs as) :
    StronglyNormalizing ((Expr.var n : Expr S).apps as) := by
  induction has with
  | intro as has ih =>
      apply Acc.intro
      intro N hN
      obtain ⟨f, hf, rfl⟩ | ⟨bs, hbs, rfl⟩ :=
        hN.apps_inv (by intro A b heq; cases heq)
      · cases hf
      · exact ih _ hbs

end StronglyNormalizing

namespace Expr
variable {S : Type u}

namespace Child
variable {M N M' : Expr S}
theorem beta_lift (h : Child M N) (hr : Beta M M') :
    ∃ N', Beta N N' ∧ Child M' N' := by
  cases h with
  | app_left f a => exact ⟨_,.app_left hr,.app_left _ _⟩
  | app_right f a => exact ⟨_,.app_right hr,.app_right _ _⟩
  | lam_domain D m => exact ⟨_,.lam_domain hr,.lam_domain _ _⟩
  | lam_body D m => exact ⟨_,.lam_body hr,.lam_body _ _⟩
  | pi_domain D E => exact ⟨_,.pi_domain hr,.pi_domain _ _⟩
  | pi_body D E => exact ⟨_,.pi_body hr,.pi_body _ _⟩

theorem sn (h : Child M N) (hs : StronglyNormalizing N) : StronglyNormalizing M := by
  cases h with
  | app_left => exact hs.app_left
  | app_right => exact hs.app_right
  | lam_domain => exact hs.lam_domain
  | lam_body => exact hs.lam_body
  | pi_domain => exact hs.pi_domain
  | pi_body => exact hs.pi_body
end Child

namespace Subterm
variable {M N L M' : Expr S}
theorem trans (h : Subterm M N) (h' : Subterm N L) : Subterm M L := by
  induction h' with
  | refl => exact h
  | tail _ hc ih => exact .tail ih hc

theorem of_child (h : Child M N) : Subterm M N := .tail (.refl M) h

theorem beta_lift (h : Subterm M N) (hr : Beta M M') :
    ∃ N', Beta N N' ∧ Subterm M' N' := by
  induction h with
  | refl => exact ⟨_,hr,.refl _⟩
  | tail h hc ih =>
    obtain ⟨N',hr',hs'⟩ := ih
    obtain ⟨L',hr'',hc'⟩ := hc.beta_lift hr'
    exact ⟨L',hr'',.tail hs' hc'⟩

theorem sn (h : Subterm M N) (hs : StronglyNormalizing N) : StronglyNormalizing M := by
  induction h with
  | refl => exact hs
  | tail h hc ih => exact ih (hc.sn hs)
end Subterm
end Expr

namespace StronglyNormalizing
variable {S : Type u}
/-- The manuscript's simultaneous reduction-height/syntax-size induction,
proved directly from accessibility, without choosing a height or raising limits. -/
theorem induction_subterms {Q : Expr S → Prop}
    (step : ∀ M, StronglyNormalizing M → (∀ N, Beta M N → Q N) →
      (∀ N, Expr.Child N M → Q N) → Q M)
    {M : Expr S} (hs : StronglyNormalizing M) : Q M := by
  have aux : ∀ M : Expr S, StronglyNormalizing M → ∀ N, Expr.Subterm N M → Q N := by
    intro M hs
    induction hs with
    | intro M hred ih =>
      intro N
      have hreds (N : Expr S) (hNM : Expr.Subterm N M) : ∀ L, Beta N L → Q L := by
        intro L hr
        obtain ⟨M',hr',hLM'⟩ := hNM.beta_lift hr
        exact ih M' hr' L hLM'
      induction N with
      | var n =>
        intro hn
        exact step _ (hn.sn (.intro M hred)) (hreds _ hn) (fun _ hc => by cases hc)
      | sort s =>
        intro hn
        exact step _ (hn.sn (.intro M hred)) (hreds _ hn) (fun _ hc => by cases hc)
      | app f a ihf iha =>
        intro hn
        apply step _ (hn.sn (.intro M hred)) (hreds _ hn)
        intro L hc
        cases hc with
        | app_left => exact ihf ((Expr.Subterm.of_child (.app_left f a)).trans hn)
        | app_right => exact iha ((Expr.Subterm.of_child (.app_right f a)).trans hn)
      | lam D m ihD ihm =>
        intro hn
        apply step _ (hn.sn (.intro M hred)) (hreds _ hn)
        intro L hc
        cases hc with
        | lam_domain => exact ihD ((Expr.Subterm.of_child (.lam_domain D m)).trans hn)
        | lam_body => exact ihm ((Expr.Subterm.of_child (.lam_body D m)).trans hn)
      | pi D E ihD ihE =>
        intro hn
        apply step _ (hn.sn (.intro M hred)) (hreds _ hn)
        intro L hc
        cases hc with
        | pi_domain => exact ihD ((Expr.Subterm.of_child (.pi_domain D E)).trans hn)
        | pi_body => exact ihE ((Expr.Subterm.of_child (.pi_body D E)).trans hn)
  exact aux M hs M (.refl M)
/-- The child hypothesis can equivalently cover every proper syntactic part. -/
theorem induction_descendants {Q : Expr S → Prop}
    (step : ∀ M, StronglyNormalizing M → (∀ N, Beta M N → Q N) →
      (∀ N, (∃ K, Expr.Child K M ∧ Expr.Subterm N K) → Q N) → Q M)
    {M : Expr S} (hs : StronglyNormalizing M) : Q M := by
  have h : Q M ∧ ∀ N, Expr.Subterm N M → Q N := by
    apply induction_subterms (Q := fun M => Q M ∧ ∀ N, Expr.Subterm N M → Q N) _ hs
    intro M hM hr hc
    have hq : Q M := step M hM (fun N h => (hr N h).1) (by
      rintro N ⟨K,hK,hN⟩
      exact (hc K hK).2 N hN)
    refine ⟨hq, ?_⟩
    intro N hN
    cases hN with
    | refl => exact hq
    | tail hN hK => exact (hc _ hK).2 _ hN
  exact h.1
end StronglyNormalizing
end PureTypeSystem

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Typing
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate _root_.OAI.PureTypeSystem.instCountableExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem

universe u

/-! Finite syntax-directed typing trees, with all generation witnesses
retained; no functionality or unique sort choices are imposed. -/

namespace Expr
variable {S : Type u}
namespace ProperPart
variable {N M L : Expr S}
theorem child (h : Child N M) : ProperPart N M := ⟨N,h,.refl N⟩
theorem subterm (h : ProperPart N M) : Subterm N M := by
  obtain ⟨K,hK,hN⟩ := h
  exact .tail hN hK
theorem trans_right (h : ProperPart N M) (hML : Subterm M L) : ProperPart N L := by
  induction hML with
  | refl => exact h
  | tail hML hL ih => exact ⟨_,hL,h.subterm.trans hML⟩
theorem trans_left (hNM : Subterm N M) (h : ProperPart M L) : ProperPart N L := by
  obtain ⟨K,hK,hM⟩ := h
  exact ⟨K,hK,hNM.trans hM⟩
end ProperPart
namespace Subterm
variable {M : Expr S}
theorem apps_head (ns : List (Expr S)) : Subterm M (M.apps ns) := by
  induction ns generalizing M with
  | nil => exact .refl M
  | cons n ns ih => exact (of_child (.app_left M n)).trans (ih (M := .app M n))
end Subterm
namespace ProperPart
variable {M n : Expr S} {ns : List (Expr S)}
theorem apps_arg (hn : n ∈ ns) : ProperPart n (M.apps ns) := by
  induction ns generalizing M with
  | nil => cases hn
  | cons a ns ih =>
    rcases List.mem_cons.mp hn with rfl | hn
    · exact (child (.app_right M n)).trans_right (Subterm.apps_head ns)
    · exact ih hn
end ProperPart
end Expr

namespace HasType
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)}
theorem spine_shape {M T : Expr S} (h : HasType P Γ M T) :
    (∃ s, M = .sort s) ∨ Neutral M ∨ (∃ A B, M = .pi A B) ∨
      (∃ A b ns, M = (Expr.lam A b).apps ns) := by
  induction M generalizing T with
  | var n => exact .inr (.inl (.var n))
  | sort s => exact .inl ⟨s,rfl⟩
  | lam A b => exact .inr (.inr (.inr ⟨A,b,[],rfl⟩))
  | pi A B => exact .inr (.inr (.inl ⟨A,B,rfl⟩))
  | app f a ihf iha =>
    obtain ⟨D,E,hf,_,_⟩ := h.generation_app
    rcases ihf hf with ⟨s,rfl⟩ | hn | ⟨A,B,rfl⟩ | ⟨A,b,ns,rfl⟩
    · exact False.elim hf.sort_cannot_have_product_type
    · exact .inr (.inl (.app hn))
    · exact False.elim hf.product_cannot_have_product_type
    · exact .inr (.inr (.inr ⟨A,b,ns ++ [a],by simp only [Expr.apps_append,Expr.apps]⟩))

theorem app_spine {f a T : Expr S} (h : HasType P Γ (.app f a) T) :
    Neutral f ∨ ∃ D b n ns, Expr.app f a = (Expr.app (.lam D b) n).apps ns := by
  obtain ⟨D,E,hf,_,_⟩ := h.generation_app
  rcases hf.spine_shape with ⟨s,rfl⟩ | hn | ⟨A,B,rfl⟩ | ⟨A,b,ns,rfl⟩
  · exact False.elim hf.sort_cannot_have_product_type
  · exact .inl hn
  · exact False.elim hf.product_cannot_have_product_type
  · right
    cases ns with
    | nil => exact ⟨A,b,a,[],rfl⟩
    | cons n ns => exact ⟨A,b,n,ns ++ [a],by simp only [Expr.apps_append,Expr.apps]⟩

theorem apps_head {M T : Expr S} {ns : List (Expr S)} (h : HasType P Γ (M.apps ns) T) :
    ∃ A, HasType P Γ M A := by
  induction ns generalizing M T with
  | nil => exact ⟨T,h⟩
  | cons n ns ih =>
    obtain ⟨A,hA⟩ := ih h
    obtain ⟨D,E,hf,_,_⟩ := hA.generation_app
    exact ⟨_,hf⟩

theorem apps_arg {M T n : Expr S} {ns : List (Expr S)}
    (h : HasType P Γ (M.apps ns) T) (hn : n ∈ ns) : ∃ A, HasType P Γ n A := by
  induction ns generalizing M T with
  | nil => cases hn
  | cons a ns ih =>
    rcases List.mem_cons.mp hn with rfl | hn
    · obtain ⟨T,hT⟩ := h.apps_head (M := .app M n) (ns := ns)
      obtain ⟨D,E,_,ha,_⟩ := hT.generation_app
      exact ⟨D,ha⟩
    · exact ih h hn
end HasType

/-- The syntactic application principle implying strong normalization.
This principle is proved from candidate interfaces, not assumed
on the PTS normalization theorem. -/
theorem stronglyNormalizing_of_application
    {S : Type u} {P : Specification S}
    (applySN : ∀ {Γ f a D E}, HasType P Γ f (.pi D E) → HasType P Γ a D →
      StronglyNormalizing f → StronglyNormalizing a → StronglyNormalizing (.app f a)) :
    SystemStronglyNormalizing P := by
  have typed : ∀ M : Expr S, ∀ {Γ A}, HasType P Γ M A → StronglyNormalizing M := by
    intro M
    induction M with
    | var n => intro Γ A h; exact (Normal.var n).stronglyNormalizing
    | sort s => intro Γ A h; exact (Normal.sort s).stronglyNormalizing
    | app f a ihf iha =>
        intro Γ A h
        obtain ⟨D, E, hf, ha, _⟩ := h.generation_app
        exact applySN hf ha (ihf hf) (iha ha)
    | lam D b ihD ihb =>
        intro Γ A h
        obtain ⟨E, s, hb, hpi, _⟩ := h.generation_lam
        obtain ⟨s₁, s₂, s₃, hD, _, _, _⟩ := hpi.generation_pi
        exact (ihD hD).lam (ihb hb)
    | pi D E ihD ihE =>
        intro Γ A h
        obtain ⟨s₁, s₂, s₃, hD, hE, _, _⟩ := h.generation_pi
        exact (ihD hD).pi (ihE hE)
  intro Γ _ M h
  obtain ⟨A, h | h⟩ := h
  · exact typed M h
  · obtain ⟨s, rfl⟩ | ⟨s, hs⟩ := h.regularity
    · exact (Normal.sort s).stronglyNormalizing
    · exact typed M hs

/-- A failed full-normalization theorem has an exact, well-typed application
counterexample whose two children are already strongly normalizing. -/
theorem exists_bad_application {S : Type u} {P : Specification S}
    (h : ¬ SystemStronglyNormalizing P) :
    ∃ Γ f a D E, HasType P Γ f (.pi D E) ∧ HasType P Γ a D ∧
      StronglyNormalizing f ∧ StronglyNormalizing a ∧ ¬ StronglyNormalizing (.app f a) := by
  classical
  by_contra hn
  apply h
  apply stronglyNormalizing_of_application
  intro Γ f a D E hf ha hfs has
  by_contra hb
  exact hn ⟨Γ, f, a, D, E, hf, ha, hfs, has, hb⟩

end PureTypeSystem

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Contexts
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem

universe u

namespace Expr

variable {S : Type u}

namespace Scoped

variable {n m : Nat} {M : Expr S}

theorem mono (h : Scoped n M) (hnm : n ≤ m) : Scoped m M := by
  simpa only [rename_id] using h.rename id (fun _ hi => lt_of_lt_of_le hi hnm)

end Scoped

end Expr

namespace ContextTower

variable {S : Type u} {P : Specification S} (Ω : ContextTower P)

theorem fresh_variable {A : Expr S} {s : S} (h : Ω.HasType A (.sort s)) (lower : Nat) :
    ∃ i, lower ≤ i ∧ Ω.HasType (.var i) A := by
  obtain ⟨n, ht⟩ := h
  have hA : A.Scoped n := by
    have hh := ht.scope.1.reverseIndex
    rwa [Ω.length, Expr.reverseIndex_twice] at hh
  obtain ⟨m, hnm, hlm, he⟩ := Ω.saturated n A s ht lower
  have hAm := hA.mono hnm
  have hm : PureTypeSystem.HasType P (Ω.context m) (A.rename (Expr.reverseIndex m)) (.sort s) :=
    Ω.at_mono (A := .sort s) ht hnm
  refine ⟨m, hlm, m+1, ?_⟩
  rw [he, hAm.reverseIndex_succ]
  have hv := PureTypeSystem.HasType.var hm
  simpa only [Expr.rename, Expr.reverseIndex, Nat.lt_succ_self, ite_true, if_true,
    Nat.add_sub_cancel, Nat.sub_self] using hv

end ContextTower

/-! Finite generic contexts may have arbitrary raw actual images in the
saturated tower. Every such substitution is witnessed in one finite prefix;
no normalization or strong-normalization of the images is assumed. -/
namespace ContextTower
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)

namespace TypedSubstitution
variable {Ω} {Γ : List (Expr S)} {σ τ : Nat → Expr S}

/-- The tower's finite-prefix identity environment uses global names. -/
theorem identity (n : Nat) : Ω.TypedSubstitution (Ω.context n) (.var ∘ Expr.reverseIndex n) := by
  intro i A hi
  have ht := PureTypeSystem.HasType.lookup (Ω.valid n) hi
  refine ⟨n, ?_⟩
  simpa only [Expr.subst_var_rename, Expr.rename, Function.comp_apply,
    Expr.reverseIndex_involutive n i, Expr.reverseIndex_twice] using ht
end TypedSubstitution

end ContextTower
end PureTypeSystem

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Candidates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem

universe u

namespace Candidates

variable {S : Type u} {P : Specification S} (Ω : ContextTower P)

namespace TestedStack

variable {Ω} {T : Expr S} {ns : List (Expr S)}

theorem sn (h : TestedStack Ω T ns) : StronglyNormalizingArgs ns := by
  induction h with
  | nil => exact .nil
  | cons hn _ ih => exact .cons hn.2 ih

end TestedStack

variable {Ω} {T M : Expr S}

theorem sort_ground_eq_top (s : S) : Ground Ω (.sort s) = Top Ω (.sort s) := by
  apply Set.Subset.antisymm ground_le_top
  intro M h
  refine ⟨h.1, ?_⟩
  intro ns hs
  cases hs
  exact h.2

theorem var_ground (n : Nat) (h : Ω.HasType (.var n) T) : .var n ∈ Ground Ω T :=
  ⟨h, fun _ hs => StronglyNormalizing.var_apps n hs.sn⟩

end Candidates

end PureTypeSystem

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Labelled
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate _root_.OAI.PureTypeSystem.instCountableExpr
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

theorem erase_liftSub (σ : Nat → Expr S) :
    (fun n => (liftSub σ n).erase) = PureTypeSystem.Expr.liftSub (fun n => (σ n).erase) := by
  funext n; cases n <;> simp only [liftSub, erase, erase_rename, PureTypeSystem.Expr.liftSub]

@[simp] theorem erase_subst (M : Expr S) (σ : Nat → Expr S) :
    (M.subst σ).erase = M.erase.subst (fun n => (σ n).erase) := by
  induction M generalizing σ <;> simp_all only [subst, erase, PureTypeSystem.Expr.subst, erase_liftSub]

@[simp] theorem erase_instantiate (b a : Expr S) :
    (b.instantiate a).erase = b.erase.instantiate a.erase := by
  simp only [instantiate, erase_subst, PureTypeSystem.Expr.instantiate]
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

theorem erase (h : Beta M N) : PureTypeSystem.Beta M.erase N.erase := by
  induction h with
  | head l A b a => simpa only [Expr.erase, Expr.erase_instantiate] using
      (PureTypeSystem.Beta.head A.erase b.erase a.erase)
  | app_left h ih => exact .app_left ih
  | app_right h ih => exact .app_right ih
  | lam_domain h ih => exact .lam_domain ih
  | lam_body h ih => exact .lam_body ih
  | pi_domain h ih => exact .pi_domain ih
  | pi_body h ih => exact .pi_body ih

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

theorem pi_inv (h : Reduces (.pi l A B) N) :
    ∃ A' B', N = .pi l A' B' ∧ Reduces A A' ∧ Reduces B B' := by
  induction h with
  | refl => exact ⟨A, B, rfl, .refl, .refl⟩
  | tail _ h ih =>
      obtain ⟨A', B', rfl, hA, hB⟩ := ih
      cases h with
      | pi_domain h => exact ⟨_, _, rfl, hA.tail h, hB⟩
      | pi_body h => exact ⟨_, _, rfl, hA, hB.tail h⟩

theorem converts {M N : Expr S} (h : Reduces M N) : Converts M N :=
  Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ h

end Reduces

namespace Converts

variable {S : Type u}

theorem product_compatibility {l k : Label} {A B A' B' : Expr S}
    (h : Converts (.pi l A B) (.pi k A' B')) : l = k ∧ Converts A A' ∧ Converts B B' := by
  obtain ⟨T, hT, hT'⟩ := h.join
  obtain ⟨D, E, hDE, hA, hB⟩ := hT.pi_inv
  obtain ⟨D', E', hDE', hA', hB'⟩ := hT'.pi_inv
  have heq := Expr.pi.inj (hDE.symm.trans hDE')
  obtain ⟨rfl, rfl, rfl⟩ := heq
  exact ⟨rfl, .trans _ _ _ hA.converts (.symm _ _ hA'.converts),
    .trans _ _ _ hB.converts (.symm _ _ hB'.converts)⟩

end Converts

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

theorem context_head_conversion {A A' b B : Expr S} {s t : S}
    (hb : HasType P (A :: Γ) b B) (hA : HasType P Γ A (.sort s))
    (hA' : HasType P Γ A' (.sort t)) (hc : Converts A A') :
    HasType P (A' :: Γ) b B := by
  have hσ : TypedSubstitution P (A :: Γ) (A' :: Γ) Expr.var := by
    intro n D hn
    rw [Expr.subst_var]
    cases hn with
    | zero =>
        exact .conversion (.var hA') (.weaken hA hA')
          (.symm _ _ (hc.rename Nat.succ))
    | succ _ hn => exact .weaken (lookup hA.valid hn) hA'
  simpa only [Expr.subst_var] using hb.subst (.cons hA'.valid hA') _ hσ

end HasType

namespace Normal

section

variable {S : Type u} {M N : Expr S}

theorem reduces_eq (hM : Normal M) (h : Reduces M N) : M = N := by
  induction h with
  | refl => rfl
  | @tail N N' _ h ih => exact False.elim (hM N' (ih ▸ h))

theorem eq_of_converts (hM : Normal M) (hN : Normal N) (h : Converts M N) : M = N := by
  obtain ⟨K, hMK, hNK⟩ := h.join
  exact (hM.reduces_eq hMK).trans (hN.reduces_eq hNK).symm

end

variable {S : Type u}
theorem sort (s : S) : Normal (.sort s : Expr S) := by intro N h; cases h
end Normal

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

theorem generation_lam {l : Label} {Γ : List (Expr S)} {A b T : Expr S}
    (h : HasType P Γ (.lam l A b) T) :
    ∃ B s, HasType P (A :: Γ) b B ∧ HasType P Γ (.pi l A B) (.sort s) ∧
      Converts T (.pi l A B) := h.generation

theorem generation_app {l : Label} {Γ : List (Expr S)} {f a T : Expr S}
    (h : HasType P Γ (.app l f a) T) :
    ∃ A B, HasType P Γ f (.pi l A B) ∧ HasType P Γ a A ∧
      Converts T (B.instantiate a) := h.generation

/-- Correctness of types, including the unsorted literal-sort alternative. -/
theorem regularity {Γ : List (Expr S)} {M A : Expr S} (h : HasType P Γ M A) :
    (∃ s, A = .sort s) ∨ (∃ s, HasType P Γ A (.sort s)) := by
  induction h with
  | ax h => exact .inl ⟨_, rfl⟩
  | var h ih => exact .inr ⟨_, .weaken h h⟩
  | weaken hM hD ihM ihD =>
      obtain ⟨s, rfl⟩ | ⟨s, hA⟩ := ihM
      · exact .inl ⟨s, rfl⟩
      · exact .inr ⟨s, .weaken hA hD⟩
  | product hA hB hr ihA ihB => exact .inl ⟨_, rfl⟩
  | abstraction hb hPi ihb ihPi => exact .inr ⟨_, hPi⟩
  | application hf ha ihf iha =>
      obtain ⟨s, heq⟩ | ⟨s, hPi⟩ := ihf
      · cases heq
      · obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := hPi.generation_pi
        exact .inr ⟨s₂, hB.instantiate ha⟩
  | conversion hM hA hc ihM ihA => exact .inr ⟨_, hA⟩

theorem product_type_sorted {l : Label} {Γ : List (Expr S)} {M A B : Expr S}
    (h : HasType P Γ M (.pi l A B)) : ∃ s, HasType P Γ (.pi l A B) (.sort s) := by
  obtain ⟨s, heq⟩ | hs := h.regularity
  · cases heq
  · exact hs

end HasType

namespace Converts

variable {S : Type u}

theorem pi {l : Label} {A A' B B' : Expr S} (hA : Converts A A') (hB : Converts B B') :
    Converts (.pi l A B) (.pi l A' B') := by
  obtain ⟨D, hD, hD'⟩ := hA.join
  obtain ⟨E, hE, hE'⟩ := hB.join
  exact .trans _ _ _ (hD.pi hE).converts (.symm _ _ (hD'.pi hE').converts)

theorem pi_not_sort {l : Label} {A B : Expr S} {s : S} : ¬ Converts (.pi l A B) (.sort s) := by
  intro h
  obtain ⟨N, hN, hs⟩ := h.join
  have heq := (Normal.sort s).reduces_eq hs
  obtain ⟨D, E, hDE, _, _⟩ := hN.pi_inv
  cases heq.trans hDE

theorem sort_inj {s t : S} (h : Converts (Expr.sort s) (.sort t)) : s = t :=
  Expr.sort.inj ((Normal.sort s).eq_of_converts (Normal.sort t) h)

theorem instantiate_right {a a' : Expr S} (h : Converts a a') (B : Expr S) :
    Converts (B.instantiate a) (B.instantiate a') := by
  induction h with
  | rel a a' h =>
      exact (Parallel.instantiate (Parallel.refl B) (Parallel.of_beta h)).reduces.converts
  | refl a => exact .refl _
  | symm a b h ih => exact .symm _ _ ih
  | trans a b c hab hbc ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

end Converts

namespace HasType

variable {S : Type u} {P : Specification S}

theorem application_type_sorted_aux {Γ : List (Expr S)} {M T : Expr S}
    (h : HasType P Γ M T) :
    ∀ l f a, M = .app l f a → ∃ s, HasType P Γ T (.sort s) := by
  induction h with
  | ax h => intro l f a heq; cases heq
  | var h ih => intro l f a heq; cases heq
  | @weaken Γ M T D s hM hD ihM ihD =>
      intro l f a heq
      cases M with
      | var n => cases heq
      | sort t => cases heq
      | lam l A b => cases heq
      | pi l A B => cases heq
      | app l g b =>
          obtain ⟨r, hr⟩ := ihM l g b rfl
          exact ⟨r, .weaken hr hD⟩
  | product hA hB hr ihA ihB => intro l f a heq; cases heq
  | abstraction hb hPi ihb ihPi => intro l f a heq; cases heq
  | application hf ha ihf iha =>
      intro l f a heq
      obtain ⟨s, hPi⟩ := hf.product_type_sorted
      obtain ⟨s₁, s₂, s₃, hA, hB, hr, hc⟩ := hPi.generation_pi
      exact ⟨s₂, hB.instantiate ha⟩
  | conversion hM hT hc ihM ihT => intro l f a heq; exact ⟨_, hT⟩

theorem application_type_sorted {l : Label} {Γ : List (Expr S)} {f a T : Expr S}
    (h : HasType P Γ (.app l f a) T) : ∃ s, HasType P Γ T (.sort s) :=
  h.application_type_sorted_aux l f a rfl

theorem abstraction_type_sorted {l : Label} {Γ : List (Expr S)} {A b T : Expr S}
    (h : HasType P Γ (.lam l A b) T) : ∃ s, HasType P Γ T (.sort s) := by
  obtain ⟨s, hT⟩ | hs := h.regularity
  · obtain ⟨B, t, hb, hPi, hc⟩ := h.generation_lam
    subst T
    exact False.elim (Converts.pi_not_sort (.symm _ _ hc))
  · exact hs

/-- Reconstructing a sorted expression at its original expected type does not
require a sorting of a terminal (unsorted) sort. -/
theorem conversion_from_sort {Γ : List (Expr S)} {M T : Expr S} {s : S}
    (h : HasType P Γ M (.sort s))
    (hT : (∃ t, T = .sort t) ∨ ∃ t, HasType P Γ T (.sort t))
    (hc : Converts T (.sort s)) : HasType P Γ M T := by
  obtain ⟨t, rfl⟩ | ⟨t, ht⟩ := hT
  · have heq := hc.sort_inj
    subst t
    exact h
  · exact .conversion h ht (.symm _ _ hc)

/-- Subject reduction at the exact original type, including binder annotations. -/
theorem subject_reduction {Γ : List (Expr S)} {M N T : Expr S}
    (h : HasType P Γ M T) (hr : Beta M N) : HasType P Γ N T := by
  induction hr generalizing Γ T with
  | head l A b a =>
      obtain ⟨r, hT⟩ := h.application_type_sorted
      obtain ⟨D, E, hf, ha, hc⟩ := h.generation_app
      obtain ⟨B, s, hb, hPi, hp⟩ := hf.generation_lam
      obtain ⟨_, hDA, hEB⟩ := hp.product_compatibility
      obtain ⟨t, hA⟩ := hPi.product_domain l A B rfl
      have haA := HasType.conversion ha hA hDA
      have hresult := hb.instantiate haA
      exact .conversion hresult hT (.trans _ _ _
        (.symm _ _ (hEB.subst (Expr.single a))) (.symm _ _ hc))
  | app_left hr ih =>
      obtain ⟨r, hT⟩ := h.application_type_sorted
      obtain ⟨A, B, hf, ha, hc⟩ := h.generation_app
      exact .conversion (.application (ih hf) ha) hT (.symm _ _ hc)
  | @app_right l f a a' hr ih =>
      obtain ⟨r, hT⟩ := h.application_type_sorted
      obtain ⟨A, B, hf, ha, hc⟩ := h.generation_app
      exact .conversion (.application hf (ih ha)) hT (.trans _ _ _
        (.symm _ _ ((show Converts a a' from .rel _ _ hr).instantiate_right B)) (.symm _ _ hc))
  | @lam_domain l A A' b hr ih =>
      obtain ⟨r, hT⟩ := h.abstraction_type_sorted
      obtain ⟨B, s, hb, hPi, hc⟩ := h.generation_lam
      obtain ⟨s₁, s₂, s₃, hA, hB, hrule, hs⟩ := hPi.generation_pi
      have hA' := ih hA
      have heq : Converts A A' := .rel _ _ hr
      have hb' := hb.context_head_conversion hA hA' heq
      have hB' := hB.context_head_conversion hA hA' heq
      have hp' := HasType.product (l := l) hA' hB' hrule
      exact .conversion (.abstraction hb' hp') hT (.trans _ _ _
        (.symm _ _ (heq.pi (.refl B))) (.symm _ _ hc))
  | lam_body hr ih =>
      obtain ⟨r, hT⟩ := h.abstraction_type_sorted
      obtain ⟨B, s, hb, hPi, hc⟩ := h.generation_lam
      exact .conversion (.abstraction (ih hb) hPi) hT (.symm _ _ hc)
  | pi_domain hr ih =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hrule, hc⟩ := h.generation_pi
      have hA' := ih hA
      have hB' := hB.context_head_conversion hA hA' (.rel _ _ hr)
      exact (HasType.product hA' hB' hrule).conversion_from_sort h.regularity hc
  | pi_body hr ih =>
      obtain ⟨s₁, s₂, s₃, hA, hB, hrule, hc⟩ := h.generation_pi
      exact (HasType.product hA (ih hB) hrule).conversion_from_sort h.regularity hc

end HasType

namespace Converts
variable {S : Type u} {M N : Expr S}
theorem erase (h : Converts M N) : PureTypeSystem.Converts M.erase N.erase := by
  induction h with
  | rel a b h => exact .rel _ _ h.erase
  | refl a => exact .refl _
  | symm a b h ih => exact .symm _ _ ih
  | trans a b c h h' ih ih' => exact .trans _ _ _ ih ih'
end Converts

namespace HasType
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M A : Expr S}
theorem erase (h : HasType P Γ M A) :
    PureTypeSystem.HasType P (Γ.map Expr.erase) M.erase A.erase := by
  induction h with
  | ax h => exact .ax h
  | var h ih => simpa only [List.map_cons, Expr.erase, Expr.erase_rename] using
      PureTypeSystem.HasType.var ih
  | weaken h hA ih ihA =>
      simpa only [List.map_cons, Expr.erase_rename] using PureTypeSystem.HasType.weaken ih ihA
  | product hA hB hr ihA ihB => exact .product ihA ihB hr
  | abstraction hb hPi ihb ihPi => exact .abstraction ihb ihPi
  | application hf ha ihf iha =>
      simpa only [Expr.erase, Expr.erase_instantiate] using PureTypeSystem.HasType.application ihf iha
  | conversion h hA hc ih ihA => exact .conversion ih ihA hc.erase
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

theorem beta {N : Expr S} (h : WellModed γ M m) (hr : Beta M N) : WellModed γ N m := by
  induction hr generalizing γ m with
  | head l A b a =>
      cases h with
      | app hf ha => cases hf with
        | lam hA hb => exact hb.instantiate ha
  | app_left hr ih => cases h with | app hf ha => exact .app (ih hf) ha
  | app_right hr ih => cases h with | app hf ha => exact .app hf (ih ha)
  | lam_domain hr ih => cases h with | lam hA hb => exact .lam (ih hA) hb
  | lam_body hr ih => cases h with | lam hA hb => exact .lam hA (ih hb)
  | pi_domain hr ih => cases h with | pi hA hB => exact .pi (ih hA) hB
  | pi_body hr ih => cases h with | pi hA hB => exact .pi hA (ih hB)

theorem reduces {N : Expr S} (h : WellModed γ M m) (hr : Reduces M N) : WellModed γ N m := by
  induction hr with
  | refl => exact h
  | tail _ hr ih => exact ih.beta hr
end WellModed

namespace Expr
variable {S : Type u}
theorem erase_lam_inv {M : Expr S} {D e : PureTypeSystem.Expr S}
    (h : M.erase = .lam D e) :
    ∃ l A b, M = .lam l A b ∧ A.erase = D ∧ b.erase = e := by
  cases M with
  | var n => cases h
  | sort s => cases h
  | app l f a => cases h
  | pi l A B => cases h
  | lam l A b =>
      have hh := PureTypeSystem.Expr.lam.inj h
      exact ⟨l, A, b, rfl, hh.1, hh.2⟩
end Expr

private theorem erased_app_step {S : Type u} {f a N : PureTypeSystem.Expr S}
    (h : PureTypeSystem.Beta (.app f a) N) :
    (∃ D b, f = .lam D b ∧ N = b.instantiate a) ∨
    (∃ f', PureTypeSystem.Beta f f' ∧ N = .app f' a) ∨
    (∃ a', PureTypeSystem.Beta a a' ∧ N = .app f a') := by
  cases h with
  | head D b a => exact .inl ⟨D, b, rfl, rfl⟩
  | app_left h => exact .inr (.inl ⟨_, h, rfl⟩)
  | app_right h => exact .inr (.inr ⟨_, h, rfl⟩)

namespace HasType
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M T : Expr S}

/-- Every erased redex of a typable labelled term has matching labels, even
inside its annotations. No weak or strong normalization is assumed. -/
theorem lift_erased_step (h : HasType P Γ M T) {N : PureTypeSystem.Expr S}
    (hr : PureTypeSystem.Beta M.erase N) :
    ∃ M', Beta M M' ∧ M'.erase = N := by
  induction M generalizing Γ T N with
  | var n => cases hr
  | sort s => cases hr
  | app l f a ihf iha =>
      obtain ⟨A, B, hf, ha, _⟩ := h.generation_app
      obtain ⟨D, b, he, rfl⟩ | ⟨f', hstep, rfl⟩ | ⟨a', hstep, rfl⟩ := erased_app_step hr
      · obtain ⟨k, D', b', rfl, _, hb'⟩ := Expr.erase_lam_inv he
        obtain ⟨B', _, _, _, hc⟩ := hf.generation_lam
        have hl := hc.product_compatibility.1
        subst k
        refine ⟨b'.instantiate a, .head l D' b' a, ?_⟩
        simp only [Expr.erase_instantiate, hb']
      · obtain ⟨g, hg, he⟩ := ihf hf hstep
        exact ⟨.app l g a, .app_left hg, by simp only [Expr.erase, he]⟩
      · obtain ⟨b, hb, he⟩ := iha ha hstep
        exact ⟨.app l f b, .app_right hb, by simp only [Expr.erase, he]⟩
  | lam l A b ihA ihb =>
      obtain ⟨B, _, hb, hPi, _⟩ := h.generation_lam
      obtain ⟨s, hA⟩ := hPi.product_domain _ _ _ rfl
      cases hr with
      | lam_domain hstep =>
          obtain ⟨D, hD, he⟩ := ihA hA hstep
          exact ⟨.lam l D b, .lam_domain hD, by simp only [Expr.erase, he]⟩
      | lam_body hstep =>
          obtain ⟨e, he, herase⟩ := ihb hb hstep
          exact ⟨.lam l A e, .lam_body he, by simp only [Expr.erase, herase]⟩
  | pi l A B ihA ihB =>
      obtain ⟨_, _, _, hA, hB, _, _⟩ := h.generation_pi
      cases hr with
      | pi_domain hstep =>
          obtain ⟨D, hD, he⟩ := ihA hA hstep
          exact ⟨.pi l D B, .pi_domain hD, by simp only [Expr.erase, he]⟩
      | pi_body hstep =>
          obtain ⟨E, hE, he⟩ := ihB hB hstep
          exact ⟨.pi l A E, .pi_body hE, by simp only [Expr.erase, he]⟩

theorem lift_erased_reduces (h : HasType P Γ M T) {N : PureTypeSystem.Expr S}
    (hr : PureTypeSystem.Reduces M.erase N) :
    ∃ M', Reduces M M' ∧ M'.erase = N ∧ HasType P Γ M' T := by
  induction hr with
  | refl => exact ⟨M, .refl, rfl, h⟩
  | tail hred hstep ih =>
      obtain ⟨M', hMM', he, ht⟩ := ih
      obtain ⟨M'', hM'M'', he'⟩ := ht.lift_erased_step (he ▸ hstep)
      exact ⟨M'', hMM'.tail hM'M'', he', ht.subject_reduction hM'M''⟩

/-- The exact final interface of the labelled-metatheory lemma. -/
theorem normal_erasure_reduct (h : HasType P Γ M T) {γ : Nat → Mode} {m : Mode}
    (hm : WellModed γ M m) (hw : PureTypeSystem.WeaklyNormalizing M.erase) :
    ∃ M', Reduces M M' ∧ HasType P Γ M' T ∧ WellModed γ M' m ∧
      PureTypeSystem.Normal M'.erase := by
  obtain ⟨N, hr, hn⟩ := hw
  obtain ⟨M', hMM', he, ht⟩ := h.lift_erased_reduces hr
  exact ⟨M', hMM', ht, hm.reduces hMM', he.symm ▸ hn⟩
end HasType

namespace Expr
variable {S : Type u}

namespace Positive
theorem rename {M : Expr S} (h : Positive M) (ρ : Nat → Nat) : Positive (M.rename ρ) := by
  induction h generalizing ρ with
  | terminal h => exact .terminal (h.rename ρ)
  | step D h ih => exact .step _ (ih _)

theorem not_pp {A B : Expr S} : ¬ Positive (.pi .pp A B) := by
  intro h
  cases h with
  | terminal h => cases h

theorem dp_body {A B : Expr S} (h : Positive (.pi .dp A B)) : Positive B := by
  cases h with
  | terminal h => cases h
  | step A h => exact h
end Positive

namespace Target
theorem rename {T : Expr S} (h : Target T) (ρ : Nat → Nat) : Target (T.rename ρ) :=
  ⟨h.1.rename ρ, by simpa only [erase_rename] using h.2.rename ρ⟩

theorem normal {T : Expr S} (h : Target T) : Normal T :=
  fun N hN => h.2 N.erase hN.erase

theorem product {l : Label} {A B T : Expr S} (h : Target T)
    (hl : l.result = .proof) (hc : Converts (.pi l A B) T) :
    l = .dp ∧ ∃ D E, T = .pi .dp D E ∧ Target E ∧ Converts A D ∧ Converts B E := by
  obtain ⟨N, hPi, hT⟩ := hc.join
  obtain ⟨D, E, hDE, hA, hB⟩ := hPi.pi_inv
  have he : T = .pi l D E := (h.normal.reduces_eq hT).trans hDE
  subst T
  cases l with
  | dd => cases hl
  | pp => exact False.elim (Positive.not_pp h.1)
  | dp =>
      exact ⟨rfl, D, E, rfl, ⟨h.1.dp_body, h.2.pi_body⟩, hA.converts, hB.converts⟩
end Target

end Expr

namespace WellModed
variable {S : Type u} {γ : Nat → Mode} {m : Mode}
theorem var_inv {n} (h : WellModed (S := S) γ (.var n) m) : γ n = m := by
  cases h; rfl

theorem app_inv {l f a} (h : WellModed (S := S) γ (.app l f a) m) :
    l.result = m ∧ WellModed γ f l.result ∧ WellModed γ a l.domain := by
  cases h; exact ⟨rfl, ‹_›, ‹_›⟩

theorem lam_inv {l A b} (h : WellModed (S := S) γ (.lam l A b) m) :
    l.result = m ∧ WellModed γ A .data ∧ WellModed (modeCons l.domain γ) b l.result := by
  cases h; exact ⟨rfl, ‹_›, ‹_›⟩

/-- A normal-erasure proof has a lambda at the root or a variable-headed spine. -/
theorem normal_proof_shape {M : Expr S} (h : WellModed γ M .proof)
    (hn : PureTypeSystem.Normal M.erase) :
    (∃ l A b, M = .lam l A b) ∨ M.Neutral := by
  induction M generalizing γ with
  | var n => exact .inr (.var n)
  | sort s => cases h
  | pi l A B ihA ihB => cases h
  | lam l A b ihA ihb => exact .inl ⟨_, _, _, rfl⟩
  | app l f a ihf iha =>
      obtain ⟨hl, hf, _⟩ := h.app_inv
      obtain ⟨k, A, b, rfl⟩ | hf' := ihf (hl ▸ hf) hn.app_left
      · exact False.elim (hn _ (.head A.erase b.erase a.erase))
      · exact .inr (.app hf')
end WellModed

namespace ProofContext
variable {S : Type u} {Γ : List (Expr S)} {γ : Nat → Mode}
theorem data_cons (h : ProofContext Γ γ) (D : Expr S) :
    ProofContext (D :: Γ) (modeCons .data γ) := by
  intro n A hn hm
  cases hn with
  | zero => cases hm
  | succ D hn =>
      obtain ⟨R, F, rfl, hR⟩ := h _ _ hn hm
      exact ⟨R.rename Nat.succ, F.rename (Expr.liftRen Nat.succ), rfl, hR.rename _⟩
end ProofContext

namespace Expr.Neutral
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {γ : Nat → Mode}
    {M T : Expr S}

/-- The first argument of a normal proof-mode converter spine is itself a
strictly smaller normal proof at a positive target. -/
theorem first_target (hM : M.Neutral) (h : HasType P Γ M T)
    (hm : WellModed γ M .proof) (hn : PureTypeSystem.Normal M.erase)
    (hΓ : ProofContext Γ γ) :
    (∃ n, M = .var n) ∨
    ∃ Q R, Q.weight < M.weight ∧ R.Target ∧ HasType P Γ Q R ∧
      WellModed γ Q .proof ∧ PureTypeSystem.Normal Q.erase := by
  induction hM generalizing T with
  | var n => exact .inl ⟨n, rfl⟩
  | @app l f a hM ih =>
      obtain ⟨D, E, hf, ha, _⟩ := h.generation_app
      obtain ⟨hl, hmf, hma⟩ := hm.app_inv
      have hmf' : WellModed γ f .proof := hl ▸ hmf
      obtain ⟨n, rfl⟩ | ⟨Q, R, hQ, hR, hQR, hmode, hnorm⟩ := ih hf hmf' hn.app_left
      · obtain ⟨A, hlookup, hc⟩ := hf.generation
        obtain ⟨R, F, rfl, hR⟩ := hΓ n A hlookup hmf'.var_inv
        obtain ⟨rfl, hDR, _⟩ := hc.product_compatibility
        obtain ⟨r, hPi⟩ := (HasType.lookup h.valid hlookup).product_type_sorted
        obtain ⟨s, hs⟩ := hPi.product_domain _ _ _ rfl
        exact .inr ⟨a, R, by simp only [weight]; omega, hR,
          .conversion ha hs hDR, hma, hn.app_right⟩
      · exact .inr ⟨Q, R, by simp only [weight]; omega, hR, hQR, hmode, hnorm⟩
end Expr.Neutral

/-- No normal erasure at a terminal. The stronger form allows a dependent
positive telescope: it uses only the outer labels, normality, typing and
the decreasing body/first-argument syntax measure. -/
theorem no_normal_proof {S : Type u} {P : Specification S}
    {Γ : List (Expr S)} {γ : Nat → Mode} {M T : Expr S}
    (hΓ : ProofContext Γ γ) (hT : T.Target) (h : HasType P Γ M T)
    (hm : WellModed γ M .proof) (hn : PureTypeSystem.Normal M.erase) : False := by
  induction M using (measure Expr.weight).wf.induction generalizing Γ γ T with
  | h M ih =>
      obtain ⟨l, A, b, rfl⟩ | hneutral := hm.normal_proof_shape hn
      · obtain ⟨B, s, hb, hPi, hc⟩ := h.generation_lam
        obtain ⟨hl, _, hmb⟩ := hm.lam_inv
        obtain ⟨rfl, D, E, rfl, hE, hAD, hBE⟩ := hT.product hl (.symm _ _ hc)
        obtain ⟨r, hTsort⟩ := h.abstraction_type_sorted
        obtain ⟨_, _, _, hD, hEopen, _, _⟩ := hTsort.generation_pi
        obtain ⟨_, hA⟩ := hPi.product_domain _ _ _ rfl
        have hEsort := hEopen.context_head_conversion hD hA (.symm _ _ hAD)
        have hbody := HasType.conversion hb hEsort hBE
        exact ih b (by change b.weight < 1 + A.weight + b.weight; omega)
          (hΓ.data_cons A) hE hbody hmb hn.lam_body
      · obtain ⟨n, rfl⟩ | ⟨Q, R, hQ, hR, hQR, hmode, hnorm⟩ :=
          hneutral.first_target h hm hn hΓ
        · obtain ⟨A, hlookup, hc⟩ := h.generation
          obtain ⟨R, F, rfl, _⟩ := hΓ n A hlookup hm.var_inv
          have hl := (hT.product rfl (.symm _ _ hc)).1
          cases hl
        · exact ih Q hQ hΓ hR hQR hmode hnorm

/-- A system-wide WN PTS has no proof-mode inhabitant of these targets in
these converter contexts. All later encodings must supply a genuine typing
and mode derivation to invoke this obstruction. -/
theorem no_proof_at_target {S : Type u} {P : Specification S}
    (hw : SystemWeaklyNormalizing P) {Γ : List (Expr S)} {γ : Nat → Mode} {M T : Expr S}
    (hΓ : ProofContext Γ γ) (hT : T.Target) (h : HasType P Γ M T)
    (hm : WellModed γ M .proof) : False := by
  obtain ⟨M', _, ht, hmode, hnorm⟩ := h.normal_erasure_reduct hm (h.erase.weaklyNormalizing hw)
  exact no_normal_proof hΓ hT ht hmode hnorm

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
namespace PureTypeSystem

namespace SignedPath
variable {V : Type*} {E : V → V → Bool → Prop}

/-- Any odd walk has a negative edge with an even remaining suffix. -/
theorem negative_even_suffix {v w : V} (h : SignedPath E v w true) :
    ∃ p g, Reach E v p ∧ E p g true ∧ SignedPath E g w false := by
  generalize hq : true = q at h
  induction h with
  | nil v => cases hq
  | @cons u v w p q he ht ih =>
      cases p <;> cases q
      · cases hq
      · obtain ⟨p, g, hp, he', hg⟩ := ih rfl
        exact ⟨p, g, (Reach.single he).trans hp, he', hg⟩
      · exact ⟨u, v, Reach.refl u, he, ht⟩
      · cases hq

/-- Restrict a finite walk when all of its intermediate points lie in a set. -/
theorem restrict {C : Set V} {v w : V} {p : Bool}
    (h : SignedPath E v w p) (hv : v ∈ C)
    (hi : ∀ z, Reach E v z → Reach E z w → z ∈ C) :
    SignedPath (fun x y p => E x y p ∧ x ∈ C ∧ y ∈ C) v w p := by
  induction h with
  | nil v => exact .nil _
  | @cons u v w p q he ht ih =>
      have hv' := hi v (Reach.single he) ⟨q, ht⟩
      exact .cons ⟨he, hv, hv'⟩ (ih hv' (fun z hz hzw =>
        hi z ((Reach.single he).trans hz) hzw))
end SignedPath

namespace IsComponent
variable {V : Type*} {E : V → V → Bool → Prop} {C : Set V}

/-- An odd closed walk in an SCC supplies both parities between all vertices. -/
theorem all_parities (hC : IsComponent E C) {r v w : V}
    (hr : r ∈ C) (ho : SignedPath E r r true) (hv : v ∈ C) (hw : w ∈ C)
    (b : Bool) : SignedPath E v w b := by
  obtain ⟨p, hp⟩ := hC.connected hv hr
  obtain ⟨q, hq⟩ := hC.connected hr hw
  have h₀ := hp.append hq
  have h₁ := (hp.append ho).append hq
  cases p <;> cases q <;> cases b <;> first | exact h₀ | exact h₁

theorem restrict_path (hC : IsComponent E C) {v w : V} {b : Bool}
    (hv : v ∈ C) (hw : w ∈ C) (hp : SignedPath E v w b) :
    SignedPath (fun x y p => E x y p ∧ x ∈ C ∧ y ∈ C) v w b :=
  hp.restrict hv (fun _ hz hzw => hC.between hv hw hz hzw)

/-- No odd cycle makes the return parity uniquely determined by the outward one. -/
theorem return_parity (hC : IsComponent E C) {v w : V} {b : Bool}
    (hv : v ∈ C) (hw : w ∈ C) (hp : SignedPath E v w b)
    (ho : ¬ SignedPath E v v true) : SignedPath E w v b := by
  obtain ⟨q, hq⟩ := hC.connected hw hv
  have hc := hp.append hq
  cases b <;> cases q <;> first | exact hq | exact False.elim (ho hc)

/-- The three internal path roles needed by the first data channel, without
assuming that the secondary component itself has an odd cycle. -/
theorem negative_routes (hC : IsComponent E C) {J k : V}
    (hJ : J ∈ C) (hk : k ∈ C) (hJk : E J k false)
    (hn : ∃ a ∈ C, ∃ b ∈ C, E a b true) :
    ∃ p ∈ C, ∃ g ∈ C, E p g true ∧ SignedPath E k p true ∧
      SignedPath E p k true ∧ SignedPath E g J false := by
  classical
  by_cases ho : ∃ r ∈ C, SignedPath E r r true
  · obtain ⟨r, hr, ho⟩ := ho
    obtain ⟨p, hp, g, hg, he⟩ := hn
    exact ⟨p, hp, g, hg, he, hC.all_parities hr ho hk hp true,
      hC.all_parities hr ho hp hk true, hC.all_parities hr ho hg hJ false⟩
  · have no_odd (r : V) (hr : r ∈ C) : ¬ SignedPath E r r true :=
      fun hh => ho ⟨r, hr, hh⟩
    obtain ⟨a, ha, b, hb, he⟩ := hn
    obtain ⟨q, hbk⟩ := hC.connected hb hk
    have hedge : ∃ p ∈ C, ∃ g ∈ C, E p g true ∧ SignedPath E g k false := by
      cases q with
      | false => exact ⟨a, ha, b, hb, he, hbk⟩
      | true =>
          obtain ⟨p, g, hbp, hpg, hgk⟩ := hbk.negative_even_suffix
          have hp := hC.between hb hk hbp ((Reach.single hpg).trans ⟨false, hgk⟩)
          have hg := hC.between hb hk (hbp.trans (Reach.single hpg)) ⟨false, hgk⟩
          exact ⟨p, hp, g, hg, hpg, hgk⟩
    obtain ⟨p, hp, g, hg, hpg, hgk⟩ := hedge
    have hpk : SignedPath E p k true := .cons hpg hgk
    have hkp := hC.return_parity hp hk hpk (no_odd p hp)
    have hkJ := hC.return_parity hJ hk (.singleton hJk) (no_odd J hJ)
    exact ⟨p, hp, g, hg, hpg, hkp, hpk, hgk.append hkJ⟩
end IsComponent

namespace ForbiddenConfiguration
universe u
variable {S : Type u} {P : Specification S} {C : Set (Set S)}

/-- Source choice-of-paths conclusion, retaining the actual triples and all
profile and seed hypotheses of the forbidden configuration. -/
theorem channel_paths (h : ForbiddenConfiguration P C) :
    ∃ D : Set (Set S), IsComponent (SecondaryEdge P C) D ∧
    ∃ I J k s p n g j h',
      ProfileTriple P I J k ∧ J ∈ D ∧ k ∈ D ∧ ({s} : Set S) ∈ D ∧
      (AxProfile P s).Nonempty ∧ PositivePath (PrimaryEdge P) (AxProfile P s) I ∧
      ProfileTriple P p n g ∧ p ∈ D ∧ g ∈ D ∧ n ∈ ObservationLayers P C ∧
      SignedPath (SecondaryEdge P C) k p true ∧
      SignedPath (SecondaryEdge P C) p k true ∧
      SignedPath (SecondaryEdge P C) g J false ∧
      DirectLayer P C j ∧ SignedPath (SecondaryEdge P C) k j true ∧
      DirectLayer P C h' ∧ SignedPath (SecondaryEdge P C) k h' false ∧
      SignedPath (SecondaryEdge P C) p h' true := by
  obtain ⟨D, hD, hplain, hneg, I, J, k, s, hI, hJ, hk, hs, hax, hpath⟩ := h
  have path_layer {T A : Set S} {b : Bool}
      (hp : SignedPath (SecondaryEdge P C) T A b) (hA : A ∈ ObservationLayers P C) :
      T ∈ ObservationLayers P C := by
    cases hp with
    | nil => exact hA
    | cons he ht => cases he with
      | positive hsrc _ _ => exact hsrc
      | negative hsrc _ _ _ => exact hsrc
  have layer_of_plain {T : Set S} (ht : PlainLayer P C T) : T ∈ ObservationLayers P C := by
    obtain ⟨A, hA, hp⟩ := ht.1
    exact path_layer hp hA.1
  have hJ' := layer_of_plain (hplain J hJ)
  have hk' := layer_of_plain (hplain k hk)
  have hJk : SecondaryEdge P C J k false := .positive hJ' hk' (.codomain hI)
  obtain ⟨p, hp, g, hg, he, hkp, hpk, hgJ⟩ := hD.negative_routes hJ hk hJk hneg
  cases he with
  | negative _ hn _ htr =>
      obtain ⟨⟨h', hh', hkh'⟩, ⟨j, hj, hkj⟩⟩ := hplain k hk
      exact ⟨D, hD, I, J, k, s, p, _, g, j, h', hI, hJ, hk, hs, hax, hpath,
        htr, hp, hg, hn, hkp, hpk, hgJ, hj, hkj, hh', hkh', hpk.append hkh'⟩
end ForbiddenConfiguration

end PureTypeSystem

namespace PureTypeSystem.Labelled

section
universe u
open Classical

namespace ProofContext
variable {S : Type u} {Γ : List (Expr S)} {γ : Nat → Mode}
theorem proof_cons (h : ProofContext Γ γ) {T F : Expr S} (hT : T.Target) :
    ProofContext (Expr.arrow .pp T F :: Γ) (modeCons .proof γ) := by
  intro n A hn hm
  cases hn with
  | zero => exact ⟨_,_,rfl,hT.rename _⟩
  | succ C hn =>
    obtain ⟨R,F,rfl,hR⟩ := h _ _ hn hm
    exact ⟨_,_,rfl,hR.rename _⟩
end ProofContext

namespace Expr
variable {S : Type u}
theorem AllData.wellModed {M : Expr S} (h : M.AllData) :
    WellModed (fun _ => .data) M .data := by
  have he : modeCons .data (fun _ => Mode.data) = fun _ => Mode.data := by
    funext n; cases n <;> rfl
  induction h with
  | var n => exact .var n
  | sort s => exact .sort s
  | app hf ha ihf iha => exact .app ihf iha
  | lam hA hb ihA ihb => apply WellModed.lam ihA; simpa only [Label.domain,Label.result,he] using ihb
  | pi hA hB ihA ihB => apply WellModed.pi ihA; simpa only [Label.domain,he] using ihB

theorem Target.arrow {D T : Expr S} (hT : T.Target)
    (hD : PureTypeSystem.Normal D.erase) : (Expr.arrow .dp D T).Target := by
  refine ⟨.step _ (hT.1.rename _),?_⟩
  exact hD.pi (by simpa only [erase_rename] using hT.2.rename Nat.succ)
end Expr

namespace WitnessFamily
variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)} {γ δ : Nat → Mode}

theorem exists_family [Fintype S] : ∃ Γ, ValidContext P Γ ∧
    Nonempty (WitnessFamily P Γ (fun _ => .data)) := by
  let F : Finset (Set S) := Finset.univ.filter (FeasibleProfile P)
  let W := DataWitnessContext.ofFeasible F (by simp only [F,Finset.mem_filter]; tauto)
  have hw (I : Set S) (hI : FeasibleProfile P I) : ∃ T e : Expr S, T.AllData ∧ e.AllData ∧
      PureTypeSystem.Normal T.erase ∧ SortedAt P W.context T I ∧ HasType P W.context e T :=
    W.witness I (by simp [F,hI])
  let ty (I : Set S) : Expr S := if hi : FeasibleProfile P I then (hw I hi).choose else .var 0
  let val (I : Set S) : Expr S := if hi : FeasibleProfile P I then
    (hw I hi).choose_spec.choose else .var 0
  have hp (I : Set S) (hI : FeasibleProfile P I) :
      (ty I).AllData ∧ (val I).AllData ∧ PureTypeSystem.Normal (ty I).erase ∧
      SortedAt P W.context (ty I) I ∧ HasType P W.context (val I) (ty I) := by
    simpa only [ty,val,dite_eq_left hI] using (hw I hI).choose_spec.choose_spec
  exact ⟨W.context,W.valid,⟨⟨ty,val,fun I hi => (hp I hi).1,
    fun I hi => (hp I hi).2.2.1,fun I hi => (hp I hi).2.2.2.1,
    fun I hi => (hp I hi).2.2.2.2,fun I hi => (hp I hi).1.wellModed,
    fun I hi => (hp I hi).2.1.wellModed⟩⟩⟩
end WitnessFamily

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

theorem positive (hA : HasType P Γ A (.sort s)) (hD : HasType P Γ D (.sort t))
    (hr : P.rule t s r) (hDm : WellModed γ D .data) :
    Transfer P Γ γ A (Expr.arrow .dp D A) := by
  refine ⟨Expr.constLam .dp (D.rename Nat.succ) (.var 0),?_,?_⟩
  · have hpi : HasType P (A :: Γ) (Expr.arrow .dp (D.rename Nat.succ) (A.rename Nat.succ)) (.sort r) := by
      simpa only [Expr.arrow_rename,Expr.rename] using HasType.weaken (hD.arrow (l := .dp) hA hr) hA
    simpa only [Expr.arrow_rename] using
      HasType.constLam (.var hA) (.weaken hD hA) hpi
  · exact (hDm.raise .proof).constLam (.var 0)

/-- The declared converter is inserted before, not after, the temporary input. -/
theorem converter (hC : HasType P Γ (Expr.arrow .pp A B) (.sort r))
    (hA : HasType P Γ A (.sort s)) :
    Transfer P (Expr.arrow .pp A B :: Γ) (modeCons .proof γ)
      (A.rename Nat.succ) (B.rename Nat.succ) := by
  let hA' := HasType.weaken hA hC
  have hc := HasType.weaken (HasType.var hC) hA'
  have hx := HasType.var hA'
  refine ⟨.app .pp (.var 1) (.var 0),?_,.app (.var 1) (.var 0)⟩
  simp only [Expr.arrow_rename,Expr.rename] at hc
  exact HasType.apply_arrow hc hx
end Transfer

end

universe u
open Classical
variable {S : Type u} {P : Specification S}

theorem edge_profiles {I J : Set S} {b : Bool} (he : PrimaryEdge P I J b) :
    FeasibleProfile P I ∧ FeasibleProfile P J := by
  cases he with
  | inclusion hi hj _ => exact ⟨hi,hj⟩
  | domain h => exact ⟨h.domain,h.product⟩
  | codomain h => exact ⟨h.codomain,h.product⟩

namespace WitnessFamily
variable {Γ : List (Expr S)} {γ : Nat → Mode} (W : WitnessFamily P Γ γ)
    {T : Expr S} {I J : Set S}

include W in
theorem carry_edge (hv : ValidContext P Γ) (hc : ProofContext Γ γ)
    (hT : T.Target) (hm : WellModed γ T .data) (ht : SortedAt P Γ T I)
    {b : Bool} (he : PrimaryEdge P I J b) : Carries (P := P) Γ γ T J := by
  cases he with
  | inclusion hi hj hij =>
    obtain ⟨s,hs⟩ := hi.1
    refine ⟨Γ,γ,Embedding.refl hv γ,hc,T,hT,hm,ht.mono hij.1,?_⟩
    simpa only [Embedding.refl,Expr.rename_id] using Transfer.refl (γ := γ) (ht s hs)
  | @codomain A B C htr =>
    obtain ⟨r,hr⟩ := htr.product.1
    obtain ⟨a,ha,b,hb,hab⟩ := htr.output ▸ hr
    let D := W.type A
    have hD : SortedAt P Γ D A := W.sorted A htr.domain
    have hU : SortedAt P Γ (Expr.arrow .dp D T) J := hD.arrow ht .dp (by rw [htr.output])
    refine ⟨Γ,γ,Embedding.refl hv γ,hc,Expr.arrow .dp D T,
      hT.arrow (W.normal A htr.domain), (W.type_mode A htr.domain).arrow hm,hU,?_⟩
    simpa only [Embedding.refl,Expr.rename_id] using
      Transfer.positive (ht b hb) (hD a ha) hab (W.type_mode A htr.domain)
  | @domain A B C htr =>
    obtain ⟨r,hr⟩ := htr.product.1
    obtain ⟨a,ha,b,hb,hab⟩ := htr.output ▸ hr
    let F := W.type B
    have hF : SortedAt P Γ F B := W.sorted B htr.codomain
    have hConv : HasType P Γ (Expr.arrow .pp T F) (.sort r) := (ht a ha).arrow (hF b hb) hab
    let e : Embedding P Γ γ (Expr.arrow .pp T F :: Γ) (modeCons .proof γ) := Embedding.cons hConv .proof
    let W' := W.rename e
    let D := W'.type I
    let F' := W'.type B
    have hD : SortedAt P (Expr.arrow .pp T F :: Γ) D I := W'.sorted I htr.domain
    have hF' : SortedAt P (Expr.arrow .pp T F :: Γ) F' B := W'.sorted B htr.codomain
    have hU : SortedAt P (Expr.arrow .pp T F :: Γ) (Expr.arrow .dp D F') J :=
      hD.arrow hF' .dp (by rw [htr.output])
    have hFT : F'.Target := ⟨.terminal (W'.allData B htr.codomain), W'.normal B htr.codomain⟩
    refine ⟨_,_,e,hc.proof_cons hT,Expr.arrow .dp D F',hFT.arrow (W'.normal I htr.domain),
      (W'.type_mode I htr.domain).arrow (W'.type_mode B htr.codomain),hU,?_⟩
    exact (Transfer.converter hConv (ht a ha)).trans
      (Transfer.positive (hF' b hb) (hD a ha) hab (W'.type_mode I htr.domain))
      (e.typing (ht a ha)) (hF' b hb)

include W in
/-- Each negative edge resets the carried type to a fixed terminal, and is
followed by its own positive lift. Thus every converter domain stays positive. -/
theorem carry_path {b : Bool} (hp : SignedPath (PrimaryEdge P) I J b)
    (hI : FeasibleProfile P I) (hv : ValidContext P Γ) (hc : ProofContext Γ γ)
    (hT : T.Target) (hm : WellModed γ T .data) (ht : SortedAt P Γ T I) :
    Carries (P := P) Γ γ T J := by
  induction hp generalizing Γ γ T with
  | nil I =>
    obtain ⟨s,hs⟩ := hI.1
    refine ⟨Γ,γ,Embedding.refl hv γ,hc,T,hT,hm,ht,?_⟩
    simpa only [Embedding.refl,Expr.rename_id] using Transfer.refl (γ := γ) (ht s hs)
  | @cons I J K b c he hp ih =>
    obtain ⟨Δ,δ,e,hΔ,U,hU,mU,tU,tr⟩ := W.carry_edge hv hc hT hm ht he
    obtain ⟨Θ,θ,f,hΘ,V,hV,mV,tV,tr'⟩ := ih (W.rename e) (edge_profiles he).2 e.valid hΔ hU mU tU
    obtain ⟨s,hs⟩ := hI.1
    obtain ⟨t,ht'⟩ := (edge_profiles he).2.1
    have htr := (tr.rename f (e.typing (ht s hs))).trans tr'
      (f.typing (e.typing (ht s hs))) (f.typing (tU t ht'))
    refine ⟨Θ,θ,e.comp f,hΘ,V,hV,mV,tV,?_⟩
    simpa only [Embedding.comp,Expr.rename_comp] using htr

/-- Terminal-converter existence. Both terminal types are the original,
fixed witnesses; only legal renaming is applied. -/
theorem terminal_transfer {C : Set (Set S)} (hC : IsComponent (PrimaryEdge P) C)
    {I₁ J₁ K₁ I₂ J₂ K₂ : Set S}
    (h₁ : ProfileTriple P I₁ J₁ K₁) (hk₁ : K₁ ∈ C)
    (h₂ : ProfileTriple P I₂ J₂ K₂) (hi₂ : I₂ ∈ C)
    (hv : ValidContext P Γ) (hc : ProofContext Γ γ) :
    ∃ Δ δ, ∃ e : Embedding P Γ γ Δ δ, ProofContext Δ δ ∧
      Transfer P Δ δ ((W.type J₁).rename e.names) ((W.type J₂).rename e.names) := by
  obtain ⟨b,hp⟩ := hC.connected hk₁ hi₂
  have route := SignedPath.cons (PrimaryEdge.codomain h₁) hp
  obtain ⟨Δ,δ,e,hΔ,U,hU,_mU,tU,tr⟩ := W.carry_path route h₁.codomain hv hc
    ⟨.terminal (W.allData J₁ h₁.codomain),W.normal J₁ h₁.codomain⟩
    (W.type_mode J₁ h₁.codomain) (W.sorted J₁ h₁.codomain)
  let W' := W.rename e
  obtain ⟨r,hr⟩ := h₂.product.1
  obtain ⟨a,ha,b,hb,hab⟩ := h₂.output ▸ hr
  have hF := W'.sorted J₂ h₂.codomain
  have hConv := (tU a ha).arrow (l := .pp) (hF b hb) hab
  let f : Embedding P Δ δ (Expr.arrow .pp U (W'.type J₂) :: Δ) (modeCons .proof δ) :=
    Embedding.cons hConv .proof
  obtain ⟨s,hs⟩ := h₁.codomain.1
  have hA := e.typing (W.sorted J₁ h₁.codomain s hs)
  have out := (tr.rename f hA).trans (Transfer.converter hConv (tU a ha))
    (f.typing hA) (f.typing (tU a ha))
  refine ⟨_,_,e.comp f,hΔ.proof_cons hU,?_⟩
  simpa only [Embedding.comp,W',WitnessFamily.rename,Expr.rename_comp,f,Embedding.cons] using out
end WitnessFamily

namespace WitnessFamily
variable {Γ : List (Expr S)} {γ : Nat → Mode} (W : WitnessFamily P Γ γ)
    {C : Set (Set S)}

/-- Previously constructed routes survive every new converter declaration. The
finite induction performs all context extensions before any logical input. -/
theorem finite_terminal_network (hC : IsComponent (PrimaryEdge P) C)
    (F : Finset (Set S × Set S))
    (hF : ∀ q ∈ F, TerminalProfile P C q.1 ∧ TerminalProfile P C q.2)
    (hv : ValidContext P Γ) (hc : ProofContext Γ γ) :
    ∃ Δ δ, ∃ e : Embedding P Γ γ Δ δ, ProofContext Δ δ ∧
      ∀ q ∈ F, Transfer P Δ δ ((W.type q.1).rename e.names) ((W.type q.2).rename e.names) := by
  induction F using Finset.induction_on generalizing Γ γ with
  | empty => exact ⟨Γ,γ,Embedding.refl hv γ,hc,by simp⟩
  | @insert a F han ih =>
    obtain ⟨ha₁,ha₂⟩ := hF a (Finset.mem_insert_self _ _)
    obtain ⟨Δ,δ,e,hΔ,hs⟩ := ih W (fun q hq => hF q (Finset.mem_insert_of_mem hq)) hv hc
    obtain ⟨I₁,K₁,h₁,_hi₁,hk₁⟩ := ha₁
    obtain ⟨I₂,K₂,h₂,hi₂,_hk₂⟩ := ha₂
    obtain ⟨Θ,θ,f,hΘ,hnew⟩ := (W.rename e).terminal_transfer hC h₁ hk₁ h₂ hi₂ e.valid hΔ
    refine ⟨Θ,θ,e.comp f,hΘ,?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · simpa only [Embedding.comp,WitnessFamily.rename,Expr.rename_comp] using hnew
    · obtain ⟨s,hsort⟩ := (hF q (Finset.mem_insert_of_mem hq)).1.feasible.1
      have ht := (hs q hq).rename f (e.typing (W.sorted q.1
        (hF q (Finset.mem_insert_of_mem hq)).1.feasible s hsort))
      simpa only [Embedding.comp,Expr.rename_comp] using ht

/-- One fixed finite legal context has every pairwise terminal transfer. -/
theorem terminal_network [Fintype S] (hC : IsComponent (PrimaryEdge P) C)
    (hv : ValidContext P Γ) (hc : ProofContext Γ γ) :
    ∃ Δ δ, ∃ e : Embedding P Γ γ Δ δ, ProofContext Δ δ ∧
      ∀ J J', TerminalProfile P C J → TerminalProfile P C J' →
        Transfer P Δ δ ((W.type J).rename e.names) ((W.type J').rename e.names) := by
  let F : Finset (Set S × Set S) := Finset.univ.filter
    (fun q => TerminalProfile P C q.1 ∧ TerminalProfile P C q.2)
  obtain ⟨Δ,δ,e,hΔ,hs⟩ := W.finite_terminal_network hC F
    (fun q hq => (Finset.mem_filter.mp hq).2) hv hc
  exact ⟨Δ,δ,e,hΔ,fun J J' hJ hJ' => hs (J,J') (by simp [F,hJ,hJ'])⟩
end WitnessFamily

namespace StableExtraction
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {W : WitnessFamily P Γ γ}
    {C : Set (Set S)} {Q A B : Expr S} {s t : S}

theorem terminal {J : Set S} (hJ : TerminalProfile P C J) : StableExtraction W C (W.type J) := by
  intro Δ δ e hk
  obtain ⟨s,hs⟩ := hJ.feasible.1
  have hF := e.typing (W.sorted J hJ.feasible s hs)
  have ht : Transfer P Δ δ ((W.type J).rename e.names) ((W.type J).rename e.names) := .refl hF
  have hr := hk Δ δ (Embedding.refl e.valid δ) J hJ
  simpa only [WitnessFamily.rename,Embedding.refl,Expr.rename_id] using hr (by
    simpa only [WitnessFamily.rename,Embedding.refl,Expr.rename_id] using ht)

end StableExtraction

namespace ProofWrapper

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {W : WitnessFamily P Γ γ}
    {C : Set (Set S)} {I J K : Set S} {a b : Bool} {R : ProofWrapper S}

theorem edge (h : Formed W C I J a R) (he : PrimaryEdge P J K b) (hJ : J ∈ C) (hK : K ∈ C) :
    ∃ R', Formed W C I K (Bool.xor a b) R' := by
  cases he with
  | inclusion hJ' hK' hsub => simpa only [Bool.xor_false] using Exists.intro R (h.inclusion hsub.1)
  | domain ht => simpa only [Bool.xor_true] using Exists.intro _ (h.negative ht hJ hK)
  | codomain ht => simpa only [Bool.xor_false] using Exists.intro _ (h.positive ht)

theorem path (h : Formed W C I J a R)
    (hp : SignedPath (fun x y s => PrimaryEdge P x y s ∧ x ∈ C ∧ y ∈ C) J K b) :
    ∃ R', Formed W C I K (Bool.xor a b) R' := by
  induction hp generalizing a R with
  | nil _ => simpa only [Bool.xor_false] using Exists.intro R h
  | @cons J K L b c he hp ih =>
    obtain ⟨R',hr⟩ := h.edge he.1 he.2.1 he.2.2
    obtain ⟨R'',hr'⟩ := ih hr
    exact ⟨R'',by simpa only [Bool.xor_assoc] using hr'⟩

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

namespace ProofWrapper.Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} (W : WitnessFamily P Γ γ)
    {C : Set (Set S)} {I J : Set S} {b : Bool}
theorem of_path (hC : IsComponent (PrimaryEdge P) C) (hI : I ∈ C) (hJ : J ∈ C)
    (hp : SignedPath (PrimaryEdge P) I J b) : ∃ R, Formed W C I J b R := by
  obtain ⟨R,hr⟩ := (Formed.identity (W := W) (C := C) (I := I)).path (hC.restrict_path hI hJ hp)
  exact ⟨R,by simpa only [Bool.false_xor] using hr⟩
end ProofWrapper.Formed

namespace QuantifierRoute
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {W : WitnessFamily P Γ γ}
    {C : Set (Set S)} {b I : Set S}

theorem exists_route (hC : IsComponent (PrimaryEdge P) C)
    {r : Set S} (hr : r ∈ C) (ho : SignedPath (PrimaryEdge P) r r true)
    (hb : b ∈ C) (hI : DirectLayer P C I) : Nonempty (QuantifierRoute W C b I) := by
  obtain ⟨J,hJ,K,hK,ht⟩ := hI.2
  obtain ⟨R,hR⟩ := ProofWrapper.Formed.of_path W hC hb hJ (hC.all_parities hr ho hb hJ false)
  obtain ⟨R',hR'⟩ := ProofWrapper.Formed.of_path W hC hK hb (hC.all_parities hr ho hK hb false)
  exact ⟨⟨J,K,ht,R,hR,R',hR'⟩⟩
end QuantifierRoute

namespace LogicSetup

section
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {C : Set (Set S)}

theorem terminal_base (L : LogicSetup P Γ γ C) : TerminalProfile P C L.base :=
  ⟨L.domain,L.product,L.triple,L.domain_mem,L.product_mem⟩

theorem bottom_formula (L : LogicSetup P Γ γ C) : L.Formula L.bottom :=
  ⟨L.witnesses.sorted L.base L.triple.codomain,L.witnesses.type_mode L.base L.triple.codomain,
    StableExtraction.terminal L.terminal_base⟩

/-- The ambient proof declarations are only the actual terminal converters, and
hence the no-normal-proof criterion applies to the eventual bottom inhabitant. -/
theorem exists_setup [Fintype S] (C : Set (Set S)) (hC : IsComponent (PrimaryEdge P) C)
    (ho : ∃ r ∈ C, SignedPath (PrimaryEdge P) r r true)
    (ht : ∃ I J K, ProfileTriple P I J K ∧ I ∈ C ∧ J ∈ C ∧ K ∈ C) :
    ∃ Γ γ, ProofContext Γ γ ∧ Nonempty (LogicSetup P Γ γ C) := by
  obtain ⟨Γ,hv,⟨W⟩⟩ := WitnessFamily.exists_family (P := P)
  have hc : ProofContext Γ (fun _ => .data) := by intro n A hn hm; cases hm
  obtain ⟨Δ,δ,e,hΔ,hτ⟩ := W.terminal_network hC hv hc
  let W' := W.rename e
  obtain ⟨r,hr,ho⟩ := ho
  obtain ⟨I,J,K,ht,hI,hJ,hK⟩ := ht
  obtain ⟨R,hR⟩ := ProofWrapper.Formed.of_path W' hC hJ hI (hC.all_parities hr ho hJ hI false)
  obtain ⟨R',hR'⟩ := ProofWrapper.Formed.of_path W' hC hK hJ (hC.all_parities hr ho hK hJ false)
  let qs (A : Set S) (hA : DirectLayer P C A) : QuantifierRoute W' C J A :=
    (QuantifierRoute.exists_route hC hr ho hJ hA).some
  exact ⟨Δ,δ,hΔ,⟨⟨W',hτ,J,I,K,ht,hI,hJ,hK,R,hR,R',hR',qs⟩⟩⟩

end

end LogicSetup
end

section
universe u
variable {S : Type u} {P : Specification S}

namespace ProofWrapper
variable {T T' : Expr S}

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {W : WitnessFamily P Γ γ}
    {C : Set (Set S)} {I J K : Set S} {a : Bool} {R : ProofWrapper S}
 theorem odd_negative (h : Formed W C I J a R) (ha : a = true) : R.containsNegative = true := by
  induction h with
  | identity => cases ha
  | inclusion h hh ih => exact ih ha
  | positive h ht ih => exact ih ha
  | negative h ht hi hk ih => rfl

 theorem edge_negative (h : Formed W C I J a R) (hn : R.containsNegative = true)
    {b : Bool} (he : PrimaryEdge P J K b) (hJ : J ∈ C) (hK : K ∈ C) :
    ∃ R', Formed W C I K (Bool.xor a b) R' ∧ R'.containsNegative = true := by
  cases he with
  | inclusion hJ' hK' hsub => exact ⟨R,by simpa only [Bool.xor_false] using h.inclusion hsub.1,hn⟩
  | domain ht => exact ⟨_,by simpa only [Bool.xor_true] using h.negative ht hJ hK,rfl⟩
  | codomain ht => exact ⟨_,by simpa only [Bool.xor_false] using h.positive ht,by simpa only [containsNegative] using hn⟩

 theorem path_negative (h : Formed W C I J a R) (hn : R.containsNegative = true)
    {b : Bool} (hp : SignedPath (fun x y s => PrimaryEdge P x y s ∧ x ∈ C ∧ y ∈ C) J K b) :
    ∃ R', Formed W C I K (Bool.xor a b) R' ∧ R'.containsNegative = true := by
  induction hp generalizing a R with
  | nil _ => exact ⟨R,by simpa only [Bool.xor_false] using h,hn⟩
  | @cons J K L b c he hp ih =>
    obtain ⟨R',hr,hn'⟩ := h.edge_negative hn he.1 he.2.1 he.2.2
    obtain ⟨R'',hr',hn''⟩ := ih hr hn'
    exact ⟨R'',by simpa only [Bool.xor_assoc] using hr',hn''⟩

 theorem exists_even_negative (hC : IsComponent (PrimaryEdge P) C)
    {r : Set S} (hr : r ∈ C) (ho : SignedPath (PrimaryEdge P) r r true) (hI : I ∈ C) (hJ : J ∈ C) :
    ∃ R, Formed W C I J false R ∧ R.containsNegative = true := by
  obtain ⟨R,hR⟩ := Formed.of_path W hC hI hJ (hC.all_parities hr ho hI hJ true)
  obtain ⟨R',hR',hn⟩ := hR.path_negative (hR.odd_negative rfl)
    (hC.restrict_path hJ hJ (hC.all_parities hr ho hJ hJ true))
  exact ⟨R',hR',hn⟩
end Formed
end ProofWrapper

namespace PositiveDataWrapper

theorem apply_rename (R : PositiveDataWrapper S) (T : Expr S) (ρ : Nat → Nat) :
    (R.apply T).rename ρ = (R.rename ρ).apply (T.rename ρ) := by
  induction R <;> simp_all only [apply,rename,Expr.arrow_rename]
namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {W : WitnessFamily P Γ γ}
    {I J K : Set S} {R : PositiveDataWrapper S}
theorem rename {Δ : List (Expr S)} {δ : Nat → Mode}
    (h : Formed W I J R) (e : Embedding P Γ γ Δ δ) : Formed (W.rename e) I J (R.rename e.names) := by
  induction h with
  | identity => exact .identity
  | inclusion h hh ih => exact ih.inclusion hh
  | positive h ht ih => exact ih.positive ht

theorem path (h : Formed W I J R) (hp : PositivePath (PrimaryEdge P) J K) :
    ∃ R', Formed W I K R' := by
  induction hp with
  | refl => exact ⟨R,h⟩
  | tail hp he ih =>
    obtain ⟨R',hr⟩ := ih
    cases he with
    | inclusion hJ hK hsub => exact ⟨_,hr.inclusion hsub.1⟩
    | codomain ht => exact ⟨_,hr.positive ht⟩

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

theorem exists_tail (hC : IsComponent (PrimaryEdge P) C)
    {r : Set S} (hr : r ∈ C) (ho : SignedPath (PrimaryEdge P) r r true)
    (hJ : J ∈ ObservationLayers P C) : ∃ U, Formed L J U := by
  obtain ⟨u,hu,hne,hpath⟩ := hJ
  obtain ⟨R,hR⟩ := (PositiveDataWrapper.Formed.identity (W := L.witnesses) (I := AxProfile P u)).path hpath
  obtain ⟨E,hE⟩ := ProofWrapper.Formed.of_path L.witnesses hC L.base_mem hu
    (hC.all_parities hr ho L.base_mem hu false)
  obtain ⟨D,hD,hn⟩ := ProofWrapper.Formed.exists_even_negative (W := L.witnesses) hC hr ho hu L.base_mem
  exact ⟨⟨u,R,E,D⟩,⟨hu,hne,hR,hE,hD,hn⟩⟩
end Formed
end DataTail
end

universe u
variable {S : Type u} {P : Specification S}

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

theorem edge (h : Formed L I J R) (hC : IsComponent (PrimaryEdge P) C)
    {r : Set S} (hr : r ∈ C) (ho : SignedPath (PrimaryEdge P) r r true)
    {c : Bool} (he : SecondaryEdge P C J K c) : ∃ R', Formed L I K (b := Bool.xor b c) R' := by
  cases he with
  | positive hJ hK he =>
    cases he with
    | inclusion _ _ hsub => cases b <;> exact ⟨R,h.inclusion hsub.1⟩
    | codomain ht => cases b <;> exact ⟨_,h.positive ht⟩
  | negative hJ hB hK ht =>
    obtain ⟨U,hU⟩ := DataTail.Formed.exists_tail (L := L) hC hr ho hB
    cases b <;> exact ⟨_,h.negative ht hU⟩

theorem path (h : Formed L I J R) (hC : IsComponent (PrimaryEdge P) C)
    {r : Set S} (hr : r ∈ C) (ho : SignedPath (PrimaryEdge P) r r true)
    {c : Bool} (hp : SignedPath (SecondaryEdge P C) J K c) : ∃ R', Formed L I K (b := Bool.xor b c) R' := by
  induction hp generalizing b R with
  | nil _ => cases b <;> exact ⟨R,h⟩
  | @cons J K M a c he hp ih =>
    obtain ⟨R',hR'⟩ := h.edge hC hr ho he
    obtain ⟨R'',hR''⟩ := ih hR'
    rw [← Bool.xor_assoc]; exact ⟨R'',hR''⟩

end

end Formed

theorem apply_append {b c : Bool} (R : DataWrapper S b) (Q : DataWrapper S c) (T : Expr S) :
    (R.append Q).apply T = Q.apply (R.apply T) := by
  induction Q with
  | identity => simp only [append,apply_reindex,apply]
  | positive Q D e ih => simp only [append,apply,ih]
  | @negative c Q U ih => simp only [append,apply_reindex,apply,ih]

namespace Formed
theorem reindex {b c : Bool} (hb : b = c)
    {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J : Set S} {R : DataWrapper S b}
    (h : R.Formed L I J) : (DataWrapper.reindex hb R).Formed L I J := by cases hb; exact h
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J K : Set S} {b c : Bool}
    {R : DataWrapper S b} {Q : DataWrapper S c}
theorem append (h : R.Formed L I J) (g : Q.Formed L J K) : (R.append Q).Formed L I K := by
  induction g with
  | identity => exact h.reindex _
  | inclusion g hs ih => exact ih.inclusion hs
  | positive g ht ih => exact ih.positive ht
  | @negative J B K c Q U g ht hU ih => exact (ih.negative ht hU).reindex _
end Formed
end DataWrapper
end PureTypeSystem.Labelled

/- A small finite compiler for the propositional term construction.
It has no type-theoretic assumptions. -/

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
variable (h : Formed R L I J K) {T t v Q : Expr S}
include h
theorem sorted (hT : SortedAt P Γ T I) : SortedAt P Γ (R.carrier T) K := h.second.sorted (h.first.sorted hT)
theorem mode (mT : WellModed γ T .data) : WellModed γ (R.carrier T) .data := h.second.mode (h.first.mode mT)

end Formed
end DoubleCode

namespace DataWrapper.Formed
theorem of_secondary_path {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} (hC : IsComponent (PrimaryEdge P) C)
    {r I J : Set S} (hr : r ∈ C) (ho : SignedPath (PrimaryEdge P) r r true)
    {b : Bool} (hp : SignedPath (SecondaryEdge P C) I J b) :
    ∃ R : DataWrapper S b, R.Formed L I J := by
  cases b <;> exact (DataWrapper.Formed.identity (L := L) (I := I)).path hC hr ho hp
end DataWrapper.Formed

namespace ChannelSetup
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
  {L : LogicSetup P Γ γ C}

theorem doubled_formed (K : ChannelSetup L) : K.doubled.Formed L K.rawVertex K.base K.rawVertex :=
  ⟨K.returnFormed,K.channelFormed.raw⟩

end ChannelSetup

namespace DoubleCode
variable (R : DoubleCode S)

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

end Formed
end DoubleCode

namespace DoubleCode
variable (R : DoubleCode S)

namespace Formed
variable {R} {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C} {I J H : Set S} (h : R.Formed L I J I)
    {U : DataWrapper S true} (hU : U.Formed L I H)
include h

theorem bp_sorted {T : Expr S} (hT : SortedAt P Γ T I) : SortedAt P Γ (R.bpType T) J :=
  h.first.sorted (h.tower_sorted hT 4)
theorem bp_mode {T : Expr S} (mT : WellModed γ T .data) : WellModed γ (R.bpType T) .data :=
  h.first.mode (h.tower_mode mT 4)
theorem param_sorted {T : Expr S} (hT : SortedAt P Γ T I) : SortedAt P Γ (R.paramType T) I :=
  h.second.sorted (h.bp_sorted hT)
theorem param_mode {T : Expr S} (mT : WellModed γ T .data) : WellModed γ (R.paramType T) .data :=
  h.second.mode (h.bp_mode mT)

end Formed
end DoubleCode

namespace ProbeCode
variable (R : ProbeCode S)

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

namespace ChannelSetup
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)} {L : LogicSetup P Γ γ C}
theorem probe_formed (K : ChannelSetup L) :
    K.probe.Formed L K.domain K.codomain K.base K.rawVertex K.tailVertex K.funVertex :=
  ⟨K.mainTriple,K.funTriple,K.ax,K.initialFormed,K.channelFormed.raw,K.returnFormed,
    K.funFormed,K.liftingFormed,K.tailFormed⟩
end ChannelSetup
end PureTypeSystem.Labelled

namespace PureTypeSystem
namespace IsComponent
variable {V : Type*} {E : V → V → Bool → Prop} {C : Set V}
/-- A secondary return can always be chosen with the outward parity. -/
theorem matched_return (hC : IsComponent E C) {v w : V} {b : Bool}
    (hv : v ∈ C) (hw : w ∈ C) (hp : SignedPath E v w b) : SignedPath E w v b := by
  by_cases ho : SignedPath E v v true
  · exact hC.all_parities hv ho hw hv b
  · exact hC.return_parity hv hw hp ho
end IsComponent

namespace Labelled
universe u
variable {S : Type u} {P : Specification S}
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)} {L : LogicSetup P Γ γ C}

namespace ChannelSetup
theorem exists_setup_return (hC : IsComponent (PrimaryEdge P) C)
    (ho : ∃ r ∈ C, SignedPath (PrimaryEdge P) r r true)
    (hf : ForbiddenConfiguration P C) : ∃ K : ChannelSetup L, Nonempty (ChannelReturn K) := by
  obtain ⟨r,hr,ho⟩ := ho
  obtain ⟨D,hD,I,J,k,s,p,n,g,j,h,ht,hJ,hk,hs,hax,hζ,htr,hp,hg,hn,hα,hβ,hκ,hj,hLam,hh,_,hη⟩ := hf.channel_paths
  obtain ⟨b,hδ⟩ := hD.connected hs hk
  obtain ⟨Rδ,hRδ⟩ := DataWrapper.Formed.of_secondary_path (L := L) hC hr ho hδ
  obtain ⟨Rret,hRret⟩ := DataWrapper.Formed.of_secondary_path (L := L) hC hr ho (hD.matched_return hs hk hδ)
  obtain ⟨Rα,hRα⟩ := DataWrapper.Formed.of_secondary_path (L := L) hC hr ho hα
  obtain ⟨Rβ,hRβ⟩ := DataWrapper.Formed.of_secondary_path (L := L) hC hr ho hβ
  obtain ⟨Rκ,hRκ⟩ := DataWrapper.Formed.of_secondary_path (L := L) hC hr ho hκ
  obtain ⟨RLam,hRLam⟩ := DataWrapper.Formed.of_secondary_path (L := L) hC hr ho hLam
  obtain ⟨Rη,hRη⟩ := DataWrapper.Formed.of_secondary_path (L := L) hC hr ho hη
  obtain ⟨Rζ,hRζ⟩ := (PositiveDataWrapper.Formed.identity (W := L.witnesses) (I := AxProfile P s)).path hζ
  obtain ⟨U,hU⟩ := DataTail.Formed.exists_tail (L := L) hC hr ho hn
  let K : ChannelSetup L := ⟨s,I,J,k,p,n,g,j,h,ht,htr,hax,hj,hh,b,Rδ,hRδ,
    ⟨RLam,Rα,Rη⟩,⟨hRLam,hRα,hRη⟩,Rβ,hRβ,Rκ,hRκ,Rζ,hRζ,U,hU⟩
  exact ⟨K,⟨⟨Rret,hRret⟩⟩⟩
end ChannelSetup

namespace ChannelReturn
variable {K : ChannelSetup L} (R : ChannelReturn K)

theorem evenLoop_formed : R.evenLoop.Formed L K.base K.base :=
  (R.formed.append K.initialFormed).reindex _
theorem fourth_formed : R.fourth.Formed L K.rawVertex K.base :=
  K.returnFormed.append R.evenLoop_formed
theorem firstDouble_formed : R.firstDouble.Formed L K.rawVertex K.base K.rawVertex :=
  K.doubled_formed
theorem outerDouble_formed : R.outerDouble.Formed L K.rawVertex K.base K.logicalVertex :=
  ⟨R.fourth_formed,K.channelFormed.logical⟩

theorem type_sorted : HasType P Γ R.type (.sort K.seed) := by
  exact R.formed.sorted (K.returnFormed.sorted (K.channelFormed.raw.sorted
    (K.returnFormed.sorted (K.channelFormed.raw.sorted K.probe_formed.carrier_sorted)))) K.seed rfl

theorem type_mode : WellModed γ R.type .data :=
  R.formed.mode (K.returnFormed.mode (K.channelFormed.raw.mode
    (K.returnFormed.mode (K.channelFormed.raw.mode K.probe_formed.carrier_mode))))

theorem evenLoop_apply (T : Expr S) : R.evenLoop.apply T = K.initial.apply (R.route.apply T) := by
  simp only [evenLoop,DataWrapper.apply_reindex,DataWrapper.apply_append]
theorem fourth_apply (T : Expr S) : R.fourth.apply T = K.initial.apply (R.route.apply (K.returnPath.apply T)) := by
  simp only [fourth,DataWrapper.apply_append,evenLoop_apply]
/-- The five odd segments have exactly the required endpoint, not merely an
isomorphic or propositionally related placeholder type. -/
theorem factorization :
    R.outerDouble.carrier (R.firstDouble.carrier (K.channel.raw.apply K.probe.carrier)) =
    K.channel.logicalType (K.initial.apply R.type) := by
  simp only [outerDouble,firstDouble,ChannelSetup.doubled,DoubleCode.carrier,ChannelCode.logicalType,
    fourth_apply,type]
end ChannelReturn
end Labelled
end PureTypeSystem

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Interface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact local obligations used when advancing a primary component.
This is an internal interface, not a hypothesis of the main PTS theorem. -/
namespace PureTypeSystem
universe u v

namespace Expected
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {A D : Expr S}
theorem of_type {M : Expr S} (h : HasType P Γ M A) : Expected P Γ A := h.regularity
end Expected

namespace ComponentInterface
open Candidates
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {hw : SystemWeaklyNormalizing P} {U C : Set (Set S)}
variable (J : ComponentInterface.{u,v} Ω hw C)

theorem admissible_extension {Γ : List (Expr S)} {D : Expr S} {s : S}
    {e : J.Env Γ} {e' : J.Env (D :: Γ)} {n : Expr S}
    (hD : HasType P Γ D (.sort s)) (he : J.Ext e e' n)
    (ha : J.Admissible (U := U) e)
    (hnC : Profile P Γ D ∈ C → n ∈ J.R D e)
    (hnU : Profile P Γ D ∈ U → StronglyNormalizing n)
    (hnG : Profile P Γ D ∉ U → Profile P Γ D ∉ C → n ∈ Ground Ω (D.subst (J.images e)).normalForm) :
    J.Admissible (U := U) e' := by
  intro i B hi
  cases hi with
  | zero =>
    have hp := Profile.weaken hw hD hD
    rw [hp,J.weakening hD (.sorted hD) he]
    simpa only [J.ext_images he,Expr.extend_zero,Expr.subst_raise_extend] using ⟨hnC,hnU,hnG⟩
  | succ D hi =>
    obtain ⟨t,hB⟩ := HasType.lookup_sorted hD.valid hi
    rw [Profile.weaken hw hB hD,J.weakening hD (.sorted hB) he]
    simpa only [J.ext_images he,Expr.extend_succ,Expr.subst_raise_extend] using ha _ _ hi

/-- Sending a binder to a fresh typed variable always preserves admissibility.
SN of that instance reflects back to the open substituted body by substitution
reflection, so no global renaming or reduction-height bound is needed. -/
theorem fresh_extension {Γ : List (Expr S)} {D : Expr S} {s : S}
    (e : J.Env Γ) (hD : HasType P Γ D (.sort s)) (ha : J.Admissible (U := U) e) :
    ∃ n, ∃ e' : J.Env (D :: Γ), J.Ext e e' (.var n) ∧ J.Admissible (U := U) e' := by
  have ht := ContextTower.HasType.subst hD (J.typed e)
  obtain ⟨n,_,hn⟩ := Ω.fresh_variable ht 0
  obtain ⟨e',he⟩ := J.extend e hD (.var n) hn
  have hng := var_ground n (hn.normalize_type hw)
  exact ⟨n,e',he,J.admissible_extension hD he ha
    (fun _ => (J.candidate e (.sorted hD)).lower hng)
    (fun _ => (Normal.var n).stronglyNormalizing) (fun _ _ => hng)⟩

end ComponentInterface

namespace Expected
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {Γ : List (Expr S)} {A : Expr S} {σ : Nat → Expr S}

theorem actual (h : Expected P Γ A) (hw : SystemWeaklyNormalizing P)
    (hσ : Ω.TypedSubstitution Γ σ) : Candidates.ActualType Ω (A.subst σ).normalForm := by
  rcases h with ⟨s,rfl⟩ | ⟨s,h⟩
  · exact .inr ⟨s,Expr.normalForm_of_normal (Normal.sort s)⟩
  · have ht := ContextTower.HasType.subst h hσ
    exact .inl ⟨(Expr.normalForm_spec (ht.weaklyNormalizing hw)).2, s, ht.normalForm hw⟩
end Expected

namespace Processed
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {U C : Set (Set S)} (H : Processed Ω U C) (hw : SystemWeaklyNormalizing P)
variable {Γ : List (Expr S)} {T : Expr S} {s : S} {σ : Nat → Expr S}
include H hw
theorem subst_closed (ht : HasType P Γ T (.sort s)) (hσ : Ω.TypedSubstitution Γ σ)
    (hT : Profile P Γ T ∈ U) : Ω.profile (T.subst σ) ∈ U :=
  H.closed hT (Ω.profile_subst_path hw ht hσ).reach

theorem subst_before (ht : HasType P Γ T (.sort s)) (hσ : Ω.TypedSubstitution Γ σ)
    (hT : Profile P Γ T ∈ C) : Ω.profile (T.subst σ) ∈ U ∨ Ω.profile (T.subst σ) ∈ C :=
  H.before hT (Ω.profile_subst_path hw ht hσ).reach

theorem top_ground_generic {e : Expr S}
    (ht : HasType P Γ T (.sort s)) (hσ : Ω.TypedSubstitution Γ σ)
    (hT : Profile P Γ T ∈ U) (he : e ∈ Candidates.Top Ω (T.subst σ).normalForm) :
    e ∈ Candidates.Ground Ω (T.subst σ).normalForm := by
  rw [H.invariant ((Expected.sorted ht).actual hw hσ) (by
    rw [Ω.profile_normalForm]
    exact H.subst_closed hw ht hσ hT)]
  exact he
end Processed

namespace ComponentInterface
open Candidates
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {hw : SystemWeaklyNormalizing P} {U C : Set (Set S)}
variable (J : ComponentInterface.{u,v} Ω hw C)

namespace Transported
variable {J} {Γ : List (Expr S)} {M A B : Expr S} {e : J.Env Γ}
theorem sn (h : J.Transported M A e) (hA : Expected P Γ A) :
    StronglyNormalizing (M.subst (J.images e)) := (J.candidate e hA).upper h.1 |>.2

theorem convert (h : J.Transported M A e) (hA : Expected P Γ A)
    (hB : Expected P Γ B) (hc : Converts A B) : J.Transported M B e := by
  have hp := Profile.converts (P := P) (Γ := Γ) (hA.wn hw) (hB.wn hw) hc
  have he := Expr.normalForm_converts (hA.subst_wn hw (J.typed e))
    (hB.subst_wn hw (J.typed e)) (hc.subst (J.images e))
  refine ⟨?_,?_⟩
  · rw [← J.conversion e hA hB hc]; exact h.1
  · intro hn hout
    rw [← he]
    exact h.2 hn (hp ▸ hout)
end Transported

theorem transported_of_ground {Γ : List (Expr S)} {M A : Expr S} {e : J.Env Γ}
    (hA : Expected P Γ A) (hg : M.subst (J.images e) ∈ Ground Ω (A.subst (J.images e)).normalForm) :
    J.Transported M A e := ⟨(J.candidate e hA).lower hg,fun _ _ => hg⟩

theorem transported_at_sort {Γ : List (Expr S)} {M : Expr S} {e : J.Env Γ} {s : S}
    (ht : HasType P Γ M (.sort s)) (hs : StronglyNormalizing (M.subst (J.images e))) :
    J.Transported M (.sort s) e := by
  apply J.transported_of_ground (.inl ⟨s,rfl⟩)
  have hh : M.subst (J.images e) ∈ Top Ω (.sort s) :=
    ⟨ContextTower.HasType.subst ht (J.typed e),hs⟩
  simpa only [Expr.subst,Expr.normalForm_of_normal (Normal.sort s),sort_ground_eq_top] using hh

variable (H : Processed Ω U C)
include H

theorem transported_var {Γ : List (Expr S)} {A : Expr S} {i : Nat}
    (ht : HasType P Γ (.var i) A) (e : J.Env Γ) (ha : J.Admissible (U := U) e) :
    J.Transported (.var i) A e := by
  obtain ⟨B,hB,hc⟩ := ht.generation
  obtain ⟨s,hBs⟩ := HasType.lookup_sorted ht.valid hB
  have hea := Expected.of_type ht
  apply Transported.convert (A := B) (hA := .sorted hBs) (hB := hea) (hc := .symm _ _ hc)
  have hdr := ha i B hB
  by_cases hBU : Profile P Γ B ∈ U
  · apply J.transported_of_ground (.sorted hBs)
    exact H.top_ground_generic hw hBs (J.typed e) hBU
      ⟨(J.typed e i B hB).normalize_type hw,hdr.2.1 hBU⟩
  · by_cases hBC : Profile P Γ B ∈ C
    · exact ⟨hdr.1 hBC,fun _ hn => False.elim (hn hBC)⟩
    · exact J.transported_of_ground (.sorted hBs) (hdr.2.2 hBU hBC)

/-- Propagation for a neutral prefix. Unlike a candidate, G has application
closure; the processed invariant handles the sole transition out of C. -/
theorem transported_neutral_app {Γ : List (Expr S)} {f n D E : Expr S} {s : S}
    (hp : HasType P Γ (.pi D E) (.sort s)) (hn : HasType P Γ n D)
    (hf : Neutral f) (e : J.Env Γ)
    (hfr : J.Transported f (.pi D E) e) (hnr : J.Transported n D e) :
    J.Transported (.app f n) (E.instantiate n) e := by
  obtain ⟨a,b,c,hD,hE,_,_⟩ := hp.generation_pi
  have hExpected := Expected.sorted (hE.instantiate hn)
  have hnt := (J.candidate e (.sorted hD)).upper hnr.1
  have hg (hfg : f.subst (J.images e) ∈ Ground Ω ((Expr.pi D E).subst (J.images e)).normalForm) :
      J.Transported (.app f n) (E.instantiate n) e := by
    apply J.transported_of_ground hExpected
    rw [← Expr.instantiate_subst,Expr.instantiate_extended]
    exact ground_application_subst hw hp (J.typed e) hfg hnt
  by_cases hK : Profile P Γ (.pi D E) ∈ C
  · by_cases hKa : Ω.profile ((Expr.pi D E).subst (J.images e)) ∈ C
    · have hr := J.specialization e hp hn hK hKa _ hfr.1 hnr.1
      refine ⟨hr,?_⟩
      intro _ ho
      have hL := H.before hK (Profile.instantiate_product_path hw hp hn).reach
      rcases hL with hLU | hLC
      · exact H.top_ground_generic hw (hE.instantiate hn) (J.typed e) hLU
          ((J.candidate e hExpected).upper hr)
      · exact False.elim (ho hLC)
    · apply hg
      have haK := (H.subst_before hw hp (J.typed e) hK).resolve_right hKa
      rw [H.invariant ((Expected.sorted hp).actual hw (J.typed e)) (by
        rwa [Ω.profile_normalForm])]
      exact (J.candidate e (.sorted hp)).upper hfr.1
  · exact hg (hfr.2 hf hK)

end ComponentInterface
end PureTypeSystem

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Components
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem

section
universe u v
namespace Neutral
variable {S : Type u} {M : Expr S} {ns : List (Expr S)}
theorem apps_head (h : Neutral (M.apps ns)) : Neutral M := by
  induction ns generalizing M with
  | nil => exact h
  | cons n ns ih =>
    have hh := ih h
    cases hh with
    | app hh => exact hh
end Neutral

namespace ComponentInterface
open Candidates
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {hw : SystemWeaklyNormalizing P} {U C : Set (Set S)}
variable (J : ComponentInterface.{u,v} Ω hw C)

/-- Reflection of the fresh-variable instance proves SN of the open body. -/
theorem open_sn {Γ : List (Expr S)} {D b B : Expr S} {s : S}
    (hb : HasType P (D :: Γ) b B) (hD : HasType P Γ D (.sort s))
    (ih : J.Transports (U := U) b) (e : J.Env Γ) (ha : J.Admissible (U := U) e) :
    StronglyNormalizing (b.subst (Expr.liftSub (J.images e))) := by
  obtain ⟨z,e',he',ha'⟩ := J.fresh_extension e hD ha
  have hsn := (ih _ _ hb e' ha').sn (.of_type hb)
  rw [J.ext_images he',← Expr.instantiate_extended] at hsn
  exact StronglyNormalizing.of_subst (Expr.single (.var z)) hsn

variable (H : Processed Ω U C)
include H

theorem transports_lam {Γ : List (Expr S)} {D b B : Expr S} {s : S}
    (hb : HasType P (D :: Γ) b B) (hp : HasType P Γ (.pi D B) (.sort s))
    (ihD : J.Transports (U := U) D) (ihb : J.Transports (U := U) b)
    (e : J.Env Γ) (ha : J.Admissible (U := U) e) :
    J.Transported (.lam D b) (.pi D B) e := by
  classical
  obtain ⟨a,c,d,hD,hB,_,_⟩ := hp.generation_pi
  have hDs := (ihD _ _ hD e ha).sn (.of_type hD)
  have hbs := J.open_sn hb hD ihb e ha
  have htop : (Expr.lam D b).subst (J.images e) ∈ Top Ω ((Expr.pi D B).subst (J.images e)).normalForm :=
    ⟨(ContextTower.HasType.subst (.abstraction hb hp) (J.typed e)).normalize_type hw,hDs.lam hbs⟩
  refine ⟨?_,fun hn => by cases hn⟩
  by_cases hK : Profile P Γ (.pi D B) ∈ C
  · by_cases hKa : Ω.profile ((Expr.pi D B).subst (J.images e)) ∈ C
    · apply J.product_intro e hp hK hKa _ htop
      intro n hn e' he
      have hnt := (J.candidate e (.sorted hD)).upper hn
      have hDomain := ContextTower.HasType.subst hD (J.typed e)
      have hnr := hnt.1.conversion hDomain
        (.symm _ _ (Expr.normalForm_spec (hDomain.weaklyNormalizing hw)).1.converts)
      have hdBefore := H.before hK (Reach.single (.domain (Profile.triple hw hp)))
      have hadm : J.Admissible (U := U) e' := J.admissible_extension hD he ha
        (fun _ => hn) (fun _ => hnt.2) (fun hnu hnc => by
          rcases hdBefore with hu | hc
          · exact False.elim (hnu hu)
          · exact False.elim (hnc hc))
      have hbody := (ihb _ _ hb e' hadm).1
      have htapp := ((ContextTower.HasType.subst (.abstraction hb hp) (J.typed e)).application hnr).normalize_type hw
      change Ω.HasType (.app (.lam (D.subst (J.images e)) (b.subst (Expr.liftSub (J.images e)))) n)
        ((B.subst (Expr.liftSub (J.images e))).instantiate n).normalForm at htapp
      rw [Expr.instantiate_extended,← J.ext_images he] at htapp
      have hbmem : (b.subst (Expr.liftSub (J.images e))).instantiate n ∈ J.R B e' := by
        rwa [Expr.instantiate_extended,← J.ext_images he]
      exact (J.candidate e' (.of_type hb)).expansion _ _ _ [] htapp hDs hbs hnt.2 .nil hbmem
    · rw [J.outside e (.sorted hp) (.inr hKa)]; exact htop
  · rw [J.outside e (.sorted hp) (.inl hK)]; exact htop

/-- Strongly-normalizing substitution transport,
including a neutral G-prefix invariant. -/
theorem sn_fundamental {M : Expr S} (hs : StronglyNormalizing M) :
    J.Transports (U := U) M := by
  apply StronglyNormalizing.induction_descendants (Q := J.Transports (U := U)) _ hs
  intro M _ ihr ihp Γ A ht e ha
  cases M with
  | var i => exact J.transported_var H ht e ha
  | sort s =>
    obtain ⟨t,hat,hc⟩ := ht.generation
    have hst := HasType.sort_of_valid ht.valid hat
    exact (J.transported_at_sort hst (Normal.sort s).stronglyNormalizing).convert
      (.inl ⟨t,rfl⟩) (.of_type ht) (.symm _ _ hc)
  | pi D E =>
    obtain ⟨a,b,c,hD,hE,hr,hc⟩ := ht.generation_pi
    have hDs := (ihp D (Expr.ProperPart.child (.pi_domain D E)) _ _ hD e ha).sn (.of_type hD)
    have hEs := J.open_sn hE hD (ihp E (Expr.ProperPart.child (.pi_body D E))) e ha
    exact (J.transported_at_sort (.product hD hE hr) (hDs.pi hEs)).convert
      (.inl ⟨c,rfl⟩) (.of_type ht) (.symm _ _ hc)
  | lam D b =>
    obtain ⟨B,s,hb,hp,hc⟩ := ht.generation_lam
    exact (J.transports_lam H hb hp
      (ihp D (Expr.ProperPart.child (.lam_domain D b)))
      (ihp b (Expr.ProperPart.child (.lam_body D b))) e ha).convert
      (.sorted hp) (.of_type ht) (.symm _ _ hc)
  | app f n =>
    rcases ht.app_spine with hf | ⟨D,b,n',ns,he⟩
    · obtain ⟨D,E,hft,hnt,hc⟩ := ht.generation_app
      obtain ⟨s,hp⟩ := hft.product_type_sorted
      have hfr := ihp f (Expr.ProperPart.child (.app_left f n)) _ _ hft e ha
      have hnr := ihp n (Expr.ProperPart.child (.app_right f n)) _ _ hnt e ha
      exact (J.transported_neutral_app H hp hnt hf e hfr hnr).convert
        (.of_type (.application hft hnt)) (.of_type ht) (.symm _ _ hc)
    · have ht' : HasType P Γ ((Expr.app (.lam D b) n').apps ns) A := he ▸ ht
      have parts : ∀ N, Expr.ProperPart N ((Expr.app (.lam D b) n').apps ns) →
          J.Transports (U := U) N := by
        intro N hN; apply ihp N; change Expr.ProperPart N (.app f n); rwa [he]
      have hlampart : Expr.ProperPart (.lam D b) ((Expr.app (.lam D b) n').apps ns) :=
        (Expr.ProperPart.child (.app_left _ _)).trans_right (Expr.Subterm.apps_head ns)
      obtain ⟨T,hthead⟩ := ht'.apps_head
      obtain ⟨D',E',hlam,hn',_⟩ := hthead.generation_app
      obtain ⟨B,s,hb,hp,_⟩ := hlam.generation_lam
      obtain ⟨a,c,d,hD,_,_,_⟩ := hp.generation_pi
      have hDs := (parts D (Expr.ProperPart.trans_left (Expr.Subterm.of_child (.lam_domain D b)) hlampart) _ _ hD e ha).sn (.of_type hD)
      have hbs := J.open_sn hb hD (parts b (Expr.ProperPart.trans_left (Expr.Subterm.of_child (.lam_body D b)) hlampart)) e ha
      have hnp := (Expr.ProperPart.child (.app_right (.lam D b) n')).trans_right (Expr.Subterm.apps_head ns)
      have hns := (parts n' hnp _ _ hn' e ha).sn (.of_type hn')
      have hargs : StronglyNormalizingArgs (ns.map (Expr.subst (J.images e))) := by
        apply StronglyNormalizingArgs.of_forall
        intro z hz
        rcases List.mem_map.mp hz with ⟨L,hL,rfl⟩
        obtain ⟨Z,hZ⟩ := ht'.apps_arg hL
        exact (parts L (Expr.ProperPart.apps_arg hL) _ _ hZ e ha).sn (.of_type hZ)
      have hred : Beta (.app f n) ((b.instantiate n').apps ns) := by
        rw [he]; exact (Beta.head D b n').apps ns
      have hctr := (ihr _ hred _ _ (ht.subject_reduction hred) e ha).1
      have hctr' : ((b.subst (Expr.liftSub (J.images e))).instantiate (n'.subst (J.images e))).apps
          (ns.map (Expr.subst (J.images e))) ∈ J.R A e := by
        simpa only [Expr.subst_apps,Expr.instantiate_subst] using hctr
      have hty := (ContextTower.HasType.subst ht' (J.typed e)).normalize_type hw
      rw [Expr.subst_apps] at hty
      have hexp := (J.candidate e (.of_type ht)).expansion _ _ _ _ hty hDs hbs hns hargs hctr'
      constructor
      · rw [he,Expr.subst_apps]
        exact hexp
      · intro hn
        rw [he] at hn
        have hh := hn.apps_head
        cases hh with
        | app hn => cases hn
end ComponentInterface

namespace StronglyNormalizing
variable {S : Type u} {M : Expr S}
theorem reverseIndex (h : StronglyNormalizing M) (k : Nat) :
    StronglyNormalizing (M.rename (Expr.reverseIndex k)) := by
  apply of_rename (Expr.reverseIndex k)
  simpa only [Expr.reverseIndex_twice] using h
end StronglyNormalizing

namespace Candidates
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)
namespace StackAt
variable {Ω} {k j : Nat} {T : Expr S} {ns : List (Expr S)}
theorem mono (h : StackAt Ω k T ns) (hkj : k ≤ j) : StackAt Ω j T ns := by
  induction h with
  | nil T => exact .nil T
  | cons hn hsn _ ih => exact .cons (Ω.at_mono hn hkj) hsn ih

theorem tested (h : StackAt Ω k T ns) : TestedStack Ω T ns := by
  induction h with
  | nil T => exact .nil T
  | cons hn hs _ ih => exact .cons ⟨⟨k,hn⟩,hs⟩ ih
end StackAt
namespace TestedStack
variable {Ω} {T : Expr S} {ns : List (Expr S)}
theorem common_stage (h : TestedStack Ω T ns) : ∃ k, StackAt Ω k T ns := by
  induction h with
  | nil T => exact ⟨0,.nil T⟩
  | cons hn _ ih =>
    obtain ⟨k,hk⟩ := ih
    obtain ⟨j,hj⟩ := hn.1
    exact ⟨max j k,.cons (Ω.at_mono hj (le_max_left j k)) hn.2 (hk.mono (le_max_right j k))⟩
end TestedStack
end Candidates

namespace ComponentInterface

section
open Candidates
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {hw : SystemWeaklyNormalizing P} {U C : Set (Set S)}
variable (J : ComponentInterface.{u,v} Ω hw C)

theorem identity_admissible {k : Nat} {e : J.Env (Ω.context k)}
    (he : J.images e = Expr.var ∘ Expr.reverseIndex k) : J.Admissible (U := U) e := by
  intro i B hi
  obtain ⟨s,hB⟩ := HasType.lookup_sorted (Ω.valid k) hi
  have ht := (J.typed e i B hi).normalize_type hw
  have hG : J.images e i ∈ Ground Ω (B.subst (J.images e)).normalForm := by
    rw [he] at ht ⊢
    exact var_ground _ ht
  exact ⟨fun _ => (J.candidate e (.sorted hB)).lower hG,
    fun _ => (ground_le_top hG).2,fun _ _ => hG⟩

end

open Candidates
variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {hw : SystemWeaklyNormalizing P} {U C : Set (Set S)}
variable (J : ComponentInterface.{u,v} Ω hw C) (H : Processed Ω U C)
include J H

theorem run_stack {k : Nat} {e : J.Env (Ω.context k)}
    (he : J.images e = Expr.var ∘ Expr.reverseIndex k)
    {T : Expr S} {ns : List (Expr S)} (hstack : StackAt Ω k T ns) :
    ∀ {s}, HasType P (Ω.context k) (T.rename (Expr.reverseIndex k)) (.sort s) →
    Normal T → Ω.profile T ∈ U ∨ Ω.profile T ∈ C →
    ∀ h, h ∈ J.R (T.rename (Expr.reverseIndex k)) e → StronglyNormalizing (h.apps ns) := by
  induction hstack with
  | nil T =>
      intro s ht hN _ h hr
      exact (J.candidate e (.sorted ht)).upper hr |>.2
  | @cons D E n ns hn hsn hstack ih =>
      intro s ht hN hprofile h hr
      have hactual : ActualType Ω (.pi D E) := .inl ⟨hN,s,⟨k,ht⟩⟩
      rcases hprofile with hU | hC
      · have htop := (J.candidate e (.sorted ht)).upper hr
        rw [J.identity_actual he,Expr.normalForm_of_normal hN] at htop
        have hg : h ∈ Ground Ω (.pi D E) := by
          rw [H.invariant hactual hU]; exact htop
        exact hg.2 (n :: ns) (.cons ⟨⟨k,hn⟩,hsn⟩ hstack.tested)
      · obtain ⟨a,b,c,hD,hE,_,_⟩ := ht.generation_pi
        have hnR := (J.sn_fundamental H (hsn.reverseIndex k) _ _ hn e
          (J.identity_admissible he)).1
        have hr' := J.specialization e ht hn (by
          change Profile P (Ω.context k) ((Expr.pi D E).rename (Expr.reverseIndex k)) ∈ C
          rwa [← Ω.profile_at hw ht])
          (by
            change Ω.profile (((Expr.pi D E).rename (Expr.reverseIndex k)).subst (J.images e)) ∈ C
            rwa [J.identity_actual he]) h hr hnR
        change Expr.app h ((n.rename (Expr.reverseIndex k)).subst (J.images e)) ∈
          J.R ((E.rename (Expr.liftRen (Expr.reverseIndex k))).instantiate
            (n.rename (Expr.reverseIndex k))) e at hr'
        rw [J.identity_actual he,Expr.instantiate_rename] at hr'
        have htarget : HasType P (Ω.context k) ((E.instantiate n).rename (Expr.reverseIndex k)) (.sort b) := by
          have hti := hE.instantiate hn
          change HasType P (Ω.context k) ((E.rename (Expr.liftRen (Expr.reverseIndex k))).instantiate
            (n.rename (Expr.reverseIndex k))) (.sort b) at hti
          rwa [Expr.instantiate_rename] at hti
        have htargetΩ : Ω.HasType (E.instantiate n) (.sort b) := ⟨k,htarget⟩
        have hwtarget := htargetΩ.weaklyNormalizing hw
        have htargetN : HasType P (Ω.context k) ((E.instantiate n).normalForm.rename (Expr.reverseIndex k)) (.sort b) := by
          rw [← Expr.normalForm_rename hwtarget]
          exact htarget.normalForm hw
        have hconv : Converts ((E.instantiate n).rename (Expr.reverseIndex k))
            ((E.instantiate n).normalForm.rename (Expr.reverseIndex k)) :=
          (Expr.normalForm_spec hwtarget).1.converts.rename _
        rw [J.conversion e (.sorted htarget) (.sorted htargetN) hconv] at hr'
        have hprofile' : Ω.profile (E.instantiate n).normalForm ∈ U ∨
            Ω.profile (E.instantiate n).normalForm ∈ C := by
          rw [Ω.profile_normalForm]
          exact H.before hC (Ω.profile_instantiate_product_path hw ⟨k,ht⟩ ⟨k,hn⟩).reach
        exact ih htargetN (Expr.normalForm_spec hwtarget).2 hprofile' (.app h n) hr'

/-- Advancing a component uses one identity evaluation, not a new
substitution choice at each stack prefix. -/
theorem advance {T : Expr S} (hT : ActualType Ω T) (hC : Ω.profile T ∈ C) :
    Ground Ω T = Top Ω T := by
  apply Set.Subset.antisymm ground_le_top
  intro h hh
  rcases hT with ⟨hN,s,ks,ht⟩ | ⟨s,rfl⟩
  · refine ⟨hh.1,?_⟩
    intro ns hstack
    obtain ⟨kn,hs⟩ := hstack.common_stage
    obtain ⟨kh,hhT⟩ := hh.1
    let k := max ks (max kn kh)
    have hkT : ks ≤ k := le_max_left _ _
    have hkN : kn ≤ k := le_trans (le_max_left _ _) (le_max_right _ _)
    have hkH : kh ≤ k := le_trans (le_max_right _ _) (le_max_right _ _)
    have ht' := Ω.at_mono ht hkT
    have hh' := Ω.at_mono hhT hkH
    obtain ⟨e,he⟩ := J.inhabit (.var ∘ Expr.reverseIndex k) (.identity k)
    have hr := (J.sn_fundamental H (hh.2.reverseIndex k) _ _ hh' e
      (J.identity_admissible he)).1
    rw [J.identity_actual he] at hr
    exact J.run_stack H he (hs.mono hkN) ht' hN (.inr hC) h hr
  · rwa [sort_ground_eq_top]

end ComponentInterface
end

universe u v
open Classical Candidates

namespace Beta
variable {S : Type u}
/-- Renaming cannot create a redex, and every renamed step has an exact source. -/
theorem rename_source {M N : Expr S} {ρ : Nat → Nat} (h : Beta (M.rename ρ) N) :
    ∃ M', Beta M M' ∧ N = M'.rename ρ := by
  induction M generalizing ρ N with
  | var n => cases h
  | sort s => cases h
  | pi A B ihA ihB =>
    cases h with
    | pi_domain hh =>
      obtain ⟨A',ha,rfl⟩ := ihA hh
      exact ⟨_,.pi_domain ha,rfl⟩
    | pi_body hh =>
      obtain ⟨B',hb,rfl⟩ := ihB hh
      exact ⟨_,.pi_body hb,rfl⟩
  | lam A b ihA ihb =>
    cases h with
    | lam_domain hh =>
      obtain ⟨A',ha,rfl⟩ := ihA hh
      exact ⟨_,.lam_domain ha,rfl⟩
    | lam_body hh =>
      obtain ⟨b',hb,rfl⟩ := ihb hh
      exact ⟨_,.lam_body hb,rfl⟩
  | app f a ihf iha =>
    cases f <;> cases h
    all_goals first
      | (rename_i hh
         obtain ⟨f',hf,rfl⟩ := ihf hh
         exact ⟨_,.app_left hf,rfl⟩)
      | (rename_i hh
         obtain ⟨a',ha,rfl⟩ := iha hh
         exact ⟨_,.app_right ha,rfl⟩)
      | exact ⟨_,.head _ _ _,Expr.instantiate_rename _ _ _⟩
end Beta
namespace StronglyNormalizing
variable {S : Type u} {M : Expr S}
theorem rename (h : StronglyNormalizing M) (ρ : Nat → Nat) :
    StronglyNormalizing (M.rename ρ) := by
  induction h with
  | intro M _ ih =>
    apply Acc.intro
    intro N hn
    obtain ⟨M',hm,rfl⟩ := hn.rename_source
    exact ih M' hm
end StronglyNormalizing

namespace ContextTower
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)

/-- Every valid finite context has a variable-valued interpretation in the
saturated tower. Substitution reflection does not require these names to be
surjective or even injective. -/
theorem variable_substitution {Γ : List (Expr S)} (hΓ : ValidContext P Γ) :
    ∃ ρ : Nat → Nat, Ω.TypedSubstitution Γ (Expr.var ∘ ρ) := by
  induction hΓ with
  | nil => exact ⟨id,fun _ _ h => nomatch h⟩
  | @cons Γ A s hΓ hA ih =>
    obtain ⟨ρ,hρ⟩ := ih
    have ht := HasType.subst hA hρ
    obtain ⟨n,_,hn⟩ := Ω.fresh_variable ht 0
    refine ⟨fun i => match i with | 0 => n | i+1 => ρ i,?_⟩
    convert hρ.cons hn using 1
    all_goals try with_reducible_and_instances rfl
    funext i; cases i <;> rfl

end ContextTower

/-- Finite primary-component induction. The supplied interfaces are consumed
one at a time, and Ground=Top is only used at strict predecessor components. -/
theorem all_ground_eq_top {S : Type u} [Fintype S] {P : Specification S}
    (Ω : ContextTower P) (hw : SystemWeaklyNormalizing P)
    (interfaces : ∀ C, IsComponent (PrimaryEdge P) C →
      Nonempty (ComponentInterface.{u,v} Ω hw C)) :
    ∀ {T}, ActualType Ω T → Ground Ω T = Top Ω T := by
  intro T hT
  let E := PrimaryEdge P
  have h : ∀ n, ∀ T : Expr S, Reach.rank E (Ω.profile T) = n → ActualType Ω T →
      Ground Ω T = Top Ω T := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hr hT
      let V := Ω.profile T
      let C := Reach.component E V
      let U := {I | Reach.rank E I < n}
      have hC : IsComponent E C := Reach.component_isComponent E V
      have rankC {I} (hi : I ∈ C) : Reach.rank E I = n := by
        exact (Nat.le_antisymm (Reach.rank_mono E hi.2) (Reach.rank_mono E hi.1)).trans hr
      have hp : Processed Ω U C := by
        refine ⟨?_,?_,?_,?_⟩
        · apply Set.disjoint_left.mpr
          intro I hI hc
          have : Reach.rank E I < n := hI
          rw [rankC hc] at this
          exact Nat.lt_irrefl _ this
        · intro I J hj hij
          exact lt_of_le_of_lt (Reach.rank_mono E hij) hj
        · intro I J hj hij
          have hle : Reach.rank E I ≤ n := (Reach.rank_mono E hij).trans (le_of_eq (rankC hj))
          rcases lt_or_eq_of_le hle with hlt | heq
          · exact .inl hlt
          · exact .inr ⟨hj.1.trans (Reach.reverse_of_rank_eq E hij (heq.trans (rankC hj).symm)),
              hij.trans hj.2⟩
        · intro A hA hAu
          exact ih _ hAu A rfl hA
      obtain ⟨J⟩ := interfaces C hC
      exact J.advance hp hT (Reach.mem_component E V)
  exact h _ T rfl hT

/-- Once all actual types have Ground=Top, typed application preserves SN.
Types and annotations are normalized using WN, not assumed SN. -/
theorem application_sn_of_ground {S : Type u} {P : Specification S}
    (Ω : ContextTower P) (hw : SystemWeaklyNormalizing P)
    (hground : ∀ {T}, ActualType Ω T → Ground Ω T = Top Ω T)
    {Γ : List (Expr S)} {f a D E : Expr S}
    (hf : HasType P Γ f (.pi D E)) (ha : HasType P Γ a D)
    (hsf : StronglyNormalizing f) (hsa : StronglyNormalizing a) :
    StronglyNormalizing (.app f a) := by
  obtain ⟨ρ,hρ⟩ := Ω.variable_substitution hf.valid
  have hf' := ContextTower.HasType.subst hf hρ
  have ha' := ContextTower.HasType.subst ha hρ
  simp only [Expr.subst_var_rename] at hf' ha'
  obtain ⟨s,hpi⟩ := hf.product_type_sorted
  have hpi' := ContextTower.HasType.subst hpi hρ
  simp only [Expr.subst_var_rename,Expr.rename] at hpi'
  obtain ⟨a',b',c',hD,hE,hr,_⟩ := hpi.generation_pi
  have hDw := (ContextTower.HasType.subst hD hρ).weaklyNormalizing hw
  simp only [Expr.subst_var_rename] at hDw
  have hPw := hpi'.weaklyNormalizing hw
  have hDN : Normal (D.rename ρ).normalForm := (Expr.normalForm_spec hDw).2
  have hPN := (Expr.normalForm_spec hPw).2
  have hpNF : ((Expr.pi D E).rename ρ).normalForm =
      .pi (D.rename ρ).normalForm (E.rename (Expr.liftRen ρ)).normalForm := by
    apply Expr.normalForm_pi hDw
    obtain ⟨target, reduces, normal⟩ := hPw
    obtain ⟨domain, body, rfl, _, bodyReduces⟩ := Reduces.pi_inv reduces
    exact ⟨body, bodyReduces, normal.pi_body⟩
  have htype : ActualType Ω ((Expr.pi D E).rename ρ).normalForm :=
    .inl ⟨hPN,s,hpi'.normalForm hw⟩
  have hfg : f.rename ρ ∈ Ground Ω ((Expr.pi D E).rename ρ).normalForm := by
    rw [hground htype]
    exact ⟨hf'.normalize_type hw,hsf.rename ρ⟩
  rw [hpNF] at hfg
  have hag : a.rename ρ ∈ Top Ω (D.rename ρ).normalForm := ⟨ha'.normalize_type hw,hsa.rename ρ⟩
  have hs := (ground_le_top (ground_application hw hfg hag)).2
  exact StronglyNormalizing.of_rename ρ hs

end PureTypeSystem

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

namespace ChannelSetup
variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    {L : LogicSetup P Γ γ C}
theorem relational_formed (K : ChannelSetup L) :
    K.relational.Formed L K.domain K.codomain K.base K.rawVertex K.tailVertex K.funVertex K.logicalVertex K.predVertex :=
  ⟨K.probe_formed,K.channelFormed⟩
end ChannelSetup
end

universe u
end PureTypeSystem.Labelled

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Diagonal
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem.Labelled.ChannelReturn
universe u
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {γ : Nat → Mode}
  {C : Set (Set S)} {L : LogicSetup P Γ γ C} {K : ChannelSetup L} (R : ChannelReturn K)
theorem specialized_formed : R.specialized.Formed L K.domain K.codomain K.base K.rawVertex K.tailVertex K.funVertex K.logicalVertex K.predVertex := by
  refine ⟨⟨K.relational_formed,R.firstDouble_formed,R.outerDouble_formed⟩,R.type_sorted,R.type_mode,R.factorization,rfl,?_⟩
  change R.fourth.apply (R.firstDouble.carrier (K.channel.raw.apply K.probe.carrier)) = K.initial.apply R.type
  simp only [fourth_apply,firstDouble,DoubleCode.carrier,ChannelSetup.doubled,type]
end PureTypeSystem.Labelled.ChannelReturn

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Restriction
attribute [-instance] _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeCandidate _root_.OAI.PureTypeSystem.Candidates.instCompleteLatticeSignedCandidate _root_.OAI.PureTypeSystem.Candidates.instInfSetCandidate _root_.OAI.PureTypeSystem.instCountableExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem

universe u

namespace Beta

variable {S T : Type u} {M N : Expr S}

theorem mapSort (h : Beta M N) (f : S → T) : Beta (M.mapSort f) (N.mapSort f) := by
  induction h with
  | head A b a =>
      simpa only [Expr.mapSort, Expr.mapSort_instantiate] using
        (Beta.head (A.mapSort f) (b.mapSort f) (a.mapSort f))
  | app_left _ ih => exact .app_left ih
  | app_right _ ih => exact .app_right ih
  | lam_domain _ ih => exact .lam_domain ih
  | lam_body _ ih => exact .lam_body ih
  | pi_domain _ ih => exact .pi_domain ih
  | pi_body _ ih => exact .pi_body ih

end Beta

namespace Reduces

variable {S T : Type u} {M N : Expr S}

theorem mapSort (h : Reduces M N) (f : S → T) : Reduces (M.mapSort f) (N.mapSort f) :=
  h.lift (Expr.mapSort f) (fun _ _ h => h.mapSort f)

end Reduces

namespace Converts

variable {S T : Type u} {M N : Expr S}

theorem mapSort (h : Converts M N) (f : S → T) : Converts (M.mapSort f) (N.mapSort f) := by
  induction h with
  | rel _ _ h => exact .rel _ _ (h.mapSort f)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

end Converts

namespace Normal

variable {S T : Type u}

theorem mapSort {M : Expr S} (h : Normal M) (f : S → T) : Normal (M.mapSort f) := by
  induction M with
  | var n => exact Normal.var _
  | sort s => exact Normal.sort _
  | pi A B ihA ihB => exact (ihA h.pi_domain).pi (ihB h.pi_body)
  | lam A b ihA ihb => exact (ihA h.lam_domain).lam (ihb h.lam_body)
  | app M a ihM iha =>
      have hM := ihM h.app_left
      have ha := iha h.app_right
      cases M with
      | lam D b => exact False.elim (h _ (.head D b a))
      | var n | sort s | app M b | pi D B =>
          intro N hN
          cases hN with
          | app_left hr => exact hM _ hr
          | app_right hr => exact ha _ hr

end Normal

namespace StronglyNormalizing

variable {S T : Type u}

theorem of_mapSort (f : S → T) {M : Expr S} (h : StronglyNormalizing (M.mapSort f)) :
    StronglyNormalizing M := by
  have aux : ∀ N : Expr T, StronglyNormalizing N →
      ∀ M : Expr S, M.mapSort f = N → StronglyNormalizing M := by
    intro N hN
    induction hN with
    | intro N hN ih =>
        intro M he
        subst N
        refine Acc.intro M ?_
        intro M' hM'
        exact ih (M'.mapSort f) (hM'.mapSort f) M' rfl
  exact aux _ h M rfl

end StronglyNormalizing

namespace WeaklyNormalizing

variable {S T : Type u}

theorem mapSort {M : Expr S} (h : WeaklyNormalizing M) (f : S → T) :
    WeaklyNormalizing (M.mapSort f) := by
  obtain ⟨N, hr, hn⟩ := h
  exact ⟨N.mapSort f, Reduces.mapSort hr f, hn.mapSort f⟩

theorem of_retraction (f : S → T) (g : T → S) (hfg : Function.LeftInverse g f)
    {M : Expr S} (h : WeaklyNormalizing (M.mapSort f)) : WeaklyNormalizing M := by
  have he : g ∘ f = id := funext hfg
  simpa only [Expr.mapSort_comp, he, Expr.mapSort_id] using h.mapSort g

end WeaklyNormalizing

namespace HasType

variable {S T : Type u} {P Q : Specification S}

theorem monotone {Γ : List (Expr S)} {M A : Expr S} (h : HasType P Γ M A)
    (ha : ∀ s t, P.axioms s t → Q.axioms s t)
    (hr : ∀ a b c, P.rule a b c → Q.rule a b c) : HasType Q Γ M A := by
  induction h with
  | ax h => exact .ax (ha _ _ h)
  | var _ ih => exact .var ih
  | weaken _ _ ihM ihA => exact .weaken ihM ihA
  | product _ _ h ihA ihB => exact .product ihA ihB (hr _ _ _ h)
  | abstraction _ _ ihb ihPi => exact .abstraction ihb ihPi
  | application _ _ ihf iha => exact .application ihf iha
  | conversion _ _ hc ihM ihA => exact .conversion ihM ihA hc

theorem mapSort {Q : Specification T} {Γ : List (Expr S)} {M A : Expr S}
    (h : HasType P Γ M A) (f : S → T)
    (ha : ∀ s t, P.axioms s t → Q.axioms (f s) (f t))
    (hr : ∀ a b c, P.rule a b c → Q.rule (f a) (f b) (f c)) :
    HasType Q (Γ.map (Expr.mapSort f)) (M.mapSort f) (A.mapSort f) := by
  induction h with
  | ax h => exact .ax (ha _ _ h)
  | var _ ih => simpa only [List.map_cons, Expr.mapSort, Expr.mapSort_rename] using HasType.var ih
  | weaken _ _ ihM ihA =>
      simpa only [List.map_cons, Expr.mapSort_rename] using HasType.weaken ihM ihA
  | product _ _ h ihA ihB => exact .product ihA ihB (hr _ _ _ h)
  | abstraction _ _ ihb ihPi => exact .abstraction ihb ihPi
  | application _ _ ihf iha =>
      simpa only [Expr.mapSort, Expr.mapSort_instantiate] using HasType.application ihf iha
  | conversion _ _ hc ihM ihA => exact .conversion ihM ihA (hc.mapSort f)

theorem has_axiom {Γ : List (Expr S)} {M A : Expr S} (h : HasType P Γ M A) :
    ∃ s t, P.axioms s t := by
  induction h with
  | ax h => exact ⟨_, _, h⟩
  | var _ ih => exact ih
  | weaken _ _ ih _ => exact ih
  | product _ _ _ ih _ => exact ih
  | abstraction _ _ ih _ => exact ih
  | application _ _ ih _ => exact ih
  | conversion _ _ _ ih _ => exact ih

end HasType

namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M T : Expr S}

theorem restrict_mono {A A' : Finset (S × S)} {R R' : Finset (S × S × S)}
    (h : HasType (P.restrict A R) Γ M T) (hA : A ⊆ A') (hR : R ⊆ R') :
    HasType (P.restrict A' R') Γ M T :=
  h.monotone (fun _ _ h => ⟨h.1, hA h.2⟩) (fun _ _ _ h => ⟨h.1, hR h.2⟩)

theorem finite_support (h : HasType P Γ M T) :
    ∃ A : Finset (S × S), ∃ R : Finset (S × S × S), HasType (P.restrict A R) Γ M T := by
  classical
  induction h with
  | ax h => exact ⟨{(_,_)}, ∅, .ax ⟨h, Finset.mem_singleton_self _⟩⟩
  | var _ ih =>
      obtain ⟨A, R, ht⟩ := ih
      exact ⟨A, R, .var ht⟩
  | weaken _ _ ihM ihA =>
      obtain ⟨A, R, hM⟩ := ihM
      obtain ⟨A', R', hA⟩ := ihA
      exact ⟨A ∪ A', R ∪ R', .weaken
        (hM.restrict_mono Finset.subset_union_left Finset.subset_union_left)
        (hA.restrict_mono Finset.subset_union_right Finset.subset_union_right)⟩
  | @product Γ D E a b c _ _ hr ihD ihE =>
      obtain ⟨A, R, hD⟩ := ihD
      obtain ⟨A', R', hE⟩ := ihE
      refine ⟨A ∪ A', insert (a,b,c) (R ∪ R'), .product
        (hD.restrict_mono Finset.subset_union_left
          (Finset.subset_union_left.trans (Finset.subset_insert _ _)))
        (hE.restrict_mono Finset.subset_union_right
          (Finset.subset_union_right.trans (Finset.subset_insert _ _))) ?_⟩
      exact ⟨hr, Finset.mem_insert_self _ _⟩
  | abstraction _ _ ihb ihPi =>
      obtain ⟨A, R, hb⟩ := ihb
      obtain ⟨A', R', hPi⟩ := ihPi
      exact ⟨A ∪ A', R ∪ R', .abstraction
        (hb.restrict_mono Finset.subset_union_left Finset.subset_union_left)
        (hPi.restrict_mono Finset.subset_union_right Finset.subset_union_right)⟩
  | application _ _ ihf iha =>
      obtain ⟨A, R, hf⟩ := ihf
      obtain ⟨A', R', ha⟩ := iha
      exact ⟨A ∪ A', R ∪ R', .application
        (hf.restrict_mono Finset.subset_union_left Finset.subset_union_left)
        (ha.restrict_mono Finset.subset_union_right Finset.subset_union_right)⟩
  | conversion _ _ hc ihM ihT =>
      obtain ⟨A, R, hM⟩ := ihM
      obtain ⟨A', R', hT⟩ := ihT
      exact ⟨A ∪ A', R ∪ R', .conversion
        (hM.restrict_mono Finset.subset_union_left Finset.subset_union_left)
        (hT.restrict_mono Finset.subset_union_right Finset.subset_union_right) hc⟩

end HasType

namespace SystemWeaklyNormalizing

variable {S : Type u} {P : Specification S}

theorem on {D : Set S} (hw : SystemWeaklyNormalizing P) (d₀ : D) :
    SystemWeaklyNormalizing (P.on D) := by
  classical
  let f : S → D := fun s => if h : s ∈ D then ⟨s,h⟩ else d₀
  have hf : Function.LeftInverse f Subtype.val := by
    intro s
    apply Subtype.ext
    simp only [f, dite_eq_left s.property]
  intro Γ _ M hM
  obtain ⟨A, h | h⟩ := hM
  · have ht := h.mapSort Subtype.val (fun _ _ h => h) (fun _ _ _ h => h)
    exact WeaklyNormalizing.of_retraction Subtype.val f hf
      (hw _ ht.valid _ ⟨_, Or.inl ht⟩)
  · have ht := h.mapSort Subtype.val (fun _ _ h => h) (fun _ _ _ h => h)
    exact WeaklyNormalizing.of_retraction Subtype.val f hf
      (hw _ ht.valid _ ⟨_, Or.inr ht⟩)

end SystemWeaklyNormalizing

namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M T : Expr S}

/-- A non-strongly-normalizing typed term has a counterexample over a finite
subspecification. No normalization conclusion for that finite PTS is assumed. -/
theorem finite_counterexample (h : HasType P Γ M T) (hn : ¬ StronglyNormalizing M)
    (hw : SystemWeaklyNormalizing P) :
    ∃ D : Finset S, ∃ Γ' : List (Expr {s // s ∈ D}),
      ∃ M' T' : Expr {s // s ∈ D},
        HasType (P.on (D : Set S)) Γ' M' T' ∧ ¬ StronglyNormalizing M' ∧
          SystemWeaklyNormalizing (P.on (D : Set S)) := by
  classical
  obtain ⟨A, R, hr⟩ := h.finite_support
  let D := A.biUnion (fun a => {a.1, a.2}) ∪
    R.biUnion (fun r => {r.1, r.2.1, r.2.2})
  have ax_mem {s t : S} (h : (s,t) ∈ A) : s ∈ D ∧ t ∈ D := by
    constructor
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨(s,t), h, by simp⟩)
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨(s,t), h, by simp⟩)
  have rule_mem {a b c : S} (h : (a,b,c) ∈ R) : a ∈ D ∧ b ∈ D ∧ c ∈ D := by
    constructor
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(a,b,c), h, by simp⟩)
    constructor
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(a,b,c), h, by simp⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨(a,b,c), h, by simp⟩)
  obtain ⟨s₀, t₀, h₀⟩ := hr.has_axiom
  let d₀ : {s // s ∈ D} := ⟨s₀, (ax_mem h₀.2).1⟩
  let f : S → {s // s ∈ D} := fun s => if h : s ∈ D then ⟨s,h⟩ else d₀
  have f_val {s : S} (h : s ∈ D) : (f s).val = s := by
    simp only [f, dite_eq_left h]
  have ha : ∀ s t, (P.restrict A R).axioms s t →
      (P.on (D : Set S)).axioms (f s) (f t) := by
    intro s t hst
    change P.axioms (f s).val (f t).val
    rw [f_val (ax_mem hst.2).1, f_val (ax_mem hst.2).2]
    exact hst.1
  have hp : ∀ a b c, (P.restrict A R).rule a b c →
      (P.on (D : Set S)).rule (f a) (f b) (f c) := by
    intro a b c habc
    change P.rule (f a).val (f b).val (f c).val
    rw [f_val (rule_mem habc.2).1, f_val (rule_mem habc.2).2.1,
      f_val (rule_mem habc.2).2.2]
    exact habc.1
  exact ⟨D, _, _, _, hr.mapSort f ha hp,
    fun hs => hn (StronglyNormalizing.of_mapSort f hs), hw.on d₀⟩

end HasType

end PureTypeSystem

end OAI
end

section
-- module Solutions.OAIQ5_T6.TypeSystem_Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PureTypeSystem

section
universe u
open Classical

/-- All three actual candidate models are selected using the exact source case
split. The exclusion interface is isolated, not hidden in a candidate law. -/
theorem interfaces_of_exclusion {S : Type u} [Fintype S] {P : Specification S}
    (Ω : ContextTower P) (hw : SystemWeaklyNormalizing P) (he : RelationalExclusion P)
    (C : Set (Set S)) (hC : IsComponent (PrimaryEdge P) C) :
    Nonempty (ComponentInterface.{u,u} Ω hw C) := by
  by_cases ho : ∃ I ∈ C, SignedPath (PrimaryEdge P) I I true
  · by_cases ht : ∃ I J K, ProfileTriple P I J K ∧ I ∈ C ∧ J ∈ C ∧ K ∈ C
    · exact ⟨ObservationValues.componentInterface Ω C (he C hC ho ht) hC⟩
    · exact ⟨OneChildInterpretation.componentInterface Ω C hw hC
        (fun h hi hj hk => ht ⟨_,_,_,h,hi,hj,hk⟩)⟩
  · exact ⟨SignedInterpretation.componentInterface Ω hC hw
      (fun I hi hp => ho ⟨I,hi,hp⟩)⟩

theorem finite_normalization_of_exclusion {S : Type u} [Fintype S] {P : Specification S}
    (hw : SystemWeaklyNormalizing P) (he : RelationalExclusion P) :
    SystemStronglyNormalizing P := by
  apply stronglyNormalizing_of_application
  intro Γ f a D E hf ha hsf hsa
  obtain ⟨s,t,hat⟩ := hf.has_axiom
  let Ω := ContextTowerConstruction.tower P hat
  exact application_sn_of_ground Ω hw
    (all_ground_eq_top Ω hw (interfaces_of_exclusion Ω hw he)) hf ha hsf hsa

/-- Finite restriction retains open contexts, annotations and every source rule.
This closes the main theorem once the typed relational exclusion is proved for
finite specifications. No finite-only conclusion is substituted for the main. -/
theorem normalization_of_finite_exclusion
    (exclude : ∀ (S : Type u) [Fintype S] (P : Specification S),
      SystemWeaklyNormalizing P → RelationalExclusion P)
    {S : Type u} {P : Specification S} (hw : SystemWeaklyNormalizing P) :
    SystemStronglyNormalizing P := by
  by_contra hn
  obtain ⟨Γ,f,a,D,E,hf,ha,hsf,hsa,hbad⟩ := exists_bad_application hn
  have htype := HasType.application hf ha
  obtain ⟨F,Γ',M',T',ht,hn',hw'⟩ := htype.finite_counterexample hbad hw
  have hsn := finite_normalization_of_exclusion hw' (exclude _ _ hw')
  exact hn' (hsn Γ' ht.valid M' ⟨T',.inl ht⟩)

end

universe u
open Labelled
/-- Relational exclusion via the concrete illative encoding
in the actual finite ambient context, not supplied as an axiom. -/
theorem relational_exclusion {S : Type u} [Fintype S] {P : Specification S}
    (hw : SystemWeaklyNormalizing P) : RelationalExclusion P := by
  intro C hC ho ht hf
  obtain ⟨Γ,γ,hΓ,⟨L⟩⟩ := LogicSetup.exists_setup C hC ho ht
  obtain ⟨K,⟨R⟩⟩ := ChannelSetup.exists_setup_return (L := L) hC ho hf
  let KY := L.quantifiers K.logicalVertex K.directLogical
  let KP := L.quantifiers K.predVertex K.directPred
  obtain ⟨b,hb,mb⟩ := R.specialized_formed.relational_bottom KY KP
  exact no_proof_at_target hw hΓ
    ⟨.terminal (L.witnesses.allData L.base L.triple.codomain),L.witnesses.normal L.base L.triple.codomain⟩ hb mb

/-- System-wide weak normalization implies strong normalization for every PTS,
including arbitrary sort types, nonfunctional rules and annotated terms. -/
theorem weak_implies_strong_oai {S : Type u} (P : Specification S)
    (h : SystemWeaklyNormalizing P) : SystemStronglyNormalizing P :=
  normalization_of_finite_exclusion (fun _ _ _ hw => relational_exclusion hw) h
end PureTypeSystem

end OAI
end

theorem solution.{u} : type_of% @OAI.PureTypeSystem.weak_implies_strong_oai.{u} := @OAI.PureTypeSystem.weak_implies_strong_oai.{u}
