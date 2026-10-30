-- Prove2me | solution 1 for HofmannStreicher1994.substitution_locality
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T01:51:08.930307+00:00
-- url     : https://prove2.me/submissions/9933faf1-1ea2-420d-8846-cd754d0eb35a

import Definitions.Def_HofmannStreicher1994_Syntax

set_option autoImplicit false


namespace HofmannStreicher1994

def Scoped (k : Nat) : Expr → Prop
  | .var n => n < k
  | .pi A B | .sigma A B | .lam A B => Scoped k A ∧ Scoped (k + 1) B
  | .identity A a b => Scoped k A ∧ Scoped k a ∧ Scoped k b
  | .nat | .universe | .zero => True
  | .el a | .succ a => Scoped k a
  | .app A B f a => Scoped k A ∧ Scoped (k + 1) B ∧ Scoped k f ∧ Scoped k a
  | .pair A B a b => Scoped k A ∧ Scoped (k + 1) B ∧ Scoped k a ∧ Scoped k b
  | .sigmaRec A B C d p =>
      Scoped k A ∧ Scoped (k + 1) B ∧ Scoped (k + 1) C ∧ Scoped (k + 2) d ∧ Scoped k p
  | .refl A a => Scoped k A ∧ Scoped k a
  | .idRec A C d a b p =>
      Scoped k A ∧ Scoped (k + 3) C ∧ Scoped (k + 1) d ∧
      Scoped k a ∧ Scoped k b ∧ Scoped k p
  | .natRec C z s n => Scoped (k + 1) C ∧ Scoped k z ∧ Scoped (k + 2) s ∧ Scoped k n

def IsTm : Expr → Prop
  | .var _ | .lam _ _ | .app _ _ _ _ | .pair _ _ _ _ | .sigmaRec _ _ _ _ _
    | .refl _ _ | .idRec _ _ _ _ _ _ | .zero | .succ _ | .natRec _ _ _ _ => True
  | _ => False

def IsTy : Expr → Prop
  | .pi _ _ | .sigma _ _ | .identity _ _ _ | .nat | .universe | .el _ => True
  | _ => False

def RenScope (k l : Nat) (ρ : Nat → Nat) : Prop := ∀ n, n < k → ρ n < l

theorem RenScope.lift {k l : Nat} {ρ : Nat → Nat} (h : RenScope k l ρ) :
    RenScope (k + 1) (l + 1) (liftRenaming ρ) := by
  intro n hn
  cases n with
  | zero => exact Nat.zero_lt_succ _
  | succ n => exact Nat.succ_lt_succ (h n (Nat.lt_of_succ_lt_succ hn))

theorem Scoped.rename {e : Expr} {k l : Nat} {ρ : Nat → Nat}
    (he : Scoped k e) (hρ : RenScope k l ρ) : Scoped l (rename ρ e) := by
  induction e generalizing k l ρ <;> simp_all [Scoped, HofmannStreicher1994.rename]
  all_goals grind only [→ RenScope.lift, RenScope]

theorem Scoped.weaken {e : Expr} {k : Nat} (h : Scoped k e) :
    Scoped (k + 1) (weaken e) := h.rename (fun _ hn => Nat.succ_lt_succ hn)

theorem IsTm.rename {e : Expr} {ρ : Nat → Nat} (h : IsTm e) :
    IsTm (rename ρ e) := by
  cases e <;> simp_all [IsTm, HofmannStreicher1994.rename]

theorem IsTy.rename {e : Expr} {ρ : Nat → Nat} (h : IsTy e) :
    IsTy (rename ρ e) := by
  cases e <;> simp_all [IsTy, HofmannStreicher1994.rename]

theorem IsTy.substitute {e : Expr} {σ : Nat → Expr} (h : IsTy e) :
    IsTy (substitute σ e) := by
  cases e <;> simp_all [IsTy, HofmannStreicher1994.substitute]

def SubScope (k l : Nat) (σ : Nat → Expr) : Prop :=
  ∀ n, n < k → Scoped l (σ n)

theorem SubScope.lift {k l : Nat} {σ : Nat → Expr} (h : SubScope k l σ) :
    SubScope (k + 1) (l + 1) (liftSubstitution σ) := by
  intro n hn
  cases n with
  | zero => exact Nat.zero_lt_succ _
  | succ n => exact (h n (Nat.lt_of_succ_lt_succ hn)).weaken

theorem Scoped.substitute {e : Expr} {k l : Nat} {σ : Nat → Expr}
    (he : Scoped k e) (hσ : SubScope k l σ) : Scoped l (substitute σ e) := by
  induction e generalizing k l σ <;> simp_all [Scoped, HofmannStreicher1994.substitute]
  all_goals grind only [→ SubScope.lift, SubScope]

def SubAgree (k : Nat) (σ τ : Nat → Expr) : Prop := ∀ n, n < k → σ n = τ n

theorem SubAgree.lift {k : Nat} {σ τ : Nat → Expr} (h : SubAgree k σ τ) :
    SubAgree (k + 1) (liftSubstitution σ) (liftSubstitution τ) := by
  intro n hn
  cases n with
  | zero => rfl
  | succ n => exact congrArg weaken (h n (Nat.lt_of_succ_lt_succ hn))

theorem Scoped.substitute_congr {e : Expr} {k : Nat} {σ τ : Nat → Expr}
    (he : Scoped k e) (hστ : SubAgree k σ τ) :
    HofmannStreicher1994.substitute σ e = HofmannStreicher1994.substitute τ e := by
  induction e generalizing k σ τ <;> simp_all [Scoped, HofmannStreicher1994.substitute]
  all_goals grind only [→ SubAgree.lift, SubAgree]

def truncSub (k : Nat) (σ : Nat → Expr) : Nat → Expr :=
  fun n => if n < k then σ n else .zero

theorem Scoped.truncSub {e : Expr} {k : Nat} {σ : Nat → Expr} (he : Scoped k e) :
    HofmannStreicher1994.substitute (truncSub k σ) e =
      HofmannStreicher1994.substitute σ e :=
  he.substitute_congr (fun _ hn => if_pos hn)

theorem IsTm.substitute {e : Expr} {k : Nat} {σ : Nat → Expr}
    (he : IsTm e) (hs : Scoped k e) (hσ : ∀ n, n < k → IsTm (σ n)) :
    IsTm (substitute σ e) := by
  cases e <;> simp_all [IsTm, Scoped, HofmannStreicher1994.substitute]

theorem truncSub_isTm {k : Nat} {σ : Nat → Expr} (hσ : ∀ n, n < k → IsTm (σ n)) :
    ∀ n, IsTm (truncSub k σ n) := by
  intro n
  by_cases hn : n < k
  · simpa only [truncSub, if_pos hn] using hσ n hn
  · simp [truncSub, hn, IsTm]

end HofmannStreicher1994


namespace HofmannStreicher1994

theorem scoped_instantiate {B a : Expr} {k : Nat}
    (hB : Scoped (k + 1) B) (ha : Scoped k a) : Scoped k (instantiate B a) := by
  apply hB.substitute
  intro n hn
  match n with
  | 0 => exact ha
  | n + 1 => exact Nat.lt_of_succ_lt_succ hn

theorem scoped_instantiate₂ {C a b : Expr} {k : Nat}
    (hC : Scoped (k + 2) C) (ha : Scoped k a) (hb : Scoped k b) :
    Scoped k (instantiate₂ C a b) := by
  apply hC.substitute
  intro n hn
  match n with
  | 0 => exact hb
  | 1 => exact ha
  | n + 2 => exact Nat.lt_of_add_lt_add_right hn

theorem scoped_instantiate₃ {C a b p : Expr} {k : Nat}
    (hC : Scoped (k + 3) C) (ha : Scoped k a) (hb : Scoped k b) (hp : Scoped k p) :
    Scoped k (instantiate₃ C a b p) := by
  apply hC.substitute
  intro n hn
  match n with
  | 0 => exact hp
  | 1 => exact hb
  | 2 => exact ha
  | n + 3 => exact Nat.lt_of_add_lt_add_right hn

def CtxScoped : Context → Prop
  | [] => True
  | A :: Γ => CtxScoped Γ ∧ Scoped Γ.length A

def GoodType (k : Nat) (A : Expr) : Prop := Scoped k A ∧ IsTy A
def GoodTerm (k : Nat) (t : Expr) : Prop := Scoped k t ∧ IsTm t
def GoodSub (k l : Nat) (σ : Nat → Expr) : Prop :=
  ∀ n, n < k → GoodTerm l (σ n)

theorem GoodType.subst {k l : Nat} {A : Expr} {σ : Nat → Expr}
    (hA : GoodType k A) (hσ : GoodSub k l σ) : GoodType l (substitute σ A) :=
  ⟨hA.1.substitute (fun n hn => (hσ n hn).1), hA.2.substitute⟩

theorem GoodTerm.subst {k l : Nat} {t : Expr} {σ : Nat → Expr}
    (ht : GoodTerm k t) (hσ : GoodSub k l σ) : GoodTerm l (substitute σ t) :=
  ⟨ht.1.substitute (fun n hn => (hσ n hn).1),
    ht.2.substitute ht.1 (fun n hn => (hσ n hn).2)⟩

theorem GoodTerm.instantiate {k : Nat} {t a : Expr}
    (ht : GoodTerm (k + 1) t) (ha : GoodTerm k a) : GoodTerm k (instantiate t a) := by
  apply ht.subst
  intro n hn
  match n with
  | 0 => exact ha
  | n + 1 => exact ⟨Nat.lt_of_succ_lt_succ hn, trivial⟩

theorem GoodTerm.instantiate₂ {k : Nat} {t a b : Expr}
    (ht : GoodTerm (k + 2) t) (ha : GoodTerm k a) (hb : GoodTerm k b) :
    GoodTerm k (instantiate₂ t a b) := by
  apply ht.subst
  intro n hn
  match n with
  | 0 => exact hb
  | 1 => exact ha
  | n + 2 => exact ⟨Nat.lt_of_add_lt_add_right hn, trivial⟩

theorem ContextEq.length_eq {Γ Δ : Context} : ContextEq Γ Δ → Γ.length = Δ.length
  | .nil => rfl
  | .cons h _ => congrArg Nat.succ (ContextEq.length_eq h)

mutual
  theorem TypeWf.metadata {Γ : Context} {A : Expr} : TypeWf Γ A → GoodType Γ.length A
    | .pi hA hB => ⟨⟨(TypeWf.metadata hA).1, (TypeWf.metadata hB).1⟩, trivial⟩
    | .sigma hA hB => ⟨⟨(TypeWf.metadata hA).1, (TypeWf.metadata hB).1⟩, trivial⟩
    | .identity hA ha hb =>
      ⟨⟨(TypeWf.metadata hA).1, (TermWf.metadata ha).1, (TermWf.metadata hb).1⟩, trivial⟩
    | .nat _ => ⟨trivial, trivial⟩
    | .universe _ => ⟨trivial, trivial⟩
    | .el ha => ⟨(TermWf.metadata ha).1, trivial⟩
    | .subst hA hσ => (TypeWf.metadata hA).subst (SubstitutionWf.metadata hσ)
    | .context hA hΓ => hΓ.length_eq ▸ TypeWf.metadata hA

  theorem TermWf.metadata {Γ : Context} {t A : Expr} : TermWf Γ t A → GoodTerm Γ.length t
    | .var _ hn => ⟨(List.getElem?_eq_some_iff.mp hn).1, trivial⟩
    | .lam hA _ hb => ⟨⟨(TypeWf.metadata hA).1, (TermWf.metadata hb).1⟩, trivial⟩
    | .app hA hB hf ha =>
      ⟨⟨(TypeWf.metadata hA).1, (TypeWf.metadata hB).1,
        (TermWf.metadata hf).1, (TermWf.metadata ha).1⟩, trivial⟩
    | .pair hA hB ha hb =>
      ⟨⟨(TypeWf.metadata hA).1, (TypeWf.metadata hB).1,
        (TermWf.metadata ha).1, (TermWf.metadata hb).1⟩, trivial⟩
    | .sigmaRec hA hB hC hd hp =>
      ⟨⟨(TypeWf.metadata hA).1, (TypeWf.metadata hB).1, (TypeWf.metadata hC).1,
        (TermWf.metadata hd).1, (TermWf.metadata hp).1⟩, trivial⟩
    | .refl hA ha => ⟨⟨(TypeWf.metadata hA).1, (TermWf.metadata ha).1⟩, trivial⟩
    | .idRec hA hC hd ha hb hp =>
      ⟨⟨(TypeWf.metadata hA).1, (TypeWf.metadata hC).1, (TermWf.metadata hd).1,
        (TermWf.metadata ha).1, (TermWf.metadata hb).1, (TermWf.metadata hp).1⟩, trivial⟩
    | .zero _ => ⟨trivial, trivial⟩
    | .succ hn => ⟨(TermWf.metadata hn).1, trivial⟩
    | .natRec hC hz hs hn =>
      ⟨⟨(TypeWf.metadata hC).1, (TermWf.metadata hz).1,
        (TermWf.metadata hs).1, (TermWf.metadata hn).1⟩, trivial⟩
    | .conv ha _ => TermWf.metadata ha
    | .subst ha hσ => (TermWf.metadata ha).subst (SubstitutionWf.metadata hσ)
    | .context ha hΓ => hΓ.length_eq ▸ TermWf.metadata ha

  theorem TypeEq.metadata {Γ : Context} {A B : Expr} :
      TypeEq Γ A B → GoodType Γ.length A ∧ GoodType Γ.length B
    | .refl hA => ⟨TypeWf.metadata hA, TypeWf.metadata hA⟩
    | .symm h => ⟨(TypeEq.metadata h).2, (TypeEq.metadata h).1⟩
    | .trans h₁ h₂ => ⟨(TypeEq.metadata h₁).1, (TypeEq.metadata h₂).2⟩
    | .pi hA hB =>
      ⟨⟨⟨(TypeEq.metadata hA).1.1, (TypeEq.metadata hB).1.1⟩, trivial⟩,
        ⟨⟨(TypeEq.metadata hA).2.1, (TypeEq.metadata hB).2.1⟩, trivial⟩⟩
    | .sigma hA hB =>
      ⟨⟨⟨(TypeEq.metadata hA).1.1, (TypeEq.metadata hB).1.1⟩, trivial⟩,
        ⟨⟨(TypeEq.metadata hA).2.1, (TypeEq.metadata hB).2.1⟩, trivial⟩⟩
    | .identity hA ha hb =>
      ⟨⟨⟨(TypeEq.metadata hA).1.1, (TermEq.metadata ha).1.1, (TermEq.metadata hb).1.1⟩, trivial⟩,
        ⟨⟨(TypeEq.metadata hA).2.1, (TermEq.metadata ha).2.1, (TermEq.metadata hb).2.1⟩, trivial⟩⟩
    | .el h => ⟨⟨(TermEq.metadata h).1.1, trivial⟩, ⟨(TermEq.metadata h).2.1, trivial⟩⟩
    | .subst h hσ => ⟨(TypeEq.metadata h).1.subst (SubstitutionWf.metadata hσ),
        (TypeEq.metadata h).2.subst (SubstitutionWf.metadata hσ)⟩
    | .substEq hA (.mk hσ hτ _) =>
      ⟨(TypeWf.metadata hA).subst (SubstitutionWf.metadata hσ),
        (TypeWf.metadata hA).subst (SubstitutionWf.metadata hτ)⟩
    | .context h hΓ => hΓ.length_eq ▸ TypeEq.metadata h

  theorem TermEq.metadata {Γ : Context} {a b A : Expr} :
      TermEq Γ a b A → GoodTerm Γ.length a ∧ GoodTerm Γ.length b
    | @TermEq.etaPi Γ A B f hA hB hf => by
      have hρ : RenScope Γ.length (Γ.length + 1) Nat.succ := fun _ hn => Nat.succ_lt_succ hn
      exact ⟨⟨⟨(TypeWf.metadata hA).1,
        (TypeWf.metadata hA).1.weaken, (TypeWf.metadata hB).1.rename hρ.lift,
        (TermWf.metadata hf).1.weaken, Nat.zero_lt_succ _⟩, trivial⟩, TermWf.metadata hf⟩
    | .refl h => by exact ⟨TermWf.metadata h, TermWf.metadata h⟩
    | .symm h => by exact ⟨(TermEq.metadata h).2, (TermEq.metadata h).1⟩
    | .trans h₁ h₂ => by exact ⟨(TermEq.metadata h₁).1, (TermEq.metadata h₂).2⟩
    | .conv h _ => by exact TermEq.metadata h
    | .lam hA _ hb => by
      exact ⟨⟨⟨(TypeEq.metadata hA).1.1, (TermEq.metadata hb).1.1⟩, trivial⟩,
        ⟨⟨(TypeEq.metadata hA).2.1, (TermEq.metadata hb).2.1⟩, trivial⟩⟩
    | .app hA hB hf ha => by
      exact ⟨⟨⟨(TypeEq.metadata hA).1.1, (TypeEq.metadata hB).1.1,
        (TermEq.metadata hf).1.1, (TermEq.metadata ha).1.1⟩, trivial⟩,
        ⟨⟨(TypeEq.metadata hA).2.1, (TypeEq.metadata hB).2.1,
        (TermEq.metadata hf).2.1, (TermEq.metadata ha).2.1⟩, trivial⟩⟩
    | .pair hA hB ha hb => by
      exact ⟨⟨⟨(TypeEq.metadata hA).1.1, (TypeEq.metadata hB).1.1,
        (TermEq.metadata ha).1.1, (TermEq.metadata hb).1.1⟩, trivial⟩,
        ⟨⟨(TypeEq.metadata hA).2.1, (TypeEq.metadata hB).2.1,
        (TermEq.metadata ha).2.1, (TermEq.metadata hb).2.1⟩, trivial⟩⟩
    | .sigmaRec hA hB hC hd hp => by
      exact ⟨⟨⟨(TypeEq.metadata hA).1.1, (TypeEq.metadata hB).1.1,
        (TypeEq.metadata hC).1.1, (TermEq.metadata hd).1.1, (TermEq.metadata hp).1.1⟩, trivial⟩,
        ⟨⟨(TypeEq.metadata hA).2.1, (TypeEq.metadata hB).2.1,
        (TypeEq.metadata hC).2.1, (TermEq.metadata hd).2.1, (TermEq.metadata hp).2.1⟩, trivial⟩⟩
    | .reflCongr hA ha => by
      exact ⟨⟨⟨(TypeEq.metadata hA).1.1, (TermEq.metadata ha).1.1⟩, trivial⟩,
        ⟨⟨(TypeEq.metadata hA).2.1, (TermEq.metadata ha).2.1⟩, trivial⟩⟩
    | .idRec hA hC hd ha hb hp => by
      exact ⟨⟨⟨(TypeEq.metadata hA).1.1, (TypeEq.metadata hC).1.1,
        (TermEq.metadata hd).1.1, (TermEq.metadata ha).1.1, (TermEq.metadata hb).1.1,
        (TermEq.metadata hp).1.1⟩, trivial⟩,
        ⟨⟨(TypeEq.metadata hA).2.1, (TypeEq.metadata hC).2.1,
        (TermEq.metadata hd).2.1, (TermEq.metadata ha).2.1, (TermEq.metadata hb).2.1,
        (TermEq.metadata hp).2.1⟩, trivial⟩⟩
    | .succ h => by exact ⟨⟨(TermEq.metadata h).1.1, trivial⟩, ⟨(TermEq.metadata h).2.1, trivial⟩⟩
    | .natRec hC hz hs hn => by
      exact ⟨⟨⟨(TypeEq.metadata hC).1.1, (TermEq.metadata hz).1.1,
        (TermEq.metadata hs).1.1, (TermEq.metadata hn).1.1⟩, trivial⟩,
        ⟨⟨(TypeEq.metadata hC).2.1, (TermEq.metadata hz).2.1,
        (TermEq.metadata hs).2.1, (TermEq.metadata hn).2.1⟩, trivial⟩⟩
    | .betaPi hA hB hb ha => by
      exact ⟨⟨⟨(TypeWf.metadata hA).1, (TypeWf.metadata hB).1,
        ⟨(TypeWf.metadata hA).1, (TermWf.metadata hb).1⟩, (TermWf.metadata ha).1⟩, trivial⟩,
        (TermWf.metadata hb).instantiate (TermWf.metadata ha)⟩
    | .betaSigma hA hB hC hd ha hb => by
      exact ⟨⟨⟨(TypeWf.metadata hA).1, (TypeWf.metadata hB).1, (TypeWf.metadata hC).1,
        (TermWf.metadata hd).1, (TypeWf.metadata hA).1, (TypeWf.metadata hB).1,
        (TermWf.metadata ha).1, (TermWf.metadata hb).1⟩, trivial⟩,
        (TermWf.metadata hd).instantiate₂ (TermWf.metadata ha) (TermWf.metadata hb)⟩
    | .betaId hA hC hd ha => by
      exact ⟨⟨⟨(TypeWf.metadata hA).1, (TypeWf.metadata hC).1, (TermWf.metadata hd).1,
        (TermWf.metadata ha).1, (TermWf.metadata ha).1,
        (TypeWf.metadata hA).1, (TermWf.metadata ha).1⟩, trivial⟩,
        (TermWf.metadata hd).instantiate (TermWf.metadata ha)⟩
    | .betaNatZero hC hz hs => by
      exact ⟨⟨⟨(TypeWf.metadata hC).1, (TermWf.metadata hz).1,
        (TermWf.metadata hs).1, trivial⟩, trivial⟩, TermWf.metadata hz⟩
    | .betaNatSucc hC hz hs hn => by
      exact ⟨⟨⟨(TypeWf.metadata hC).1, (TermWf.metadata hz).1,
        (TermWf.metadata hs).1, (TermWf.metadata hn).1⟩, trivial⟩,
        (TermWf.metadata hs).instantiate₂ (TermWf.metadata hn)
          ⟨⟨(TypeWf.metadata hC).1, (TermWf.metadata hz).1,
            (TermWf.metadata hs).1, (TermWf.metadata hn).1⟩, trivial⟩⟩
    | .subst h hσ => by exact ⟨(TermEq.metadata h).1.subst (SubstitutionWf.metadata hσ),
        (TermEq.metadata h).2.subst (SubstitutionWf.metadata hσ)⟩
    | .substEq h hστ => by
      cases hστ with
      | mk hσ hτ _ => exact ⟨(TermWf.metadata h).subst (SubstitutionWf.metadata hσ),
          (TermWf.metadata h).subst (SubstitutionWf.metadata hτ)⟩
    | .context h hΓ => by exact hΓ.length_eq ▸ TermEq.metadata h


  theorem SubstitutionWf.metadata {Γ Δ : Context} {σ : Nat → Expr} :
      SubstitutionWf Γ Δ σ → GoodSub Γ.length Δ.length σ
    | .mk _ _ h => fun n hn => TermWf.metadata (h n (Γ[n]) (List.getElem?_eq_getElem hn))
end

theorem ContextWf.scoped {Γ : Context} : ContextWf Γ → CtxScoped Γ
  | .nil => trivial
  | .cons hΓ hA => ⟨ContextWf.scoped hΓ, (TypeWf.metadata hA).1⟩

theorem SubstitutionEq.metadata {Γ Δ : Context} {σ τ : Nat → Expr} :
    SubstitutionEq Γ Δ σ τ → GoodSub Γ.length Δ.length σ ∧ GoodSub Γ.length Δ.length τ
  | .mk hσ hτ _ => ⟨SubstitutionWf.metadata hσ, SubstitutionWf.metadata hτ⟩

end HofmannStreicher1994

open HofmannStreicher1994

theorem solution
    (Γ : Context) (e : Expr) (σ τ : Nat → Expr)
    (h : TypeWf Γ e ∨ ∃ A, TermWf Γ e A)
    (hστ : ∀ n, n < Γ.length → σ n = τ n) :
    substitute σ e = substitute τ e := by
  have he : Scoped Γ.length e := h.elim (fun hA => hA.metadata.1)
    (fun ⟨_, ht⟩ => ht.metadata.1)
  exact he.substitute_congr hστ
