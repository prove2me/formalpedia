-- Prove2me | solution 1 for Grodin2026.lemmas_4_4_to_4_12_credits_debits_and_clist
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T17:23:27.769767+00:00
-- url     : https://prove2.me/submissions/4a6d6b8e-66a3-4c55-8a05-e3f82bda016c

import Definitions.Def_Grodin2026_Banker

open Grodin2026

/-- Equivalence between the physicist's $\mathsf{Potential}(\Phi : X \to \mathbb{N})$ and the
banker's dependent copower $(x : X) \ltimes \triangleright^{\Phi(x)} \top$ (Lemma 4.10). -/
private def potentialBankerEquiv (X : Type) (Phi : X → Nat) :
    CompEquiv (PotentialType X Phi) (BankerPotentialComp X Phi) where
  toHom := {
    hom_top := {
      fn := fun ⟨c, x⟩ => ⟨x, (c, PUnit.unit)⟩
      map_charge := fun _ _ => rfl
      mono := by
        rintro ⟨c₁, x₁⟩ ⟨c₂, x₂⟩ ⟨h, rfl⟩
        exact ⟨rfl, h, rfl⟩
    }
    hom_abs := {
      fn := fun ⟨c, x⟩ => ⟨x, (c, PUnit.unit)⟩
      map_charge := fun _ _ => rfl
      mono := by
        rintro ⟨c₁, x₁⟩ ⟨c₂, x₂⟩ ⟨h, rfl⟩
        exact ⟨rfl, h, rfl⟩
    }
    comm := fun ⟨c, x⟩ =>
      congrArg (fun k => (⟨x, (k, PUnit.unit)⟩ : (BankerPotentialComp X Phi).abs.carrier))
        (Nat.add_comm (Phi x) c)
  }
  invHom := {
    hom_top := {
      fn := fun ⟨x, (c, _)⟩ => (c, x)
      map_charge := fun _ ⟨_, (_, _)⟩ => rfl
      mono := by
        rintro ⟨x₁, ⟨c₁, _⟩⟩ ⟨x₂, ⟨c₂, _⟩⟩ ⟨rfl, h, _⟩
        exact ⟨h, rfl⟩
    }
    hom_abs := {
      fn := fun ⟨x, (c, _)⟩ => (c, x)
      map_charge := fun _ ⟨_, (_, _)⟩ => rfl
      mono := by
        rintro ⟨x₁, ⟨c₁, _⟩⟩ ⟨x₂, ⟨c₂, _⟩⟩ ⟨rfl, h, _⟩
        exact ⟨h, rfl⟩
    }
    comm := fun ⟨x, (c, _)⟩ =>
      Prod.ext (Nat.add_comm c (Phi x)) rfl
  }
  left_inv := rfl
  right_inv := by
    ext p <;> {
      rcases p with ⟨x, ⟨c, ⟨⟩⟩⟩
      rfl
    }

/-- Credit–debit hom-type adjunction $\mathsf{LaxCompHom}(\triangleright^c A, B) \simeq
\mathsf{CompHom}(A, \triangleleft^c B)$ (Lemma 4.12). -/
private def creditDebitAdjEquiv (c : Nat) (A B : CompType) :
    LaxCompHom (CreditComp c A) B ≃ CompHom A (DebitComp c B) where
  toFun := fun f => {
    hom_top := {
      fn := fun (a : A.top.carrier) => ⟨(f.hom_top.fn a, f.hom_abs.fn (A.alpha.fn a)), by
        have h_lax := f.lax_comm a
        have h_eq : f.hom_abs.fn ((CreditComp c A).alpha.fn a) =
            B.abs.charge c (f.hom_abs.fn (A.alpha.fn a)) :=
          f.hom_abs.map_charge c (A.alpha.fn a)
        rw [h_eq] at h_lax
        exact h_lax⟩
      map_charge := fun c' (a : A.top.carrier) => by
        apply Subtype.ext
        apply Prod.ext
        · exact f.hom_top.map_charge c' a
        · calc f.hom_abs.fn (A.alpha.fn (A.top.charge c' a))
            _ = f.hom_abs.fn (A.abs.charge c' (A.alpha.fn a)) :=
              congrArg f.hom_abs.fn (A.alpha.map_charge c' a)
            _ = B.abs.charge c' (f.hom_abs.fn (A.alpha.fn a)) :=
              f.hom_abs.map_charge c' (A.alpha.fn a)
      mono := fun h => ⟨f.hom_top.mono h, f.hom_abs.mono (A.alpha.mono h)⟩
    }
    hom_abs := f.hom_abs
    comm := fun _ => rfl
  }
  invFun := fun g => {
    hom_top := {
      fn := fun a => (g.hom_top.fn a).1.1
      map_charge := fun c' a =>
        congrArg (fun p => p.1.1) (g.hom_top.map_charge c' a)
      mono := fun h => (g.hom_top.mono h).1
    }
    hom_abs := g.hom_abs
    lax_comm := fun (a : A.top.carrier) => by
      have h_sub : B.abs.le (B.alpha.fn (g.hom_top.fn a).1.1)
          (B.abs.charge c (g.hom_top.fn a).1.2) :=
        (g.hom_top.fn a).2
      have h_comm : (g.hom_top.fn a).1.2 = g.hom_abs.fn (A.alpha.fn a) :=
        g.comm a
      rw [h_comm] at h_sub
      have h_eq : B.abs.charge c (g.hom_abs.fn (A.alpha.fn a)) =
          g.hom_abs.fn ((CreditComp c A).alpha.fn a) :=
        (g.hom_abs.map_charge c (A.alpha.fn a)).symm
      rw [h_eq] at h_sub
      exact h_sub
  }
  left_inv := fun f => by
    ext a <;> rfl
  right_inv := fun g => by
    ext a
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact (g.comm a).symm
    · rfl

/-- Exact cost and value formula for `revAppendTop` (Example 4.15). -/
private theorem revAppendTop_eq {X : Type} (l : List X) :
    ∀ acc : List X, revAppendTop l acc = (l.length, l.reverseAux acc) := by
  induction l with
  | nil =>
      intro acc
      rfl
  | cons x xs ih =>
      intro acc
      simp only [revAppendTop, ih (x :: acc), List.length_cons, List.reverseAux]
      exact Prod.ext (Nat.add_comm 1 xs.length) rfl

/-- Strict computation homomorphism for `reverse` on $\mathsf{CList}^1_1(FX)$ (Example 4.15). -/
private def reverseCList1CompHom (X : Type) :
    CompHom (CList1Comp 1 X) (FreeComp (List X)) where
  hom_top := reverseCList1Top
  hom_abs := reverseCList1Abs
  comm := fun ⟨c₀, l⟩ => by
    apply Prod.ext
    · change c₀ + (revAppendTop l []).1 = c₀ + l.length * 1
      rw [revAppendTop_eq l [], Nat.mul_one]
    · change (revAppendTop l []).2 = l.reverse
      rw [revAppendTop_eq l []]
      rfl

/-- Constructive proof of Milestone 4 (Lemmas 4.4, 4.6, 4.8, 4.10, 4.12, Corollaries 4.14 & 4.19, Example 4.15). -/
theorem solution :
    (∀ (c : Nat) (A : CompType),
      ClosedComp (CreditComp c A) = ClosedComp A ∧
      OpenComp (CreditComp c A) = OpenComp A) ∧
    (∀ (A : CompType),
      CreditComp 0 A = A ∧
      (∀ c₁ c₂ : Nat, CreditComp (c₁ + c₂) A = CreditComp c₁ (CreditComp c₂ A))) ∧
    (∀ (c : Nat) (A : CompType),
      (spendComp c A).comp (saveComp c A) = chargeCompHom A c) ∧
    (∀ (X : Type) (Phi : X → Nat),
      Nonempty (CompEquiv (PotentialType X Phi) (BankerPotentialComp X Phi))) ∧
    (∀ (c : Nat) (A B : CompType),
      Nonempty (LaxCompHom (CreditComp c A) B ≃ CompHom A (DebitComp c B))) ∧
    (∀ (X : Type) (c c₁ c₂ : Nat),
      OpenComp (CList1Comp c X) = OpenComp (FreeComp (List X)) ∧
      OpenComp (CList2Comp c₁ c₂ X) = OpenComp (FreeComp (List X)) ∧
      (∀ l acc : List X, revAppendTop l acc = (l.length, l.reverseAux acc)) ∧
      ∃ revHom : CompHom (CList1Comp 1 X) (FreeComp (List X)),
        revHom.hom_top = reverseCList1Top ∧ revHom.hom_abs = reverseCList1Abs) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c A
    exact ⟨rfl, rfl⟩
  · intro A
    refine ⟨?_, ?_⟩
    · cases A with
      | mk top abs alpha =>
        exact congrArg (CompType.mk top abs)
          (CostHom.ext (funext (fun a => abs.charge_zero (alpha.fn a))))
    · intro c₁ c₂
      cases A with
      | mk top abs alpha =>
        exact congrArg (CompType.mk top abs)
          (CostHom.ext (funext (fun a => abs.charge_add c₁ c₂ (alpha.fn a))))
  · intro c A
    ext a <;> rfl
  · intro X Phi
    exact ⟨potentialBankerEquiv X Phi⟩
  · intro c A B
    exact ⟨creditDebitAdjEquiv c A B⟩
  · intro X c c₁ c₂
    exact ⟨rfl, rfl, fun l acc => revAppendTop_eq l acc,
      reverseCList1CompHom X, rfl, rfl⟩
