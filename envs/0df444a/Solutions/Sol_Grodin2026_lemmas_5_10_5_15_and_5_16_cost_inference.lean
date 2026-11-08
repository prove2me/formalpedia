-- Prove2me | solution 1 for Grodin2026.lemmas_5_10_5_15_and_5_16_cost_inference
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T17:23:29.131238+00:00
-- url     : https://prove2.me/submissions/5845bf8a-e885-4919-8e4b-03369923ba85

import Definitions.Def_Grodin2026_Giralf

open Grodin2026

/-- Under `h : ¬ abs`, the synthetic abstract modality `OpenModal abs X = (abs → X)` is equivalent
to `PUnit` (Lemma 5.10). -/
private def openModalNotAbsEquiv (abs : Prop) (X : Type) (h : ¬ abs) :
    OpenModal abs X ≃ PUnit where
  toFun := fun _ => PUnit.unit
  invFun := fun _ ha => False.elim (h ha)
  left_inv := fun _ => funext (fun ha => False.elim (h ha))
  right_inv := fun ⟨⟩ => rfl

/-- Under `h : ¬ abs`, `ClosedRel abs X` only relates `Sum.inl x₁` and `Sum.inl x₂` when `x₁ = x₂`. -/
private def closedModalExtract (abs : Prop) (X : Type) (h : ¬ abs) :
    Sum X (PLift abs) → X
  | .inl x => x
  | .inr ⟨ha⟩ => False.elim (h ha)

private theorem closedModalExtract_respects (abs : Prop) (X : Type) (h : ¬ abs)
    {s₁ s₂ : Sum X (PLift abs)} (rel : ClosedRel abs X s₁ s₂) :
    closedModalExtract abs X h s₁ = closedModalExtract abs X h s₂ := by
  induction rel with
  | refl _ => rfl
  | glue _ ha => exact False.elim (h ha)
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact Eq.trans ih₁ ih₂

/-- Under `h : ¬ abs`, the synthetic concrete pushout `ClosedModal abs X` is equivalent to `X`
(Lemma 5.10). -/
private def closedModalNotAbsEquiv (abs : Prop) (X : Type) (h : ¬ abs) :
    ClosedModal abs X ≃ X where
  toFun := Quot.lift (closedModalExtract abs X h) (fun _ _ rel => closedModalExtract_respects abs X h rel)
  invFun := etaClosed abs
  left_inv := fun z => by
    refine Quot.inductionOn z (fun s => ?_)
    cases s with
    | inl x => rfl
    | inr ha => exact False.elim (h ha.down)
  right_inv := fun _ => rfl

/-- Lemma 5.16 (and the addition half of Lemma 5.15):
adding a cost-free annotation (`ValidSnocRecAnnotation 0 A₂`) to a cost-aware annotation
(`ValidSnocRecAnnotation stepCost A₁`) preserves validity for `stepCost`. -/
private theorem validSnocRecAnnotation_add (stepCost : Nat) (A₁ A₂ : ListRecAnnotation)
    (h₁ : ValidSnocRecAnnotation stepCost A₁)
    (h₂ : ValidSnocRecAnnotation 0 A₂) :
    ValidSnocRecAnnotation stepCost (ListRecAnnotation.add A₁ A₂) := by
  intro n
  have hn₁ := h₁ n
  have hn₂ := h₂ n
  simp only [ListRecAnnotation.add] at hn₁ hn₂ ⊢
  have d₁ : (n + 1) * (A₁.out_lin + A₂.out_lin) =
      (n + 1) * A₁.out_lin + (n + 1) * A₂.out_lin :=
    Nat.left_distrib (n + 1) A₁.out_lin A₂.out_lin
  have d₂ : binom2 (n + 1) * (A₁.out_quad + A₂.out_quad) =
      binom2 (n + 1) * A₁.out_quad + binom2 (n + 1) * A₂.out_quad :=
    Nat.left_distrib (binom2 (n + 1)) A₁.out_quad A₂.out_quad
  have d₃ : n * (A₁.in_lin + A₂.in_lin) = n * A₁.in_lin + n * A₂.in_lin :=
    Nat.left_distrib n A₁.in_lin A₂.in_lin
  have d₄ : binom2 n * (A₁.in_quad + A₂.in_quad) =
      binom2 n * A₁.in_quad + binom2 n * A₂.in_quad :=
    Nat.left_distrib (binom2 n) A₁.in_quad A₂.in_quad
  omega

/-- Scalar multiplication half of Lemma 5.15:
multiplying a cost-free annotation (`ValidSnocRecAnnotation 0 A₁`) by `k : Nat` preserves
cost-free validity. -/
private theorem validSnocRecAnnotation_smul (k : Nat) (A₁ : ListRecAnnotation)
    (h₁ : ValidSnocRecAnnotation 0 A₁) :
    ValidSnocRecAnnotation 0 (ListRecAnnotation.smul k A₁) := by
  intro n
  have hn₁ := h₁ n
  simp only [ListRecAnnotation.smul, Nat.mul_zero, Nat.zero_add] at hn₁ ⊢
  have hk := Nat.mul_le_mul_left k hn₁
  have e₁ : (n + 1) * (k * A₁.out_lin) = k * ((n + 1) * A₁.out_lin) := by
    rw [← Nat.mul_assoc, Nat.mul_comm (n + 1) k, Nat.mul_assoc]
  have e₂ : binom2 (n + 1) * (k * A₁.out_quad) = k * (binom2 (n + 1) * A₁.out_quad) := by
    rw [← Nat.mul_assoc, Nat.mul_comm (binom2 (n + 1)) k, Nat.mul_assoc]
  have e₃ : n * (k * A₁.in_lin) = k * (n * A₁.in_lin) := by
    rw [← Nat.mul_assoc, Nat.mul_comm n k, Nat.mul_assoc]
  have e₄ : binom2 n * (k * A₁.in_quad) = k * (binom2 n * A₁.in_quad) := by
    rw [← Nat.mul_assoc, Nat.mul_comm (binom2 n) k, Nat.mul_assoc]
  have d_lhs : k * ((n + 1) * A₁.out_lin) + k * (binom2 (n + 1) * A₁.out_quad) =
      k * ((n + 1) * A₁.out_lin + binom2 (n + 1) * A₁.out_quad) :=
    (Nat.left_distrib k _ _).symm
  have d_rhs :
      k * (n * A₁.in_lin) + k * (binom2 n * A₁.in_quad) + k * A₁.ctx_q + k * A₁.debit =
      k * (n * A₁.in_lin + binom2 n * A₁.in_quad + A₁.ctx_q + A₁.debit) := by
    simp only [Nat.left_distrib, Nat.add_assoc]
  rw [e₁, e₂, d_lhs, e₃, e₄, d_rhs]
  exact hk

private theorem valid_snocAnnCA : ValidSnocRecAnnotation 1 snocAnnCA := by
  intro n
  simp [snocAnnCA]

private theorem valid_snocAnnCF1 : ValidSnocRecAnnotation 0 snocAnnCF1 := by
  intro n
  simp [snocAnnCF1]

private theorem valid_snocAnnCF2 : ValidSnocRecAnnotation 0 snocAnnCF2 := by
  intro n
  simp [snocAnnCF2, binom2]

/-- Constructive proof of Milestone 6 (Lemma 5.10, Corollary 5.11, Lemmas 5.15 & 5.16, Examples 5.14 & 5.17). -/
theorem solution :
    (∀ (abs : Prop) (X : Type),
      ¬ abs → Nonempty (OpenModal abs X ≃ PUnit) ∧ Nonempty (ClosedModal abs X ≃ X)) ∧
    (∀ (A_top A_abs : CostAlg) (alpha : CostHom A_top A_abs) (A : CompType)
       (X : Type) (p c c₁ c₂ : Nat),
      (AbstractionComp A_top A_abs alpha).top = A_top ∧
      (CreditComp p A).top = A.top ∧
      (spendComp c A).hom_top = chargeCostHom A.top c ∧
      (CList1Comp c X).top = FreeCostAlg (List X) ∧
      (CList2Comp c₁ c₂ X).top = FreeCostAlg (List X)) ∧
    (∀ (A₁ A₂ : ListRecAnnotation) (k : Nat),
      ValidSnocRecAnnotation 0 A₁ →
      ValidSnocRecAnnotation 0 A₂ →
      ValidSnocRecAnnotation 0 (ListRecAnnotation.add A₁ A₂) ∧
      ValidSnocRecAnnotation 0 (ListRecAnnotation.smul k A₁)) ∧
    (∀ (stepCost : Nat) (A₁ A₂ : ListRecAnnotation),
      ValidSnocRecAnnotation stepCost A₁ →
      ValidSnocRecAnnotation 0 A₂ →
      ValidSnocRecAnnotation stepCost (ListRecAnnotation.add A₁ A₂)) ∧
    (ValidSnocRecAnnotation 1 snocAnnCA ∧
     ValidSnocRecAnnotation 0 snocAnnCF1 ∧
     ValidSnocRecAnnotation 0 snocAnnCF2 ∧
     ∀ p₁ p₂ : Nat,
       snocSymbolicAnnotation p₁ p₂ = ⟨1 + p₁ + p₂, p₂, 0, p₁, p₁, p₂⟩ ∧
       ValidSnocRecAnnotation 1 (snocSymbolicAnnotation p₁ p₂)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro abs X h
    exact ⟨⟨openModalNotAbsEquiv abs X h⟩, ⟨closedModalNotAbsEquiv abs X h⟩⟩
  · intro A_top A_abs alpha A X p c c₁ c₂
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · intro A₁ A₂ k h₁ h₂
    exact ⟨validSnocRecAnnotation_add 0 A₁ A₂ h₁ h₂, validSnocRecAnnotation_smul k A₁ h₁⟩
  · intro stepCost A₁ A₂ h₁ h₂
    exact validSnocRecAnnotation_add stepCost A₁ A₂ h₁ h₂
  · refine ⟨valid_snocAnnCA, valid_snocAnnCF1, valid_snocAnnCF2, ?_⟩
    intro p₁ p₂
    refine ⟨?_, ?_⟩
    · simp [snocSymbolicAnnotation, ListRecAnnotation.add, ListRecAnnotation.smul,
        snocAnnCA, snocAnnCF1, snocAnnCF2]
    · exact validSnocRecAnnotation_add 1
        (ListRecAnnotation.add snocAnnCA (ListRecAnnotation.smul p₁ snocAnnCF1))
        (ListRecAnnotation.smul p₂ snocAnnCF2)
        (validSnocRecAnnotation_add 1 snocAnnCA (ListRecAnnotation.smul p₁ snocAnnCF1)
          valid_snocAnnCA (validSnocRecAnnotation_smul p₁ snocAnnCF1 valid_snocAnnCF1))
        (validSnocRecAnnotation_smul p₂ snocAnnCF2 valid_snocAnnCF2)
