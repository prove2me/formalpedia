-- Prove2me | solution 1 for Grodin2026.theorems_2_3_to_2_7_value_fracture_gluing
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T17:23:25.503473+00:00
-- url     : https://prove2.me/submissions/4262c306-2510-410c-97fb-8cbe7f4ca6b6

import Definitions.Def_Grodin2026_Physicist

open Grodin2026

/-- Helper: under `h : abs`, every element of `ClosedModal abs X` equals `starClosed abs h`. -/
private theorem closedModal_eq_star (abs : Prop) (X : Type) (h : abs)
    (z : ClosedModal abs X) : z = starClosed abs (X := X) h := by
  refine Quot.inductionOn z (fun s => ?_)
  cases s with
  | inl x => exact closed_glue abs x h
  | inr ha => rfl

/-- Canonical equivalence $X \simeq \mathsf{Glue}(\bullet X, \bigcirc X, \bullet \eta^\circ_X)$
(Theorem 2.3). -/
private def valFractureGlueEquiv (X : ValType) : ValEquiv X (FractureGlueVal X) where
  toHom := {
    f_top := fun x => ⟨(x, X.chi x), rfl⟩
    f_abs := fun y => ⟨(PUnit.unit, y), rfl⟩
    comm := fun _ => rfl
  }
  invHom := {
    f_top := fun p => p.1.1
    f_abs := fun p => p.1.2
    comm := fun p => p.2
  }
  left_inv := rfl
  right_inv := by
    ext p
    · rcases p with ⟨⟨x, y⟩, h⟩
      change (⟨(x, X.chi x), rfl⟩ : (FractureGlueVal X).top) = ⟨(x, y), h⟩
      apply Subtype.ext
      exact Prod.ext rfl h
    · rcases p with ⟨⟨⟨⟩, y⟩, h⟩
      rfl

/-- Canonical equivalence $\bullet(\mathsf{Glue}(\bullet X, \bigcirc X, \bullet \eta^\circ_X)) \simeq \bullet X$
(Theorem 2.3). -/
private def closedFractureGlueValEquiv (X : ValType) :
    ValEquiv (ClosedVal (FractureGlueVal X)) (ClosedVal X) where
  toHom := {
    f_top := fun p => p.1.1
    f_abs := fun _ => PUnit.unit
    comm := fun _ => rfl
  }
  invHom := {
    f_top := fun x => ⟨(x, X.chi x), rfl⟩
    f_abs := fun _ => PUnit.unit
    comm := fun _ => rfl
  }
  left_inv := by
    ext p
    · rcases p with ⟨⟨x, y⟩, h⟩
      apply Subtype.ext
      exact Prod.ext rfl h
    · rfl
  right_inv := rfl

/-- Canonical equivalence $\bigcirc(\mathsf{Glue}(\bullet X, \bigcirc X, \bullet \eta^\circ_X)) \simeq \bigcirc X$
(Theorem 2.3). -/
private def openFractureGlueValEquiv (X : ValType) :
    ValEquiv (OpenVal (FractureGlueVal X)) (OpenVal X) where
  toHom := {
    f_top := fun p => p.1.2
    f_abs := fun p => p.1.2
    comm := fun _ => rfl
  }
  invHom := {
    f_top := fun y => ⟨(PUnit.unit, y), rfl⟩
    f_abs := fun y => ⟨(PUnit.unit, y), rfl⟩
    comm := fun _ => rfl
  }
  left_inv := by
    ext p <;> {
      rcases p with ⟨⟨⟨⟩, y⟩, _⟩
      rfl
    }
  right_inv := rfl

/-- Canonical equivalence between the pullback gluing form and direct form of
$\mathsf{Abstraction}(\chi : X_\top \to X_{\mathsf{abs}})$ (Definition 2.5). -/
private def glueAbstractionValEquiv (X_top X_abs : Type) (chi : X_top → X_abs) :
    ValEquiv (GlueAbstractionVal X_top X_abs chi) (AbstractionVal X_top X_abs chi) :=
  (valFractureGlueEquiv (AbstractionVal X_top X_abs chi)).symm

/-- Constructive proof of Milestone 1 (Theorem 2.3, Corollaries 2.4 & 2.6, Lemma 2.7, Example 2.8). -/
theorem solution :
    (∀ (abs : Prop) (X : Type), abs → ∀ z₁ z₂ : ClosedModal abs X, z₁ = z₂) ∧
    (∀ X : ValType,
      Nonempty (ValEquiv X (FractureGlueVal X)) ∧
      Nonempty (ValEquiv (ClosedVal (FractureGlueVal X)) (ClosedVal X)) ∧
      Nonempty (ValEquiv (OpenVal (FractureGlueVal X)) (OpenVal X))) ∧
    (∀ (X_top X_abs : Type) (chi : X_top → X_abs),
      Nonempty (ValEquiv (GlueAbstractionVal X_top X_abs chi) (AbstractionVal X_top X_abs chi))) ∧
    (∀ T : Type,
      Nonempty (ValEquiv (ConstVal T) (GlueAbstractionVal T T id))) ∧
    (∀ {X Y : ValType} (f : ValHom X Y),
      (ClosedVal.map (etaOpenVal Y)).comp (ClosedVal.map f) =
        ClosedVal.map ((OpenVal.map f).comp (etaOpenVal X))) ∧
    (∀ (α : Type) (n : α),
      ∃ enq : ValHom (BatchedQueueVal α) (BatchedQueueVal α),
        enq.f_top = enqueueValTop n ∧ enq.f_abs = enqueueValAbs n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro abs X h z₁ z₂
    rw [closedModal_eq_star abs X h z₁, closedModal_eq_star abs X h z₂]
  · intro X
    exact ⟨⟨valFractureGlueEquiv X⟩, ⟨closedFractureGlueValEquiv X⟩, ⟨openFractureGlueValEquiv X⟩⟩
  · intro X_top X_abs chi
    exact ⟨glueAbstractionValEquiv X_top X_abs chi⟩
  · intro T
    exact ⟨valFractureGlueEquiv (ConstVal T)⟩
  · intro X Y f
    ext x
    · exact f.comm x
    · rfl
  · intro α n
    refine ⟨{
      f_top := enqueueValTop n
      f_abs := enqueueValAbs n
      comm := fun ⟨l₁, l₂⟩ => by
        simp [BatchedQueueVal, AbstractionVal, queueChi, enqueueValTop, enqueueValAbs, List.append_assoc]
    }, rfl, rfl⟩
