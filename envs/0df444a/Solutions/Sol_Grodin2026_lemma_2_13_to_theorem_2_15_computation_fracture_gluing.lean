-- Prove2me | solution 1 for Grodin2026.lemma_2_13_to_theorem_2_15_computation_fracture_gluing
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-07T17:23:26.231981+00:00
-- url     : https://prove2.me/submissions/f59bd0a2-d354-4b35-934f-4edfd19713fa

import Definitions.Def_Grodin2026_Physicist

open Grodin2026

/-- Lex preservation of pullbacks by $\bigcirc$ on computation types (Lemma 2.14). -/
private def openCompPullbackEquiv {A B C : CompType}
    (f : CompHom A C) (g : CompHom B C) :
    CompEquiv (OpenComp (CompPullback f g))
      (CompPullback (OpenComp.map f) (OpenComp.map g)) where
  toHom := {
    hom_top := CostHom.id _
    hom_abs := CostHom.id _
    comm := fun _ => rfl
  }
  invHom := {
    hom_top := CostHom.id _
    hom_abs := CostHom.id _
    comm := fun _ => rfl
  }
  left_inv := rfl
  right_inv := rfl

/-- Lex preservation of pullbacks by $\bullet$ on computation types (Lemma 2.14). -/
private def closedCompPullbackEquiv {A B C : CompType}
    (f : CompHom A C) (g : CompHom B C) :
    CompEquiv (ClosedComp (CompPullback f g))
      (CompPullback (ClosedComp.map f) (ClosedComp.map g)) where
  toHom := {
    hom_top := CostHom.id _
    hom_abs := {
      fn := fun _ => ⟨(PUnit.unit, PUnit.unit), rfl⟩
      map_charge := fun _ _ => rfl
      mono := fun _ => ⟨trivial, trivial⟩
    }
    comm := fun _ => rfl
  }
  invHom := {
    hom_top := CostHom.id _
    hom_abs := toUnitCostHom _
    comm := fun _ => rfl
  }
  left_inv := rfl
  right_inv := by
    ext p
    · rfl
    · rcases p with ⟨⟨⟨⟩, ⟨⟩⟩, _⟩
      rfl

/-- Canonical fracture and gluing equivalence
$A \simeq \mathsf{Glue}(\bullet A, \bigcirc A, \bullet \eta^\circ_A)$ in $\mathcal{C}$
(Theorem 2.15). -/
private def compFractureGlueEquiv (A : CompType) : CompEquiv A (FractureGlueComp A) where
  toHom := {
    hom_top := {
      fn := fun a => ⟨(a, A.alpha.fn a), rfl⟩
      map_charge := fun c a => Subtype.ext (Prod.ext rfl (A.alpha.map_charge c a))
      mono := fun h => ⟨h, A.alpha.mono h⟩
    }
    hom_abs := {
      fn := fun b => ⟨(PUnit.unit, b), rfl⟩
      map_charge := fun _ _ => rfl
      mono := fun h => ⟨trivial, h⟩
    }
    comm := fun _ => rfl
  }
  invHom := {
    hom_top := {
      fn := fun p => p.1.1
      map_charge := fun _ _ => rfl
      mono := fun h => h.1
    }
    hom_abs := {
      fn := fun p => p.1.2
      map_charge := fun _ _ => rfl
      mono := fun h => h.2
    }
    comm := fun p => p.2
  }
  left_inv := rfl
  right_inv := by
    ext p
    · rcases p with ⟨⟨a, b⟩, h⟩
      apply Subtype.ext
      exact Prod.ext rfl h
    · rcases p with ⟨⟨⟨⟩, b⟩, _⟩
      rfl

/-- Canonical equivalence $\bullet(\mathsf{Glue}(\bullet A, \bigcirc A, \bullet \eta^\circ_A)) \simeq \bullet A$
(Theorem 2.15). -/
private def closedFractureGlueCompEquiv (A : CompType) :
    CompEquiv (ClosedComp (FractureGlueComp A)) (ClosedComp A) where
  toHom := {
    hom_top := {
      fn := fun p => p.1.1
      map_charge := fun _ _ => rfl
      mono := fun h => h.1
    }
    hom_abs := toUnitCostHom _
    comm := fun _ => rfl
  }
  invHom := {
    hom_top := {
      fn := fun a => ⟨(a, A.alpha.fn a), rfl⟩
      map_charge := fun c a => Subtype.ext (Prod.ext rfl (A.alpha.map_charge c a))
      mono := fun h => ⟨h, A.alpha.mono h⟩
    }
    hom_abs := toUnitCostHom _
    comm := fun _ => rfl
  }
  left_inv := by
    ext p
    · rcases p with ⟨⟨a, b⟩, h⟩
      apply Subtype.ext
      exact Prod.ext rfl h
    · rfl
  right_inv := rfl

/-- Canonical equivalence $\bigcirc(\mathsf{Glue}(\bullet A, \bigcirc A, \bullet \eta^\circ_A)) \simeq \bigcirc A$
(Theorem 2.15). -/
private def openFractureGlueCompEquiv (A : CompType) :
    CompEquiv (OpenComp (FractureGlueComp A)) (OpenComp A) where
  toHom := {
    hom_top := {
      fn := fun p => p.1.2
      map_charge := fun _ _ => rfl
      mono := fun h => h.2
    }
    hom_abs := {
      fn := fun p => p.1.2
      map_charge := fun _ _ => rfl
      mono := fun h => h.2
    }
    comm := fun _ => rfl
  }
  invHom := {
    hom_top := {
      fn := fun b => ⟨(PUnit.unit, b), rfl⟩
      map_charge := fun _ _ => rfl
      mono := fun h => ⟨trivial, h⟩
    }
    hom_abs := {
      fn := fun b => ⟨(PUnit.unit, b), rfl⟩
      map_charge := fun _ _ => rfl
      mono := fun h => ⟨trivial, h⟩
    }
    comm := fun _ => rfl
  }
  left_inv := by
    ext p <;> {
      rcases p with ⟨⟨⟨⟩, b⟩, _⟩
      rfl
    }
  right_inv := rfl

/-- Equivalence between pullback-glued and direct forms of
$\mathsf{Abstraction}(\alpha : A_\top \multimap A_{\mathsf{abs}})$ (Definition 2.17). -/
private def glueAbstractionCompEquiv (A_top A_abs : CostAlg) (alpha : CostHom A_top A_abs) :
    CompEquiv (GlueAbstractionComp A_top A_abs alpha) (AbstractionComp A_top A_abs alpha) :=
  (compFractureGlueEquiv (AbstractionComp A_top A_abs alpha)).symm

/-- Constructive proof of Milestone 2 (Lemmas 2.13–2.14, Theorem 2.15, Corollaries 2.16 & 2.18, Lemma 2.19). -/
theorem solution :
    (∀ A : CompType,
      ForgetComp (OpenComp A) = OpenVal (ForgetComp A) ∧
      ForgetComp (ClosedComp A) = ClosedVal (ForgetComp A)) ∧
    (∀ {A B C : CompType} (f : CompHom A C) (g : CompHom B C),
      Nonempty (CompEquiv (OpenComp (CompPullback f g))
        (CompPullback (OpenComp.map f) (OpenComp.map g))) ∧
      Nonempty (CompEquiv (ClosedComp (CompPullback f g))
        (CompPullback (ClosedComp.map f) (ClosedComp.map g)))) ∧
    (∀ A : CompType,
      Nonempty (CompEquiv A (FractureGlueComp A)) ∧
      Nonempty (CompEquiv (ClosedComp (FractureGlueComp A)) (ClosedComp A)) ∧
      Nonempty (CompEquiv (OpenComp (FractureGlueComp A)) (OpenComp A))) ∧
    (∀ (A_top A_abs : CostAlg) (alpha : CostHom A_top A_abs),
      Nonempty (CompEquiv (GlueAbstractionComp A_top A_abs alpha)
        (AbstractionComp A_top A_abs alpha))) ∧
    (∀ C₀ : CostAlg,
      Nonempty (CompEquiv (ConstComp C₀) (GlueAbstractionComp C₀ C₀ (CostHom.id C₀)))) ∧
    (∀ {A B : CompType} (f : CompHom A B),
      (ClosedComp.map (etaOpenComp B)).comp (ClosedComp.map f) =
        ClosedComp.map ((OpenComp.map f).comp (etaOpenComp A))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A
    exact ⟨rfl, rfl⟩
  · intro A B C f g
    exact ⟨⟨openCompPullbackEquiv f g⟩, ⟨closedCompPullbackEquiv f g⟩⟩
  · intro A
    exact ⟨⟨compFractureGlueEquiv A⟩, ⟨closedFractureGlueCompEquiv A⟩, ⟨openFractureGlueCompEquiv A⟩⟩
  · intro A_top A_abs alpha
    exact ⟨glueAbstractionCompEquiv A_top A_abs alpha⟩
  · intro C₀
    exact ⟨compFractureGlueEquiv (ConstComp C₀)⟩
  · intro A B f
    ext a
    · exact f.comm a
    · rfl
