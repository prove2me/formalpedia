-- Prove2me | solution 1 for HofmannStreicher1994.semantic_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T07:30:57.046993+00:00
-- url     : https://prove2.me/submissions/027a2bcf-bc7e-4e02-8f88-46b07bdac9f8

import Definitions.Def_HofmannStreicher1994_Groupoids
open CategoryTheory HofmannStreicher1994

theorem hs_loop_ne : (counterexampleLoop : counterexampleObject ⟶ counterexampleObject) ≠ 𝟙 counterexampleObject := by
  intro h
  have h2 := congrArg (fun f : counterexampleObject ⟶ counterexampleObject =>
    (show Equiv.Perm Bool from match f with | CategoryTheory.Sigma.SigmaHom.mk g => g)) h
  have h3 : Equiv.swap false true = (1 : Equiv.Perm Bool) := h2
  have := congrArg (fun e : Equiv.Perm Bool => e false) h3
  simp at this

theorem solution :
    ¬ SemanticUIP UniverseTotal.{0} ∧ ¬ SemanticBasedUIP UniverseTotal.{0} := by
  have key : ¬ Nonempty ((Discrete.mk counterexampleLoop : Discrete (counterexampleObject ⟶ counterexampleObject)) ⟶
      Discrete.mk (𝟙 counterexampleObject)) := by
    rintro ⟨f⟩
    exact hs_loop_ne (Discrete.eq_of_hom f)
  exact ⟨fun H => key (H counterexampleObject counterexampleObject _ _),
    fun H => key (H counterexampleObject counterexampleLoop)⟩

