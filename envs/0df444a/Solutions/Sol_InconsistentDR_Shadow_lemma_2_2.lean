-- Prove2me | solution 1 for InconsistentDR.Shadow.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:50:13.507903+00:00
-- url     : https://prove2.me/submissions/aec2a617-c85b-4edb-9ef5-cd35141920f4

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_InconsistentDR_Shadow_Operators

open InconsistentDR.Shadow

open scoped InnerProductSpace
open ThreeOpSplitting.Convergence


theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (A B : X → Set X) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (JA JB : X → X) (hJA : IsResolvent 1 A JA) (hJB : IsResolvent 1 B JB) (x : X) :
    (JA x - JA (drT JA JB x) = resInv JA (drT JA JB x) + resInv JB (refl JA x) ∧
      JA x - JA (drT JA JB x) ∈ setR A B) ∧
    (resInv JA x - resInv JA (drT JA JB x) = JA (drT JA JB x) - JB (refl JA x) ∧
      resInv JA x - resInv JA (drT JA JB x) ∈ setD A B) := by
  have hA1 : ∀ y, y - JA y ∈ A (JA y) := fun y => by simpa using hJA y
  have hB1 : ∀ y, y - JB y ∈ B (JB y) := fun y => by simpa using hJB y
  have e1 : JA x - JA (drT JA JB x) = resInv JA (drT JA JB x) + resInv JB (refl JA x) := by
    simp only [drT, InconsistentDR.Shadow.refl, resInv]; module
  have e2 : resInv JA x - resInv JA (drT JA JB x) = JA (drT JA JB x) - JB (refl JA x) := by
    simp only [drT, InconsistentDR.Shadow.refl, resInv]; module
  refine ⟨⟨e1, ?_⟩, ⟨e2, ?_⟩⟩
  · rw [e1]
    exact Set.add_mem_add ⟨_, hA1 _⟩ ⟨_, hB1 _⟩
  · rw [e2]
    exact Set.sub_mem_sub ⟨_, hA1 _⟩ ⟨_, hB1 _⟩
