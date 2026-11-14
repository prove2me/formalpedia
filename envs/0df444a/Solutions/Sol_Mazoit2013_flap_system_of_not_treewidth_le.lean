-- Prove2me | solution 1 for Mazoit2013.flap_system_of_not_treewidth_le
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T23:16:29.16648+00:00
-- url     : https://prove2.me/submissions/b3775590-6283-4c14-ad46-024ca75472ab

import Theorems.Thm_Mazoit2013_partial_families_star_and_nonempty
import Theorems.Thm_Mazoit2013_partial_decomposition_gluing
open RobertsonSeymour1986.GM5 StableMSR.Recovery.Havens StableMSR.Recovery.PartialDecompositions
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : ℕ) (hwidth : ¬ TreewidthLE G w) :
    ∃ (F : Finset (Finset V)) (D : Finset (Finset (Finset V))),
      (∀ d ∈ D, d.Nonempty ∧ d ⊆ F) ∧
      (∀ dX ∈ D, ∀ dY ∈ D, ∀ X ∈ dX, ∀ Y ∈ dY, ¬ Touch G X Y →
        ∃ d ∈ D, ∀ Z ∈ d,
          (∃ A ∈ dX, A ≠ X ∧ Z ⊆ A) ∨ (∃ A ∈ dY, A ≠ Y ∧ Z ⊆ A)) ∧
      (∀ W : Finset V, W.card < w+2 →
        ∃ d ∈ D, ∀ X ∈ d, ConnectedSet G X ∧ Disjoint W X)  := by
  classical
  obtain ⟨hne,hstar⟩ := Mazoit2013.partial_families_star_and_nonempty G w hwidth
  refine ⟨Finset.univ,partialFamilies G (w+1),?_,?_,hstar⟩
  · exact fun d hd => ⟨hne d hd,Finset.subset_univ d⟩
  · intro dX hdX dY hdY X hX Y hY hnot
    obtain ⟨d,hd,h⟩ := Mazoit2013.partial_decomposition_gluing G (w+1) dX dY
      (mem_partialFamilies.mp hdX) (mem_partialFamilies.mp hdY) X Y hX hY hnot
    exact ⟨d,mem_partialFamilies.mpr hd,h⟩
