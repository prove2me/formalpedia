-- Prove2me | solution 1 for MazurTransfer.original_cyclic_character_conjugation
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T22:10:29.59327+00:00
-- url     : https://prove2.me/submissions/94e10cdf-bd1f-409a-814b-a10140189f5b

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: conjugate the given cyclic group automorphism through its fixed isomorphism, preserving compatibility with every original character.
Named downstream consumer: normalization of the same selected integral mu19 quotient arithmetic point label by its original bialgebra automorphism.
-/
import Definitions.Def_MazurTransfer_OriginalCyclicCharacterConjugationData20261020
open MazurTransfer.CyclicCharacterConjugation
namespace MazurTransfer.OriginalCyclicCharacterConjugationBoundary20261020
end MazurTransfer.OriginalCyclicCharacterConjugationBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: conjugating a cyclic-group automorphism through a fixed
isomorphism commutes with EVERY character, retaining the fixed isomorphism.
Named downstream consumer: normalization of the selected integral mu19
quotient's existing arithmetic point label by a bialgebra automorphism.
-/

namespace MazurTransfer.OriginalCyclicCharacterConjugationProof20261020
variable {C P : Type} [Group C] [Group P] [IsCyclic P]



theorem character_conjugate (r : C ≃* P) (α : P ≃* P) (χ : C →* P) (c : C) :
    χ (conjugate r α c) = α (χ c) := by
  obtain ⟨j, hj⟩ := MonoidHom.map_cyclic α.toMonoidHom
  have hc : conjugate r α c = c ^ j := by
    apply r.injective
    change r (r.symm (α (r c))) = r (c ^ j)
    rw [MulEquiv.apply_symm_apply, map_zpow]
    exact hj (r c)
  rw [hc, map_zpow]
  exact (hj (χ c)).symm

end MazurTransfer.OriginalCyclicCharacterConjugationProof20261020

theorem solution : ∀ {C P : Type} [Group C] [Group P] [IsCyclic P], ∀ (r : C ≃* P) (α : P ≃* P) (χ : C →* P) (c : C),
χ (conjugate r α c) = α (χ c) := by
  exact MazurTransfer.OriginalCyclicCharacterConjugationProof20261020.character_conjugate
#print axioms solution
