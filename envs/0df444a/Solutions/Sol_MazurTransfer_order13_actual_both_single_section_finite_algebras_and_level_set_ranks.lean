-- Prove2me | solution 1 for MazurTransfer.order13_actual_both_single_section_finite_algebras_and_level_set_ranks
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T05:54:05.109613+00:00
-- url     : https://prove2.me/submissions/430634e8-3fc2-4e7c-847e-a226e3b30bc8

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses the original mixed single-section algebra constructions of Vas and contributors,
and the exact official Anthropic FLT quotient/base-change bridge, Apache-2.0,
at pin 6e837e75355538c7f80bab5b956861e86c4eacc2.
Design boundary: original inverse and ordinary parameter algebras have polynomial
rank three; every nontrivial coefficient level set is finite free of rank three.
Named downstream consumer: the actual single-section affine atlas and degree-three
FiniteMapData. The geometric affine-open identification remains separate.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13MixedOriginalRecoveredReciprocalAndSingleSectionPolynomialBasesData20261019
noncomputable section
universe u
open scoped MazurTransfer.Order13MixedInverseParameterFiniteAlgebra MazurTransfer.Order13MixedSingleSectionFiniteAlgebra
namespace MazurTransfer.OriginalSingleSectionFiniteAlgebraRanksInterface20261019
end MazurTransfer.OriginalSingleSectionFiniteAlgebraRanksInterface20261019
theorem solution : (∀ (R : Type u) [CommRing R] [IsDomain R], Module.Free (Polynomial R) (MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.candidateAlgebra R)) ∧ (∀ (R : Type u) [CommRing R] [IsDomain R], Module.finrank (Polynomial R) (MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.candidateAlgebra R) = 3) ∧ (∀ (R : Type u) [CommRing R] [IsDomain R] (S : Type u) [CommRing S] [Algebra R S] [Nontrivial S] (s : S), Module.Finite S (MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.levelSet R S s) ∧ Module.Free S (MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.levelSet R S s) ∧ Module.finrank S (MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.levelSet R S s) = 3) ∧ (∀ (R : Type u) [CommRing R] [IsDomain R], Module.Free (Polynomial R) (MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.candidateAlgebra R)) ∧ (∀ (R : Type u) [CommRing R] [IsDomain R], Module.finrank (Polynomial R) (MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.candidateAlgebra R) = 3) ∧ (∀ (R : Type u) [CommRing R] [IsDomain R] (S : Type u) [CommRing S] [Algebra R S] [Nontrivial S] (s : S), Module.Finite S (MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.levelSet R S s) ∧ Module.Free S (MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.levelSet R S s) ∧ Module.finrank S (MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.levelSet R S s) = 3) := by
  exact ⟨MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.candidateAlgebra_free,MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.candidateAlgebra_finrank,MazurTransfer.Order13MixedInverseParameterFiniteAlgebra.levelSet_finite_free_finrank,MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.candidateAlgebra_free,MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.candidateAlgebra_finrank,MazurTransfer.Order13MixedSingleSectionFiniteAlgebra.levelSet_finite_free_finrank⟩
#print axioms solution
