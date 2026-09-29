-- Prove2me | solution 1 for HorizontalPadicL.primitiveCharacters_boundedConductor_finite_v2
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T14:11:49.846851+00:00
-- url     : https://prove2.me/submissions/253df150-bf20-46af-8fb7-512ff86ef721

import Definitions.Def_KN_PrimePowerPropagationV2
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace HorizontalPadicL

private theorem fixedLevelCharacters_finite (n : ℕ) :
    ((fun χ : DirichletCharacterWithLevel => χ.1.1) ⁻¹' ({n} : Set ℕ)).Finite := by
  by_cases hn : 0 < n
  · let g : DirichletCharacter MTT.Qbar n → DirichletCharacterWithLevel :=
      fun χ => ⟨⟨n, hn⟩, χ⟩
    refine (Set.finite_range g).subset ?_
    rintro ⟨⟨m, hm⟩, χ⟩ hχ
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hχ
    subst m
    have hhm : hm = hn := Subsingleton.elim _ _
    subst hm
    exact ⟨χ, rfl⟩
  · have hempty :
        (fun χ : DirichletCharacterWithLevel => χ.1.1) ⁻¹' ({n} : Set ℕ) = ∅ := by
      ext χ
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false,
        iff_false]
      intro h
      exact hn (h ▸ χ.1.2)
    rw [hempty]
    exact Set.finite_empty

theorem _root_.solution (X : ℝ) :
    {χ : DirichletCharacterWithLevel |
      χ.2.IsPrimitive ∧ (χ.2.conductor : ℝ) ≤ X}.Finite := by
  obtain ⟨M, hM⟩ := exists_nat_gt X
  have hlevels : {n : ℕ | (n : ℝ) ≤ X}.Finite := by
    refine (Set.finite_Iio M).subset ?_
    intro n hn
    change (n : ℝ) ≤ X at hn
    change n < M
    exact_mod_cast lt_of_le_of_lt hn hM
  have hpreimage := hlevels.preimage'
    (fun n _ => fixedLevelCharacters_finite n)
  refine hpreimage.subset ?_
  intro χ hχ
  change (χ.1.1 : ℝ) ≤ X
  rw [← hχ.1]
  exact hχ.2

end HorizontalPadicL
