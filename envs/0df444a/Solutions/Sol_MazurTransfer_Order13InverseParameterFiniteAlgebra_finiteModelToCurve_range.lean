-- Prove2me | solution 1 for MazurTransfer.Order13InverseParameterFiniteAlgebra.finiteModelToCurve_range
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T06:29:13.547353+00:00
-- url     : https://prove2.me/submissions/0f16e664-6056-4e39-98ac-fc3bfa886f57

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the original global inverse comparison has exactly the union of its two actual chart images.
Named downstream consumer: the actual affine-open inverse-chart isomorphism. Original proof body retained. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13InverseFiniteModelToCurve
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13InverseParameterFiniteAlgebra
theorem solution (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (h104 : IsUnit (104 : R)) :
    Set.range (finiteModelToCurve R h104) =
      Set.range (ordinaryParameterCurveMap R) ∪ Set.range (positiveReciprocalCurveMap R) := by
  ext q
  constructor
  · rintro ⟨p,rfl⟩
    have hp : p ∈ Set.range (ordinaryParameterToFiniteAffineScheme R) ∪
        Set.range (reciprocalToFiniteAffineScheme R h104) := by
      rw [finiteScheme_two_chart_range_cover]
      trivial
    rcases hp with ⟨a,rfl⟩ | ⟨a,rfl⟩
    · rw [← Scheme.Hom.comp_apply,ordinaryParameterToFiniteAffineScheme_finiteModelToCurve]
      exact Or.inl ⟨a,rfl⟩
    · rw [← Scheme.Hom.comp_apply,reciprocalToFiniteAffineScheme_finiteModelToCurve]
      exact Or.inr ⟨a,rfl⟩
  · rintro (⟨a,rfl⟩ | ⟨a,rfl⟩)
    · refine ⟨ordinaryParameterToFiniteAffineScheme R a,?_⟩
      rw [← Scheme.Hom.comp_apply,ordinaryParameterToFiniteAffineScheme_finiteModelToCurve]
    · refine ⟨reciprocalToFiniteAffineScheme R h104 a,?_⟩
      rw [← Scheme.Hom.comp_apply,reciprocalToFiniteAffineScheme_finiteModelToCurve]
#print axioms solution
