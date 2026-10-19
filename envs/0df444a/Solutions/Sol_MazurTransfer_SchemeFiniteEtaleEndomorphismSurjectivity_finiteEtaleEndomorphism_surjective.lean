-- Prove2me | solution 1 for MazurTransfer.SchemeFiniteEtaleEndomorphismSurjectivity.finiteEtaleEndomorphism_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T20:34:48.304953+00:00
-- url     : https://prove2.me/submissions/61fb2ad2-0de4-4785-84c2-02fe6a17a7c4

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a finite etale endomorphism of a nonempty connected
scheme is surjective, from its nonempty clopen image.
Named downstream consumer: actual rational Picard norm isogenies.
-/
import Mathlib

open AlgebraicGeometry
universe u

theorem solution {X : Scheme.{u}}
    [PreconnectedSpace X] [Nonempty X] (g : X ⟶ X) [IsFinite g] [Etale g] : Surjective g := by
  refine ⟨?_⟩
  have h : Set.range g = Set.univ :=
    IsClopen.eq_univ ⟨g.isClosedMap.isClosed_range, g.isOpenMap.isOpen_range⟩ (Set.range_nonempty g)
  exact Set.range_eq_univ.mp h


#print axioms solution
