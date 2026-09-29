-- Prove2me | solution 1 for IharaLemma.IdempotentSplitting.finite_cornerRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/0446366e-6ef7-5673-b7f8-c50d5c81a233

import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.RingTheory.Finiteness.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaLemma_IdempotentSplitting_finite_cornerRing

set_option autoImplicit false

private theorem finite_cornerSubmodule_of_finite {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B]
    [Algebra 𝒪 B] {V : Type} [AddCommGroup V] [Module B V] [Module 𝒪 V] [IsScalarTower 𝒪 B V]
    (e : B) [Module.Finite 𝒪 V] :
    Module.Finite 𝒪 ↥(IharaLemma.cornerSubmodule (M := V) e) := by
  have h : (IharaLemma.cornerSubmodule (M := V) e).restrictScalars 𝒪
      = LinearMap.range ((e • (LinearMap.id : V →ₗ[B] V)).restrictScalars 𝒪) := by
    ext v
    simp only [Submodule.restrictScalars_mem, IharaLemma.cornerSubmodule, LinearMap.mem_range,
      LinearMap.coe_restrictScalars]
  rw [show (Module.Finite 𝒪 ↥(IharaLemma.cornerSubmodule (M := V) e))
      = Module.Finite 𝒪 ↥((IharaLemma.cornerSubmodule (M := V) e).restrictScalars 𝒪) from rfl, h]
  exact Module.Finite.range _

open IharaLemma in
theorem solution {𝒪 : Type} [CommRing 𝒪] {B : Type}
    [CommRing B] [Algebra 𝒪 B] (S : IharaLemma.IdempotentSplitting B) (i : Fin S.n)
    [Module.Finite 𝒪 B] : Module.Finite 𝒪 (S.CornerRing i) := by
  haveI : Module.Finite 𝒪 ↥(cornerSubmodule (M := B) (S.e i)) :=
    finite_cornerSubmodule_of_finite (S.e i)
  exact Module.Finite.equiv (S.cornerRingLinearEquiv i 𝒪).symm

end S_IharaLemma_IdempotentSplitting_finite_cornerRing
end P2MW
export P2MW.S_IharaLemma_IdempotentSplitting_finite_cornerRing (solution)
