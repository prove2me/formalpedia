-- Prove2me | solution 1 for IharaLemma.free_cornerSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/65ddc5f7-0277-5eeb-875e-ccc5c5c58c53

import Definitions.Def_IharaLemma_IdempotentSplitting
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.Algebra.Module.Projective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaLemma_free_cornerSubmodule

set_option autoImplicit false

private theorem toCorner_comp_subtype_module {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B]
    [Algebra 𝒪 B] {V : Type} [AddCommGroup V] [Module B V] [Module 𝒪 V] [IsScalarTower 𝒪 B V]
    (e : B) (he : IsIdempotentElem e) :
    ((IharaLemma.toCorner (M := V) e).restrictScalars 𝒪).comp
      ((IharaLemma.cornerSubmodule (M := V) e).subtype.restrictScalars 𝒪) = LinearMap.id := by
  ext x
  obtain ⟨y, hy⟩ := x.2
  simp only [LinearMap.smul_apply, LinearMap.id_apply] at hy
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    Submodule.coe_subtype, LinearMap.id_coe, id_eq, IharaLemma.toCorner_apply]
  rw [← hy, smul_smul, he.eq]

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
theorem solution {𝒪 : Type} [CommRing 𝒪] {B : Type} [CommRing B]
    [Algebra 𝒪 B] {V : Type} [AddCommGroup V] [Module B V] [Module 𝒪 V] [IsScalarTower 𝒪 B V]
    (e : B) (he : IsIdempotentElem e) [IsLocalRing 𝒪] [Module.Finite 𝒪 V] [Module.Free 𝒪 V] :
    Module.Free 𝒪 ↥(IharaLemma.cornerSubmodule (M := V) e) := by
  haveI : Module.Projective 𝒪 ↥(cornerSubmodule (M := V) e) :=
    Module.Projective.of_split
      ((cornerSubmodule (M := V) e).subtype.restrictScalars 𝒪)
      ((toCorner (M := V) e).restrictScalars 𝒪)
      (toCorner_comp_subtype_module (𝒪 := 𝒪) e he)
  haveI : Module.Finite 𝒪 ↥(cornerSubmodule (M := V) e) :=
    finite_cornerSubmodule_of_finite e
  exact Module.free_of_flat_of_isLocalRing

end S_IharaLemma_free_cornerSubmodule
end P2MW
export P2MW.S_IharaLemma_free_cornerSubmodule (solution)
