-- Prove2me | solution 1 for Module.Flat.projective_ker_and_bijective_kerBaseChangeHom_of_forall_ker_baseChange_le_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/0ae614d5-6f9e-5c98-9d23-bdb398459105

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Theorems.Thm_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range
import Theorems.Thm_Module_Flat_flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Module_Flat_projective_ker_and_bijective_kerBaseChangeHom_of_forall_ker_baseChange_le_range

set_option autoImplicit false

universe u

open TensorProduct

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype))
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K] (i : ℕ),
      LinearMap.ker ((d (i + 1)).baseChange K) ≤ LinearMap.range ((d i).baseChange K)) :
    Module.Projective R (LinearMap.ker (d 0)) ∧
      (∀ (A : Type u) [CommRing A] [Algebra R A],
        Function.Bijective (TwoChartCech.kerBaseChangeHom (d 0) A)) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A] (i : ℕ),
        LinearMap.ker ((d (i + 1)).baseChange A) ≤ LinearMap.range ((d i).baseChange A) := by
  have hex : ∀ i : ℕ, LinearMap.ker (d (i + 1)) ≤ LinearMap.range (d i) :=
    Module.Flat.ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range C d hdd n hbd hfin
      (fun 𝔪 _ i => by letI := Ideal.Quotient.field 𝔪; exact hfib (R ⧸ 𝔪) i)
  obtain ⟨hflat, hbij, hc⟩ :=
    Module.Flat.flat_ker_and_bijective_kerBaseChangeHom_of_forall_ker_le_range C d hdd n hbd hex
  refine ⟨?_, hbij, hc⟩
  haveI := hflat
  haveI := hfin0
  haveI : Module.FinitePresentation R ↥(LinearMap.ker (d 0)) := Module.finitePresentation_of_finite R _
  exact Module.Flat.projective_of_finitePresentation

end S_Module_Flat_projective_ker_and_bijective_kerBaseChangeHom_of_forall_ker_baseChange_le_range
end P2MW
export P2MW.S_Module_Flat_projective_ker_and_bijective_kerBaseChangeHom_of_forall_ker_baseChange_le_range (solution)
